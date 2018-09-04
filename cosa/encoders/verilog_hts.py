# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import re
import os
import math

VPARSER = True

try:
    from pyverilog.vparser.parser import parse
    from pyverilog.vparser.ast import *
except:
    VPARSER = False

from pysmt.shortcuts import Symbol, BV, simplify, TRUE, FALSE, get_type, get_model
from pysmt.shortcuts import And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, BVExtract, BVAdd, BVConcat, BVULT
from pysmt.fnode import FNode
from pysmt.typing import BOOL, BVType, ArrayType, INT

from cosa.utils.logger import Logger
from cosa.encoders.template import ModelParser
from cosa.walkers.verilog_walker import VerilogWalker
from cosa.representation import HTS, TS
from cosa.utils.generic import bin_to_dec
from cosa.utils.formula_mngm import BV2B, get_free_variables

KEYWORDS = ""
KEYWORDS += "module wire assign else reg always endmodule end define integer generate "
KEYWORDS += "for localparam begin input output parameter posedge negedge or and if"
KEYWORDS = KEYWORDS.split()

POSEDGE = "posedge"
NEGEDGE = "negedge"

class VerilogParser(ModelParser):
    parser = None
    extensions = ["v"]
    name = "Verilog"

    files_from_dir = False
    
    def __init__(self):
        self.walker = VerilogSTSWalker()

    def is_available(self):
        return VPARSER

    def parse_file(self, strfile, flags=None):
        invar_props = []
        ltl_props = []
        
        absstrfile = os.path.abspath(strfile)
        ast, directives = parse([absstrfile])
        hts = self.walker.walk(ast)
        return (hts, invar_props, ltl_props)

    def get_extensions(self):
        return self.extensions

    @staticmethod        
    def get_extensions():
        return VerilogParser.extensions

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name

class VerilogSTSWalker(VerilogWalker):
    varmap = {}
    paramdic = {}
    hts = None
    ts = None

    id_vars = 0
    
    def __init__(self):
        self.hts = HTS()
        self.ts = TS()

    def _fresh_symbol(self, name):
        VerilogSTSWalker.id_vars += 1
        return "%s__%d"%(name, VerilogSTSWalker.id_vars)
        
    def Paramlist(self, el, args):
        return el

    def Port(self, el, args):
        if el.width is None:
            self.varmap[el.name] = (el.width, el.type)
        return el

    def Portlist(self, el, args):
        return args

    def Decl(self, el, args):
        if args[0] == None:
            return args

        direction = el.children()[0]

        if type(direction) in [Input, Output]:
            width = args[0][1]
            typ = el.children()[0]

            width = 1 if width is None else width[0]

            if typ.name in self.varmap:
                prev_width = self.varmap[typ.name][0]
                if (prev_width is not None) and (prev_width != width):
                    Logger.error("Unmatched variable size at line %d"%el.lineno)

            var = Symbol(typ.name, BVType(width))

            if type(direction) == Input:
                self.ts.add_input_var(var)
            elif type(direction) == Output:
                self.ts.add_output_var(var)
            else:
                self.ts.add_state_var(var)

            self.varmap[typ.name] = var

            return var

        if type(direction) == RegArray:
            low, high = args[0][1][1], args[0][1][0]
            width = args[0][0]
            vname = el.children()[0].name
            var_idxs = []
            for i in range(low, high+1, 1):
                vname_idx = "%s_%d"%(vname, i)
                var_idx = Symbol(vname_idx, BVType(width))
                var_idxs.append(var_idx)
                self.varmap[vname] = (vname, (low, high))
                self.varmap[vname_idx] = var_idx
            return var_idxs
        
        Logger.error("Unmanaged type %s"%type(direction))
        
    def Sens(self, el, args):
        var = self.varmap[el.sig.name]

        zero = BV(0, var.symbol_type().width)
        one = BV(1, var.symbol_type().width)
        
        if el.type == POSEDGE:
            return And(EqualsOrIff(var, zero), EqualsOrIff(TS.get_prime(var), one))

        if el.type == NEGEDGE:
            return And(EqualsOrIff(var, one), EqualsOrIff(TS.get_prime(var), zero))

        Logger.error("Unknown driver at line %d"%el.lineno)

    def Lvalue(self, el, args):
        return args[0]

    def Rvalue(self, el, args):
        return args[0]

    def NonblockingSubstitution(self, el, args):
        value = args[1]
        if type(value) == int:
            value = BV(value, get_type(args[0]).width)

        return EqualsOrIff(TS.to_next(args[0]), value)

    def BlockingSubstitution(self, el, args):
        left, right = args[0], args[1]
        if type(left) == int:
            left = BV(left, 32)
        if type(right) == int:
            right = BV(right, 32)
        return EqualsOrIff(left, right)

    def SensList(self, el, args):
        return And(args)

    def Integer(self, el, args):
        self.varmap[el.name] = Symbol(el.name, BVType(32))
        return None
    
    def IntConst(self, el, args):
        if "'d" in el.value:
            width, value = el.value.split("'d")
            if width == "":
                return int(value)
            return BV(int(value), int(width))

        if "'b" in el.value:
            width, value = el.value.split("'b")
            if width == "":
                return int(bin_to_dec(value))
            return BV(int(bin_to_dec(value)), int(width))
        
        return int(el.value)

    def Identifier(self, el, args):
        if el.name in self.paramdic:
            return self.paramdic[el.name]
        if el.name in self.varmap:
            return self.varmap[el.name]

        return el.name
    
    def Width(self, el, args):
        return (args[0] - args[1])+1

    def Input(self, el, args):
        return (el.name, args)
    
    def Output(self, el, args):
        return (el.name, args)

    def Wire(self, el, args):
        return (el.name, args)

    def Reg(self, el, args):
        return (el.name, args)
    
    def Block(self, el, args):
        return And(args)

    def IfStatement(self, el, args):
        if type(args[1]) == list:
            # statements
            pass
        else:

            if type(args[0]) == int:
                condition = TRUE() if args[0] == 1 else FALSE()
            elif get_type(args[0]) == BOOL:
                condition = args[0]
            else:
                one = BV(1, get_type(args[0]).width)
                condition = EqualsOrIff(args[0], one)

            if len(args) == 2:
                return Implies(condition, args[1])
            else:
                return Ite(condition, args[1], args[2])

    def Always(self, el, args):
        return Implies(args[0], args[1])

    def ForStatement(self, el, args):
        
        print(get_free_variables(args[0]))
        fv = get_free_variables(args[0])
        init_model = get_model(args[0])
        state_c = And([EqualsOrIff(v, init_model[v]) for v in fv])
        state_n = And([EqualsOrIff(TS.to_next(v), init_model[v]) for v in fv])
        state = And(state_c, state_n)
        formulae = []
        while True:
            print(state)
            formula = simplify(And(state, args[3]))
            print(get_free_variables(simplify(formula)))
            print(formula)
            formulae.append(formula)
            quit(0)
        
        quit(0)

        
        print(args)
        quit(0)
    
    def ModuleDef(self, el, args):
        children = list(el.children())
        always_ids = [children.index(a) for a in children if isinstance(a, Always)]
        always = And([args[i] for i in always_ids])
        self.ts.trans = always
        self.hts.add_ts(self.ts)
        return self.hts

    def Description(self, el, args):
        return args[0]

    def Source(self, el, args):
        return args[0]

    # TODO: Fix operations to manage both ints and BV
    def Divide(self, el, args):
        return int(int(args[0])/int(args[1]))

    def Minus(self, el, args):
        return int(args[0])-int(args[1])

    def Plus(self, el, args):
        left, right = args[0], args[1]

        if type(right) == int:
            right = BV(right, 32)
        
        if (type(left) == int) and (type(right) == int):
            return left+right
        
        if type(right) == int:
            right = BV(right, get_type(left).width)
        return BVAdd(left, right)
    
    def Eq(self, el, args):
        return EqualsOrIff(args[0], args[1])

    def NotEq(self, el, args):
        return Not(EqualsOrIff(args[0], args[1]))

    def And(self, el, args):
        return And([BV2B(x) for x in args])

    def LessThan(self, el, args):
        left, right = args[0], args[1]
        if type(right) == int:
            right = BV(right, 32)
        return BVULT(left, right)
             
    def Ulnot(self, el, args):
        zero = BV(0, args[0].symbol_type().width)
        return EqualsOrIff(args[0], zero)

    def Unot(self, el, args):
        return self.Ulnot(el, args)
    
    def Parameter(self, el, args):
        self.paramdic[el.name] = args[0]
        return None

    def SystemCall(self, el, args):
        if el.syscall == "clog2":
            return math.ceil(math.log(args[0])/math.log(2))

    def Ioport(self, el, args):
        return self.Decl(el, args)

    def Partselect(self, el, args):
        return BVExtract(args[0], args[2], args[1])

    def Assign(self, el, args):
        return el

    def _mem_access(self, address, locations, width, idx=0):
        if len(locations) == 1:
            return locations[0]
        location = BV(idx, width)
        return Ite(EqualsOrIff(address, location), locations[0], self._mem_access(address, locations[1:], width, idx+1))
    
    def Pointer(self, el, args):
        if type(args[0]) == tuple:
            width = get_type(args[1]).width
            mem_size = args[0][1]
            mem_locations = ["%s_%d"%(args[0][0], i) for i in range(mem_size[0], mem_size[1]+1)]
            return self._mem_access(args[1], [self.varmap[v] for v in mem_locations], width)

        if type(args[1]) == FNode:
            width = get_type(args[1]).width
            mem_locations = [BVExtract(args[0], i, i) for i in range(width)]
            return self._mem_access(args[1], mem_locations, width)
        
        return BVExtract(args[0], args[1], args[1])

    def Concat(self, el, args):
        return args

    def _rec_repeat(self, el, count):
        if count == 1:
            return el
        return simplify(BVConcat(el, self._rec_repeat(el, count-1)))
    
    def Repeat(self, el, args):
        return self._rec_repeat(args[0][0], args[1])
    
    def PortArg(self, el, args):
        return args

    def Instance(self, el, args):
        return args

    def InstanceList(self, el, args):
        return args

    def ParamArg(self, el, args):
        return args

    def StringConst(self, el, args):
        return el.value

    def Localparam(self, el, args):
        return self.Parameter(el, args)

    def GenerateStatement(self, el, args):
        return args

    def Length(self, el, args):
        return args

    def RegArray(self, el, args):
        return args
