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

from pysmt.shortcuts import Symbol, BV, simplify, TRUE, FALSE, get_type, get_model, is_sat
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

        if flags is None:
            Logger.error("Module name not provided")
        
        absstrfile = os.path.abspath(strfile)
        ast, directives = parse([absstrfile])
        hts = self.walker.walk(ast, "")
        hts.flatten()
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
    varmap = None
    paramdic = None
    subhtsdic = None
    hts = None
    ts = None

    id_vars = 0
    
    def __init__(self):
        self.reset_structures()

    def reset_structures(self, modulename=""):
        self.hts = HTS(modulename)
        self.ts = TS()
        self.varmap = {}
        self.paramdic = {}
        self.subhtsdic = {}
        
    def _fresh_symbol(self, name):
        VerilogSTSWalker.id_vars += 1
        return "%s__%d"%(name, VerilogSTSWalker.id_vars)

    def varname(self, modulename, varname):
        if modulename == "":
            return varname
        return "%s.%s"%(modulename, varname)
    
    def Paramlist(self, modulename, el, args):
        return el

    def Port(self, modulename, el, args):
        if el.width is None:
            self.varmap[el.name] = (el.width, el.type)
        return el

    def Portlist(self, modulename, el, args):
        paramlist = [(v.symbol_name(), v) for v in args]
        paramlist.sort()
        for param in paramlist:
            self.hts.add_param(param[1])
        
        return args

    def Decl(self, modulename, el, args):
        if args[0] == None:
            return args

        direction = el.children()[0]

        if type(direction) in [Input, Output, Reg, Wire]:
            width = args[0][1]
            typ = el.children()[0]

            width = 1 if width is None else width[0]

            if typ.name in self.varmap:
                prev_width = self.varmap[typ.name][0] if type(self.varmap[typ.name]) is not FNode else self.varmap[typ.name].symbol_type().width
                if (prev_width is not None) and (prev_width != width):
                    Logger.error("Unmatched variable size at line %d"%el.lineno)

            var = Symbol(self.varname(modulename, typ.name), BVType(width))

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
                var_idx = Symbol(self.varname(modulename, vname_idx), BVType(width))
                var_idxs.append(var_idx)
                self.varmap[vname] = (vname, (low, high))
                self.varmap[vname_idx] = var_idx
                self.ts.add_state_var(var_idx)
            return var_idxs
        
        Logger.error("Unmanaged type %s"%type(direction))
        
    def Sens(self, modulename, el, args):
        var = self.varmap[el.sig.name]

        zero = BV(0, var.symbol_type().width)
        one = BV(1, var.symbol_type().width)
        
        if el.type == POSEDGE:
            return And(EqualsOrIff(var, zero), EqualsOrIff(TS.get_prime(var), one))

        if el.type == NEGEDGE:
            return And(EqualsOrIff(var, one), EqualsOrIff(TS.get_prime(var), zero))

        Logger.error("Unknown driver at line %d"%el.lineno)

    def Lvalue(self, modulename, el, args):
        return args[0]

    def Rvalue(self, modulename, el, args):
        return args[0]

    def NonblockingSubstitution(self, modulename, el, args):
        value = args[1]
        if type(value) == int:
            value = BV(value, get_type(args[0]).width)

        return EqualsOrIff(TS.to_next(args[0]), value)

    def BlockingSubstitution(self, modulename, el, args):
        left, right = args[0], args[1]
        if type(left) == int:
            left = BV(left, 32)
        if type(right) == int:
            right = BV(right, 32)
        return EqualsOrIff(TS.to_next(left), right)

    def SensList(self, modulename, el, args):
        return And(args)

    def Integer(self, modulename, el, args):
        self.varmap[el.name] = Symbol(self.varname(modulename, el.name), BVType(32))
        return None
    
    def IntConst(self, modulename, el, args):
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

    def Identifier(self, modulename, el, args):
        if el.name in self.paramdic:
            return self.paramdic[el.name]
        if el.name in self.varmap:
            return self.varmap[el.name]

        return el.name
    
    def Width(self, modulename, el, args):
        return (args[0] - args[1])+1

    def Input(self, modulename, el, args):
        return (el.name, args)
    
    def Output(self, modulename, el, args):
        return (el.name, args)

    def Wire(self, modulename, el, args):
        return (el.name, args)

    def Reg(self, modulename, el, args):
        return (el.name, args)
    
    def Block(self, modulename, el, args):
        return And(args)

    def IfStatement(self, modulename, el, args):
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

    def Always(self, modulename, el, args):
        fv = [v for v in get_free_variables(args[1]) if not TS.is_prime(v)]
        frame_cond = And([EqualsOrIff(v, TS.get_prime(v)) for v in fv])
        active = Implies(args[0], args[1])
        passive = Implies(Not(args[0]), frame_cond)
        
        return And(active, passive)

    def ForStatement(self, modulename, el, args):
        fv = get_free_variables(args[0])
        model = get_model(args[0])
        state_n = [(v, model[v]) for v in fv]
        state_c = [(TS.get_ref_var(v), model[v]) for v in fv]
        state = dict(state_c + state_n)
        formulae = []
        while True:
            # Evaluate new instance
            formula = simplify(args[3].substitute(state))
            formulae.append(formula)

            # Compute next step
            model = get_model(And(And([EqualsOrIff(v[0], v[1]) for v in state_c]), args[2]))
            state_n = [(v, model[v]) for v in fv]
            state_c = [(TS.get_ref_var(v), model[v]) for v in fv]
            state = dict(state_c + state_n)

            # Exit condition
            if not is_sat(And(And([EqualsOrIff(v[0], v[1]) for v in state_c]), args[1])):
                break

        return And(formulae)
    
    def ModuleDef(self, modulename, el, args):
        children = list(el.children())
        always_ids = [children.index(a) for a in children if isinstance(a, Always)]
        always = And([args[i] for i in always_ids])
        self.ts.trans = always
        self.hts.add_ts(self.ts)
        return self.hts

    def Description(self, modulename, el, args):
        return args[0]

    def Source(self, modulename, el, args):
        return args[0]

    # TODO: Fix operations to manage both ints and BV
    def Divide(self, modulename, el, args):
        return int(int(args[0])/int(args[1]))

    def Minus(self, modulename, el, args):
        return int(args[0])-int(args[1])

    def Plus(self, modulename, el, args):
        left, right = args[0], args[1]

        if (type(left) == int) and (type(right) == int):
            return left+right
        
        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)

        if (type(right) == int):
            right = BV(right, 32)
                    
        return BVAdd(left, right)
    
    def Eq(self, modulename, el, args):
        return EqualsOrIff(args[0], args[1])

    def NotEq(self, modulename, el, args):
        return Not(EqualsOrIff(args[0], args[1]))

    def And(self, modulename, el, args):
        return And([BV2B(x) for x in args])

    def LessThan(self, modulename, el, args):
        left, right = args[0], args[1]
        if type(right) == int:
            right = BV(right, 32)
        return BVULT(left, right)
             
    def Ulnot(self, modulename, el, args):
        zero = BV(0, args[0].symbol_type().width)
        return EqualsOrIff(args[0], zero)

    def Unot(self, modulename, el, args):
        return self.Ulnot(modulename, el, args)
    
    def Parameter(self, modulename, el, args):
        if el.name not in self.paramdic:
            self.paramdic[el.name] = args[0]
        return None

    def SystemCall(self, modulename, el, args):
        if el.syscall == "clog2":
            return math.ceil(math.log(args[0])/math.log(2))

    def Ioport(self, modulename, el, args):
        return self.Decl(modulename, el, args)

    def Partselect(self, modulename, el, args):
        return BVExtract(args[0], args[2], args[1])

    def Assign(self, modulename, el, args):
        invar = EqualsOrIff(args[0], args[1])
        self.ts.invar = And(self.ts.invar, invar)
        return el

    def _mem_access(self, address, locations, width, idx=0):
        if len(locations) == 1:
            return locations[0]
        location = BV(idx, width)
        return Ite(EqualsOrIff(address, location), locations[0], self._mem_access(address, locations[1:], width, idx+1))
    
    def Pointer(self, modulename, el, args):
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

    def Concat(self, modulename, el, args):
        return args

    def _rec_repeat(self, el, count):
        if count == 1:
            return el
        return simplify(BVConcat(el, self._rec_repeat(el, count-1)))
    
    def Repeat(self, modulename, el, args):
        return self._rec_repeat(args[0][0], args[1])
    
    def PortArg(self, modulename, el, args):
        return (el.portname, args[0])

    def Instance(self, modulename, el, args):
        el_child = el.children()
        paramargs_idx = [el_child.index(p) for p in el_child if type(p) == ParamArg]
        portargs_idx = [el_child.index(p) for p in el_child if type(p) == PortArg]
        width_idx = [el_child.index(p) for p in el_child if type(p) == Width]

        portargs = [args[i] for i in portargs_idx]
        portargs.sort()
        paramargs = [args[i] for i in paramargs_idx]
        paramargs.sort()
        width = args[width_idx[0]] if len(width_idx) > 0 else None

        if el.module not in self.subhtsdic:
            instancewalker = VerilogSTSWalker()
            subhts = instancewalker.walk(self.modulesdic[el.module], el.module)
            self.subhtsdic[el.module] = subhts

        subhts = self.subhtsdic[el.module]

        self.hts.add_sub(el.name, subhts, tuple([a[1].symbol_name() for a in portargs]))
        return args

    def InstanceList(self, modulename, el, args):
        return args

    def ParamArg(self, modulename, el, args):
        return (el.paramname, args[0])

    def StringConst(self, modulename, el, args):
        return el.value

    def Localparam(self, modulename, el, args):
        return self.Parameter(modulename, el, args)

    def GenerateStatement(self, modulename, el, args):
        return args

    def Length(self, modulename, el, args):
        return args

    def RegArray(self, modulename, el, args):
        return args
