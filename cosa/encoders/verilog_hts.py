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

VPARSER = True

try:
    from pyverilog.vparser.parser import parse
    from pyverilog.vparser.ast import *
except:
    VPARSER = False

from pysmt.shortcuts import Symbol, BV, simplify, \
    TRUE, FALSE, \
    And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, get_type
from pysmt.typing import BOOL, BVType, ArrayType

from cosa.utils.logger import Logger
from cosa.encoders.template import ModelParser
from cosa.walkers.verilog_walker import VerilogWalker
from cosa.representation import HTS, TS

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
    hts = None
    ts = None
    
    def __init__(self):
        self.hts = HTS()
        self.ts = TS()

    def Paramlist(self, el, args):
        return el

    def Port(self, el, args):
        if el.width is None:
            self.varmap[el.name] = (el.width, el.type)
        return el

    def Portlist(self, el, args):
        return args

    def Wire(self, el, args):
        return el

    def Reg(self, el, args):
        return el
    
    def Decl(self, el, args):
        (width, typ) = args
        width = 1 if width is None else width[0]
        prev_width = self.varmap[typ.name][0]
        if (prev_width is not None) and (prev_width != width):
            Logger.error("Unmatched variable size at line %d"%el.lineno)
        
        var = Symbol(typ.name, BVType(width))

        direction = el.children()[0]
        if type(direction) == Input:
            self.ts.add_input_var(var)
        elif type(direction) == Output:
            self.ts.add_output_var(var)
        else:
            self.ts.add_state_var(var)

        self.varmap[typ.name] = var
            
        return var

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
        return EqualsOrIff(TS.to_next(args[0]), args[1])
    
    def SensList(self, el, args):
        return And(args)
    
    def IntConst(self, el, args):
        if "'d" in el.value:
            width, value = el.value.split("'d")
            return BV(int(value), int(width))
        
        return int(el.value)

    def Identifier(self, el, args):
        return self.varmap[el.name]
    
    def Width(self, el, args):
        return (args[0] - args[1])+1

    def Input(self, el, args):
        return args
    
    def Output(self, el, args):
        return args

    def Block(self, el, args):
        return And(args)

    def IfStatement(self, el, args):
        one = BV(1, get_type(args[0]).width)
        return Ite(EqualsOrIff(args[0], one), args[1], args[2])

    def Always(self, el, args):
        return Implies(args[0], args[1])

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
