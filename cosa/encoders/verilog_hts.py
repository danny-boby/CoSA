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
from pysmt.shortcuts import And, Implies, Iff, Not, BVAnd, EqualsOrIff, Ite, Or, Xor, BVExtract, BVAdd, BVConcat, BVULT, BVXor, BVOr
from pysmt.fnode import FNode
from pysmt.typing import BOOL, BVType, ArrayType, INT
from pysmt.rewritings import conjunctive_partition

from cosa.utils.logger import Logger
from cosa.encoders.template import ModelParser
from cosa.walkers.verilog_walker import VerilogWalker
from cosa.representation import HTS, TS
from cosa.utils.generic import bin_to_dec
from cosa.utils.formula_mngm import B2BV, BV2B, get_free_variables

KEYWORDS = ""
KEYWORDS += "module wire assign else reg always endmodule end define integer generate "
KEYWORDS += "for localparam begin input output parameter posedge negedge or and if"
KEYWORDS = KEYWORDS.split()

MAXINT = 64

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
        hts = self.walker.walk(ast, flags[0])
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
    modulesdic = None
    hts = None
    ts = None

    id_vars = 0
    
    def __init__(self):
        self.reset_structures()

    def reset_structures(self, modulename=""):
        self.hts = HTS(modulename)
        self.ts = TS()
        self.subhtsdic = {}
        if self.varmap is None: self.varmap = {}
        if self.paramdic is None: self.paramdic = {}
        if self.modulesdic is None: self.modulesdic = {} 
        
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
            self.add_var(modulename, el.name, (el.width, el.type))
            #self.varmap[el.name] = (el.width, el.type)
        return el

    def Portlist(self, modulename, el, args):
        paramlist = [(v.symbol_name(), v) for v in args]
        paramlist.sort()
        for param in paramlist:
            self.hts.add_param(param[1])
        
        return args

    def add_var(self, modulename, varname, value):
        self.varmap[varname] = value
    
    def Decl(self, modulename, el, args):
        if args[0] == None:
            return args

        direction = el.children()[0]

        if type(direction) in [Input, Output, Reg, Wire]:
            width = args[0][1]
            typ = el.children()[0]

            # Setting variable width according with previous values
            if width is None:
                if (typ.name in self.varmap):
                    var_inmap = self.varmap[typ.name]
                    if type(var_inmap) == tuple:
                        width = var_inmap[0]
                    else:
                        width = var_inmap.symbol_type().width
                else:
                    width = 1
            else:
                width = width[0]
            
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

            self.add_var(modulename, typ.name, var)

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
                self.add_var(modulename, vname, (vname, (low, high)))
                self.add_var(modulename, vname_idx, var_idx)
                self.ts.add_state_var(var_idx)
            return var_idxs
        
        Logger.error("Unmanaged type %s, line %d"%(type(direction), el.lineno))
        
    def Sens(self, modulename, el, args):
        if el.sig is None:
            return TRUE()
            
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
        
        if (type(left) == int) and (type(right) == FNode):
            left = BV(left, get_type(right).width)

        if (type(right) == int) and (type(left) == FNode):
            right = BV(right, get_type(left).width)
            
        if type(left) == int:
            left = BV(left, MAXINT)
        if type(right) == int:
            right = BV(right, MAXINT)

        fv_left = get_free_variables(left)
        fv_right = get_free_variables(right)

        return EqualsOrIff(left, right)

    def SensList(self, modulename, el, args):
        return And(args)

    def Integer(self, modulename, el, args):
        intvar = Symbol(self.varname(modulename, el.name), BVType(MAXINT))
        self.add_var(modulename, el.name, intvar)
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
            Logger.error("Not Implemented")
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

    def Initial(self, modulename, el, args):
        self.ts.init = And(self.ts.init, And(args))
        return args
            
    def Always(self, modulename, el, args):
        fv = [v for v in get_free_variables(args[1]) if not TS.is_prime(v)]
        frame_cond = And([EqualsOrIff(v, TS.get_prime(v)) for v in fv])
        active = args[1] if args[0] == TRUE() else Implies(args[0], args[1])
        passive = TRUE() if args[0] == TRUE() else Implies(Not(args[0]), frame_cond)
        return And(active, passive)

    def ForStatement(self, modulename, el, args):

        # Refining definition in primed format e.g., for(i=0;i<10;i=i+1) into for(i'=0;i<10;i'=i+1)
        args[0] = args[0].substitute(dict([(v, TS.get_prime(v)) for v in get_free_variables(args[0])]))
        cp = list(conjunctive_partition(args[2]))
        newcp = []
        for ass in cp:
            left, right = ass.args()[0], ass.args()[1]
            assert (ass.is_equals() or ass.is_iff()) and (left.is_symbol() or right.is_symbol())
            if left.is_symbol():
                newcp.append(EqualsOrIff(TS.get_prime(left), right))
            if right.is_symbol():
                newcp.append(EqualsOrIff(TS.get_prime(right), left))

        args[2] = And(newcp)

        # Performining the For-loop unrolling
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
            right = BV(right, MAXINT)
                    
        return BVAdd(left, right)
    
    def Eq(self, modulename, el, args):
        return EqualsOrIff(args[0], args[1])

    def NotEq(self, modulename, el, args):
        return Not(EqualsOrIff(args[0], args[1]))

    def to_bool(self, el):
        if type(el) == int:
            return FALSE() if el == 0 else TRUE()
        return BV2B(el)
    
    def And(self, modulename, el, args):
        return And([self.to_bool(x) for x in args])

    def Xor(self, modulename, el, args):
        return BVXor(args[0], args[1])

    def Or(self, modulename, el, args):
        return BVOr(B2BV(args[0]), B2BV(args[1]))
    
    def LessThan(self, modulename, el, args):
        left, right = args[0], args[1]
        if type(right) == int:
            right = BV(right, MAXINT)
        return BVULT(left, right)
             
    def Ulnot(self, modulename, el, args):
        if type(args[0]) == int:
            return TRUE() if el == 0 else FALSE()
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

        Logger.error("Unimplemented system call \"%s\", line %d"%(el.syscall, el.lineno))
        
    def Ioport(self, modulename, el, args):
        return self.Decl(modulename, el, args)

    def Partselect(self, modulename, el, args):
        return BVExtract(args[0], args[2], args[1])

    def Assign(self, modulename, el, args):
        invar = EqualsOrIff(B2BV(args[0]), B2BV(args[1]))
        self.ts.invar = And(self.ts.invar, invar)
        return el

    def _mem_access(self, address, locations, width_mem, width_idx, idx=0):
        if len(locations) == 1:
            return locations[0]
        location = BV(idx, width_idx)
        return Ite(EqualsOrIff(address, location), locations[0], self._mem_access(address, locations[1:], width_mem, width_idx, idx+1))
    
    def Pointer(self, modulename, el, args):
        if type(args[0]) == tuple:
            width = get_type(args[1]).width
            mem_size = args[0][1]
            mem_locations = ["%s_%d"%(args[0][0], i) for i in range(mem_size[0], mem_size[1]+1)]
            return self._mem_access(args[1], [self.varmap[v] for v in mem_locations], width, width)

        if type(args[1]) == FNode:
            width_mem = get_type(args[0]).width
            width_idx = get_type(args[1]).width
            mem_locations = [BVExtract(args[0], i, i) for i in range(width_mem)]
            return self._mem_access(args[1], mem_locations, width_mem, width_idx)
        
        return BVExtract(args[0], args[1], args[1])

    def Concat(self, modulename, el, args):
        if len(args) == 1:
            return args[0]
        return BVConcat(args[0], args[1])

    def _rec_repeat(self, el, count):
        if count == 1:
            return el
        return simplify(BVConcat(el, self._rec_repeat(el, count-1)))
    
    def Repeat(self, modulename, el, args):
        return self._rec_repeat(args[0], args[1])
    
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

        if el.module not in self.modulesdic:
            Logger.error("Module definition \"%s\" not found, line %d"%(el.module, el.lineno))
        
        param_modulename = el.module

        include_varargs = False
        varmap = {}
        
        parameterized_type = ["%s%s"%(p[0], p[1]) for p in paramargs]

        if include_varargs:
            parameterized_type += ["%s%s"%(p[0], get_type(p[1]).width) for p in portargs]
            for portarg in portargs:
                varmap[portarg[0]] = (get_type(portarg[1]).width, None)

        if len(parameterized_type) > 0:
            param_modulename = "%s__|%s|"%(param_modulename, ",".join(parameterized_type))

        instances = []

        # Management of multi instances
        if len(width_idx) > 0:
            formal_args = [p[0] for p in portargs]
            args_width_idx = [formal_args.index(c.portname) for c in el_child if type(c.children()[0]) == Partselect]
            map_ports = dict([(dict(portargs)[c.portname], dict(portargs)[c.portname].args()[0]) for c in el_child if type(c.children()[0]) == Partselect])
            remap_ports = [(p[0], map_ports[p[1]] if p[1] in map_ports else p[1]) for p in portargs]

            extract_port = lambda p,i: BVExtract(p, i, i)
            
            for i in range(args[width_idx[0]]):
                idx_params = [(p[0], extract_port(p[1], i) if remap_ports.index(p) in args_width_idx else p[1]) for p in remap_ports]
                idx_instance_name = "%s_%d"%(el.name, i)
                instances.append((idx_instance_name, idx_params))
        else:        
            instances = [(el.name, portargs)]
            
        for (instance, actualargs) in instances:
            if param_modulename not in self.subhtsdic:
                instancewalker = VerilogSTSWalker()
                instancewalker.paramdic = dict(paramargs)
                instancewalker.varmap = varmap
                instancewalker.modulesdic = self.modulesdic
                subhts = instancewalker.walk_module(self.modulesdic[el.module], param_modulename)
                self.subhtsdic[param_modulename] = subhts

            subhts = self.subhtsdic[param_modulename]
            subhts.name = param_modulename

            self.hts.add_sub(instance, subhts, tuple([a[1] for a in actualargs]))
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
