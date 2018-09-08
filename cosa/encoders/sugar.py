# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Not, And, get_type, BV, EqualsOrIff, get_env, get_type
from pysmt.parsing import Rule, UnaryOpAdapter, InfixOpAdapter, FunctionCallAdapter
from cosa.utils.logger import Logger
from cosa.representation import TS
from cosa.encoders.template import SyntacticSugar
from cosa.utils.formula_mngm import BV2B, B2BV, mem_access

class Posedge(SyntacticSugar):
    name = "posedge"
    description = "Clock Posedge"

    def adapter(self):
        return UnaryOpAdapter(self.Posedge, 100)

    def Posedge(self, x):
        if get_type(x).is_bool_type():
            return And(Not(x), TS.to_next(x))
        return And(EqualsOrIff(x, BV(0,1)), BV2B(TS.to_next(x)))

class Negedge(SyntacticSugar):
    name = "negedge"
    description = "Clock Negedge"

    def adapter(self):
        return UnaryOpAdapter(self.Negedge, 100)
        
    def Negedge(self, x):
        if get_type(x).is_bool_type():
            return And(x, Not(TS.to_next(x)))
        return And(BV2B(x), EqualsOrIff(TS.to_next(x), BV(0,1)))
    
class Change(SyntacticSugar):
    name = "change"
    description = "Signal Changes"

    def adapter(self):
        return UnaryOpAdapter(self.Change, 100)
    
    def Change(self, x):
        return Not(EqualsOrIff(x), TS.to_next(x))

class NoChange(SyntacticSugar):
    name = "nochange"
    description = "Signal doesn't Change"

    def adapter(self):
        return UnaryOpAdapter(self.NoChange, 100)

    def NoChange(self, x):
        return EqualsOrIff(x, TS.to_next(x))

class MaxBvVal(SyntacticSugar):
    name = "maxbvval"
    description = "Maximum Bitvector value"

    def adapter(self):
        return UnaryOpAdapter(self.MaxBvVal, 100)

    def MaxBvVal(self, x):
        if type(x) == int:
            return BV((2**x)-1,x)
        size = get_type(x).width
        return BV((2**size)-1,size)
    
class MemAccess(SyntacticSugar):
    name = "memacc"
    description = "Memory Access"

    def adapter(self):
        return FunctionCallAdapter(self.MemAcc, 60)

    def MemAcc(self, left, right):
        primed = False
        if TS.is_prime(left):
            primed = True
            left = TS.get_ref_var(left)

        timed_symbol = lambda v: v if not primed else TS.get_prime(v)
            
        memname = left.symbol_name()
        allsymbols = list(get_env().formula_manager.get_all_symbols())
        memsymbols = [(v.symbol_name(), timed_symbol(v)) for v in allsymbols \
                      if (not TS.is_prime(v)) and (not TS.is_timed(v)) and (v.symbol_name()[:len(memname)] == memname) \
                      and v.symbol_name() != memname]
        memsymbols.sort()
        memsize = len(memsymbols)

        if memsize < 1:
            Logger.error("Memory \"%s\" has size 1"%(memname))
        
        if right.is_int_constant():
            location = right.constant_value()
            if location > memsize-1:
                Logger.error("Out of bound access for memory \"%s\", size %d"%(memname, memsize))
            return memsymbols[location][1]
        else:
            if not (right.is_symbol() and right.symbol_type().is_bv_type()):
                Logger.error("Symbolic memory access requires Bitvector indexing")
            width_idx = right.symbol_type().width
            width_mem = min(memsize, width_idx)
            return mem_access(right, [m[1] for m in memsymbols], width_idx)
    
