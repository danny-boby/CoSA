# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Not, And, get_type, BV, EqualsOrIff
from pysmt.parsing import Rule, UnaryOpAdapter
from cosa.utils.logger import Logger
from cosa.representation import TS
from cosa.utils.formula_mngm import KEYWORDS, BV2B, B2BV

class SyntacticSugarFactory(object):
    ssugar = []

    # Additional syntactic sugar should be registered here #
    @staticmethod
    def init_ssugar():
        SyntacticSugarFactory.register_sugar(Posedge())
        SyntacticSugarFactory.register_sugar(Negedge())

        for name in SyntacticSugarFactory.sugar_names():
            if name not in KEYWORDS:
                KEYWORDS.append(name)
        
    @staticmethod
    def register_sugar(sugar):
        if sugar.get_name() not in dict(SyntacticSugarFactory.ssugar):
            SyntacticSugarFactory.ssugar.append((sugar.get_name(), sugar))

    @staticmethod
    def sugar_names():
        return [x[0] for x in SyntacticSugarFactory.ssugar]
    
    @staticmethod
    def get_ssugar():
        return [x[1] for x in SyntacticSugarFactory.ssugar]

class SyntacticSugar(object):
    name = "Syntactic Sugar"
    description = "MISSING DESCRIPTION!"

    def __init__(self):
        pass

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description

    def insert_lexer_rule(self, rules):
        pass
    
class Posedge(SyntacticSugar):
    name = "posedge"
    description = "Clock Posedge definition"

    def insert_lexer_rule(self, rules):
        rules.insert(0, Rule(r"(posedge)", UnaryOpAdapter(self.Posedge, 100), False))

    def Posedge(self, x):
        if get_type(x).is_bool_type():
            return And(Not(x), TS.to_next(x))
        return And(EqualsOrIff(x, BV(0,1)), BV2B(TS.to_next(x)))

class Negedge(SyntacticSugar):
    name = "negedge"
    description = "Clock Negedge definition"

    def insert_lexer_rule(self, rules):
        rules.insert(0, Rule(r"(negedge)", UnaryOpAdapter(self.Negedge, 100), False))

    def Negedge(self, x):
        if get_type(x).is_bool_type():
            return And(x, Not(TS.to_next(x)))
        return And(BV2B(x), EqualsOrIff(TS.to_next(x), BV(0,1)))
    
