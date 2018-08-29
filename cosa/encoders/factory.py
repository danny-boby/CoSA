# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from cosa.encoders.symbolic_transition_system import SymbolicTSParser
from cosa.encoders.explicit_transition_system import ExplicitTSParser
from cosa.encoders.btor2 import BTOR2Parser
from cosa.encoders.coreir import CoreIRParser
        
class ModelParsersFactory(object):
    parsers = []

    # Additional parsers should be registered here #
    @staticmethod
    def init_parsers():
        ModelParsersFactory.register_parser(CoreIRParser())
        ModelParsersFactory.register_parser(SymbolicTSParser())
        ModelParsersFactory.register_parser(ExplicitTSParser())
        ModelParsersFactory.register_parser(BTOR2Parser())

    @staticmethod
    def get_default():
        return ModelParsersFactory.default_parser

    @staticmethod
    def register_parser(parser):
        if parser.get_name() not in dict(ModelParsersFactory.parsers):
            ModelParsersFactory.parsers.append((parser.get_name(), parser))

    @staticmethod
    def parser_by_name(name):
        ModelParsersFactory.init_parsers()
        dprint = dict(ModelParsersFactory.parsers)
        if name not in dprint:
            Logger.error("Parser \"%s\" is not registered"%name)
        return dprint[name]

    @staticmethod
    def get_parsers():
        ModelParsersFactory.init_parsers()
        return [x[0] for x in ModelParsersFactory.parsers]
