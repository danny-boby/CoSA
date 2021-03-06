# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import configparser
import copy

from cosa.utils.logger import Logger
from cosa.utils.generic import auto_convert
from cosa.encoders.formulae import StringParser

DEFAULT = "DEFAULT"
GENERAL = "GENERAL"
VERIFICATION = "verification"
LIVENESS = "liveness"
EVENTUALLY = "eventually"
SAFETY = "safety"
LTL = "ltl"
EQUIVALENCE = "equivalence"
SIMULATION = "simulation"
FORMULA = "formula"
MODEL_FILE = "model_file"

class VerificationStatus(object):
    UNC = "UNCHECKED"
    UNK = "UNKNOWN"
    TRUE = "TRUE"
    FALSE = "FALSE"

    @staticmethod        
    def convert(status):
        if type(status) == bool:
            return VerificationStatus.TRUE if status else VerificationStatus.FALSE
        
        if status.upper() in [VerificationStatus.TRUE,\
                              VerificationStatus.FALSE,\
                              VerificationStatus.UNK,\
                              VerificationStatus.UNC]:
            return status.upper()
        
        Logger.error("Invalid Verification Status \"%s\""%status)

        
class VerificationType(object):
    SAFETY = 0
    LIVENESS = 1
    EVENTUALLY = 2
    EQUIVALENCE = 3
    SIMULATION = 4
    LTL = 5

class Problems(object):
    problems = None
    model_file = None
    bmc_length = 10
    abstract_clock = False
    no_clock = False
    run_coreir_passes = True
    equivalence = None
    relative_path = None
    boolean = None
    time = False

    def __init__(self):
        self.problems = []
        # need to create TS for each symbolic init value
        self.symbolic_inits = set()

    def add_problem(self, problem):
        self.problems.append(problem)
        self.symbolic_inits.add(problem.symbolic_init)

    def generate_problem(self, name, pbm_values):
        pbm = Problem()
        
        if VERIFICATION not in pbm_values:
            Logger.error("Verification type missing in problem \"%s\""%(name))
        else:
            pbm.set_verification(pbm_values[VERIFICATION].lower())
            del(pbm_values[VERIFICATION])

        for attr,value in pbm_values.items():
            if hasattr(pbm, attr):
                setattr(pbm, attr, auto_convert(value))
            else:
                Logger.error("Attribute \"%s\" not found"%attr)

        return pbm
        
    def load_problems(self, problems_file):
        config = configparser.ConfigParser()
        config.optionxform=str
        with open(problems_file, "r") as f:
            config.read_string(u""+f.read())

        self.relative_path = ("/".join(problems_file.split("/")[:-1]))

        if self.relative_path !="":
            self.relative_path += "/"
            
        for value in config:
            problem = dict(config[value])
            if DEFAULT == value:
                continue
            if GENERAL == value:
                for attr,value in problem.items():
                    if hasattr(self, attr):
                        setattr(self, attr, auto_convert(value))
                continue
            pbm = self.generate_problem(value, problem)
            pbm.name = value
            self.add_problem(pbm)

class Problem(object):
    assumptions = None
    lemmas = None
    strategy = None
    incremental = None
    symbolic_init = None
    smt2_tracing = None

    full_trace = False
    trace_vars_change = False
    trace_all_vars = False
    trace_prefix = None
    
    verbosity = None
    description = None

    status = VerificationStatus.UNC
    verification = None
    formula = None
    prove = False
    expected = None
    bmc_length = 10
    bmc_length_min = 0
    equivalence = None
    
    model_file = None
    monitors = None
    relative_path = None
    name = None
    trace = None
    time = None

    vcd = False
    skip_solving = False

    solver_name = None

    def __init__(self):
        self.status = VerificationStatus.UNC
        self.description = ""

    def __repr__(self):
        return self.name

    def set_verification(self, value):
        if value == LIVENESS:
            self.verification = VerificationType.LIVENESS
            return

        if value == EVENTUALLY:
            self.verification = VerificationType.EVENTUALLY
            return
        
        if value == SAFETY:
            self.verification = VerificationType.SAFETY
            return

        if value == EQUIVALENCE:
            self.verification = VerificationType.EQUIVALENCE
            return

        if value == SIMULATION:
            self.verification = VerificationType.SIMULATION
            return

        if value == LTL:
            self.verification = VerificationType.LTL
            return
        
        Logger.error("Unknown verification type \"%s\""%value)
