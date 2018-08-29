# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os
import shutil

from cosa.representation import HTS, TS
from cosa.utils.logger import Logger

from cosa.encoders.template import ModelParser
from cosa.encoders.btor2 import BTOR2Parser

from cosa.utils.generic import suppress_output, restore_output

PASSES = []
PASSES.append("hierarchy -check")
PASSES.append("proc")
PASSES.append("flatten")
PASSES.append("memory")
PASSES.append("techmap -map +/adff2dff.v")
PASSES.append("setundef -zero -undriven")
PASSES.append("pmuxtree")
PASSES.append("opt")
PASSES.append("rename -hide")
PASSES.append("clk2fflogic")

COMMANDS = []
COMMANDS.append("read_verilog -sv {FILES}")
COMMANDS.append("hierarchy -top {TARGET}")
COMMANDS.append("{PASSES}")
COMMANDS.append("write_btor -v {BTORFILE}")

TMPFILE = "__yosys_verilog__.btor2"

CMD = "yosys"

class VerilogYosysParser(ModelParser):
    parser = None
    extensions = ["v"]
    name = "Verilog"
    
    def __init__(self):
        pass

    def is_available(self):
        return shutil.which(CMD) is not None

    def _get_extension(self, strfile):
        return strfile.split(".")[-1]
    
    def parse_file(self, strfile, flags=None):
        if flags is None:
            Logger.error("Top module not provided")

        topmodule = flags[0]
        absstrfile = os.path.abspath(strfile)
        directory = "/".join(absstrfile.split("/")[:-1])
        files = ["%s/%s"%(directory, f) for f in os.listdir(directory) if self._get_extension(f) in self.extensions]

        command = "%s -p \"%s\""%(CMD, "; ".join(COMMANDS))
        command = command.format(FILES=" ".join(files), \
                                 TARGET=topmodule, \
                                 PASSES="; ".join(PASSES), \
                                 BTORFILE=TMPFILE)

        Logger.log("Command: %s"%command, 2)
        
        print_level = 3
        if not Logger.level(print_level):
            saved_stdout = suppress_output()
        
        retval = os.system(command)

        if not Logger.level(print_level):
            restore_output(saved_stdout)

        if retval != 0:
            Logger.error("Error in Verilog conversion")
            
        parser = BTOR2Parser()
        ret = parser.parse_file(TMPFILE)

        if not Logger.level(1):
            os.remove(TMPFILE)
        
        return ret

    def get_extensions(self):
        return self.extensions

    @staticmethod        
    def get_extensions():
        return VerilogYosysParser.extensions

    def remap_an2or(self, name):
        return name

    def remap_or2an(self, name):
        return name
    
    def parse_string(self, strinput):
        return

        return (hts, invar_props, ltl_props)
