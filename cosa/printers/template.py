# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from six.moves import cStringIO

from cosa.utils.logger import Logger

class HTSPrinterType(object):
    NONE = 0

    c_size = 10
    ####################

    SMV = 11
    STS = 12

    TRANSSYS = 20

    ####################

class HTSPrinter(object):
    name = "PRINTER"
    description = "MISSING DESCRIPTION!"
    TYPE = HTSPrinterType.NONE
    EXT  = ".none"

    def __init__(self):
        self.stream = cStringIO()

    def print_hts(self, hts):
        Logger.error("Not implemented")

    def get_name(self):
        return self.name

    def get_desc(self):
        return self.description
