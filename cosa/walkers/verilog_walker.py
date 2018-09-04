# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import inspect

VPARSER = True

try:
    from pyverilog.vparser.ast import Node
except:
    VPARSER = False

from cosa.utils.generic import class_name
from cosa.utils.logger import Logger

class VerilogWalker(object):
    methods = None
    
    def __init__(self):
        pass

    def __init_methods(self):
        if self.methods is None:
            self.methods = [x[0] for x in inspect.getmembers(self, predicate=inspect.ismethod)]    
        
    def analyze_element(self, el, args):
        if not VPARSER:
            Logger.error("Pyverilog is not available")
        Logger.log("Processing Node: %s ---> %s"%(class_name(el), None if el.children() is None else [class_name(c) for c in el.children()]), 2)
        Logger.log("Args: %s"%(str(args)), 2)
        self.__init_methods()
        
        classname = class_name(el)
        if classname in self.methods:
            local_handler = getattr(self, classname)
            return local_handler(el, args)

        Logger.error("Unmanaged Node type \"%s\""%classname)
        return el

    def walk(self, ast):
        to_visit = [ast]
        visited = []
        args = None

        i = 0
        while i < len(to_visit):
            el = to_visit[i]
            if id(el) in visited:
                i += 1
                continue
            visited.append(id(el))
            if isinstance(el, Node) and len(list(el.children())) > 0:
                child = list(el.children())
                to_visit = to_visit[:i] + child + to_visit[i:]

        prevels = []
        processed = []
        memoization = {}
        while len(to_visit) > 0:
            el = to_visit.pop(0)
            elc = list(el.children())
            children = None
            if (len(elc) > 0) and ([type(p) for p in prevels[-len(elc):]] == [type(p) for p in elc]):
                children = processed[-len(elc):]
                prevels = prevels[:len(prevels)-len(elc)]
                processed = processed[:len(processed)-len(elc)]

            if id(el) in memoization:
                nel = memoization[id(el)]
            else:
                nel = self.analyze_element(el, children)
                memoization[id(el)] = nel
            prevels.append(el)
            processed.append(nel)

        return processed[0]
    
class IdentityVerilogWalker(VerilogWalker):

    def Paramlist(self, el, args):
        return el

    def Port(self, el, args):
        return el

    def Portlist(self, el, args):
        return el

    def Wire(self, el, args):
        return el

    def Reg(self, el, args):
        return el
    
    def Decl(self, el, args):
        return el

    def Sens(self, el, args):
        return el
        
    def Lvalue(self, el, args):
        return el

    def Rvalue(self, el, args):
        return el

    def NonblockingSubstitution(self, el, args):
        return el
    
    def SensList(self, el, args):
        return el
    
    def IntConst(self, el, args):
        return el

    def Identifier(self, el, args):
        return el
    
    def Width(self, el, args):
        return el

    def Input(self, el, args):
        return el
    
    def Output(self, el, args):
        return el

    def Block(self, el, args):
        return el

    def IfStatement(self, el, args):
        return el

    def Always(self, el, args):
        return el

    def ModuleDef(self, el, args):
        return el

    def Description(self, el, args):
        return el

    def Source(self, el, args):
        return el
    
    def analyze_element(self, el, args):
        classname = class_name(el)
        if classname in self.methods:
            local_handler = getattr(self, classname)
            return local_handler(el, args)

        Logger.error("Unmanaged Node type \"%s\""%classname)
        return el
