import sys
import os
from optparse import OptionParser
import copy

# the next line can be removed after installation
#sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pyverilog.utils.version
from pyverilog.vparser.parser import parse
from pyverilog.vparser.ast import *


class VerilogWalker(object):

    def __init__(self):
        pass

    def Paramlist(self, el, args):
        return None

    def Port(self, el, args):
        print(el)
        return None
    
    def analyze_element(self, el, args):
        #print(el)

        if type(el) == Paramlist:
            return self.Paramlist(el, args)

        if type(el) == Port:
            return self.Port(el, args)

        return el
    
def visit_ast(ast, walker):
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
            to_visit = to_visit[:i] + list(el.children()) + to_visit[i:]

    prevels = []
    processed = {}
    while len(to_visit) > 0:
        el = to_visit.pop(0)
        elc = list(el.children())
        children = None
        if (len(elc) > 0) and ([type(p) for p in prevels[-len(elc):]] == [type(p) for p in elc]):
            children = prevels[-len(elc):]
            prevels = prevels[:len(prevels)-len(elc)]

        if id(el) in processed:
            nel = processed[id(el)]
        else:
            nel = walker.analyze_element(el, children)
            processed[id(el)] = nel
        prevels.append(nel)

    print(prevels)

def main():
    INFO = "Verilog code parser"
    VERSION = pyverilog.utils.version.VERSION
    USAGE = "Usage: python example_parser.py file ..."

    def showVersion():
        print(INFO)
        print(VERSION)
        print(USAGE)
        sys.exit()

    optparser = OptionParser()
    optparser.add_option("-v","--version",action="store_true",dest="showversion",
                         default=False,help="Show the version")
    optparser.add_option("-I","--include",dest="include",action="append",
                         default=[],help="Include path")
    optparser.add_option("-D",dest="define",action="append",
                         default=[],help="Macro Definition")
    (options, args) = optparser.parse_args()

    filelist = args
    if options.showversion:
        showVersion()

    for f in filelist:
        if not os.path.exists(f): raise IOError("file not found: " + f)

    if len(filelist) == 0:
        showVersion()

    ast, directives = parse(filelist,
                            preprocess_include=options.include,
                            preprocess_define=options.define)
    #print(directives, type(ast))

    walker = VerilogWalker()
    visit_ast(ast, walker)
    
    for lineno, directive in directives:
        print('Line %d : %s' % (lineno, directive))
        
if __name__ == '__main__':
    main()
