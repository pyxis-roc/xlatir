#!/usr/bin/env python3
#
# xirconvert.py
#
# Check that XIR/Python is valid syntactically and convert it to
# XIR/Imp, expanding macros on the way.
#
# Author: Sreepathi Pai

from xlatir.xir.syntax import XIRSyntaxCheck, PyToXIRImp
from xlatir.xir.macros import LoadMacros, ApplyMacros

import ast
import astunparse

if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(description="Convert XIR/Python code to XIR/Imp")
    p.add_argument("pyfile", help="Python-syntax XIR file")
    p.add_argument("--xm", dest="expand_macros", help="Expand macros", action="store_true")
    p.add_argument("-o", metavar="FILE", dest="output", help="Output file")

    args = p.parse_args()

    with open(args.pyfile, 'r') as f:
        src = f.read()
        pysrc = ast.parse(src, args.pyfile)

    sc = XIRSyntaxCheck()
    sc._xir_filename = args.pyfile
    sc._xir_source = src.splitlines()
    sc.visit(pysrc)

    p2x = PyToXIRImp()
    xir = p2x.visit(pysrc)

    if args.expand_macros:
        lm = LoadMacros()
        macros, mxirast = lm.load(xir)

        am = ApplyMacros()
        xir = am.apply(macros, mxirast)

    output = astunparse.unparse(xir)
    if args.output:
        with open(args.output, 'w') as f:
            f.write(output)
    else:
        print(output)
