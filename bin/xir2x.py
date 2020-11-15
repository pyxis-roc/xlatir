#!/usr/bin/env python3
#
# xir2x.py
#
# Unified interface to all translators.
#
# Author: Sreepathi Pai
#
#

import xir
import ast
import extract_ex_semantics
from xirtyping import *
import os
import xirxlat
import xir2c
import xir2smt2
import logging
import sys

if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Translate XIR")
    p.add_argument("semfile", help="XIR semantics")
    p.add_argument("language", choices=["c", "smt2"])
    p.add_argument("output", help="Output file for main output (headers may be produced)" )
    p.add_argument('ptxinsn', nargs="*", help="PTX instruction in underscore form (e.g. add_u16)")
    p.add_argument('-i', dest="interactive", action="store_true", help="Interactive, fail immediately")
    p.add_argument('-d', dest="debug", action="store_true", help="Enable debugging logs")

    args = p.parse_args()

    gl, semantics = extract_ex_semantics.load_execute_functions(args.semfile)
    translator = xirxlat.XIRToX()

    if args.debug:
        logging.basicConfig(level=logging.DEBUG)

    if args.language == "c":
        translator.X = xir2c.CXlator(translator)
    elif args.language == "smt2":
        translator.X = xir2smt2.SMT2Xlator(translator)
        sys.setrecursionlimit(2500)
    else:
        assert False, f"Unrecognized language {args.language}"

    if not args.ptxinsn or (len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all'):
        args.ptxinsn = [k[len("execute_"):] for k in semantics]

    out = []
    defns = []
    tyerrors = []
    xlaterrors = []

    xh = xir.HandleXIRHints()
    rp = xir.RewritePythonisms()
    rp.desugar_boolean_xor = translator.X.desugar_boolean_xor
    for pi in args.ptxinsn:
        print("==>", pi)
        sem = semantics["execute_" + pi]
        xh.handle_hints(sem)
        rp.visit(sem)
        sem = translator.X.pre_xlat_transform(sem)

        try:
            ty = xir.infer_types(sem, xir.TYPE_DECLS)
        except AssertionError as e:
            if not args.interactive:
                tyerrors.append((pi, e))
                continue
            else:
                raise
        except NotImplementedError as e:
            if not args.interactive:
                tyerrors.append((pi, e))
                continue
            else:
                raise

        try:
            xlation = translator.translate(sem, ty)
            out.append(xlation)
        except Exception as e:
            if not args.interactive:
                xlaterrors.append((pi, e))
                continue
            else:
                raise

        defns.extend(translator.defns)

    translator.X.write_output(args.output, out, defns)

    if len(tyerrors): print("*** TYPE ERRORS")
    for x, e in tyerrors:
        print(x, e)

    if len(xlaterrors): print("*** TRANSLATION ERRORS")
    for x, e in xlaterrors:
        print(x, e)

