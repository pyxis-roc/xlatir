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
import xir2c
import xirxlat

if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Translate XIR")
    p.add_argument("semfile", help="XIR semantics")
    p.add_argument("language", choices=["c"])
    p.add_argument("output", help="Output file for main output (headers may be produced)" )
    p.add_argument('ptxinsn', nargs="*", help="PTX instruction in underscore form (e.g. add_u16)")

    args = p.parse_args()

    gl, semantics = extract_ex_semantics.load_execute_functions(args.semfile)
    translator = xirxlat.XIRToX()

    if args.language == "c":
        translator.X = xir2c.CXlator(translator)
        debug_exclude = xir2c.debug_exclude # TODO: remove this?
    else:
        assert False, f"Unrecognized language {args.language}"

    if not args.ptxinsn or (len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all'):
        args.ptxinsn = [k[len("execute_"):] for k in semantics]

    out = []
    defns = []
    tyerrors = []
    xlaterrors = []

    rp = xir.RewritePythonisms()
    for pi in args.ptxinsn:
        sem = semantics["execute_" + pi]
        rp.visit(sem)

        try:
            ty = xir.infer_types(sem)
        except AssertionError as e:
            tyerrors.append((pi, e))
            continue

        try:
            xlation = translator.translate(sem, ty)
            out.append(xlation)
        except Exception as e:
            xlaterrors.append((pi, e))
            continue

        defns.extend(translator.defns)

    translator.X.write_output(args.output, out, defns)

    if len(tyerrors): print("*** TYPE ERRORS")
    for x, e in tyerrors:
        print(x, e)

    if len(xlaterrors): print("*** TRANSLATION ERRORS")
    for x, e in xlaterrors:
        print(x, e)

