#!/usr/bin/env python3
#
# xir2x.py
#
# Unified interface to all translators.
#
# Author: Sreepathi Pai
#
#

import xlatir.xir.xir as xir
import ast
from xlatir.xir.xirtyping import *
import xlatir.xir.xirtyping as xirtyping
import os
import xlatir.xir.xirxlat as xirxlat
import xlatir.xir.xir2c as xir2c
import xlatir.xir.xir2smt2 as xir2smt2
import xlatir.xir.xirpeval as xirpeval
import logging
import sys
import warnings

#TODO: build a uniform loader for XIR files.

def load_execute_functions(semfile):
    """This loads the low-level semantics file produced by the semantics compiler"""
    out = {}
    gl = {}

    with open(semfile, "r") as f:
        e = ast.parse(f.read(), semfile)

        for s in e.body:
            if isinstance(s, ast.FunctionDef):
                assert s.name not in out, f"Duplicate {s.name} in {semfile}"
                out[s.name] = s
            elif isinstance(s, ast.Assign):
                assert len(s.targets) == 1 and isinstance(s.targets[0], ast.Name), f"Unsupported global assignment"
                gl[s.targets[0].id] = s

    return gl, out

def load_usrlib_declarations(semantics, libs):
    import xlatir.xir.usrlib as usrlib
    import xlatir.xir.anno as xiranno

    usrdecls = {}
    out = {}
    d2t = usrlib.Decl2Type(xirtyping)
    for f in semantics:
        if not xiranno.has_anno(semantics[f], xiranno.XIR_IGNORE):
            if usrlib.is_xir_declaration(semantics[f]):
                usrdecls[f] = d2t.from_FunctionDef(semantics[f])
            else:
                out[f] = semantics[f]

    for l in libs:
        for d in usrlib.load_xir_declarations(l):
            if isinstance(d, ast.FunctionDef):
                f = d.name
                if f in usrdecls:
                    warnings.warn(f"{l}:{d.lineno}: Duplicate declaration for {f}")

                usrdecls[f] = d2t.from_FunctionDef(d)
            elif isinstance(d, ast.Assign): # only type declaration assignments
                d2t.add_type_decl(d)

    return usrdecls, out

def load_pemod(pemodeps, pemod):
    def loader(mod, modfile):
        spec = importlib.util.spec_from_file_location(mod, modfile)
        assert spec is not None, f'Cannot load {mod} from {modfile}'
        module = importlib.util.module_from_spec(spec)
        sys.modules[mod] = module
        spec.loader.exec_module(module)
        return module

    import importlib
    import importlib.util

    for pd in pemodeps:
        assert pd[-3:] == ".py"
        mod = pd[:-3] # remove .py
        loader(mod, pd)

    assert pemod[-3:] == ".py"
    pemodname = pemod[:-3] # remove .py
    utilsmod = loader(pemodname, pemod)
    xirpeval.set_utils(utilsmod)

if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Translate XIR")
    p.add_argument("semfile", help="XIR semantics")
    p.add_argument("language", choices=["c", "smt2"])
    p.add_argument("output", help="Output file for main output (headers may be produced)" )
    p.add_argument('ptxinsn', nargs="*", help="PTX instruction in underscore form (e.g. add_u16)")
    p.add_argument('-i', dest="interactive", action="store_true", help="Interactive, fail immediately")
    p.add_argument('-d', dest="debug", action="store_true", help="Enable debugging logs")
    p.add_argument('--noptx', action='store_true', help="Do not assume PTX conventions")
    p.add_argument('-l', metavar='LIBFILE', dest='lib', action='append', help="Use LIB (full filename) as a source of user-defined declarations", default=[])
    p.add_argument('--pemdeps', dest='pedeps', metavar='MODULEFILE', action='append', help='Import MODULEFILE as a dependency for pemodule', default=[])
    p.add_argument('--pem', dest='pemodule', metavar='MODULEFILE', help='Import MODULEFILE as utils for partial evaluator')
    args = p.parse_args()

    gl, semantics = load_execute_functions(args.semfile)
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

    usrdecls = None
    if args.lib:
        usrdecls, semantics = load_usrlib_declarations(semantics, args.lib)

    if not args.ptxinsn or (len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all'):
        if args.noptx:
            args.ptxinsn = list(semantics.keys())
        else:
            args.ptxinsn = [k[len("execute_"):] for k in semantics if k.startswith("execute_")]


    if args.pemodule:
        load_pemod(args.pedeps, args.pemodule)

    out = []
    defns = []
    tyerrors = []
    xlaterrors = []
    stats = {}
    xh = xir.HandleXIRHints()
    rp = xir.RewritePythonisms()
    rp.desugar_boolean_xor = translator.X.desugar_boolean_xor
    rp.elim_x_value = args.noptx or len(args.lib) > 0

    for pi in args.ptxinsn:
        print("==>", pi)

        if args.noptx:
            sem = semantics[pi]
        else:
            sem = semantics["execute_" + pi]

        xh.handle_hints(sem)
        rp.visit(sem)
        sem = translator.X.pre_xlat_transform(sem)

        try:
            ty = xir.infer_types(sem, xir.TYPE_DECLS, usrdecls, stats, args.noptx)
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

    translator.X.write_output(args.output, out, defns, ptx=not args.noptx)

    if len(tyerrors): print("*** TYPE ERRORS")
    for x, e in tyerrors:
        print(x, e)

    if len(xlaterrors): print("*** TRANSLATION ERRORS")
    for x, e in xlaterrors:
        print(x, e)

    print("*** STATISTICS")
    print(f"Total functions: {stats['totalfns']}")
    print(f"Usrlib functions: {stats['usrlibfns']}")
    print(f"Unknown functions: {stats['unkfns']}")
