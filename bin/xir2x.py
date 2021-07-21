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
import xlatir.xir.xirsrc as xirsrc
from xlatir.xir.syntax import XIRSyntaxError
import xlatir.xir.srcutils as srcutils
import xlatir.xir.typeparser as typeparser

import logging
import sys
import warnings
import itertools

def debug_ih(show_builtins = False):
    for n in sys.modules:
        nn = sys.modules[n]
        if not show_builtins and "(built-in)" in str(nn):
            continue

        print(f"{n}: {nn}")

# DEPRECATED
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

# DEPRECATED
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

    return usrdecls, out, d2t

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
        mod = os.path.basename(pd[:-3]) # remove .py
        loader(mod, pd)

    assert pemod[-3:] == ".py"
    pemodname = os.path.basename(pemod[:-3]) # remove .py
    utilsmod = loader(pemodname, pemod)
    xirpeval.set_utils(utilsmod)

def setup_ptx_typeenv(te):
    """Compatibility for PTX"""
    te.type_constants.add('b1')
    te.type_constants.add('b8')
    te.type_constants.add('u8')
    te.type_constants.add('u16')
    te.type_constants.add('u32')
    te.type_constants.add('u64')
    te.type_constants.add('b16')
    te.type_constants.add('b32')
    te.type_constants.add('b64')
    te.type_constants.add('s16')
    te.type_constants.add('s32')
    te.type_constants.add('s64')
    te.type_constants.add('f32')
    te.type_constants.add('f64')
    te.type_constants.add('carryflag')
    te.type_constants.add('cc_reg_ref')
    te.type_constants.add('cc_reg')
    te.type_constants.add('bool')
    te.type_constants.add('pred')
    te.type_constants.add('intptr_t')

def load_xir_source(src, libs, libdirs):
    import xlatir.xir.xirsrc as xirsrc

    libdirs.append(os.path.join(os.path.dirname(xirsrc.__file__), 'stdlib'))
    lloc = srcutils.IncludeLocator(libdirs)
    gl = {}
    semantics = {}
    usrdecls = None
    typedecls = None
    gltyenv = typeparser.TypeEnv()
    setup_ptx_typeenv(gltyenv)

    s = xirsrc.XIRSource()
    setup_ptx_typeenv(s.tyenv)
    s.load(src)
    gl, semantics, usrdecls = s.parse()
    gltyenv.merge(s.tyenv)

    # for now, everything lives in a global namespace, typedecls handled separately using merge
    names = set(itertools.chain(gl.keys(), semantics.keys(), usrdecls.keys()))

    for l in libs:
        lpath = lloc.locate(l)
        ls = xirsrc.XIRSource()
        setup_ptx_typeenv(ls.tyenv) # NOTE: this means that type environments are per source, we need to namespace this into a global type environment
        ls.load(lpath)

        lgl, lsemantics, lusrdecls = ls.parse(names)

        names |= set(itertools.chain(lgl.keys(),
                                     lsemantics.keys(),
                                     lusrdecls.keys()))

        if len(lgl) > 0:
            warnings.warn(f'{l}: Globals in libraries not supported')
            lgl = {}

        if len(lsemantics) > 0:
            raise NotImplementedError(f'{l}: Functions with bodies in libraries not yet supported')

        usrdecls.update(lusrdecls)

        try:
            gltyenv.merge(ls.tyenv)
        except ValueError as e:
            print(f"ERROR when processing library {l}")
            raise

    return s, gl, semantics, usrdecls, gltyenv


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
    p.add_argument('--rp', action='store_true', help="Rewrite Pythonisms")
    p.add_argument('-l', metavar='LIBFILE', dest='lib', action='append', help="Use LIB (full filename) as a source of user-defined declarations", default=[])
    p.add_argument('--pemdeps', dest='pedeps', metavar='MODULEFILE', action='append', help='Import MODULEFILE as a dependency for pemodule', default=[])
    p.add_argument('--pem', dest='pemodule', metavar='MODULEFILE', help='Import MODULEFILE as utils for partial evaluator')
    p.add_argument('-I', dest='include_dirs', metavar='DIR', help='Look for included files in this directory', action='append', default=[])
    p.add_argument('-L', dest='lib_dirs', metavar='DIR', help='Look for library files in DIR', action='append', default=[])
    p.add_argument('--ih', dest="import_hell", action="store_true", help="Debug imported packages")
    args = p.parse_args()


    if args.import_hell:
        debug_ih()

    args.lib_dirs.insert(0, os.path.dirname(args.semfile))
    args.lib_dirs.insert(0, os.getcwd())

    xsrc, gl, semantics, usrdecls, gltyenv = load_xir_source(args.semfile, args.lib, args.lib_dirs)

    translator = xirxlat.XIRToX()
    translator.INC = srcutils.IncludeLocator(args.include_dirs)
    translator.polyinst = xirxlat.PolymorphicInst(translator)

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
        if args.rp: rp.visit(sem)
        sem = translator.X.pre_xlat_transform(sem)

        try:
            ty = xir.infer_types(sem, xir.TYPE_DECLS, usrdecls, stats, args.noptx, typeenv=gltyenv, xsrc=xsrc)
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
        except XIRSyntaxError as e:
            if not args.interactive:
                tyerrors.append((pi, e))
                continue
            else:
                raise

        translator.polyinst.get_instantiations(sem, ty, gltyenv)

        try:
            xlation = translator.translate(sem, ty, gltyenv)
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
