#!/usr/bin/env python3
#
# imp2func_ssa.py
#
# Convert imperative code with assignments, to purely functional code (SMT2).
#
# Based on Andrew W. Appel, "SSA is Functional Programming", ACM SIGPLAN Notices, 1998
#
# Author: Sreepathi Pai
#
# Copyright (c) 2020 University of Rochester


import argparse
from xlatir import smt2ast

# for legacy purposes
from xlatir.imp2func.imp2func_ssa import LegacyConvertToFunctionalPass, LegacyConvertToSSAPass, LegacyConvertSSAToFunctionalPass

from xlatir.imp2func.passmgr import *
from xlatir.imp2func.passes import *
import sys
import itertools
import logging
import warnings

def get_cfg_name(name, prefix):
    if prefix is None:
        prefix = ''
    else:
        prefix = '-' + prefix

    return f'cfg{prefix}-{name}.dot'

logger = logging.getLogger(__name__)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert imperative code to functional code")
    p.add_argument("xir", help="Serialized XIR, SMT2-like syntax as used internally by xir2smt")
    p.add_argument("--debug", help="Enable debug trace", action="store_true")
    p.add_argument("--linear", help="Generate linear code", action="store_true")
    p.add_argument("--gv", dest="globalvars", metavar="SYMBOL",
                   action="append", help="Treat SYMBOL as a global in linear code", default=[])
    p.add_argument("--backend", dest="backend", choices=['python', 'smt2'], default='python',
                   help="Backend for code output")
    p.add_argument("--types", dest="types", help="Type file containing name-of-symbol type-of-symbol pairs, one per line. Required for smt2.")
    p.add_argument("--prefix", dest="name_prefix", help="Name prefix.", default='')
    p.add_argument("--dump-cfg", dest="dump_cfg", help="Dump CFG as dot files.", action='store_true')
    p.add_argument("--prune-unreachable", dest="prune_unreachable", help="Remove unreachable nodes from CFG.", action='store_true')
    p.add_argument("--non-exit-error", help="Stop if non-exit nodes are present.", action='store_true')
    p.add_argument("--prologue", metavar="FILE", help="Print the contents of FILE before output")
    p.add_argument("--legacy", dest="legacy", action="store_true",
                   help="Use legacy converter (for testing only)")
    args = p.parse_args()

    if args.debug:
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig()

    i2f_cfg = I2FConfig(linear = args.linear,
                        name_prefix = args.name_prefix,
                        dump_cfg = args.dump_cfg,
                        debug = args.debug,
                        loglevel = logging.WARNING if not args.debug else logging.DEBUG)

    i2f_cfg.prune_unreachable = args.prune_unreachable
    i2f_cfg.error_on_non_exit_nodes = args.non_exit_error

    pm = PassManager(i2f_cfg)
    pm.ctx.typed_backend = args.backend == 'smt2'

    pm.add(XIRFileLoaderPass(args.xir))
    if not args.types:
        pm.add(InlineTypesPass())
    else:
        pm.add(TypesFilePass(args.types))

    pm.add(InitBackendPass(args.backend))

    if not args.legacy:
        pm.ctx.globalvars = set(args.globalvars)
        pm.add(AnnotationsPass())
        pm.add(PhasePass('BUILDING CFG')) # maybe actual "Phases"
        pm.add(CFGBuilderPass())

        # clean up the CFG
        pm.add(CFGUnreachableNodesPass(action='prune' if i2f_cfg.prune_unreachable else None))
        pm.add(CFGIdentifyNonExitingPass())
        pm.add(CFGHandleNonExitingPass(action='exit' if i2f_cfg.error_on_non_exit_nodes else 'prune'))
        pm.add(CFGMergeBranchExitNodesPass())

        if args.dump_cfg: pm.add(CFGDumperPass(get_cfg_name('initial', args.name_prefix)))

        # convert to SSA form
        pm.add(PhasePass('CONVERTING TO SSA'))
        assemble_convert_to_SSA(pm)
        if args.dump_cfg: pm.add(CFGDumperPass(get_cfg_name('after-ssa', args.name_prefix)))

        pm.add(PhasePass('CONVERTING TO FUNCTIONAL'))
        pm.add(LegacyConvertSSAToFunctionalPass())
    else:
        pm.add(LegacyConvertToFunctionalPass(args.globalvars))


    pm.add(SetStdOutPass())
    if args.prologue:
        with open(args.prologue, "r") as f:
            pm.add(PrologueOutputPass(f.read()))

    pm.add(BackendOutputPass())

    if not pm.run_all():
        sys.exit(1)
