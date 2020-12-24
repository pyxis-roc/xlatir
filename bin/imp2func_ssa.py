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
from xlatir.imp2func.imp2func_ssa import *
import sys
import itertools
import logging
import warnings

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

    args = p.parse_args()

    if args.debug:
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig()

    statements = load_xir(args.xir)

    if args.backend == 'python':
        backend = PyOutput()
    elif args.backend == 'smt2':
        symtypes = {}
        if not args.types:
            for s in statements:
                if smt2ast.is_call(s, 'type'):
                    break
            else:
                print("ERROR: smt2 backend requires a types file (specify using --types) or inline types")
                sys.exit(1)

            symtypes = read_inline_types(statements)
        else:
            symtypes = read_types_file(args.types)

        backend = SMT2Output(symtypes)
    else:
        raise NotImplementedError(f"Unsupported backend {args.backend}")

    cfg = convert_to_functional(statements, set(args.globalvars), backend,
                                args.linear, args.name_prefix,
                                dump_cfg = args.dump_cfg,
                                prune_unreachable = args.prune_unreachable,
                                error_on_non_exit_nodes = args.non_exit_error)
    if cfg:
        if args.prologue:
            with open(args.prologue, "r") as f:
                print(f.read())

        print(backend.get_output())

