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
import smt2ast
import sys
import itertools
from impdfanalysis import *
from impssa import convert_to_SSA

"""
# Syntax of the XIR Serialized SMT2-like Syntax.

## Basics

One imperative statement per line. Usually this is an assignment statement:

(= symbol value)

The last statement is treated as the return value, and the expression
corresponding to that will be returned.

symbol is an SMT2 symbol.

value is any SMT2 expression (like a function call).

## Handling deconstruction

To handle assignments like:

```
a, b = f()
```

Convert them into:

(= tmp (f))
(= a (first tmp))
(= b (second tmp))

## Handling datatype assignments (TOVERIFY)

To handle something like this:

flags.carry = add(a, b)

where flags is a structure containing two fields/selectors `carry` and
`overflow` and has the type `FlagsType` and constructor `mk-flags`.

Write:

```
(= (_xir_attr_ref carry flags FlagsType) (add a b))
(= flags (mk-flags (_xir_attr_ref carry flags FlagsType) (_xir_attr_ref overflow flags FlagsType)))
```

The first line notes the assignment to the field, and the second
reconstructs `flags` using the new values.
"""

def load_xir(xirf):
    p = smt2ast.SMT2Parser()
    with open(xirf, "r") as f:
        code = f.read()
        statements = p.parse(code)

        return statements

class FunctionalCFG(object):
    """Convert a CFG in SSA form to a functional program."""

    def __init__(self, cfg):
        self.cfg = cfg
        self.formal_parameters = {} # formal parameters for BB that contain phi functions
        self.let_levels = {} # nesting levels of let statements -- 0 is parameter

        self.dom = self.cfg.run_idfa(Dominators())

        get_reads_and_writes(self.cfg)
        self._bb_formal_params()

        uses = self.cfg.run_idfa(Uses())
        self.captured_parameters = dict([(k, list(v)) for k, v in uses.captured_parameters.items()]) # parameters that a BB reads from an enclosing scope
        self.rdef = self.cfg.run_idfa(ReachingDefinitions())

        self._bb_function_order()
        self._bb_let_levels()

    def _bb_formal_params(self):
        formal_parameters = {}
        levels = {}
        cfg = self.cfg
        let_stmts = {}

        # identify formal parameters and let-binding levels
        # the levels help in nesting let bindings when only parallel lets are available
        for n in cfg.nodes:
            bb = cfg.nodes[n]
            formal_parameters[n] = []
            levels[n] = {}
            let_stmts[n] = {}

            for stmtcon in bb:
                if smt2ast.is_call(stmtcon.stmt, "="):
                    if is_phi(stmtcon.stmt):
                        v = stmtcon.stmt.v[1].v
                        formal_parameters[n].append(v)
                        levels[n][v] = 0
                    else:
                        stmtlevel = 0
                        for x in stmtcon.rwinfo['reads']:
                            # if a variable doesn't exist in levels, it
                            # exists in an enclosing scope, making it
                            # similar to a parameter
                            stmtlevel = max(stmtlevel, levels[n][x] if x in levels[n] else 0)

                        stmtlevel = stmtlevel + 1

                        # this conveys levels
                        for x in stmtcon.rwinfo['writes']:
                            assert x not in levels[n], f"Can't have two writes to same variable {x}"
                            levels[n][x] = stmtlevel
                            let_stmts[n][x] = stmtcon.stmt

                        stmtcon.level = stmtlevel

        self.formal_parameters = formal_parameters
        self.levels = levels
        self.let_stmts = let_stmts

        self._bb_let_levels()

    def _bb_function_order(self):
        order = []
        visited = set()
        wl = ['_START']

        # currently breadth first

        while len(wl):
            n = wl.pop()
            if n in visited: continue
            order.append(n)
            visited.add(n)
            wl.extend(list(cfg.succ[n]))

        self.order = order

    def _bb_let_levels(self):
        self.let_levels = {}

        for n in self.levels:
            levn = self.levels[n]

            lets = sorted([(l, v) for v, l in levn.items() if l > 0], key=lambda x: x[0])

            last_level = None
            last_level_lets = []
            let_levels = []

            for l, v in lets:
                if l != last_level:
                    if len(last_level_lets): let_levels.append(last_level_lets)
                    last_level = l
                    last_level_lets = []

                last_level_lets.append(v)

            if len(last_level_lets): let_levels.append(last_level_lets)

            self.let_levels[n] = let_levels

    def _dump_body(self, n, indent = 1, stmt_xlat = str):
        ind = "  "*indent

        for stmtcon in self.cfg.nodes[n]:
            stmt = stmtcon.stmt

            if isinstance(stmt, smt2ast.SExprList):
                sym = stmt.v[0].v
                if sym not in ('=', 'branch', 'cbranch', 'label'):
                    print(ind + stmt_xlat(stmt))
                elif sym == '=' and smt2ast.is_call(stmt.v[2], "phi"):
                    pass

        if len(self.cfg.succ[n]) == 1:
            succ = list(self.cfg.succ[n])[0]

            if len(self.cfg.nodes[n]):
                last_stmt = self.cfg.nodes[n][-1].stmt
                if smt2ast.is_call(last_stmt, "branch"):
                    print(ind + stmt_xlat(last_stmt))
                else:
                    print(ind + "return_ft1 ", succ, "()")
            else:
                print(ind + "return_ft2 ", succ, "()")
        elif len(self.cfg.succ[n]) == 2:
            ite = self.cfg.nodes[n][-1].stmt
            print(ind + stmt_xlat(ite))

    def dump_nested(self, n = "_START", indent = 0, visited = set(), stmt_xlat = str):
        if n in visited:
            return

        visited.add(n)

        ind = "  "*indent

        print(ind + "def ", n, f"({', '.join(self.formal_parameters[n])}): ", "#", self.let_levels[n], self.captured_parameters[n])

        for lv in self.let_levels[n]:
            for lvv in lv:
                print(ind+"  " + stmt_xlat(self.let_stmts[n][lvv]))

        # define mutually recursive functions
        if n in self.dom.domtree:
            # first do all the actual functions
            for s in self.dom.domtree[n]:
                if len(self.formal_parameters[s]):
                    self.dump_nested(s, indent+1, visited, stmt_xlat = stmt_xlat)

            for s in self.dom.domtree[n]:
                if not len(self.formal_parameters[s]):
                    self.dump_nested(s, indent+1, visited, stmt_xlat = stmt_xlat)

        self._dump_body(n, indent+1, stmt_xlat)

    def fixup_linear_calls(self):
        def _fixup(*calls):
            for call in calls:
                n = call.v[0].v
                assert n in self.captured_parameters, f"No captured_parameters found for label {n}"
                call.v.extend([smt2ast.Symbol(s) for s in self.captured_parameters[n]])

        for n in self.cfg.nodes:
            bb = self.cfg.nodes[n]
            for stmtcon in bb:
                stmt = stmtcon.stmt
                if smt2ast.is_call(stmt, "branch"):
                    _fixup(stmt.v[1])
                elif smt2ast.is_call(stmt, "cbranch"):
                    _fixup(stmt.v[2], stmt.v[3])

    def dump_linear(self, n = "_START", visited = set(), stmt_xlat = str):
        # define mutually recursive functions
        if n in self.dom.domtree:
            # first do all the actual functions
            for s in self.dom.domtree[n]:
                #if len(self.formal_parameters[s]):
                self.dump_linear(s, visited, stmt_xlat = stmt_xlat)

        if n in visited:
            return

        visited.add(n)

        params = ', '.join(itertools.chain(self.formal_parameters[n], self.captured_parameters[n]))
        print("def ", n,
              f"({params}): ",
              "#", self.let_levels[n], self.captured_parameters[n])

        for lv in self.let_levels[n]:
            for lvv in lv:
                print("  " + stmt_xlat(self.let_stmts[n][lvv]))

        self._dump_body(n, 1, stmt_xlat)

def xirs_to_py(s):
    if smt2ast.is_call(s, "="):
        return f"{s.v[1]} = {xirs_to_py(s.v[2])}"
    elif smt2ast.is_call(s, "branch"):
        return f"return {xirs_to_py(s.v[1])}"
    elif smt2ast.is_call(s, "cbranch"):
        return f"return {xirs_to_py(s.v[2])} if {xirs_to_py(s.v[1])} else {xirs_to_py(s.v[3])}"
    elif isinstance(s, (smt2ast.Symbol, smt2ast.Decimal, smt2ast.Numeral)):
        return str(s)
    elif isinstance(s, smt2ast.SExprList):
        fn = s.v[0].v
        args = [xirs_to_py(x) for x in s.v[1:]]

        if fn in ('<', '+'): # infix
            return f"({args[0]} {fn} {args[1]})"
        else:
            args = ', '.join(args)
            return f"{fn}({args})"
    else:
        raise NotImplementedError(f"No translation for {s}/{type(s)} to python yet")

def convert_to_functional(cfg, linear = False):
    x = FunctionalCFG(cfg)
    #print(x.rdef.rev_defns)
    if linear:
        x.fixup_linear_calls()
        x.dump_linear(stmt_xlat = xirs_to_py)
    else:
        x.dump_nested(stmt_xlat = xirs_to_py)

    print("print(_START())")

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert imperative code to functional code")
    p.add_argument("xir", help="Serialized XIR, SMT2-like syntax as used internally by xir2smt")
    p.add_argument("--debug", help="Enable debug trace", action="store_true")
    p.add_argument("--linear", help="Generate linear code", action="store_true")
    args = p.parse_args()

    statements = load_xir(args.xir)
    cfg = get_cfg(statements)
    convert_to_SSA(cfg)
    convert_to_functional(cfg, args.linear)
    cfg.dump_dot('test.dot')

    #v = create_dag(statements, args.debug)
    #print(eliminate_xir_attr_ref(v))
