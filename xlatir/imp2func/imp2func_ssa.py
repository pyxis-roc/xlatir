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

# this is out-of-date
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

    def __init__(self, cfg, globalvars = set(), keep_dead_writes = False):
        self.cfg = cfg
        self.formal_parameters = {} # formal parameters for BB that contain phi functions
        self.let_levels = {} # nesting levels of let statements -- 0 is parameter

        self.dom = self.cfg.run_idfa(Dominators())

        get_reads_and_writes(self.cfg)
        if not keep_dead_writes: self._remove_dead_writes()
        #TODO: run a copy-propagation pass
        #TODO: eliminate non-phi containing functions that have no lets by inlining them.
        self._bb_formal_params()

        uses = self.cfg.run_idfa(Uses())
        self.captured_parameters = dict([(k, list(v - globalvars)) for k, v in uses.captured_parameters.items()]) # parameters that a BB reads from an enclosing scope

        self.rdef = self.cfg.run_idfa(ReachingDefinitions())

        self._bb_function_order()
        self._bb_let_levels()

    def _remove_dead_writes(self):
        all_reads = set()
        for n in self.cfg.nodes:
            for stmtcon in self.cfg.nodes[n]:
                all_reads |= stmtcon.rwinfo['reads']

        for n in self.cfg.nodes:
            out = []
            for stmtcon in self.cfg.nodes[n]:
                if smt2ast.is_call(stmtcon.stmt, '='): # write
                    if any([v in all_reads for v in stmtcon.rwinfo['writes']]):
                        out.append(stmtcon)
                else:
                    out.append(stmtcon)

            self.cfg.nodes[n] = out

    def _bb_formal_params(self):
        """Identify formal parameters and let-binding levels"""

        formal_parameters = {}
        levels = {}
        cfg = self.cfg
        let_stmts = {}

        # the levels help in nesting let bindings when only parallel lets are available
        for n in cfg.nodes:
            bb = cfg.nodes[n]
            formal_parameters[n] = []
            levels[n] = {}
            let_stmts[n] = {}

            for stmtcon in bb:
                if smt2ast.is_call(stmtcon.stmt, "=") or smt2ast.is_call(stmtcon.stmt, "branch") or smt2ast.is_call(stmtcon.stmt, "cbranch"):
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
            wl.extend(list(self.cfg.succ[n]))

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

    def _dump_body(self, output_engine, n):
        for stmtcon in self.cfg.nodes[n]:
            stmt = stmtcon.stmt

            if isinstance(stmt, smt2ast.SExprList):
                sym = stmt.v[0].v
                if sym not in ('=', 'branch', 'cbranch', 'label'):
                    output_engine.xlat_stmt(stmt)
                elif sym == '=' and smt2ast.is_call(stmt.v[2], "phi"):
                    pass

        if len(self.cfg.succ[n]) == 1:
            succ = list(self.cfg.succ[n])[0]

            if len(self.cfg.nodes[n]):
                last_stmt = self.cfg.nodes[n][-1].stmt
                assert smt2ast.is_call(last_stmt, "branch"), f'Last statement of {n} with one successor needs to be a branch'
                output_engine.xlat_stmt(last_stmt)
            else:
                assert False, f"Node {n} has no statements" # needs at least a branch
        elif len(self.cfg.succ[n]) == 2:
            cbranch = self.cfg.nodes[n][-1].stmt
            assert smt2ast.is_call(cbranch, "cbranch"), f'Last statement of {n} with multiple successors needs to be a cbranch'
            output_engine.xlat_stmt(cbranch)
        elif len(self.cfg.succ[n]) == 0:
            pass
        else:
            raise NotImplementedError(f"Don't support more than 2 successors for node {n}")

    def dump_nested(self, output_engine, n = "_START", indent = 0, visited = set()):
        if n in visited:
            return

        visited.add(n)

        output_engine.xlat_func_def(n, self.formal_parameters[n])
        output_engine.open_func()

        for i, lv in enumerate(self.let_levels[n], 1):
            output_engine.xlat_let([self.let_stmts[n][lvv] for lvv in lv], i)
            output_engine.open_let()

        # define mutually recursive functions
        if n in self.dom.domtree:
            # first do all the actual functions, those with phi
            for s in self.dom.domtree[n]:
                if len(self.formal_parameters[s]):
                    self.dump_nested(output_engine, s, indent+1, visited)

            # these successors don't have phi, and should really be eliminated
            for s in self.dom.domtree[n]:
                if not len(self.formal_parameters[s]):
                    self.dump_nested(output_engine, s, indent+1, visited)

        self._dump_body(output_engine, n)

        for i in self.let_levels[n]:
            output_engine.close_let()

        output_engine.close_func()

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

    def dump_linear(self, output_engine, n = "_START", visited = set()):
        # define functions
        if n in self.dom.domtree:
            # nodes that don't dominate other nodes won't be found in dominator tree
            # which is organized as parent -> [children]
            for s in self.dom.domtree[n]:
                self.dump_linear(output_engine, s, visited)

        if n in visited:
            return

        visited.add(n)

        params = itertools.chain(self.formal_parameters[n], self.captured_parameters[n])
        output_engine.xlat_func_def(n, params)
        output_engine.open_func()

        for i, lv in enumerate(self.let_levels[n], 1):
            output_engine.xlat_let([self.let_stmts[n][lvv] for lvv in lv], i)
            output_engine.open_let()

        self._dump_body(output_engine, n)

        for i in self.let_levels[n]:
            output_engine.close_let()

        output_engine.close_func()

    def convert(self, output_engine):
        output_engine.func = self

        if output_engine.linear:
            self.fixup_linear_calls()
            self.dump_linear(output_engine)
        else:
            self.dump_nested(output_engine)


class PyOutput(object):
    def __init__(self):
        self.nesting = 0

    def finish(self):
        print("print(_START())")

    def open_func(self):
        self.nesting += 1

    def close_func(self):
        self.nesting -= 1

        assert self.nesting >= 0
        print("")

    def open_let(self):
        # we ignore nests for let since we serialize lets in Python
        pass

    def close_let(self):
        pass

    def xlat_func_def(self, n, params):
        assert self.nesting >= 0

        ind = "  " * self.nesting
        print(ind + "def ", n,
              f"({', '.join(params)}): ",
              '#', self.func.let_levels[n], self.func.captured_parameters[n])

    def xlat_let(self, lstmts, level):
        for lsi in lstmts:
            self.xlat_stmt(lsi)

    def xlat_stmt(self, s):
        ss = self._strify_stmt(s)
        print("  "*self.nesting + ss)

    def _strify_stmt(self, s):
        if smt2ast.is_call(s, "="):
            return f"{s.v[1]} = {self._strify_stmt(s.v[2])}"
        elif smt2ast.is_call(s, "branch"):
            return f"return {self._strify_stmt(s.v[1])}"
        elif smt2ast.is_call(s, "cbranch"):
            return f"return {self._strify_stmt(s.v[2])} if {self._strify_stmt(s.v[1])} else {self._strify_stmt(s.v[3])}"
        elif isinstance(s, (smt2ast.Symbol, smt2ast.Decimal, smt2ast.Numeral)):
            return str(s)
        elif isinstance(s, smt2ast.SExprList):
            fn = s.v[0].v
            args = [self._strify_stmt(x) for x in s.v[1:]]

            if fn in ('<', '+', '=='): # infix
                return f"({args[0]} {fn} {args[1]})"
            else:
                args = ', '.join(args)
                return f"{fn}({args})"
        else:
            raise NotImplementedError(f"No translation for {s}/{type(s)} to python yet")

def convert_ssa_to_functional(ssa_cfg, globalvars, linear = False):
    po = PyOutput()
    po.linear = linear

    fcfg = FunctionalCFG(ssa_cfg, globalvars)
    fcfg.convert(po)

    po.finish()

def convert_to_functional(statements, globalvars):
    cfg = get_cfg(statements)
    cfg.dump_dot('test.dot')
    orig_names = convert_to_SSA(cfg, cvt_branches_to_functions = True)
    cfg.orig_names = orig_names
    convert_ssa_to_functional(cfg, globalvars, args.linear)
    return cfg

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert imperative code to functional code")
    p.add_argument("xir", help="Serialized XIR, SMT2-like syntax as used internally by xir2smt")
    p.add_argument("--debug", help="Enable debug trace", action="store_true")
    p.add_argument("--linear", help="Generate linear code", action="store_true")
    p.add_argument("--gv", dest="globalvars", metavar="SYMBOL",
                   action="append", help="Treat SYMBOL as a global in linear code", default=[])
    args = p.parse_args()

    statements = load_xir(args.xir)
    cfg = convert_to_functional(statements, set(args.globalvars))
    #cfg.dump_dot('test.dot')
