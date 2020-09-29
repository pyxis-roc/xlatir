#!/usr/bin/env python3
#
# imp2func2.py
#
# Convert imperative code with assignments, to functional code (SMT2).
#
# Author: Sreepathi Pai
#
# Copyright (c) 2020 University of Rochester


import argparse
import smt2ast
from xir2smt2 import create_dag, eliminate_xir_attr_ref # this should be eventually dropped
from functools import reduce
import sys

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

class Stmt(object):
    """Container for statements found in basic blocks.

       Convenient to add annotations, data flow facts, etc. on a per-statement basis"""

    def __init__(self, stmt):
        self.stmt = stmt

    def __str__(self):
        return f"Stmt(stmt={repr(self.stmt)})"

    __repr__ = __str__

class ControlFlowGraph(object):
    def __init__(self, nodes, edges):
        """nodes: Dictionary of names to lists of statements
           edges: List of tuples, i.e. graph in COO form
        """

        self.nodes = nodes
        self.edges = edges

        # construct lists of successors and predecessors for each node
        self.succ = dict([(k, set()) for k in self.nodes.keys()])
        self.pred = dict([(k, set()) for k in self.nodes.keys()])

        for src, dst in self.edges:
            self.succ[src].add(dst)
            self.pred[dst].add(src)

    def run_idfa(self, idfa):
        idfa.initialize(self)

        changed = True
        while changed:
            changed = False
            for n in self.nodes: # TODO: get a order
                changed = idfa.xfer(n) or changed

        return idfa

    def dump_dot(self, output, stmt_fn = str):
        with open(output, "w") as f:
            print("digraph {", file=f)
            print("node [shape=rect]", file=f)
            for block in self.nodes:
                label =  '\\n'.join([stmt_fn(s) for s in self.nodes[block]])
                if label == '': label = block
                print(f'\t {block} [label="{label}"];', file=f)

            for s, e in cfg.edges:
                print(f"{s} -> {e};", file=f)

            print("}", file=f)

class IDFA(object):
    def __init__(self):
        pass

    def initialize(self, cfg):
        pass

    def xfer(self, node):
        """Return true if update was made, false otherwise"""
        pass

    @staticmethod
    def meet_intersection(inputs):
        if len(inputs):
            return reduce(lambda x, y: x.intersection(y), inputs, inputs[0])

        return set()

    @staticmethod
    def meet_union(inputs):
        if len(inputs):
            return reduce(lambda x, y: x.union(y), inputs, inputs[0])

        return set()

class Dominators(IDFA):
    def initialize(self, cfg):
        # each node dominates itself
        self.dominators = dict([(k, set(cfg.nodes.keys())) for k in cfg.nodes.keys()])
        self._dominated = None
        self._frontier = None
        self.cfg = cfg

    def xfer(self, node):
        input_facts = [self.dominators[pred] for pred in self.cfg.pred[node]]

        doms = IDFA.meet_intersection(input_facts)
        doms.add(node)

        #print(node, cfg.pred[node], input_facts, doms)

        if doms != self.dominators[node]:
            self.dominators[node] = doms
            return True

        return False

    @property
    def dominated(self):
        if self._dominated is None:
            dominated = dict([(k, set()) for k in self.dominators.keys()])

            for n in self.dominators:
                for dom in self.dominators[n]:
                    dominated[dom].add(n)

            self._dominated = dominated

        return self._dominated

    @property
    def frontier(self):
        verbose = False
        # the dominance frontier of a node is the set of nodes that it does not strictly dominate,
        # and that are one hop away from a node it does dominate

        # inefficient, should build domtree
        # stolen from CSC455 checker

        if self._frontier is not None:
            return self._frontier

        cfg = self.cfg
        dominated = self.dominated
        df = dict([(k, set()) for k in cfg.nodes])

        # for each node
        for n in cfg.nodes:
            if verbose: print("node", n)

            # find the nodes that this node dominates
            if verbose: print("\t dominates", dominated[n])
            for d in dominated[n]:
                if verbose: print("\t\t", d,"'s edges", cfg.succ[d])

                # find nodes that d connects to
                for e in cfg.succ[d]:
                    # n does not strictly dominate e
                    if e in dominated[n] and (e != n):
                        if verbose: print("\t\t\t", e, "is strictly dominated by", n, "skipping")
                        continue

                    if verbose: print("\t\t\t", e, "is not strictly dominated by", n, "adding")
                    df[n].add(e)

        self._frontier = df
        return self._frontier

class ReachingDefinitions(IDFA):
    def initialize(self, cfg):
        self.cfg = cfg

        # assign definitions numbers
        dndx = 1
        defns = {}
        self.rdef = dict([(k, set()) for k in self.cfg.nodes])

        for n in self.cfg.nodes:
            for stmtcon in self.cfg.nodes[n]:
                stmtcon.rdef_def = set()

                for w in stmtcon.rwinfo['writes']:
                    dno = f"d{dndx}"
                    if w not in defns: defns[w] = set()
                    defns[w].add(dno)
                    dndx +=1
                    stmtcon.rdef_def.add(dno)

        self.defns = defns

        for n in self.cfg.nodes:
            for stmtcon in self.cfg.nodes[n]:
                stmtcon.rdef_in = set()
                stmtcon.rdef_out = set()
                stmtcon.rdef_kill = reduce(lambda x, y: x.union(y),
                                           [defns[w] - stmtcon.rdef_def for w in stmtcon.rwinfo['writes']], set())

    def xfer(self, node):
        in_facts = IDFA.meet_union([self.rdef[p] for p in self.cfg.pred[node]])
        changed = False

        for stmtcon in self.cfg.nodes[node]:
            changed = changed or (in_facts != stmtcon.rdef_in)

            stmtcon.rdef_in = in_facts
            out_facts = stmtcon.rdef_def.union(in_facts - stmtcon.rdef_kill)

            changed = changed or (out_facts != stmtcon.rdef_out)
            stmtcon.rdef_out = out_facts
            in_facts = out_facts

        self.rdef[node] = in_facts

        return changed

def get_branch_targets(xirstmts):
    labels = set()
    for s in xirstmts:
        if smt2ast.is_call(s, "branch"):
            labels.add(s.v[1].v)
        elif smt2ast.is_call(s, "cbranch"):
            labels.add(s.v[2].v)
            labels.add(s.v[3].v)

    return labels

def get_cfg(xirstmts):
    def add_basic_block(bb):
        if len(bb):
            basic_blocks.append(bb)

        return []

    labels = get_branch_targets(xirstmts)

    basic_blocks = []
    bb = []
    cur_label = "_START"
    clndx = 1

    # demarcate basic blocks
    for s in xirstmts:
        if smt2ast.is_call(s, "label"):
            if s.v[1].v in labels:
                bb = add_basic_block(bb)

            bb.append(s)
        elif smt2ast.is_call(s, "branch") or smt2ast.is_call(s, "return"):
            bb.append(s)
            bb = add_basic_block(bb)
        elif smt2ast.is_call(s, "cbranch"):
            if len(bb) > 1 or (len(bb) == 1 and not smt2ast.is_call(bb[0], "label")):
                bb = add_basic_block(bb)

            # bb is either empty or contains only a single label
            bb.append(s)
            bb = add_basic_block(bb)
        else:
            bb.append(s)

    if len(bb): add_basic_block(bb)

    # form the CFG
    prev_label = "_START"
    lbl_ndx = 1
    connect_to_previous = True

    nodes = {'_START': [], '_EXIT': [smt2ast.SExprList(*[smt2ast.Symbol("return"),
                                                         smt2ast.Symbol("_retval")])]}
    cfg_edges = []

    for bb in basic_blocks:
        if (len(bb) == 0) or (len(bb) > 1 and not smt2ast.is_call(bb[0], "label")):
            # no label, so generate one
            bb_label = f"_label_{lbl_ndx}"
            lbl_ndx += 1
        elif (len(bb) > 1 and smt2ast.is_call(bb[0], "label")):
            bb_label = bb[0].v[1].v

        nodes[bb_label] = bb

        if connect_to_previous:
            cfg_edges.append((prev_label, bb_label))
            prev_label = None
            connect_to_previous = False

        if len(bb):
            last_stmt = bb[-1]
            if smt2ast.is_call(last_stmt, "branch"):
                cfg_edges.append((bb_label, last_stmt.v[1].v))
            elif smt2ast.is_call(last_stmt, "return"):
                bb[-1] = smt2ast.SExprList(*[smt2ast.Symbol("="),
                                             smt2ast.Symbol("_retval"),
                                             last_stmt.v[1]])
                cfg_edges.append((bb_label, "_EXIT"))
            elif smt2ast.is_call(last_stmt, "cbranch"):
                for lbl in last_stmt.v[2:]:
                    cfg_edges.append((bb_label, lbl.v))
            else:
                # bb didn't end in a branch, so fall through
                connect_to_previous = True
                prev_label = bb_label

    # convert all stmts in basic blocks to Stmt
    for n in nodes:
        nodes[n] = [Stmt(s) for s in nodes[n]]

    return ControlFlowGraph(nodes, cfg_edges)

def get_symbols(s):
    def _get_symbols(s, out=set()):
        if isinstance(s, (smt2ast.Symbol, smt2ast.QuotedSymbol)):
            out.add(s.v)
        elif isinstance(s, smt2ast.SExprList):
            # assume this is a function call and get symbols from the arguments
            for v in s.v[1:]:
                _get_symbols(v, out)

    o = set()
    _get_symbols(s, o)
    return o

def get_reads_and_writes(cfg):
    for bbn, bb in cfg.nodes.items():
        for stmtcon in bb:
            stmt = stmtcon.stmt

            assert isinstance(stmt, smt2ast.SExprList)
            sty = stmt.v[0].v
            rw = {'reads': set(), 'writes': set()}

            if sty in ('label', 'branch'):
                rw = {'reads': set(), 'writes': set()}
            elif sty == 'return':
                rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
            elif sty == 'cbranch':
                rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
            elif sty == '=':
                lhs = stmt.v[1]
                rhs = stmt.v[2]

                if isinstance(lhs, smt2ast.Symbol):
                    # (= symbol ...)
                    rw = {'reads': get_symbols(rhs), 'writes': get_symbols(lhs)}
                elif isinstance(stmt.v[1], smt2ast.SExprList):
                    # (= () ...)
                    raise NotImplementedError
                    rw = {'reads': get_symbols(rhs), 'writes': get_symbols(lhs)}
                else:
                    raise NotImplementedError(f"Don't support assignment {stmt}")
            else:
                raise NotImplementedError(f"Don't recognize top-level {stmt}")

            stmtcon.rwinfo = rw

def replace_symbols(s, replacement):
    if isinstance(s, smt2ast.Symbol) and s.v in replacement:
        return smt2ast.Symbol(replacement[s.v])
    elif isinstance(s, smt2ast.SExprList):
        return smt2ast.SExprList(*[replace_symbols(ss, replacement) for ss in s.v])
    else:
        return s

def rename(rdef):
    # rename lhs

    varndx = dict([(x, 0) for x in rdef.defns.keys()])
    defn2var = {}

    for n in rdef.cfg.nodes:
        bb = rdef.cfg.nodes[n]
        for stmtcon in bb:
            if len(stmtcon.rdef_def):
                stmt = stmtcon.stmt
                assert len(stmtcon.rdef_def) == 1, f"Don't support multiple assignments {stmtcon.rdef_def}/{stmt}"
                for def_ in stmtcon.rdef_def:
                    if isinstance(stmt.v[1], smt2ast.Symbol):
                        v = stmt.v[1].v
                        assert def_ in rdef.defns[v], f"Mismatch {def_} for variable {v}"
                        stmt.v[1].v = v + str(varndx[v])
                        defn2var[def_] = (v, v + str(varndx[v]))
                        varndx[v] += 1
                    else:
                        raise NotImplementedError(f"Don't know how to rename LHS for {stmt}")

                    break # since we're only doing one

    # rename rhs
    for n in rdef.cfg.nodes:
        bb = rdef.cfg.nodes[n]

        for i in range(len(bb)):
            stmtcon = bb[i]
            stmt = stmtcon.stmt
            rd = stmtcon.rdef_in
            replacements = [defn2var[rdd] for rdd in rd]

            if smt2ast.is_call(stmt, "=") and smt2ast.is_call(stmt.v[2], "phi"):
                v = stmt.v[2].v[1].v
                repl = [smt2ast.Symbol(x[1]) for x in replacements if x[0] == v]

                # this is an inconsistency
                assert len(stmt.v[2].v) == len(repl) + 1, f"Missing definition for phi statement {stmt}, {repl}"
                stmt.v[2].v[1:len(repl)+1] = repl
                #print(stmtcon.stmt)
            else:
                #print(replacements)
                repl = dict(replacements)
                assert len(replacements) == len(repl), f"Two definitions for the same variable cannot reach the same non-phi statement: {replacements}/{repl} for {stmtcon.stmt}"

                stmtcon.stmt = replace_symbols(stmtcon.stmt, repl)

def place_phi(cfg, domfrontier):
    placed_phi = dict()
    writes = dict([(k, set()) for k in cfg.nodes])

    # collect all writes per BB
    for n in cfg.nodes:
        w = set()
        for stmtcon in cfg.nodes[n]:
            w = w | stmtcon.rwinfo['writes']

        writes[n] = w

    placed = True
    while placed:
        placed = False

        for n in cfg.nodes:
            df = domfrontier[n]

            for w in writes[n]:
                for dfn in df: #TODO: check only join nodes?
                    if dfn not in placed_phi:
                        placed_phi[dfn] = set()

                    if w not in placed_phi[dfn]:
                        placed_phi[dfn].add(w)
                        writes[dfn].add(w)
                        placed = True

    for n, phiv in placed_phi.items():
        bb = cfg.nodes[n]
        for v in phiv:
            phistmt = Stmt(smt2ast.SExprList(smt2ast.Symbol('='), smt2ast.Symbol(v),
                                                smt2ast.SExprList(smt2ast.Symbol('phi'),
                                                                  smt2ast.Symbol(v),
                                                                  smt2ast.Symbol(v))))
            bb.insert(0, phistmt)
            phistmt.rwinfo = {'reads': set([v]), 'writes': set([v])}

def convert_to_SSA(cfg):
    get_reads_and_writes(cfg)
    dom = cfg.run_idfa(Dominators())
    place_phi(cfg, dom.frontier)
    rdef = cfg.run_idfa(ReachingDefinitions())
    rename(rdef)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert imperative code to functional code")
    p.add_argument("xir", help="Serialized XIR, SMT2-like syntax as used internally by xir2smt")
    p.add_argument("--debug", help="Enable debug trace", action="store_true")

    args = p.parse_args()

    statements = load_xir(args.xir)
    cfg = get_cfg(statements)
    convert_to_SSA(cfg)
    cfg.dump_dot('test.dot')

    #v = create_dag(statements, args.debug)
    #print(eliminate_xir_attr_ref(v))
