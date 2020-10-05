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
import itertools

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

def is_phi(stmt):
    return smt2ast.is_call(stmt, "=") and smt2ast.is_call(stmt.v[2], "phi")

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
        self._idom = None
        self._domtree = None

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

    @property
    def idom(self):
        if self._idom is not None:
            return self._idom

        # this could be improved

        idom = {}
        for n in self.cfg.nodes:
            dom = self.dominators[n]

            # idom(n) is m where m strictly dominates n and m is
            # strictly dominated by x where x is a dominator of n

            for d in dom:
                if d == n: continue

                ddom = self.dominators[d]
                for odom in dom:
                    if odom != n and odom not in ddom: break
                else:
                    idom[n] = d # all other dominators of n dominate d
                    break

        self._idom = idom
        return self._idom

    @property
    def domtree(self):
        if self._domtree is not None:
            return self._domtree

        domtree = {}
        for n, x in self.idom.items():
            if x not in domtree: domtree[x] = []
            domtree[x].append(n)

        self._domtree = domtree
        return self._domtree

    def dump_idom_dot(self, output):
        with open(output, "w") as f:
            print("digraph {", file=f)
            for n, x in self.idom.items():
                print(f"{x} -> {n};", file=f)
            print("}", file=f)

class ReachingDefinitions(IDFA):
    def initialize(self, cfg):
        self.cfg = cfg

        # assign definitions numbers
        dndx = 1
        defns = {}
        rev_defns = {}
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
                    rev_defns[dno] = w

        self.defns = defns
        self.rev_defns = rev_defns

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

class Uses(IDFA):
    """Identify variables first used in a block ignoring phi
       statements. These are, in functional SSA form, from the
       `enclosing' scope
     """

    def initialize(self, cfg):
        self.cfg = cfg
        self.writes = {} # variables written/defined in this block
        self.reads = {} # variables read in this block
        self.outer_reads = {} # variables read, but not defined in this block
        self.captured_parameters = {} # variables needed in this block that are not formal parameters

        for n in self.cfg.nodes:
            self.writes[n] = set()
            self.outer_reads[n] = set()
            self.reads[n] = set()
            self.writes[n] = set()

            for stmtcon in self.cfg.nodes[n]:
                self.writes[n] |= stmtcon.rwinfo['writes']

                # phi nodes are formal parameters, so don't include
                # their reads
                if not is_phi(stmtcon.stmt):
                    self.reads[n] |= stmtcon.rwinfo['reads']

            self.outer_reads[n] = self.reads[n] - self.writes[n]
            self.captured_parameters[n] = self.outer_reads[n]

    def xfer(self, node):
        out_facts = IDFA.meet_union([self.captured_parameters[s] for s in self.cfg.succ[node]])

        new_in = self.outer_reads[node] | (out_facts - self.writes[node])
        if new_in != self.captured_parameters[node]:
            self.captured_parameters[node] = new_in
            return True

        return False

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

            # add an explicit branch
            nodes[prev_label].append(smt2ast.SExprList(smt2ast.Symbol("branch"),
                                                       smt2ast.Symbol(bb_label))),
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
                bb.append(smt2ast.SExprList(smt2ast.Symbol("branch"),
                                            smt2ast.Symbol('_EXIT')))
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

            if is_phi(stmt):
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

def branches_to_functions(cfg):
    def fixup_branch(stmt, *indices):
        for index in indices:
            br = stmt.v[index].v
            if br in params:
                call = [stmt.v[index]] + [smt2ast.Symbol(p) for p in params[br]]
                stmt.v[index] = smt2ast.SExprList(*call)

        return stmt

    params = {}
    for n in cfg.nodes:
        params[n] = []

        for stmtcon in cfg.nodes[n]:
            stmt = stmtcon.stmt
            if is_phi(stmt):
                params[n].append(stmt.v[1].v)

    #print(params)

    for n in cfg.nodes:
        for stmtcon in cfg.nodes[n]:
            stmt = stmtcon.stmt
            if smt2ast.is_call(stmt, "branch"):
                #import pdb
                #pdb.set_trace()
                stmt = fixup_branch(stmt, 1)
            elif smt2ast.is_call(stmt, "cbranch"):
                stmt = fixup_branch(stmt, 2, 3)

            stmtcon.stmt = stmt


def convert_to_SSA(cfg):
    get_reads_and_writes(cfg)
    dom = cfg.run_idfa(Dominators())
    #print(dom.idom, dom.domtree)
    dom.dump_idom_dot("idom.dot")
    place_phi(cfg, dom.frontier)
    branches_to_functions(cfg)
    rdef = cfg.run_idfa(ReachingDefinitions())
    rename(rdef)


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
