#!/usr/bin/env python3
#
# impdfanalysis.py
#
# Dataflow analysis for imperative code written using smt2ast
#
# Author: Sreepathi Pai
#
# Copyright (C) 2020, University of Rochester

import smt2ast
from functools import reduce
import toposort

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

    def topo_order(self):
        try:
            return toposort.toposort_flatten(self.succ)
        except toposort.CircularDependencyError as e:
            return None

    def dump_dot(self, output, stmt_fn = str):
        with open(output, "w") as f:
            print("digraph {", file=f)
            print("node [shape=rect]", file=f)
            for block in self.nodes:
                label =  '\\n'.join([stmt_fn(s) for s in self.nodes[block]])
                label = f'**{block}**' + '\\n' + label
                print(f'\t {block} [label="{label}"];', file=f)

            for s, e in self.edges:
                print(f"{s} -> {e};", file=f)

            print("}", file=f)

class IDFA(object):
    """Iterative data flow analysis base class"""
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
    """Get all labels that are targets of branches"""
    labels = set()
    for s in xirstmts:
        if smt2ast.is_call(s, "branch"):
            labels.add(s.v[1].v)
        elif smt2ast.is_call(s, "cbranch"):
            labels.add(s.v[2].v)
            labels.add(s.v[3].v)

    return labels

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
    """Get reads/writes for each statement"""
    for bbn, bb in cfg.nodes.items():
        for stmtcon in bb:
            stmt = stmtcon.stmt

            assert isinstance(stmt, smt2ast.SExprList)
            sty = stmt.v[0].v
            rw = {'reads': set(), 'writes': set()}

            if sty == 'label':
                rw = {'reads': set(), 'writes': set()}
            elif sty == 'branch':
                # in SSA functional form, branches are calls...
                rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
            elif sty == 'return':
                rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
            elif sty == 'cbranch':
                cond_r = get_symbols(stmt.v[1])
                # in SSA functional form, branches are calls...
                br_1 = get_symbols(stmt.v[2])
                br_2 = get_symbols(stmt.v[3])
                rw = {'reads': cond_r | br_1 | br_2, 'writes': set()}
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

def get_cfg(xirstmts):
    """Construct a CFG"""
    def add_basic_block(bb):
        if len(bb):
            basic_blocks.append(bb)

        return []

    labels = get_branch_targets(xirstmts)
    #print(labels)

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
        if (len(bb) == 0) or (len(bb) > 0 and not smt2ast.is_call(bb[0], "label")):
            # no label, so generate one
            bb_label = f"_label_{lbl_ndx}"
            lbl_ndx += 1
        elif (len(bb) > 0 and smt2ast.is_call(bb[0], "label")):
            bb_label = bb[0].v[1].v
        else:
            assert False

        #print(bb, bb_label)
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

        #print(bb, nodes)

    # convert all stmts in basic blocks to Stmt
    for n in nodes:
        nodes[n] = [Stmt(s) for s in nodes[n]]

    return ControlFlowGraph(nodes, cfg_edges)
