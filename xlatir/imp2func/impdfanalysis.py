#!/usr/bin/env python3
#
# impdfanalysis.py
#
# Dataflow analysis for imperative code written using smt2ast
#
# Author: Sreepathi Pai
#
# Copyright (C) 2020, University of Rochester

from .. import smt2ast
from functools import reduce
import toposort
import sys
import itertools
import logging
from .passmgr import Pass

logger = logging.getLogger(__name__)

def is_phi(stmt):
    return smt2ast.is_call(stmt, "=") and smt2ast.is_call(stmt.v[2], "phi")

class Stmt(object):
    """Container for statements found in basic blocks.

       Convenient to add annotations, data flow facts, etc. on a per-statement basis"""

    def __init__(self, stmt):
        self.stmt = stmt

    def __str__(self):
        attrs = ['rdef_def', 'rwinfo', 'rdef_in', 'rdef_out']
        out = [f'stmt={repr(self.stmt)}']
        for a in attrs:
            if hasattr(self, a):
                out.append(f'{a}={getattr(self, a)}')

        return f"Stmt({', '.join(out)})"

    __repr__ = __str__

class ControlFlowGraph(object):
    def __init__(self, nodes, edges, name_prefix = ''):
        """nodes: Dictionary of names to lists of statements
           edges: List of tuples, i.e. graph in COO form
        """

        self.start_node = f'{name_prefix}_START'
        self.exit_node = f'{name_prefix}_EXIT'

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

    def check_structure(self, prune_unreachable = False):
        reachable = set()
        wl = [self.start_node]
        while len(wl):
            n = wl.pop()
            reachable.add(n)
            for c in self.succ[n]:
                if c not in reachable: wl.append(c)

        unreachable = set(self.nodes.keys()) - reachable
        logger.debug(f'Unreachable nodes {unreachable}')
        for n in unreachable:
            for s in self.succ[n]:
                if s in reachable:
                    logger.error(f"Node {n} is unreachable, but connects to reachable node {s}")
                    logger.error(f"Contents of {n}")
                    for stmtcon in self.nodes[n]:
                        logger.error(f"\t{stmtcon.stmt}")

        if prune_unreachable:
            logger.info(f"Removing unreachable nodes {unreachable}")
            self.remove_nodes(unreachable)

        # TODO: check loops?

    check_unreachable = check_structure

    def identify_unreachable(self):
        reachable = set()
        wl = [self.start_node]
        while len(wl):
            n = wl.pop()
            reachable.add(n)
            for c in self.succ[n]:
                if c not in reachable: wl.append(c)

        unreachable = set(self.nodes.keys()) - reachable
        logger.debug(f'Unreachable nodes {unreachable}')
        return unreachable

    def remove_nodes(self, nodes):
        nodes = set(nodes)

        for n in nodes:
            for neighbour in self.pred[n]:
                if neighbour not in nodes:
                    self.succ[neighbour].remove(n)

            for neighbour in self.succ[n]:
                if neighbour not in nodes:
                    self.pred[neighbour].remove(n)

            del self.pred[n]
            del self.succ[n]
            del self.nodes[n]

        self.edges = [(u, v) for (u, v) in self.edges if not (u in nodes or v in nodes)]

    def add_edge(self, src, dst):
        if dst not in self.succ[src]:
            self.succ[src].add(dst)
            self.pred[dst].add(src)
            self.edges.append((src, dst))

    def check_non_exit(self, prune_non_exit = False):
        """Check for nodes that can be reached, but cannot reach EXIT. Must be
           executed after check_unreachable for relevant results."""

        reachable = set()
        wl = [self.exit_node]
        while len(wl):
            n = wl.pop()
            reachable.add(n)
            for c in self.pred[n]:
                if c not in reachable: wl.append(c)

        non_exit_nodes = set(self.nodes.keys() - reachable)
        if len(non_exit_nodes):
            logger.error(f"Nodes {non_exit_nodes} do not reach {self.exit_node}")

        if prune_non_exit:
            bridge_nodes = set()
            for n in non_exit_nodes:
                for neighbour in itertools.chain(self.pred[n], self.succ[n]):
                    if neighbour not in non_exit_nodes:
                        # connected to a part of the reachable CFG
                        bridge_nodes.add(neighbour)
                        break

            logger.info(f'Removing non-exiting nodes {non_exit_nodes}')

            self.remove_nodes(non_exit_nodes)

            logger.info(f'Patching up bridge nodes {bridge_nodes}')
            for bn in bridge_nodes:
                assert len(self.succ[bn]) > 0, f"Bridge node {bn} has zero successors"
                last_stmt = self.nodes[bn][-1].stmt
                assert smt2ast.is_call(last_stmt, "cbranch"), f"Bridge node {bn} does not end in cbranch"
                dst = [x for x in last_stmt.v[2:] if str(x) not in non_exit_nodes]
                assert len(dst) == 1, f"Bridge node {bn} does not connect to a node that reaches exit, current connections: {dst}"
                self.nodes[bn][-1].stmt = smt2ast.SExprList(smt2ast.Symbol("branch"), dst[0])

        return len(non_exit_nodes) > 0

    def dump_dot(self, output, stmt_fn = str):
        with open(output, "w") as f:
            print("digraph {", file=f)
            print("node [shape=rect]", file=f)
            for block in self.nodes:
                label =  '\\n'.join([stmt_fn(s) for s in self.nodes[block]])
                label = f'**{block}**' + '\\n' + label
                label = label.replace('"', r'\"')
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

class PostDominators(Dominators):
    def xfer(self, node):
        input_facts = [self.dominators[succ] for succ in self.cfg.succ[node]]

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
        raise NotImplementedError

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
    encountered_labels = set()
    labels = set()
    for s in xirstmts:
        if smt2ast.is_call(s, "branch"):
            labels.add(s.v[1].v)
        elif smt2ast.is_call(s, "cbranch"):
            labels.add(s.v[2].v)
            labels.add(s.v[3].v)
        elif smt2ast.is_call(s, "label"):
            l = str(s.v[1])
            assert l not in encountered_labels, f"Duplicate label {l}"
            encountered_labels.add(l)

    logger.debug(f'Targeted branches: {labels}')
    return labels

def get_symbols(s):
    def _get_symbols(s, out=None):
        if out is None:
            out = set()

        if isinstance(s, (smt2ast.Symbol, smt2ast.QuotedSymbol)):
            out.add(s.v)
        elif isinstance(s, smt2ast.SExprList):
            # assume this is a function call and get symbols from the arguments
            if smt2ast.is_call(s, "_xir_attr_ref"):
                out.add(str(s.v[2]))
            else:
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

            assert isinstance(stmt, smt2ast.SExprList), f'{stmt} needs to be SExprList, is {type(stmt)}'

            rw = {'reads': set(), 'writes': set()}

            if len(stmt.v) == 0:
                stmtcon.rwinfo = rw
                continue

            sty = stmt.v[0].v

            if sty == 'label':
                rw = {'reads': set(), 'writes': set()}
            elif sty == 'type':
                rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
                # hack
                if '_retval' in rw['reads']:
                    rw['reads'] = set()
            elif sty == 'branch':
                # in SSA functional form, branches are calls...
                if isinstance(stmt.v[1], smt2ast.SExprList):
                    rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
                else:
                    rw = {'reads': set(), 'writes': set()}
            elif sty == 'return':
                rw = {'reads': get_symbols(stmt.v[1]), 'writes': set()}
            elif sty == 'cbranch':
                cond_r = get_symbols(stmt.v[1])
                # in SSA functional form, branches are calls...
                if isinstance(stmt.v[2], smt2ast.SExprList):
                    br_1 = get_symbols(stmt.v[2])
                    br_2 = get_symbols(stmt.v[3])
                    rw = {'reads': cond_r | br_1 | br_2, 'writes': set()}
                else:
                    rw = {'reads': cond_r, 'writes': set()}
            elif sty == '=':
                lhs = stmt.v[1]
                rhs = stmt.v[2]

                if isinstance(lhs, smt2ast.Symbol):
                    # (= symbol ...)
                    rw = {'reads': get_symbols(rhs), 'writes': get_symbols(lhs)}
                elif isinstance(stmt.v[1], smt2ast.SExprList):
                    # (= () ...)
                    if smt2ast.is_call(stmt.v[1], "_xir_attr_ref"):
                        lhs = stmt.v[1]
                        rhs = stmt.v[2]
                        # treat (_xir_attr_ref fieldname variable variable-type) as a write to variable
                        rw = {'reads': get_symbols(rhs), 'writes': get_symbols(lhs.v[2])}
                    else:
                        raise NotImplementedError(f"Don't know how to handle {stmt.v[1]}")
                else:
                    raise NotImplementedError(f"Don't support assignment {stmt}")
            else:
                raise NotImplementedError(f"Don't recognize top-level {stmt}")

            logger.debug(f'Read/Writes for {stmtcon.stmt}: {rw}')
            stmtcon.rwinfo = rw

# deprecated, do not use.
def bb_builder(xirstmts):
    def add_basic_block(bb):
        if len(bb):
            basic_blocks.append(bb)

        return []

    labels = get_branch_targets(xirstmts)

    basic_blocks = []
    bb = []

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

    return basic_blocks

def bb_builder_2(xirstmts):
    break_after = set()
    last_stmt = None
    labels = get_branch_targets(xirstmts)
    basic_blocks = []
    for i, s in enumerate(xirstmts):
        if smt2ast.is_call(s, "label") and s.v[1].v in labels:
            if i > 0: break_after.add(i - 1)
        elif smt2ast.is_call(s, "branch") or smt2ast.is_call(s, "return"):
            break_after.add(i) # ends here (except if next statement is type and this is return)
        elif smt2ast.is_call(s, "cbranch"):
            # start at a label if possible
            if smt2ast.is_call(last_stmt, "label"):
                # label, cbranch form
                if str(last_stmt.v[1]) not in labels:
                    if i > 2: break_after.add(i - 2) # start block at previous label

                break_after.add(i) # end block at cbranch
            else:
                if i > 1: break_after.add(i - 1 ) # start block at this cbranch
                break_after.add(i) # end block at this cbranch
        # elif smt2ast.is_call(s, "type"):
        #     if smt2ast.is_call(last_stmt, "return") and str(s.v[1]) == "_retval":
        #         break_after.remove(i - 1)
        #         break_after.add(i)

        last_stmt = s


    break_after.add(len(xirstmts) - 1)

    bb = []
    for i, s in enumerate(xirstmts):
        bb.append(s)
        if i in break_after:
            basic_blocks.append(bb)
            bb = []

    assert len(bb) == 0

    return basic_blocks

def get_cfg(xirstmts, name_prefix = ''):
    """Construct a CFG"""

    basic_blocks = bb_builder_2(xirstmts)
    if False:
        logger.debug('Basic blocks')
        for bb in basic_blocks:
            logger.debug("\n".join([str(s) for s in bb]))
            logger.debug("\n")

    # form the CFG
    prev_label = f"{name_prefix}_START"
    lbl_ndx = 1
    connect_to_previous = True

    nodes = {f'{name_prefix}_START': [],
             f'{name_prefix}_EXIT': [smt2ast.SExprList(*[smt2ast.Symbol("return"),
                                                         smt2ast.Symbol("_retval")])]}
    cfg_edges = []

    for bb in basic_blocks:
        if (len(bb) == 0) or (len(bb) > 0 and not smt2ast.is_call(bb[0], "label")):
            # no label, so generate one
            bb_label = f"{name_prefix}_label_{lbl_ndx}"
            logger.debug(f'Generating label {bb_label}')
            lbl_ndx += 1
        elif (len(bb) > 0 and smt2ast.is_call(bb[0], "label")):
            bb_label = bb[0].v[1].v
        else:
            assert False

        #print(bb, bb_label)
        nodes[bb_label] = bb

        if connect_to_previous:
            logger.debug(f'Connecting {bb_label} implicitly to previous {prev_label} (no explicit branch found at end)')
            cfg_edges.append((prev_label, bb_label))

            # add an explicit branch
            nodes[prev_label].append(smt2ast.SExprList(smt2ast.Symbol("branch"),
                                                       smt2ast.Symbol(bb_label))),
            prev_label = None
            connect_to_previous = False

        if len(bb):
            last_stmt_ndx = -1
            #if smt2ast.is_call(bb[last_stmt_ndx], "type") and bb[last_stmt_ndx].v[1].v == "_retval":
            #    last_stmt_ndx = -2

            last_stmt = bb[last_stmt_ndx]

            if smt2ast.is_call(last_stmt, "branch"):
                cfg_edges.append((bb_label, last_stmt.v[1].v))
            elif smt2ast.is_call(last_stmt, "return"):
                bb[last_stmt_ndx] = smt2ast.SExprList(*[smt2ast.Symbol("="),
                                             smt2ast.Symbol("_retval"),
                                             last_stmt.v[1]])
                bb.append(smt2ast.SExprList(smt2ast.Symbol("branch"),
                                            smt2ast.Symbol(f'{name_prefix}_EXIT')))
                cfg_edges.append((bb_label, f"{name_prefix}_EXIT"))
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

    return ControlFlowGraph(nodes, cfg_edges, name_prefix)

def remove_branch_cascades(cfg):
    # identify basic blocks that only do have a label and a branch
    def find(x):
        if x not in targets:
            return x

        tgt = find(targets[x])
        targets[x] = tgt
        return tgt

    targets = {}
    labels_to_nodes = {}

    for n in cfg.nodes:
        bb = cfg.nodes[n]
        if smt2ast.is_call(bb[-1].stmt, 'branch'):
            if len(bb) == 2 and smt2ast.is_call(bb[0].stmt, 'label'):
                lbl = str(bb[0].stmt.v[1])
                tgt = str(bb[-1].stmt.v[1])
                labels_to_nodes[lbl] = n
                targets[lbl] = tgt

    # find the final target branch for each branch only node
    # assumes no loops! else infinite loop
    changed = True
    while changed:
        changed = False

        for t in targets:
            ot = targets[t]
            nt = find(t)
            changed = changed or (ot != nt)

    # patch up branches to nodes that are being removed
    for n in cfg.nodes:
        if n in targets: continue
        bb = cfg.nodes[n]
        stmt = bb[-1].stmt
        if smt2ast.is_call(stmt, 'branch') or smt2ast.is_call(stmt, 'cbranch'):
            for x in range(1, len(stmt.v)):
                lbl = str(stmt.v[x])
                if lbl in targets:
                    tgt = targets[lbl]
                    stmt.v[x] = smt2ast.Symbol(tgt)
                    cfg.add_edge(n, tgt)
        else:
            if n != cfg.exit_node:
                raise NotImplementedError(f"Need a branch or cbranch at end of basic block {bb}")

    # remove branch-only nodes
    cfg.remove_nodes([labels_to_nodes[x] for x in targets])

class CFGBuilderPass(Pass):
    """Build a CFG from the XIR statements. """
    def run(self, ctx):
        ctx.cfg = get_cfg(ctx.statements, ctx.config.name_prefix)
        return ctx.cfg is not None

class CFGStructureCheckerPass(Pass):
    """Checks CFG structure, deprecated, use separate passes for finer control. """
    def run(self, ctx):
        ctx.cfg.check_structure(prune_unreachable = ctx.config.prune_unreachable)
        return True

class CFGUnreachableNodesPass(Pass):
    """Checks CFG for unreachable nodes.

       Stores set of unreachable node in ctx.results['CFGUnreachableNodesPass'].

       If specified, action is one of 'prune' or 'exit'. The former
       prunes the CFG, the latter exit with an error.

    """

    def __init__(self, action = None):
        assert action is None or action in ('prune', 'exit')
        self.action = action

    def run(self, ctx):
        unreachable = ctx.cfg.identify_unreachable()
        ctx.results[self.__class__.__name__] = unreachable

        if len(unreachable):
            if self.action == 'prune':
                logger.info(f"Removing unreachable nodes {unreachable}")
                ctx.cfg.remove_nodes(unreachable)
                return True
            elif self.action == 'exit':
                logger.error(f"Unreachable nodes found, exiting as requested")
                return False
            elif self.action is None:
                return True
            else:
                assert False

        return True


class CFGNonExitingPrunePass(Pass):
    """Identify non-exiting nodes and prune them. Deprecated, use a separate identification pass and a handling pass instead. """

    def run(self, ctx):
        if ctx.cfg.check_non_exit(True):
            logger.warning("CFG contains nodes that cannot reach exit. Nodes removed and CFG patched. This may not be what you want!")

            if ctx.config.error_on_non_exit_nodes:
                logger.error("Exiting on presence of non-exit nodes as requested")
                return False

        return True

class CFGMergeBranchExitNodesPass(Pass):
    """Converts a nested sequence of if/then CFG nodes to meet at a common node."""

    def run(self, ctx):
        remove_branch_cascades(ctx.cfg)
        return True

class CFGDumperPass(Pass):
    """Dump the CFG to a file. """
    def __init__(self, filename):
        self.filename = filename

    def run(self, ctx):
        logging.debug(f'Dumping CFG to {self.filename}')
        ctx.cfg.dump_dot(self.filename)
        return True

