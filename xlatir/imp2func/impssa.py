#!/usr/bin/env python3
#
# impssa.py
#
# Convert smt2ast/imp code into SSA form.
#
# Author: Sreepathi Pai
#
# Copyright (C) 2020, University of Rochester
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT

from .. import smt2ast
from .impdfanalysis import Dominators, ReachingDefinitions, get_reads_and_writes, Stmt, is_phi, CFGDumperPass
import functools
import logging
from .passmgr import Pass

logger = logging.getLogger(__name__)

def replace_symbols(s, replacement):
    if isinstance(s, smt2ast.Symbol) and s.v in replacement:
        return smt2ast.Symbol(replacement[s.v])
    elif isinstance(s, smt2ast.SExprList):
        if smt2ast.is_call(s, '_xir_attr_ref'):
            return smt2ast.SExprList(s.v[0], s.v[1], replace_symbols(s.v[2], replacement), s.v[3])
        else:
            return smt2ast.SExprList(*[replace_symbols(ss, replacement) for ss in s.v])
    else:
        return s

def rename(rdef, sep='_', params=set()):
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
                        new_name = v + sep + str(varndx[v])
                        stmt.v[1].v = new_name
                        defn2var[def_] = (v, new_name)
                        varndx[v] += 1
                    elif smt2ast.is_call(stmt.v[1], "_xir_attr_ref"):
                        assert len(stmtcon.rwinfo['writes']) == 1, f"Multiple writes for _xir_attr_ref {stmtcon.rwinfo['writes']}"
                        v = list(stmtcon.rwinfo['writes'])[0]
                        assert def_ in rdef.defns[v], f"Mismatch {def_} for variable {v}"

                        new_name = v + sep + str(varndx[v])
                        stmt.v[1].v[2] = smt2ast.Symbol(new_name)
                        defn2var[def_] = (v, new_name)
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

            if not is_phi(stmt):
                rd = stmtcon.rdef_in
                replacements = [defn2var[rdd] for rdd in rd]
            else:
                # when there are more than > 2 pred, we get definitions from each path
                # otherwise we'll get complaints of missing definitions for a phi statement
                replacements = []
                for pred in rdef.cfg.pred[n]:
                    rd = rdef.cfg.nodes[pred][-1].rdef_out
                    replacements.extend([defn2var[rdd] for rdd in rd])

            # restrict definitions to those actually used, needed when phis are not placed for dead writes
            replacements = [x for x in replacements if x[0] in stmtcon.rwinfo['reads']]

            if is_phi(stmt):
                v = stmt.v[2].v[1].v
                repl = [smt2ast.Symbol(x[1]) for x in replacements if x[0] == v]

                if len(replacements) < len(rdef.cfg.pred[n]) and params and v in params:
                    repl = repl + [smt2ast.Symbol(v) for i in range(len(rdef.cfg.pred[n]) - len(replacements))]

                assert len(stmt.v[2].v) == len(repl) + 1, f"Potentially missing definition for phi statement {stmt} with replacements {repl}"

                stmt.v[2].v[1:len(repl)+1] = repl
                #print(stmtcon.stmt)
            elif smt2ast.is_call(stmt, "label"):
                pass
            else:
                #print(replacements)
                repl = dict(replacements)
                assert len(replacements) == len(repl), f"Two definitions for the same variable cannot reach the same non-phi statement: {replacements}/{repl} for {stmtcon.stmt}"

                stmtcon.stmt = replace_symbols(stmtcon.stmt, repl)

    renamed = dict([(rv, v) for v, rv in defn2var.values()])
    assert len(renamed) == len(defn2var) # duplicate names!

    return renamed


def identify_dead_writes_for_phi(cfg, dom):
    rdef = cfg.run_idfa(ReachingDefinitions())
    # for each defn, construct a defn -> BB use map
    def2bb = {}
    def2use = {}
    for n in cfg.nodes:
        bb = cfg.nodes[n]
        bb_used = set()
        bb_defined = set()
        for stmtcon in bb:
            bb_defined |= stmtcon.rdef_def
            bb_used |= stmtcon.rdef_in.intersection(functools.reduce(lambda x, y: x.union(y), [rdef.defns[x] for x in stmtcon.rwinfo['reads'] if x in rdef.defns], set()))

        for d in bb_defined:
            def2bb[d] = n

        # those we use from outside the BB
        for d in bb_used - bb_defined:
            if d not in def2use: def2use[d] = set()
            def2use[d].add(n)

    logger.debug(f'def2bb {def2bb}')
    logger.debug(f'def2use {def2use}')

    global_used_defns = set()
    for d in def2bb:
        if d not in def2use: continue # never used beyond basic block
        n = def2bb[d]
        uses = def2use[d]

        # does node n dominate all the uses?
        for bb in uses:
            if n not in dom.dominators[bb]:
                # d reaches a node that is not dominated by n, so a phi function is needed
                global_used_defns.add(d)
                break

    return global_used_defns

def remove_dead_phi(cfg, dom):
    rdef = cfg.run_idfa(ReachingDefinitions())

    used_definitions = set()
    for n in cfg.nodes:
        bb = cfg.nodes[n]
        bb_used = set()
        bb_defined = set()
        for stmtcon in bb:
            bb_defined |= stmtcon.rdef_def
            bb_used |= stmtcon.rdef_in.intersection(functools.reduce(lambda x, y: x.union(y), [rdef.defns[x] for x in stmtcon.rwinfo['reads'] if x in rdef.defns], set()))

        used_definitions |= bb_used

    logger.debug(f'used_definitions: {used_definitions}')

    removed = False
    for n in cfg.nodes:
        bb = cfg.nodes[n]

        out = []
        for stmtcon in bb:
            if is_phi(stmtcon.stmt):
                if stmtcon.rdef_def.intersection(used_definitions) == set():
                    removed = True
                    continue

            out.append(stmtcon)

        cfg.nodes[n] = out

    return removed

def place_phi(cfg, dom, no_phi_for_dead_writes = True):
    domfrontier = dom.frontier

    if no_phi_for_dead_writes:
        # in this case, we mean writes that do not cross BB boundaries
        # i.e., they might be used in the BB itself, but are dead beyond it.
        logger.debug(f'Not placing phi functions for dead definitions')
        rdef = cfg.run_idfa(ReachingDefinitions())
        global_used_defns = set()
        for n in cfg.nodes:
            bb = cfg.nodes[n]
            bb_used = set()
            bb_defined = set()
            for stmtcon in bb:
                bb_defined |= stmtcon.rdef_def
                bb_used |= stmtcon.rdef_in.intersection(functools.reduce(lambda x, y: x.union(y), [rdef.defns[x] for x in stmtcon.rwinfo['reads'] if x in rdef.defns], set()))

            global_used_defns |= bb_used - bb_defined

        global_used_defns_new = identify_dead_writes_for_phi(cfg, dom)
        logger.debug(f'def->var {rdef.rev_defns}')
    else:
        global_used_defns = None
        global_used_defns_new = None

    logger.debug(f'Global used definitions: {global_used_defns}')
    logger.debug(f'Global used definitions new: {global_used_defns_new}')

    #TODO: keep the old code around for compat
    global_used_defns = global_used_defns_new

    placed_phi = dict()
    writes = dict([(k, set()) for k in cfg.nodes])

    # collect all writes per BB
    for n in cfg.nodes:
        w = set()
        for stmtcon in cfg.nodes[n]:
            if len(stmtcon.rwinfo['writes']) == 0: continue

            if global_used_defns is not None:
                if len(global_used_defns.intersection(stmtcon.rdef_def)):
                    # note there will only be one write...
                    assert len(stmtcon.rwinfo['writes']) <= 1
                    w = w | stmtcon.rwinfo['writes']
                else:
                    logger.debug(f"Write to {stmtcon.rwinfo['writes']}/{stmtcon.rdef_def} is dead beyond BB {n}")
            else:
                w = w | stmtcon.rwinfo['writes']

        writes[n] = w

    logger.debug(f'Writes per BB: {writes}')

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
                        logger.debug(f'Placing phi for {w} in node {n} in its dominance frontier node {dfn}')
                        placed_phi[dfn].add(w)
                        writes[dfn].add(w) #TODO: adding a write to the DF is only useful if there is a consumer otherwise it's a dead phi
                        placed = True

    logger.debug(f'placed_phi = {placed_phi}')
    for n, phiv in placed_phi.items():
        bb = cfg.nodes[n]
        phistmts = []

        for v in sorted(phiv): # make argument order deterministic
            incoming = [smt2ast.Symbol(v) for i in range(len(cfg.pred[n]))]
            phistmt = Stmt(smt2ast.SExprList(smt2ast.Symbol('='), smt2ast.Symbol(v),
                                                smt2ast.SExprList(smt2ast.Symbol('phi'),
                                                                  *incoming)))
            phistmts.append(phistmt)
            phistmt.rwinfo = {'reads': set([v]), 'writes': set([v])}

        bb[0:0] = phistmts

    if no_phi_for_dead_writes:
        while remove_dead_phi(cfg, dom):
            pass


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

class SSAPlacePhiPass(Pass):
    """First half of SSA conversion, placing phi functions at dominance frontiers."""
    def run(self, ctx):
        get_reads_and_writes(ctx.cfg)
        dom = ctx.cfg.run_idfa(Dominators())
        place_phi(ctx.cfg, dom)
        return True

class SSABranchesToFunctionsPass(Pass):
    """Converts branches at the end of basic blocks to function calls.

       Required only if converting ultimately to functional form."""

    def run(self, ctx):
        branches_to_functions(ctx.cfg)

        # update reads and writes for newly created function calls
        #TODO: should do this incrementally
        get_reads_and_writes(ctx.cfg)
        return True

class SSARenameVariablesPass(Pass):
    """Second half of SSA conversion, renaming variables."""

    def run(self, ctx):
        rdef = ctx.cfg.run_idfa(ReachingDefinitions())
        params = None if ctx.params is None else set(ctx.params)
        renamed = rename(rdef, params=params)
        ctx.cfg.orig_names = renamed

        return True

def assemble_convert_to_SSA(pm, cvt_branches_to_functions = True):
    """Add the passes required to convert a CFG to SSA form."""
    pm.add(SSAPlacePhiPass())

    if pm.ctx.config.name_prefix:
        prefix = '-' + pm.ctx.config.name_prefix
    else:
        prefix = ''

    if pm.ctx.config.dump_cfg:
        pm.add(CFGDumperPass(f'cfg{prefix}-phi.dot'))

    if cvt_branches_to_functions: pm.add(SSABranchesToFunctionsPass())

    pm.add(SSARenameVariablesPass())

    if pm.ctx.config.dump_cfg:
        pm.add(CFGDumperPass(f'cfg{prefix}-renamed.dot'))

    return pm

# legacy, do not use.
def convert_to_SSA(cfg, cvt_branches_to_functions = True, dump_cfg = False, name_prefix = ''):
    get_reads_and_writes(cfg)
    dom = cfg.run_idfa(Dominators())
    place_phi(cfg, dom)

    if name_prefix != '': name_prefix = '_' + name_prefix

    if dump_cfg:
        logger.debug(f'Dumping CFG after phi placement to cfg-phi{name_prefix}.dot')
        cfg.dump_dot(f'cfg-phi{name_prefix}.dot')

    if cvt_branches_to_functions:
        logger.debug(f'Converting branches to function calls')
        branches_to_functions(cfg)
        get_reads_and_writes(cfg)

    rdef = cfg.run_idfa(ReachingDefinitions())
    renamed = rename(rdef)
    if dump_cfg:
        logger.debug(f'Dumping CFG after renaming to cfg-renaming{name_prefix}.dot')
        cfg.dump_dot(f'cfg-renaming{name_prefix}.dot')

    return renamed

