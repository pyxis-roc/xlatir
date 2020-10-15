#!/usr/bin/env python3
#
# impssa.py
#
# Convert smt2ast/imp code into SSA form.
#
# Author: Sreepathi Pai
#
# Copyright (C) 2020, University of Rochester

import smt2ast
from impdfanalysis import Dominators, ReachingDefinitions, get_reads_and_writes, Stmt, is_phi
import functools

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

def rename(rdef, sep='_'):
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
            rd = stmtcon.rdef_in
            replacements = [defn2var[rdd] for rdd in rd]

            # restrict definitions to those actually used, needed when phis are not placed for dead writes
            replacements = [x for x in replacements if x[0] in stmtcon.rwinfo['reads']]

            if is_phi(stmt):
                v = stmt.v[2].v[1].v
                repl = [smt2ast.Symbol(x[1]) for x in replacements if x[0] == v]

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

def place_phi(cfg, domfrontier, no_phi_for_dead_writes = True):
    if no_phi_for_dead_writes:
        # in this case, we mean writes that do not cross BB boundaries
        # i.e., they might be used in the BB itself, but are dead beyond it.

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
    else:
        global_used_defns = None

    placed_phi = dict()
    writes = dict([(k, set()) for k in cfg.nodes])

    # collect all writes per BB
    for n in cfg.nodes:
        w = set()
        for stmtcon in cfg.nodes[n]:
            if global_used_defns is not None:
                if len(global_used_defns.intersection(stmtcon.rdef_def)):
                    w = w | stmtcon.rwinfo['writes']
            else:
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

def convert_to_SSA(cfg, cvt_branches_to_functions = True):
    get_reads_and_writes(cfg)
    dom = cfg.run_idfa(Dominators())
    #dom.dump_idom_dot("idom.dot")
    place_phi(cfg, dom.frontier)
    if cvt_branches_to_functions: branches_to_functions(cfg)
    rdef = cfg.run_idfa(ReachingDefinitions())
    renamed = rename(rdef)
    #cfg.dump_dot('after_renaming.dot')
    return renamed

