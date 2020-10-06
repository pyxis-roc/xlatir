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

def convert_to_SSA(cfg, cvt_branches_to_functions = True):
    get_reads_and_writes(cfg)
    dom = cfg.run_idfa(Dominators())
    #dom.dump_idom_dot("idom.dot")
    place_phi(cfg, dom.frontier)
    if cvt_branches_to_functions: branches_to_functions(cfg)
    rdef = cfg.run_idfa(ReachingDefinitions())
    rename(rdef)
