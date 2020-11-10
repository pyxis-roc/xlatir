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
        wl = [self.cfg.start_node]

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
                if len(stmt.v):
                    sym = stmt.v[0].v
                else:
                    sym = None

                if sym is None:
                    pass
                elif sym not in ('=', 'branch', 'cbranch', 'label'):
                    output_engine.xlat_stmt(stmt)
                elif sym == '=' and smt2ast.is_call(stmt.v[2], "phi"):
                    pass
                else:
                    # ignore all statements
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

        output_engine.start()
        if output_engine.linear:
            self.fixup_linear_calls()
            self.dump_linear(output_engine, n = self.cfg.start_node)
        else:
            self.dump_nested(output_engine, n = self.cfg.start_node)

        output_engine.finish()

class OutputBackend(object):
    param_order = {}

    def set_linear(self, linear):
        raise NotImplementedError

    def set_param_order(self, param_order):
        self.param_order = dict([(p, i) for i, p in enumerate(param_order)])
        assert len(self.param_order) == len(param_order), f"Duplicates in param_order"

    def get_symtypes(self):
        out = {}
        phi = []
        for n in self.func.cfg.nodes:
            bb = self.func.cfg.nodes[n]
            for stmtcon in bb:
                stmt = stmtcon.stmt
                if smt2ast.is_call(stmt, 'type'):
                    v = str(stmt.v[1])
                    if v not in out: out[v] = set()
                    out[v].add(str(stmt.v[2]))
                elif is_phi(stmt):
                    phi.append(stmt)

        for pstmt in phi:
            v = str(pstmt.v[1])
            if v in self.func.cfg.orig_names and self.func.cfg.orig_names[v] == '_retval':
                continue

            phicall = pstmt.v[2]
            ty = reduce(lambda x, y: x.union(y), [out[av.v] for av in phicall.v[2:] if av.v in out], set())
            out[v] = set(ty)
            assert len(out[v]) > 0, f"phi variable {v} has no types"
            assert len(out[v]) == 1, f"phi variable {v} has multiple types {out[v]}"

        return out

    def get_output(self):
        raise NotImplementedError

    def start(self):
        raise NotImplementedError

    def open_func(self):
        raise NotImplementedError

    def close_func(self):
        raise NotImplementedError

    def open_let(self):
        raise NotImplementedError

    def close_let(self):
        raise NotImplementedError

    def xlat_func_def(self, n, params):
        raise NotImplementedError

    def xlat_let(self, lstmts, level):
        raise NotImplementedError

    def xlat_stmt(self, s):
        raise NotImplementedError

    def finish(self):
        raise NotImplementedError

class PyOutput(OutputBackend):
    def __init__(self):
        self.nesting = 0
        self.output = []

    def set_linear(self, linear):
        self.linear = linear

    def start(self):
        pass

    def finish(self):
        #self.output.append("print(_START())")
        pass

    def get_output(self):
        return '\n'.join(self.output)

    def open_func(self):
        self.nesting += 1

    def close_func(self):
        self.nesting -= 1

        assert self.nesting >= 0
        self.output.append("")

    def open_let(self):
        # we ignore nests for let since we serialize lets in Python
        pass

    def close_let(self):
        pass

    def xlat_func_def(self, n, params):
        assert self.nesting >= 0

        ind = "  " * self.nesting
        if n == self.func.cfg.start_node:
            params = sorted(params, key = lambda x: self.param_order.get(x, len(self.param_order)))

        self.output.append(f"{ind}def {n}({', '.join(params)}): # let_levels={self.func.let_levels[n]}, captured_params={self.func.captured_parameters[n]}")

    def xlat_let(self, lstmts, level):
        for lsi in lstmts:
            self.xlat_stmt(lsi)

    def xlat_stmt(self, s):
        ss = self._strify_stmt(s)
        if ss: self.output.append("  "*self.nesting + ss)

    def _strify_stmt(self, s):
        if smt2ast.is_call(s, "="):
            return f"{s.v[1]} = {self._strify_stmt(s.v[2])}"
        elif smt2ast.is_call(s, 'type'):
            return ''
        elif smt2ast.is_call(s, "branch"):
            return f"return {self._strify_stmt(s.v[1])}"
        elif smt2ast.is_call(s, "cbranch"):
            return f"return {self._strify_stmt(s.v[2])} if {self._strify_stmt(s.v[1])} else {self._strify_stmt(s.v[3])}"
        elif isinstance(s, (smt2ast.Symbol, smt2ast.Decimal, smt2ast.Numeral)):
            return str(s)
        elif isinstance(s, smt2ast.Binary):
            return f'0b' + str(s)[2:]
        elif isinstance(s, smt2ast.Hexadecimal):
            return f'0x' + str(s)[2:]
        elif isinstance(s, smt2ast.SExprList):
            fn = self._strify_stmt(s.v[0])
            args = [self._strify_stmt(x) for x in s.v[1:]]

            if fn in ('<', '+', '=='): # infix
                return f"({args[0]} {fn} {args[1]})"
            else:
                # TODO: add translations for SMT2 internal functions to Python?
                args = ', '.join(args)
                return f"{fn}({args})"
        else:
            raise NotImplementedError(f"No translation for {s}/{type(s)} to python yet")

class SMT2Output(OutputBackend):
    def __init__(self, symtypes, entry_fn = None):
        self.nesting = 0
        self.output = []
        self.output_fn = {}
        self.fn = None
        self.linear = True
        self.symtypes = symtypes
        self._entry_fn = entry_fn if entry_fn is not None else lambda n, params, ret_type: (n, "(" + str(params) + ")", ret_type)
        self._xir_attr_refs = {}

    def _get_func_return_types(self):
        def find(x):
            if x in self.symtypes:
                return x
            elif x in self.func.cfg.orig_names:
                return self.func.cfg.orig_names[x]

            if out[x] != x:
                return find(out[x])

            return out[x]

        def unify(x, y):
            nx = find(y)
            if nx != out[x]:
                out[x] = nx
                return True

            return False

        # if this turns into an infinite loop, it indicates the
        # presence of a loop that does not lead to _EXIT
        out = dict([(n, n) for n in self.func.cfg.nodes])
        changed = True
        while changed:
            changed = False
            for n in self.func.order:
                bb = self.func.cfg.nodes[n]
                last_stmt = bb[-1].stmt

                if smt2ast.is_call(last_stmt, "return"):
                    changed = unify(n, "_retval") or changed
                elif smt2ast.is_call(last_stmt, "branch"):
                    changed = unify(n, last_stmt.v[1].v[0].v) or changed
                elif smt2ast.is_call(last_stmt, "cbranch"):
                    changed = unify(n, last_stmt.v[2].v[0].v) or changed
                    changed = unify(n, last_stmt.v[3].v[0].v) or changed
                else:
                    assert False, last_stmt

        self.func_types = out

    def start(self):
        self._xir_attr_refs = {}
        self.symtypes.update(self.get_symtypes())

        # infer types for retval
        for n in self.func.cfg.nodes:
            for stmtcon in self.func.cfg.nodes[n]:
                stmt = stmtcon.stmt
                if smt2ast.is_call(stmt, '='):
                    if stmt.v[1].v.startswith('_retval_'):
                        if isinstance(stmt.v[2], smt2ast.Symbol):
                            # only (= _retval symbol) not (= _retval (fn ...))
                            for r in stmtcon.rwinfo['reads']:
                                try:
                                    self.symtypes['_retval'] = set([self.get_type(r)])
                                    break
                                except ValueError:
                                    continue

                        if '_retval' in self.symtypes: break

            if '_retval' in self.symtypes: break

        if '_retval' not in self.symtypes:
            raise ValueError(f'Unable to infer type for _retval, must be supplied')

        self._get_func_return_types()

    def set_linear(self, linear):
        if linear == False: print("WARNING: SMT2 backend only supports linear output")
        self.linear = True

    def get_output(self):
        def _output_fn(fo):
            n, params, ret_type = fo[0]
            if rec:
                out = f"(define-fun-rec {n} {params} {ret_type}"
            else:
                out = f"(define-fun {n} {params} {ret_type}"

            return out + '\n' + '\n'.join(fo[1:])

        assert len(self.output) == 0, "Function {self.fn} not closed"

        order = self.func.cfg.topo_order()
        if order is None:
            # TODO: identify SCCs and only make them recursive...
            rec = True
            # TODO: identify SCCs and actually get a proper ordering ...
            order = list(self.output_fn.keys())
        else:
            rec = False

        return '\n'.join([_output_fn(self.output_fn[fn]) for fn in order if fn in self.output_fn])

    def finish(self):
        #print("print(_START())")
        pass

    def open_func(self):
        self.nesting += 1

    def close_func(self):
        self.nesting -= 1

        assert self.nesting >= 0
        self.output.append(")")
        self.output.append('')
        self.output_fn[self.fn] = self.output
        self.output = []
        self.fn = None

    def open_let(self):
        self.nesting += 1

    def close_let(self):
        self.nesting -= 1
        assert self.nesting >= 0

        self.output.append('  '*self.nesting + ')')

    def get_type(self, v):
        # check if renamed variable is in self.symtypes (due to inline types)
        if v not in self.symtypes:
            # otherwise check if there is an original name
            if v in self.func.cfg.orig_names:
                orig_name = self.func.cfg.orig_names[v]
            else:
                orig_name = v
        else:
            orig_name = v

        if orig_name not in self.symtypes:
            raise ValueError(f"No type for symbol '{v}'/'{orig_name}' found")

        ty = self.symtypes[orig_name]
        if len(ty) > 1:
            print(self.symtypes)
            raise ValueError(f"Multiple types {ty} for symbol '{v}'/'{orig_name}'")

        return next(iter(ty))

    def xlat_entry_fn(self, n, params, ret_type):
        return self._entry_fn(n, params, ret_type)

    def xlat_func_def(self, n, params):
        assert self.nesting >= 0

        self.fn = n

        if n == self.func.cfg.start_node:
            params = sorted(params, key = lambda x: self.param_order.get(x, len(self.param_order)))

        params_types = [(p, self.get_type(p)) for p in params]
        params = " ".join([f"({p} {ptype})" for p, ptype in params_types])
        ret_type = self.get_type(self.func_types[n])

        if n == self.func.cfg.start_node:
            self.output.append(self.xlat_entry_fn(n, params, ret_type))
        else:
            self.output.append((n, "(" + params + ")", ret_type))

        self.output.append(f'; let_levels={self.func.let_levels[n]}, captured_params={self.func.captured_parameters[n]}')

    def xlat_let(self, lstmts, level):
        lets = []

        for ls in lstmts:
            if smt2ast.is_call(ls.v[1], '_xir_attr_ref'):
                ss = str(ls.v[1])
                self._xir_attr_refs[ss] = ls.v[2]
            else:
                lets.append(f'({self._strify_stmt(ls.v[1])} {self._strify_stmt(ls.v[2])})')

        if len(lets):
            lets = ' '.join(lets)
            self.output.append("  "*self.nesting + f'(let ({lets})')

    def xlat_stmt(self, s):
        ss = self._strify_stmt(s)
        if ss: self.output.append("  "*self.nesting + ss)

    def _strify_stmt(self, s):
        if smt2ast.is_call(s, "="):
            return f"(= {s.v[1]} {self._strify_stmt(s.v[2])})"
        elif smt2ast.is_call(s, "type"):
            return ""
        elif smt2ast.is_call(s, "branch"):
            return self._strify_stmt(s.v[1])
        elif smt2ast.is_call(s, "cbranch"):
            return f"(ite {self._strify_stmt(s.v[1])} {self._strify_stmt(s.v[2])} {self._strify_stmt(s.v[3])})"
        elif isinstance(s, (smt2ast.Symbol, smt2ast.Decimal, smt2ast.Numeral, smt2ast.Hexadecimal, smt2ast.Binary)):
            return str(s)
        elif isinstance(s, smt2ast.String):
            return repr(s)
        elif isinstance(s, smt2ast.SExprList):
            if smt2ast.is_call(s, 'return'):
                return self._strify_stmt(s.v[1])
            elif smt2ast.is_call(s, '_xir_attr_ref'):
                ss = str(s)
                if ss in self._xir_attr_refs:
                    # replace with written value
                    return self._strify_stmt(self._xir_attr_refs[ss])
                else:
                    # use selector to read
                    return self._strify_stmt(smt2ast.SExprList(smt2ast.Symbol(s.v[1].v),
                                                               s.v[2]))
            else:
                strify = ' '.join([self._strify_stmt(x) for x in s.v])
                return f"({strify})"
        else:
            raise NotImplementedError(f"No translation for {s}/{type(s)} to smt2 yet")

def convert_ssa_to_functional(backend, ssa_cfg, globalvars, linear = False):
    backend.set_linear(linear)

    fcfg = FunctionalCFG(ssa_cfg, globalvars)
    fcfg.convert(backend)

def convert_to_functional(statements, globalvars, backend, linear = False, name_prefix = '', dump_cfg = False, prune_unreachable = False, error_on_non_exit_nodes = False):
    if len(statements) and smt2ast.is_call(statements[0], "global"):
        inline_globals = set([str(s) for s in statements[0].v[1:]])
        statements = statements[1:]
        globalvars |= inline_globals

    if len(statements) and smt2ast.is_call(statements[0], "param"):
        param_order = [str(s) for s in statements[0].v[1:]]
        statements = statements[1:]
        backend.set_param_order(param_order)

    cfg = get_cfg(statements, name_prefix)
    cfg.check_structure(prune_unreachable = prune_unreachable)

    if cfg.check_non_exit(True):
        print("WARNING: CFG contains nodes that cannot reach exit. Nodes removed and CFG patched. This may not be what you want!")
        if error_on_non_exit_nodes:
            print("ERROR: Exiting on presence of non-exit nodes as requested")
            return None

    if dump_cfg: cfg.dump_dot(f'cfg{"_" if name_prefix else ""}{name_prefix}.dot')
    orig_names = convert_to_SSA(cfg, cvt_branches_to_functions = True, dump_cfg = dump_cfg)
    cfg.orig_names = orig_names
    if dump_cfg: cfg.dump_dot(f'cfg-after-ssa{"_" if name_prefix else ""}{name_prefix}.dot')
    convert_ssa_to_functional(backend, cfg, globalvars, linear)
    return cfg

def read_inline_types(stmts):
    out = {}
    for s in stmts:
        if smt2ast.is_call(s, 'type'):
            v = str(s.v[1])
            ty = str(s.v[2])
            if v not in out:
                out[v] = set([ty])
            else:
                out[v].add(ty)

    return out

def read_types_file(tf):
    out = {}
    with open(tf, "r") as f:
        for l in f:
            ls = l.strip()
            if not ls or (ls[0] == '#'): continue

            sym, symtype = ls.split(' ', 1)
            if sym not in out: out[sym] = set()
            out[sym].add(symtype)

    return out

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

    args = p.parse_args()

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
        print(backend.get_output())

