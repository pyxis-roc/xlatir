#!/usr/bin/env python3
#
# xir.py
#
# eXtensible, Xlation (translation) IR for semantics. Converting the
# semantics expressed in the Python-like IR into other languages. Also
# includes utilities like type inference and loop unrolling.
#
# Author: Sreepathi Pai
#
# TODO: Move this into a separate package gpurosetta?

import ast
import extract_ex_semantics
import argparse
from collections import namedtuple
import astunparse
from xirtyping import *

Def_GenericCompare = PolyTyDef(["gamma"], TyApp(TyConstant('bool'),
                                                [TyVar("gamma"), TyVar("gamma")]))

Def_GenericBinOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"),
                                              [TyVar("gamma"), TyVar("gamma")]))

Def_GenericUnaryOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"), [TyVar("gamma")]))

Def_IfExp = PolyTyDef(["if_gamma"], TyApp(TyVar("if_gamma"),
                                          [TyConstant('bool'),
                                           TyVar("if_gamma"),
                                           TyVar("if_gamma")]))


ARITH_FNS = set(['ADD', 'SUB', 'MUL', 'DIV', 'POW', 'REM'])
BITWISE_FNS = set(['AND'])
COMPARE_FNS = set(['GT', 'LT'])
FLOAT_FNS = set(['ROUND', 'FTZ', 'SATURATE', 'ABSOLUTE', 'ISNAN'])

class TypeEqnGenerator(ast.NodeVisitor):
    def __init__(self):
        self.type_variables = {}
        self.equations = []
        self.ret = 0
        self.fn = None

    def generate_type_variable(self, name, literal=None):
        assert name not in self.type_variables

        if literal is None:
            ty = TyVar(f"TY:{name}")
        else:
            ty = TyVarLiteral(f"TY:{name}", literal)

        self.type_variables[name] = ty
        return ty

    def get_or_gen_ty_var(self, name, literal = None):
        if name not in self.type_variables:
            return self.generate_type_variable(name, literal)

        return self.type_variables[name]

    def visit_Attribute(self, node):
        if isinstance(node.value, ast.Name) and node.value.id == 'cc_reg':
            if node.attr == 'cf':
                return self.get_or_gen_ty_var('cc_reg.cf')

        raise NotImplementedError(f"Attribute node {node} not handled")

    def visit_FunctionDef(self, node):
        for a in node.args.args:
            t = self.get_or_gen_ty_var(a.arg)
            a._xir_type = t

        ret = self.get_or_gen_ty_var(f"fn_{node.name}_retval")
        fnty = TyApp(ret, [a._xir_type for a in node.args.args])
        node._xir_type = fnty

        # not supported
        assert node.args.vararg is None
        assert node.args.kwarg is None

        self.fn = node
        x = self.generic_visit(node)
        self.fn = None
        return x

    def visit_Return(self, node):
        if node.value:
            tyv = self.visit(node.value)
        else:
            tyv = TyConstant('void')

        self.equations.append(TyEqn(tyv, self.fn._xir_type.ret))

    def _generate_poly_call_eqns(self, fn, args, typedef):
        ret = self.get_or_gen_ty_var(f"ret{self.ret}")
        fnt = self.get_or_gen_ty_var(f"{fn}{self.ret}") # this is polymorphic ops

        subst = {}
        for uqv in typedef.uqvars:
            uqt = self.get_or_gen_ty_var(f"{uqv}{self.ret}")
            subst[uqv] = uqt.name

        self.ret += 1

        arg_types = [self.visit(a) for a in args]
        app = TyApp(ret, arg_types)
        defty = typedef.get(subst)

        self.equations.append(TyEqn(fnt, app))
        self.equations.append(TyEqn(app, defty))

        return ret, fnt, defty, app

    def visit_Compare(self, node):
        # not supported
        assert len(node.ops) == 1, node
        assert len(node.comparators) == 1, node

        if isinstance(node.ops[0], ast.Lt):
            fn = f'op_Lt'
        elif isinstance(node.ops[0], ast.Gt):
            fn = f'op_Gt'
        else:
            raise NotImplementedError(f"Unknown compare operator: {node.ops[0]}")

        args = [node.left, node.comparators[0]]
        ret, fnt, defty, app = self._generate_poly_call_eqns(fn, args,
                                                             Def_GenericCompare)

        node._xir_type = fnt

        return ret

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Add):
            fn = f'op_Add'
        elif isinstance(node.op, ast.Mult):
            fn = f'op_Mult'
        elif isinstance(node.op, ast.Sub):
            fn = f'op_Sub'
        elif isinstance(node.op, ast.Pow):
            fn = f'op_Pow'
        elif isinstance(node.op, ast.Mod):
            fn = f'op_Mod'
        elif isinstance(node.op, ast.BitAnd):
            fn = f'op_BitAnd'
        else:
            raise NotImplementedError(f"Unknown binary operator: {node.op}")

        ret, fnt, _, _ = self._generate_poly_call_eqns(fn, [node.left, node.right],
                                                       Def_GenericBinOp)
        node._xir_type = fnt

        return ret

    def visit_Num(self, node):
        #TODO: more nuanced?
        return self.get_or_gen_ty_var(node.n, literal=node.n)

    def visit_UnaryOp(self, node):
        self.generic_visit(node)

        if isinstance(node.op, ast.USub):
            fn = f'op_USub'
        else:
            raise NotImplementedError(f"Unknown operator: {node.op}")

        ret, fnt, _, app = self._generate_poly_call_eqns(fn, [node.operand], Def_GenericUnaryOp)
        node._xir_type = fnt

        return ret

    def visit_Call(self, node):
        def _get_ty_from_fn_call(vararg, signarg, tyarg, widtharg):
            assert isinstance(vararg, ast.Name)
            v = vararg.id

            assert isinstance(signarg, ast.NameConstant)
            sign = signarg.value

            assert isinstance(tyarg, ast.Str) # changes in 3.8?
            ty = tyarg.s

            assert isinstance(widtharg, ast.Num) # changes in 3.8?
            width = widtharg.n

            if ty == 'Integer':
                fullty = f"{'s' if sign else 'u'}{width}"
            elif ty == 'Float':
                fullty = f"f{width}"
            else:
                assert False, f"Unrecognized type: {ty}"

            return v, fullty

        if isinstance(node.func, ast.Name):
            fn = node.func.id
            if fn == 'set_sign_bitWidth':
                v, fullty = _get_ty_from_fn_call(node.args[0], node.args[1],
                                                 node.args[2], node.args[3])

                tv = self.get_or_gen_ty_var(v)
                self.equations.append(TyEqn(tv, TyConstant(fullty)))
                return tv
            elif fn == 'set_value':
                v, fullty = _get_ty_from_fn_call(node.args[2], node.args[0],
                                                 node.args[3], node.args[1])
                tv = self.get_or_gen_ty_var(v)
                self.equations.append(TyEqn(tv, TyConstant(fullty)))
                return tv
            elif fn in ARITH_FNS or fn in BITWISE_FNS:
                #note: call is: add(a, b, 'Integer', 16), so there is type information we're not using?
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                               Def_GenericBinOp)
                node._xir_type = fnt

                return ret
            elif fn in COMPARE_FNS:
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                               Def_GenericCompare)

                node._xir_type = fnt
            elif fn in FLOAT_FNS:
                # note: saturate also carries a type, but not a width ...
                argty = self.visit(node.args[0])
                #TODO: add equations?
                node._xir_type = TyApp(argty, [argty])
                return argty
            elif fn == 'set_memory':
                sm_var = self.get_or_gen_ty_var(fn)
                addrty = self.visit(node.args[0])
                sm_ty = TyApp(TyConstant('void'), [TyConstant('intptr_t'), self.visit(node.args[1])])
                self.equations.append(TyEqn(sm_var, sm_ty))
                self.equations.append(TyEqn(addrty, TyConstant('intptr_t')))
            elif fn == 'int':
                return self.visit(node.args[0])

        fnt = self.get_or_gen_ty_var(f'unknown_fn{self.ret}')
        self.ret += 1
        self.generic_visit(node)

        return fnt

    def visit_IfExp(self, node):
        ret, fnt, depty, _ = self._generate_poly_call_eqns("if_exp",
                                                           [node.test, node.body, node.orelse],
                                                           Def_IfExp)
        return ret

    def visit_Name(self, node):
        v = self.get_or_gen_ty_var(node.id)
        node._xir_type = v
        return v

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Multiple targets in assign not supported"

        lhs = self.visit(node.targets[0])
        rhs = self.visit(node.value)

        self.equations.append(TyEqn(lhs, rhs))
        # no return because this is a statement


def find(n, reps):
    key = str(n)

    if key not in reps:
        reps[key] = n

    if reps[key] is not n:
        r = find(reps[key], reps)
        reps[key] = r

    return reps[key]

def union(s, t, reps):
    if isinstance(s, TyConstant):
        reps[str(t)] = reps[str(s)]
    elif isinstance(t, TyConstant):
        reps[str(s)] = reps[str(t)]
    else:
        reps[str(s)] = reps[str(t)]

# dragon book, figure 6.32
def unify(m, n, reps = None):
    if reps is None:
        reps = {}

    s = find(m, reps)
    t = find(n, reps)

    #print(f"{m} {s}")
    #print(f"{n} {t}")

    if s is t: return True

    if isinstance(s, TyConstant) and isinstance(t, TyConstant) and s == t: return True

    if isinstance(s, TyApp) and isinstance(t, TyApp):
        if len(s.args) == len(t.args):
            union(s, t, reps)
            if not unify(s.ret, t.ret, reps):
                return False

            for a, b in zip(s.args, t.args):
                if not unify(a, b, reps):
                    print(f"Failed to unify {a} and {b}")
                    return False

            return True
        else:
            return False

    if isinstance(s, TyVar) or isinstance(t, TyVar):
        union(s, t, reps)
        return True

    print("FAIL", s, t)
    return False

def infer_types(insn_sem):
    # generate type equations
    print(astunparse.unparse(insn_sem))
    print(ast.dump(insn_sem))
    eqg = TypeEqnGenerator()
    eqg.visit(insn_sem)
    reps = {}
    #print(eqg.type_variables)
    #print(eqg.equations)

    for eq in eqg.equations:
        print(eq)

    for eq in eqg.equations:
        if not unify(eq.lhs, eq.rhs, reps):
            assert False, f"Failing to unify: {eq}"

    print("****")
    for v in reps:
        print(v, reps[v], find(reps[v], reps))

    return reps

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Run various bits of xir on a semantic")
    p.add_argument('semfile', help="File containing executable semantics")
    p.add_argument('task', help="Task to perform", choices=['types'])
    p.add_argument('ptxinsn', nargs="+", help="PTX instruction in underscore form (e.g. add_u16)")

    args = p.parse_args()
    semantics = extract_ex_semantics.load_execute_functions(args.semfile)

    if args.task == 'types':
        if len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all':
            args.ptxinsn = [k[len("execute_"):] for k in semantics]

        for pi in args.ptxinsn:
            infer_types(semantics["execute_" + pi])

