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

class TypeEqnGenerator(ast.NodeVisitor):
    def __init__(self):
        self.type_variables = {}
        self.equations = []
        self.ret = 0

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
            self.get_or_gen_ty_var(a.arg)

        # not supported
        assert node.args.vararg is None
        assert node.args.kwarg is None

        return self.generic_visit(node)

    def _generate_poly_call_eqns(self, fn, args):
        ret = self.get_or_gen_ty_var(f"ret{self.ret}")
        fnt = self.get_or_gen_ty_var(f"{fn}{self.ret}") # this is polymorphic ops
        gmt = self.get_or_gen_ty_var(f"gamma{self.ret}") # this are polymorphic ops
        self.ret += 1

        arg_types = [self.visit(a) for a in args]

        app = TyApp(ret, arg_types)
        self.equations.append(TyEqn(fnt, app))
        self.equations.append(TyEqn(app, TyApp(gmt, [gmt] * len(args))))

        return ret, fnt, gmt, app

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

        ret = self.get_or_gen_ty_var(f"ret{self.ret}")
        fnt = self.get_or_gen_ty_var(f"{fn}{self.ret}") # this is polymorphic ops
        gmt = self.get_or_gen_ty_var(f"gamma{self.ret}") # this are polymorphic ops
        self.ret += 1

        arg_types = [self.visit(a) for a in [node.left, node.comparators[0]]]

        app = TyApp(ret, arg_types)
        self.equations.append(TyEqn(fnt, app))
        #TODO: this requires a typedef
        self.equations.append(TyEqn(app, TyApp(TyConstant('bool'), [gmt, gmt])))

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

        ret, fnt, _, _ = self._generate_poly_call_eqns(fn, [node.left, node.right])
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

        ret, fnt, _, app = self._generate_poly_call_eqns(fn, [node.operand])

        # not needed?
        #self.equations.append(TyEqn(ret, app.args[0])) # unary operators have the same type as their arguments
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
            elif fn in ('add', 'sub', 'mul', 'div', 'pow'):
                #note: call is: add(a, b, 'Integer', 16), so there is type information we're not using?
                ret, fnt, gmt, _ = self._generate_poly_call_eqns(fn, node.args[:2])
                node._xir_type = fnt

                return ret
            elif fn in ('set_round', 'FTZ', 'saturate', 'ABSOLUTE', 'isnan'):
                # note: saturate also carries a type, but not a width ...
                return self.visit(node.args[0])

        fnt = self.get_or_gen_ty_var(f'unknown_fn{self.ret}')
        self.ret += 1
        self.generic_visit(node)

        return fnt

    def visit_IfExp(self, node):
        tt = self.visit(node.test)
        tcbool = TyConstant('bool')
        self.equations.append(TyEqn(tt, tcbool))

        bt = self.visit(node.body)
        ort = self.visit(node.orelse)

        ret = self.get_or_gen_ty_var(f"if_{self.ret}")
        gt = self.get_or_gen_ty_var(f"if_gamma_{self.ret}")
        self.ret += 1

        #TODO: use type definitions
        self.equations.append(TyEqn(TyApp(ret, [tcbool, bt, ort]),
                                    TyApp(gt, [tcbool, gt, gt])))

        return ret

    def visit_Name(self, node):
        return self.get_or_gen_ty_var(node.id)

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Multiple targets in assign not supported"

        lhs = self.visit(node.targets[0])
        rhs = self.visit(node.value)

        self.equations.append(TyEqn(lhs, rhs))
        # no return because this is a statement


def find(n):
    if not hasattr(n, '_rep') and isinstance(n, (TyConstant, TyApp)):
        n._rep = n

    if n._rep is not n:
        r = find(n._rep)
        n._rep = r # short

    return n._rep

def union(s, t):
    if isinstance(s, TyConstant):
        t._rep = s._rep
    elif isinstance(t, TyConstant):
        s._rep = t._rep
    else:
        s._rep = t._rep

# dragon book, figure 6.32
def unify(m, n):
    s = find(m)
    t = find(n)

    #print(f"{m} {s}")
    #print(f"{n} {t}")

    if s is t: return True

    if isinstance(s, TyConstant) and isinstance(t, TyConstant) and s == t: return True

    if isinstance(s, TyApp) and isinstance(t, TyApp):
        if len(s.args) == len(t.args):
            union(s, t)
            if not unify(s.ret, t.ret):
                return False

            for a, b in zip(s.args, t.args):
                if not unify(a, b):
                    print(f"Failed to unify {a} and {b}")
                    return False

            return True
        else:
            return False

    if isinstance(s, TyVar) or isinstance(t, TyVar):
        union(s, t)
        return True

    print("FAIL", s, t)
    return False

def infer_types(insn_sem):
    # generate type equations
    print(astunparse.unparse(insn_sem))
    print(ast.dump(insn_sem))
    eqg = TypeEqnGenerator()
    eqg.visit(insn_sem)
    print(eqg.type_variables)
    #print(eqg.equations)

    tyvar = eqg.type_variables
    for v in tyvar:
        tyvar[v]._rep = tyvar[v]

    for eq in eqg.equations:
        print(eq)

    for eq in eqg.equations:
        if not unify(eq.lhs, eq.rhs):
            assert False, f"Failing to unify: {eq}"

    for v in tyvar:
        print(v, tyvar[v], find(tyvar[v]))

    pass


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

