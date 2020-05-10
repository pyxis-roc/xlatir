#!/usr/bin/python3
#
# xirxlat.py
#
# Utilities for helping with translating XIR to other languages

import xir
import ast
import extract_ex_semantics
from xirtyping import *

# The passing of actual arguments instead of just node in the xlat_*
# functions is meant to make things convenient. In case this doesn't
# work, a class where only the node is passed and the arguments are
# passed as lambdas returning a dictionary might be useful?

class Xlator(object):
    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor

    def get_declaration(self, node, declname = None):
        # must return a declaration
        raise NotImplementedError

    def get_native_type(self, xirty, declname = None):
        raise NotImplementedError

    def xlat_Name(self, name: str, node):
        raise NotImplementedError

    def xlat_NameConstant(self, value, node):
        raise NotImplementedError

    def xlat_Attribute(self, value, attr: str, node):
        raise NotImplementedError

    def xlat_Str(self, s, node):
        raise NotImplementedError

    def xlat_Num(self, n, nty, node):
        raise NotImplementedError

    def xlat_BoolOp(self, op, opty, values, node):
        raise NotImplementedError

    def xlat_BinOp(self, op, opty, left, right, node):
        raise NotImplementedError

    def xlat_Compare(self, op, opty, left, right, node):
        raise NotImplementedError

    def xlat_UnaryOp(self, op, opty, value, node):
        raise NotImplementedError

    def xlat_IfExp(self, test, body, orelse, opty, node):
        raise NotImplementedError

    def xlat_If(self, test, body, orelse, node):
        raise NotImplementedError

    def xlat_Break(self, node):
        raise NotImplementedError

    def xlat_float_val(self, v):
        raise NotImplementedError

    def xlat_float_compare(self, comparefn, constval, compareto):
        raise NotImplementedError

    def xlat_Call(self, fn, fnty, args, node):
        raise NotImplementedError

    def xlat_Return(self, v, vty, node):
        raise NotImplementedError

    def xlat_Assign(self, lhs, rhs, node): #TODO types?
        raise NotImplementedError

    def xlat_While(self, test, body, node):
        raise NotImplementedError

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        raise NotImplementedError

    def write_output(self, output, translations, defns):
        raise NotImplementedError

class XIRToX(ast.NodeVisitor):
    X = None # structured like a node visitor, except with xlat_X instead of visit_X

    def _get_type(self, tyterm):
        ty = xir.find(tyterm, self.types)
        if isinstance(ty, TyApp):
            ty = TyApp(self._get_type(ty.ret), [self._get_type(a) for a in ty.args])

        # TODO: other types
        assert isinstance(ty, TyTerm)
        return ty

    def _get_op_type(self, op, opty):
        opty = xir.find(opty, self.types)
        assert isinstance(opty, TyApp)
        arg_types = [self.X.get_native_type(self._get_type(a)) for a in opty.args]

        if len(arg_types) == 2:
            return (op, arg_types[0], arg_types[1])
        elif len(arg_types) == 1:
            return (op, arg_types[0])
        elif len(arg_types) > 2: # TODO: break this up?
            if op == '||' or op == '&&':
                return tuple([op] + arg_types)
            elif op == 'logical_op3' and len(arg_types) == 4:
                print("for lop3", arg_types)
                return tuple([op] + arg_types)

        raise NotImplementedError(f"Arguments of length {len(arg_types)} for {op}/{opty} not currently handled")

    def _get_float_val(self, node):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'float':
            assert isinstance(node.args[0], ast.Str), "Don't support non-str-const uses of float"
            x = node.args[0].s.lower()
            s = ''
            if x[0] == '-' or x[1] == '+':
                s = x[0] if x[0] == '-' else ''
                x = x[1:]

            assert x in ('inf', 'nan', '0.0'), f"Unrecognized value {x}"
            return True, s + x

        return False, None

    def visit_Name(self, node):
        if hasattr(self, 'fn') and self.fn:
            if isinstance(node.ctx, ast.Store):
                if node.id not in self.fn._xir_decls:
                    self.fn._xir_decls[node.id] = self.X.get_declaration(node)

        return self.X.xlat_Name(node.id, node)

    def visit_NameConstant(self, node):
        return self.X.xlat_NameConstant(node.value, node)

    def visit_Attribute(self, node):
        #TODO decide whether to use . or ->
        # TODO: use visit
        return self.X.xlat_Attribute(self.visit(node.value), node.attr, node)

    def visit_Str(self, node):
        return self.X.xlat_Str(node.s, node)

    def visit_Num(self, node):
        ty = self.X.get_native_type(self._get_type(node._xir_type))

        return self.X.xlat_Num(node.n, ty, node)

    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.And):
            op = '&&'
        elif isinstance(node.op, ast.Or):
            op = '||'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_BoolOp(op, opty, [self.visit(v) for v in node.values], node)

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Mult):
            op = '*'
        elif isinstance(node.op, ast.BitAnd):
            op = '&'
        elif isinstance(node.op, ast.Add):
            op = '+'
        elif isinstance(node.op, ast.Sub):
            op = '-'
        elif isinstance(node.op, ast.Pow):
            op = '**'
        elif isinstance(node.op, ast.Mod):
            op = '%'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_BinOp(op, opty, self.visit(node.left), self.visit(node.right), node)

    def visit_Compare(self, node):
        assert len(node.ops) == 1, f"Not supported, more than op: {node.ops}"
        assert len(node.comparators) == 1, f"Not supported, more than one comparator: {node.ops}"

        if isinstance(node.ops[0], ast.Lt):
            op = '<'
        elif isinstance(node.ops[0], ast.Gt):
            op = '>'
        else:
            raise NotImplementedError(node.ops[0])

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_Compare(op, opty, self.visit(node.left),
                                   self.visit(node.comparators[0]), node)

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            op = '-'
        elif isinstance(node.op, ast.Not):
            op = '!' # logical not
        elif isinstance(node.op, ast.Invert):
            op = '~'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_UnaryOp(op, opty, self.visit(node.operand), node)

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_IfExp(self, node):
        opty = self._get_type(node._xir_type)

        opty = ('?:', self.X.get_native_type(opty.ret),
                self.X.get_native_type(opty.args[0]),
                self.X.get_native_type(opty.args[1]),
                self.X.get_native_type(opty.args[2]))

        return self.X.xlat_IfExp(self.visit(node.test),
                                 self.visit(node.body),
                                 self.visit(node.orelse),
                                 opty,
                                 node)

    def visit_If(self, node):
        return self.X.xlat_If(self.visit(node.test),
                              [self.visit(x) for x in node.body],
                              [self.visit(x) for x in node.orelse],
                              node)

    def visit_Break(self, node):
        return self.X.xlat_Break(node)

    def visit_Call(self, node):
        #TODO: this str is needed because the return values are from xlat_

        n = str(self.visit(node.func))

        if n == 'set_sign_bitWidth':
            return self.visit(node.args[0])
        elif n == 'int':
            return self.visit(node.args[0])
        elif n == 'set_value':
            return self.visit(node.args[2])
        elif n == 'float':
            _, v = self._get_float_val(node)
            assert v is not None, node.args[0]

            return self.X.xlat_float_val(v)
        elif n == 'FLOAT_COMPARE_EQ' or n == 'FLOAT_COMPARE_NOTEQ':
            _, v = self._get_float_val(node.args[1])
            assert v is not None, node.args[1]

            if v == 'inf' or v == '-inf':
                fn = "!isfinite"
            elif v == 'nan' or v == '-nan':
                fn = "isnan"

            return self.X.xlat_float_compare(n, v, self.visit(node.args[0]))

        #TODO: add the name of the function
        assert hasattr(node, '_xir_type'), f"Function {n} does not have _xir_type on node"

        fnty = self._get_op_type(n, node._xir_type)

        if hasattr(self.X, 'lib'):
            if hasattr(self.X.lib, n):
                fnxlat = getattr(self.X.lib, n)
                return fnxlat(n, fnty, [self.visit(a) for a in node.args], node)

        return self.X.xlat_Call(n, fnty, [self.visit(a) for a in node.args], node)

    def visit_Tuple(self, node):
        # this assumes that this will always be structure initialization
        return [self.visit(e) for e in node.elts]

    def visit_Return(self, node):
        if node.value:
            v = self.visit(node.value)
        else:
            v = None

        #TODO: embed struct name?
        return self.X.xlat_Return(v, self._retval_ty, node)

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Not supported"

        #TODO: types?
        return self.X.xlat_Assign(self.visit(node.targets[0]), self.visit(node.value), node)

    def visit_While(self, node):
        assert len(node.orelse) == 0, f"orelse for While node not supported"

        #TODO: type checking?
        test = self.visit(node.test)
        body = [self.visit(x) for x in node.body]

        return self.X.xlat_While(test, body, node)

    def visit_FunctionDef(self, node):
        # perhaps make this per block?
        self.fn = node

        node._xir_decls = {}
        args = []
        for a in node.args.args:
            t = self.X.get_declaration(a, declname=a.arg)
            node._xir_decls[a.arg] = None
            args.append(t)


        func = node.name
        retval = self.X.get_native_type(node._xir_type.ret,
                                        func[len('execute_'):] if isinstance(self._get_type(node._xir_type.ret), TyProduct) else None)

        self._retval_ty = retval

        # order is important!
        body = [self.visit(s) for s in node.body]
        decls = [(v, t) for (v, t) in self.fn._xir_decls.items() if t is not None]

        self.fn = None

        return self.X.xlat_FunctionDef(func, args, retval, decls, body, node)

    def translate(self, sem, types):
        self.types = types
        #TODO: handle this?
        self.defns = []
        return self.visit(sem)
