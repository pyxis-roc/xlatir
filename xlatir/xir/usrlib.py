#!/usr/bin/env python3
#
# usrlib.py
# Support for user-defined libraries.
#
# Author: Sreepathi Pai
#
# Ultimately, we want to move support for intrinsics out of the
# compiler and into user-defined per-language libraries (which can
# include a standard set of XIR libraries, much like SMT-LIB theories).


import ast

XIR_DECL_ANNO = 'xirdecl'

def is_xir_declaration(node):
    def check_decl_deco(dl):
        for x in dl:
            if isinstance(x, ast.Name) and x.id == XIR_DECL_ANNO:
                return True

    def check_stub(f): # mypy style stubs
        if len(f.body) == 1 and isinstance(f.body[0], ast.Expr) \
           and isinstance(f.body[0].value, ast.Ellipsis):
            return True

    return isinstance(node, ast.FunctionDef) and \
        (check_decl_deco(node.decorator_list) or check_stub(node))

def load_xir_declarations(srcfile):
    with open(srcfile, 'r') as f:
        src = ast.parse(f.read(), srcfile)

        out = []
        for l in src.body:
            if is_xir_declaration(l):
                out.append(l)

        return out

class Decl2Type(object):
    TypeConstants = set(['u32', 'b32', 'f32', 's32'])
    def __init__(self, typing):
        self.typing = typing # hack, for now

    def py_type_expr_to_xirtype(self, expr):
        if isinstance(expr, ast.Name):
            if expr.id in self.TypeConstants:
                return self.typing.TyConstant(expr.id)
            else:
                raise SyntaxError(f'Unknown type constant {expr.id}')
        else:
            raise NotImplementedError(f'Unrecognized annotation expression type {expr}')

    def from_FunctionDef(self, fdefnode):
        #TODO: SyntaxCheck to prohibit all other kinds of args

        if not fdefnode.returns:
            raise SyntaxError(f'FunctionDef must have a return type')

        ret = self.py_type_expr_to_xirtype(fdefnode.returns)
        arg_types = []

        for a in fdefnode.args.args:
            if a.annotation:
                arg_types.append(self.py_type_expr_to_xirtype(a.annotation))
            else:
                raise SyntaxError(f'All arguments must be annotated with types')

        return self.typing.TyApp(ret, arg_types)

