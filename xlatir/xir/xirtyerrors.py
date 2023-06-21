# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT
#
# SPDX-Contributor: Sreepathi Pai
#

import ast
from .xirtyping import *

class SubsTy(ast.NodeTransformer):
    def visit_Literal(self, node):
        return node

    def _get_root(self, ty):
        try:
            xt = find(ty, self.reps)
            return xt
        except KeyError:
            if isinstance(ty, TyVar): return ty
            return None

    def _get_ty(self, ty):
        xt = self._get_root(ty)
        if isinstance(xt, TyApp):
            return self._get_ty(xt.ret)
        elif isinstance(xt, TyVarLiteral):
            if xt is ty: return xt.name
            return self._get_ty(xt)
        elif isinstance(xt, TyVar):
            if xt is ty: return xt.name
            return self._get_ty(xt)
        elif isinstance(xt, TyConstant):
            return xt.value
        elif isinstance(xt, TyProduct):
            t = ' * '.join([self._get_ty(a) for a in xt.args])
            return f"({t})"
        elif isinstance(xt, TyArray):
            t = self._get_ty(xt.elt)
            s = ', '.join([str(s) for s in xt.sizes])
            return f"<{t}[{s}]>"
        elif xt is None:
            return "?"

        return f"??{type(xt)}??"

    def visit_Num(self, node):
        #return self.visit_Constant(node)
        if hasattr(node, '_xir_type'):
            xt = self._get_ty(node._xir_type)
            return ast.Name(id = str(node.n) + "'" + xt, ctx = ast.Load())

        return node

    def visit_Name(self, node):
        if hasattr(node, '_xir_type'):
            node.id = node.id+"'"+self._get_ty(node._xir_type)

        return node

    def visit_Call(self, node):
        self.generic_visit(node)

        return node

    def rewrite(self, node, reps):
        self.reps = reps
        return self.visit(node)

