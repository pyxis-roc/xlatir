#!/usr/bin/env python3

import argparse
import ast
import astunparse
import copy
from collections import OrderedDict

XIRMACRO = 'xirmacro'

class Expander(ast.NodeTransformer):
    def visit_Name(self, node):
        if node.id in self._expansions:
            return self._expansions[node.id]

        return node

    def expand(self, expansions, xmacro):
        body = copy.deepcopy(xmacro.body)
        self._expansions = expansions
        out = []

        for s in body:
            o = self.visit(s)

            if isinstance(o, list):
                out.extend(o)
            elif o is None:
                pass
            else:
                out.append(o)

        # handle expression macros
        if xmacro.is_expression_macro:
            if len(out) == 1 and isinstance(out[0], ast.Expr):
                out = out[0].value
            else:
                # warning
                pass

        self._expansions = None
        return out

class XIRMacro(object):
    def __init__(self, node):
        self.macro = node
        # no support for keyword params
        self.parameters = OrderedDict([(n.arg, None) for n in node.args.args])
        self.expander = Expander()
        self.is_expression_macro = len(self.macro.body) == 1 and isinstance(self.macro.body[0], ast.Expr)

    @property
    def body(self):
        return self.macro.body

    def expand(self, call):
        assert isinstance(call.func, ast.Name) and call.func.id == self.macro.name, f"Can't expand {self.macro.name} for call {call}"

        if len(call.args) != len(self.parameters):
            #TODO: print a better error message including line number and column
            raise SyntaxError(f"Parameter mismatch in call {astunparse.unparse(call)} to {self.macro.name}, expected {len(self.parameters)}, got {len(call.args)}.")
        params = {}
        for k, v in zip(self.parameters, call.args):
            params[k] = v

        return self.expander.expand(params, self)

class LoadMacros(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        for n in node.decorator_list:
            if isinstance(n, ast.Name) and n.id == XIRMACRO:
                self._macros[node.name] = XIRMacro(node)
                return None

        return node


    def load(self, mxir):
        self._macros = {}
        mxir = self.visit(mxir)
        return self._macros, mxir

class ApplyMacros(ast.NodeTransformer):
    def _is_macro_call(self, node):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            return node.func.id in self._macros

        return False

    def visit_Expr(self, node):
        if self._is_macro_call(node.value):
            macro = self._macros[node.value.func.id]
            if not macro.is_expression_macro:
                self._expanded = True
                return macro.expand(node.value)

        node.value = self.visit(node.value)
        return node

    def visit_Call(self, node):
        if self._is_macro_call(node):
            self._expanded = True
            return self._macros[node.func.id].expand(node)

        return node

    def apply(self, macros, mxir):
        self._macros = macros
        self._expanded = True
        while self._expanded:
            self._expanded = False
            mxir = self.visit(mxir)

        return mxir

if __name__ == '__main__':
    p = argparse.ArgumentParser(description="Apply XIR macros")
    p.add_argument("input", help="XIR with macros")

    args = p.parse_args()

    with open(args.input, 'r') as f:
        mxirast = ast.parse(f.read(), args.input)

    lm = LoadMacros()
    macros, mxirast = lm.load(mxirast)

    am = ApplyMacros()
    xir_expanded = am.apply(macros, mxirast)
    print(ast.dump(xir_expanded))
    print(astunparse.unparse(xir_expanded))

