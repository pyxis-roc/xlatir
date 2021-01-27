#!/usr/bin/env python3

import argparse
import ast
import astunparse
import copy
from collections import OrderedDict

XIRMACRO = 'xirmacro'

#TODO
class FreeVariables(ast.NodeVisitor):
    _fdef = None

    def visit_Name(self, node):
        assert self._fdef is not None

        if node.id not in self._fdef._bound:
            #print('adding to free', node.id)
            # TODO: revisit this, right now it isn't very useful
            # since we want to it to apply only to variables, not function names
            self._fdef._free.add(node.id)

    def visit_FunctionDef(self, node):
        # Note: names can be bound in Python in multiple places
        #   comprehensions
        #   lambda functions
        #
        # Since XIR does not support these constructs, the only place
        # we bind names are in function definitions.
        #
        # TODO: also add nonlocal to bound

        node._free = set()
        node._bound = set()

        for a in node.args.args:
            node._bound.add(a.arg)

        node._bound.add(node.name)

        pfdef = self._fdef
        self._fdef = node
        self.generic_visit(node)
        self._fdef = pfdef


class Expander(ast.NodeTransformer):
    _fdef = None

    def _is_free(self, name):
        if name in self._expansions: return False
        if self._fdef and name in self._fdef._bound:
            return False

        return True

    def visit_Name(self, node):
        #if self._fdef and node.id in self._fdef._bound:
        #   return node

        if node.id in self._expansions:
            return self._expansions[node.id]

        return node

    def visit_Assign(self, node):
        node = self.generic_visit(node)

        #if isinstance(node.targets[0], ast.Name):
        #    print(node.targets[0].id, self._is_free(node.targets[0].id))

        return node

    def visit_Call(self, node):
        # Strangely, nodeTransformer does not visit Call args...
        node.func = self.visit(node.func)
        node.args = [self.visit(a) for a in node.args]
        return node

    def visit_FunctionDef(self, node):
        pfdef = self._fdef

        self._fdef = node
        node = self.generic_visit(node)
        self._fdef = pfdef

        if node.name in self._expansions:
            node.name = self._expansions[node.name].id

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
        FreeVariables().visit(self.macro)

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
        node = self.generic_visit(node)

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

