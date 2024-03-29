#!/usr/bin/env python3
#
# xirpeval.py
#
# An ad hoc partial evaluator for XIR.
#
# Author: Sreepathi Pai
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT

import ast
import astunparse
import logging
import copy
from .astcompat import AC

logger = logging.getLogger(__name__)

utils = None

class DearrayificationPrep(ast.NodeVisitor):
    def __init__(self):
        self.arrays = {} # array_name: length
        self.non_numeric_accesses = set()

    def is_array_literal(self, node):
        # this doesn't handle [0]*4
        if isinstance(node, ast.List):
            return True

        return False

    def visit_Assign(self, node):
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if self.is_array_literal(node.value):
                self.arrays[node.targets[0].id] = len(node.value.elts)

    def visit_Subscript(self, node):
        if isinstance(node.slice, ast.Index):
            # will be wrong if the array is aliased!
            if isinstance(node.value, ast.Name):
                if not isinstance(node.slice.value, AC.isNum):
                        self.non_numeric_accesses.add(node.value.id)

class Dearrayification(ast.NodeTransformer):
    def visit_Assign(self, node):
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in self._prep.arrays:
                out = []
                for i, x in enumerate(node.value.elts):
                    out.append(ast.Assign([ast.Name(node.targets[0].id + "_" + str(i), ast.Store())], self.visit(x)))

                return out

        node = self.generic_visit(node)
        return node

    def visit_Subscript(self, node):
        if isinstance(node.slice, ast.Index):
            if isinstance(node.value, ast.Name):
                if node.value.id in self._prep.arrays:
                    return ast.Name(id=f"{node.value.id}_{AC.value(node.slice.value)}", ctx=node.ctx)

        return self.generic_visit(node)

    def dearrayify(self, ast):
        self._prep = DearrayificationPrep()
        self._prep.visit(ast)

        for x in self._prep.non_numeric_accesses:
            if x in self._prep.arrays: del self._prep.arrays[x]

        return self.visit(ast)


class UsedNames(ast.NodeVisitor):
    """Check which names are read/written in code, and identify function-level live-ins/live-outs.

       NOTE: this works on the AST, so it can be wrong..."""
    def __init__(self):
        self._names = set()
        self._read_first = set()
        self._written_first = set()
        self._read = set()
        self._written = set()

    def visit_Assign(self, node):
        # visit LHS first
        self.visit(node.value)
        for x in node.targets:
            self.visit(x)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load):
            self._read.add(node.id)
        elif isinstance(node.ctx, ast.Store):
            self._written.add(node.id)

        if node.id not in self._names:
            self._names.add(node.id)

            if isinstance(node.ctx, ast.Load):
                self._read_first.add(node.id)
            elif isinstance(node.ctx, ast.Store):
                self._written_first.add(node.id)

class EvalConstExpr(ast.NodeTransformer):
    def __init__(self):
        self.stk = []

    def visit_Name(self, node):
        if len(self.stk):
            self.stk[-1] = False

        return self.generic_visit(node)

    def visit_Call(self, node):
        if len(self.stk):
            self.stk[-1] = False

        return self.generic_visit(node)

    def visit_Subscript(self, node):
        # not necessarily?
        if len(self.stk):
            self.stk[-1] = False

        return self.generic_visit(node)

    def _get_val(self, v):
        val = astunparse.unparse(v)
        try:
            val = eval(val)

            # bool checks must precede int checks
            if isinstance(val, bool) or val is None:
                return AC.mk_constant(val)
            elif isinstance(val, int):
                return AC.mk_constant(val)
            elif isinstance(val, str):
                return AC.mk_constant(val)
            else:
                raise NotImplementedError(f"unknown constant expression type: {val} (from {v})")
        except:
            pass

        return v

    def visit_Expr(self, node):
        self.stk.append(True)
        node = self.generic_visit(node)
        r = self.stk.pop()

        if r and len(self.stk) == 0:
            if not (isinstance(node.value, AC.isNum) \
                    or isinstance(node.value, AC.isStr) \
                    or isinstance(node.value, AC.isNameConstant)):
                node.value = self._get_val(node.value)
        else:
            # should never happen since Expr is a statement?
            if not r and len(self.stk) > 0:
                self.stk[-1] = False

        return node

    def visit_BoolOp(self, node):
        self.stk.append(True)
        node = self.generic_visit(node)
        r = self.stk.pop()

        # short-circuit, todo generalize to Or?
        if isinstance(node.op, ast.And):
            print(ast.dump(node))
            node.values = [x for x in node.values if not (isinstance(x, AC.isNameConstant) and AC.value(x) is True)]
            if len([x for x in node.values if isinstance(x, AC.isNameConstant) and AC.value(x) is False]):
                node.values = [AC.mk_constant(False)]

            if len(node.values) == 1:
                node = node.values[0]
            elif len(node.values) == 0:
                node = AC.mk_constant(True)

        if len(self.stk):
            self.stk[-1] = r
        else:
            if r:
                return self._get_val(node)

        return node

    def visit_BinOp(self, node):
        self.stk.append(True)
        node = self.generic_visit(node)
        r = self.stk.pop()

        if len(self.stk):
            self.stk[-1] = r
            return node

        if r:
            return self._get_val(node)

        return node

    def visit_UnaryOp(self, node):
        self.stk.append(True)
        node = self.generic_visit(node)
        r = self.stk.pop()

        if r: # were we a constant?
            node = self._get_val(node)

        if len(self.stk):
            self.stk[-1] = r

        return node

class EvalIf(ast.NodeVisitor):
    def eval_isnan(self, call_node):
        if isinstance(call_node.args[0], ast.Name):
            # print(call_node.args[0].id, self.variable_types)
            if call_node.args[0].id in self.variable_types:
                if self.variable_types[call_node.args[0].id] not in ('Float', 'Double'):
                    return AC.mk_constant(False)

        return call_node

    def visit_If(self, node):
        test = astunparse.unparse(node.test)
        logger.debug(f"Test is {test}")
        try:
            d = {'NOTEQ': utils.NOTEQ, 'EQ': utils.EQ}
            d.update(self.values)
            val = eval(test, d)
            logger.debug(f"Evaluation returned {val}")
            if val:
                node.test = AC.mk_constant(True)
            else:
                node.test = AC.mk_constant(False)
        except:
            if isinstance(node.test, ast.Call) and isinstance(node.test.func, ast.Name):
                if node.test.func.id == 'ISNAN':
                    node.test = self.eval_isnan(node.test)
            else:
                pass

        self.generic_visit(node)

    def visit_IfExp(self, node):
        test = astunparse.unparse(node.test)
        try:
            # src1, src2, and src3 are always non-None in executable semantics
            d = {'NOTEQ': utils.NOTEQ, 'EQ': utils.EQ}
            d.update(self.values)
            val = eval(test, d)
            if val:
                node.test = AC.mk_constant(True)
            else:
                node.test = AC.mk_constant(False)
        except:
            pass

        self.generic_visit(node)

class EvalFunc(ast.NodeTransformer):
    def visit_Call(self, node):
        node = self.generic_visit(node)

        if not isinstance(node.func, ast.Name): return node

        if node.func.id == 'MUL':
            if all([isinstance(x, AC.isNum) for x in node.args[:2]]):
                num1 = AC.value(node.args[0], (int, float))
                num2 = AC.value(node.args[1], (int, float))
                ty = AC.value(node.args[2], (str,))
                wd = AC.value(node.args[3], (int, float))
                return AC.mk_constant(utils.MUL(num1, num2, ty, wd))
        elif node.func.id == 'MIN':
            if all([isinstance(x, AC.isNum) for x in node.args[:2]]):
                num1 = AC.value(node.args[0], (int, float))
                num2 = AC.value(node.args[1], (int, float))
                return AC.mk_constant(utils.MIN(num1, num2))
        elif node.func.id == 'SUB':
            if all([isinstance(x, AC.isNum) for x in node.args[:2]]):
                num1 = AC.value(node.args[0], (int, float))
                num2 = AC.value(node.args[1], (int, float))
                ty = AC.value(node.args[2], (str,))
                wd = AC.value(node.args[3], (int, float))
                return AC.mk_constant(utils.SUB(num1, num2, ty, wd))
        elif node.func.id == 'ADD':
            if all([isinstance(x, AC.isNum) for x in node.args[:2]]):
                num1 = AC.value(node.args[0], (int, float))
                num2 = AC.value(node.args[1], (int, float))
                ty = AC.value(node.args[2], (str,))
                wd = AC.value(node.args[3], (int, float))
                return AC.mk_constant(utils.ADD(num1, num2, ty, wd))
        elif node.func.id == 'generate_mask':
            if all([isinstance(x, t) for x, t in [(node.args[0], AC.isStr),
                                                  (node.args[1], AC.isNum),
                                                  (node.args[2], AC.isNum),
                                                  (node.args[3], AC.isStr)]]):

                return AC.mk_constant(utils.generate_mask(AC.value(node.args[0], (str,)),
                                                          AC.value(node.args[1], (int, float)),
                                                          AC.value(node.args[2], (int, float)),
                                                          AC.value(node.args[3], (str,))))
        return self.generic_visit(node)

class StripUnread(ast.NodeTransformer):
    remove = None

    def visit_Assign(self, node):
        if len(node.targets) == 1:
            if isinstance(node.targets[0], ast.Name) and node.targets[0].id in self.remove:
                print("Removing", astunparse.unparse(node))
                return None

        return node

class StripCode(ast.NodeTransformer):
    retvalue = None

    def visit_Return(self, node):
        if isinstance(node.value, ast.Name) and node.value.id == 'thread_pc_count':
            # TODO: add dst?
            node.value = self.retvalue

        return node

    def visit_Subscript(self, node):
        node = self.generic_visit(node)

        if isinstance(node.value, ast.Name) and node.value.id == 'regFile':
            t0 = node.slice
            if isinstance(t0, ast.Index) and isinstance(t0.value, ast.Name):
                logger.debug(f"changing index context from {t0.value.ctx} to {node.ctx}")
                t0.value.ctx = node.ctx
                return t0.value #ast.Name(id=t0.value.id, ctx=ast.Store())

        return self.generic_visit(node)

    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id == 'ROUND':
                # set_round_mode(var, None)
                if isinstance(node.args[-1], AC.isNameConstant) and AC.value(node.args[-1]) is None:
                    return node.args[0] # var

        return self.generic_visit(node)

    def visit_Assign(self, node):
        node = self.generic_visit(node)

        if not hasattr(node, 'value'): # was deleted
            return None

        if len(node.targets) == 1:
            if isinstance(node.targets[0], AC.isNameConstant) and AC.value(node.targets[0]) is None:
                # strip None=None
                #return None
                #print(ast.dump(node))
                return None
            elif isinstance(node.targets[0], ast.Name) and node.targets[0].id == 'thread_pc_count':
                # delete thread_pc_count
                return None
            elif isinstance(node.targets[0], ast.Name) and isinstance(node.value, ast.Name):
                if node.targets[0].id == node.value.id:
                    # delete trivial copies
                    # e.g. tmp_dst = tmp_dst
                    return None


        return node

    def visit_IfExp(self, node):
        node = self.generic_visit(node)
        if isinstance(node.test, AC.isNameConstant):
            if AC.value(node.test) is False:
                return node.orelse
            elif AC.value(node.test) is True:
                return node.body

        return node

    def visit_If(self, node):
        if isinstance(node.test, AC.isNameConstant):
            if value(node.test) == False:
                r = list(filter(lambda x: x is not None, [self.visit(x) for x in node.orelse]))
            elif value(node.test) == True:
                # drop the else part
                r = list(filter(lambda x: x is not None, [self.visit(x) for x in node.body]))
            else:
                return node

            if len(r) == 1:
                return r[0] # huh?
            else:
                return r
        else:
            node.test = self.visit(node.test)
            node.body = list(filter(lambda x: x is not None, [self.visit(x) for x in node.body]))
            node.orelse = list(filter(lambda x: x is not None, [self.visit(x) for x in node.orelse]))

            if len(node.body) == 0 and len(node.orelse) == 0:
                return None

        return node

class UnrollChecker(ast.NodeVisitor):
    def visit_For(self, node):
        assert len(node.orelse) == 0, f"OrElse not supported for For"

        unroll = False
        if isinstance(node.target, ast.Name):
            if isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and node.iter.func.id == 'range':
                assert isinstance(node.iter.args[0], AC.isNum)
                assert isinstance(node.iter.args[1], AC.isNum)
                unroll = True

        node._unroll = unroll
        self.generic_visit(node)

class ReplaceIndex(ast.NodeTransformer):
    def visit_Name(self, node):
        if node.id == self._idx_var:
            return AC.mk_constant(self._idx_val)

        return node

class UnrollLoop(ast.NodeTransformer):
    def _unroll_body(self, idxvar, body, start, end):
        out = []
        ri = ReplaceIndex()
        ri._idx_var = idxvar

        for i in range(start, end):
            c = copy.deepcopy(body)
            ri._idx_val = i
            for s in c:
                out.append(ri.visit(s))

        return out

    def visit_For(self, node):
        node = self.generic_visit(node)

        if node._unroll:
            start = node.iter.args[0].n
            end = node.iter.args[1].n
            out = self._unroll_body(node.target.id, node.body, start, end)
            return out

        return node

class PropagateConstants(ast.NodeTransformer):
    def visit_Name(self, node):
        if node.id in self._constants:
            if isinstance(node.ctx, ast.Load):
                return AC.mk_constant(self._constants[node.id])

        return node

    def visit_Assign(self, node):
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) and node.targets[0].id in self._constants:
            return ast.Pass() # delete the assignment

        return self.generic_visit(node)

    def propagate(self, node, constants):
        self._constants = constants
        return self.visit(node)

# extremely simple, we really need a better partial evaluator ...
class GatherConstants(ast.NodeVisitor):
    def visit_Assign(self, node):
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            v = node.targets[0].id
            if v in self._constants:
                # two writes to the same variable. Without better analysis, assume NAC.
                del self._constants[v]
                self._non_constants[v] = node.value
            elif v not in self._non_constants:
                if isinstance(node.value, AC.isNum):
                    self._constants[v] = AC.value(node.value, (int, float))

    def gather(self, node):
        self._constants = {}
        self._non_constants = {}
        self.visit(node)
        return self._constants

def set_utils(new_utils):
    """Hack to set the old utils variables that contains implementations
       of functions used to partially evaluate code."""
    global utils
    utils = new_utils

def constantify(s):
    g = GatherConstants()
    p = PropagateConstants()

    c = g.gather(s)
    if len(c):
        s = p.propagate(s, c)
        x = EvalFunc()
        s = x.visit(s)

    return s

def Unroll(s):
    ulc = UnrollChecker()
    ulc.visit(s)

    ul = UnrollLoop()
    o = ul.visit(s)

    return o

def test_UnrollLoop():
    import astunparse

    loop = """
for i in range(0, 4):
   a[i] = b[i]
"""

    r = ast.parse(loop)
    ulc = UnrollChecker()
    ulc.visit(r)

    ul = UnrollLoop()
    o = ul.visit(r)

    print(astunparse.unparse(o))

def test_GatherConstants():
    code = """
x = 1
y = 2
x = 3
z = x + y
"""
    i = ast.parse(code)

    v = GatherConstants()
    print(v.gather(i))
