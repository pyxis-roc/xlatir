#!/usr/bin/env python3
#
# xirsyntax.py
# Check that XIR/Python is valid syntactically and transform it to XIR/Imp.
#
# Author: Sreepathi Pai
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT


import ast
from collections import namedtuple

SourceInfo = namedtuple('SourceInfo', 'filename lineno col_offset srcline')

class XIRSyntaxError(SyntaxError):
    pass

class XIRSyntaxCheck(ast.NodeVisitor):
    """Check that the Python program uses the subset of syntax supported by XIR"""

    _xir_filename = '' # should be name of file
    _xir_source = None # should be an array of lines from source code

    # may remove support for Pow
    _xir_supported_binop = (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Mod, ast.Pow,
                            ast.LShift, ast.RShift, ast.BitOr, ast.BitXor, ast.BitAnd, ast.FloorDiv)

    _xir_supported_cmpop = (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)

    def _synerr_params(self, node):
        return SourceInfo(filename=self._xir_filename,
                          lineno=node.lineno if hasattr(node, 'lineno') else None,
                          col_offset=node.col_offset if hasattr(node, 'col_offset') else None,
                          srcline=self._xir_source[node.lineno-1] if hasattr(node, 'lineno') else None)

    def _unsupported(self, node, se_node = None):
        # se_node is a node that is an instance of ast.expr or ast.stmt
        # its lineno, col_offset will be used if node does not have them

        if se_node is not None:
            assert isinstance(se_node, (ast.expr, ast.stmt))

        si = None
        if isinstance(node, (ast.expr, ast.stmt)):
            assert hasattr(node, 'lineno'), f"Node {node} is missing lineno information"
            si = self._synerr_params(node)
        else:
            if se_node:
                assert hasattr(se_node, 'lineno'), f"se_node {node} is missing lineno information"
                si = self._synerr_params(se_node)
            else:
                si = self._synerr_params(node) # this will just have ??

        if si.srcline is None:
            raise XIRSyntaxError(f"{si.filename}:{si.lineno}.{si.col_offset}:Don't support {node.__class__.__name__} in XIR ({si.srcline})", si)
        else:
            # SyntaxError will show the correct
            raise XIRSyntaxError(f"Don't support {node.__class__.__name__} in XIR", si)

    visit_AsyncFunctionDef = _unsupported
    #visit_ClassDef = _unsupported # TODO: we only support a subset
    visit_Delete = _unsupported

    def visit_AugAssign(self, node):
        if not isinstance(node.op, self._xir_supported_binop):
            raise XIRSyntaxError(f"Don't support operator {node.op} in XIR", self._synerr_params(node))

        self.generic_visit(node)

    #TODO: for restrictions

    visit_AsyncFor = _unsupported
    visit_With = _unsupported
    visit_AsyncWith = _unsupported
    visit_Raise = _unsupported
    visit_Try = _unsupported
    #visit_Assert = _unsupported #
    visit_Nonlocal = _unsupported # for now?

    visit_NamedExpr = _unsupported
    visit_Lambda = _unsupported
    visit_Await = _unsupported
    visit_YieldFrom = _unsupported

    def visit_Compare(self, node):
        if len(node.ops) != 1 and len(node.comparators) != 1:
            raise XIRSyntaxError(f"Don't support chained comparisons", self._synerr_params(node))

        if not isinstance(node.ops[0], self._xir_supported_cmpop):
            raise XIRSyntaxError(f"Don't support comparison operator {node.ops[0]} in XIR", self._synerr_params(node))

        self.generic_visit(node)

    def visit_Call(self, node):
        if len(node.keywords):
            raise XIRSyntaxError(f"Don't support keywords in calls", self._synerr_params(node))

        self.generic_visit(node)

    visit_FormattedValue = _unsupported
    visit_JoinedStr = _unsupported

    #TODO: Constant [things like None are not allowed except for partial evaluation]
    visit_Starred = _unsupported

    #TODO: List
    #TODO: Tuple

    def visit_Subscript(self, node):
        self.visit(node.value)
        if isinstance(node.slice, ast.Slice):
            #TODO: we should be able to support slices later, but for now we only support indices.
            self._unsupported(node.slice, node)


class PyToXIRImp(ast.NodeTransformer):
    """Convert Python-using XIR to strict XIR syntax (e.g., no operators)"""

    def _make_call(self, func, node, args):
        # note: this does not add type annotation triple (sign,
        # varType, bitWidth) since XIR doesn't need it.

        # TODO: add coordinates
        # expression context?
        return ast.Call(ast.Name(id=func), args, {})

    def visit_AugAssign(self, node):
        node = self.generic_visit(node)

        # LHS could be name, array ref, etc.
        #TODO: change ctx to Load for RHS value.
        return self.visit(ast.Assign([node.target], ast.BinOp(node.target, node.op, node.value)))

    def visit_BinOp(self, node):
        node = self.generic_visit(node)

        op = node.op
        node_args = (node, [node.left, node.right])

        if isinstance(op, ast.Add):
            return self._make_call('ADD', *node_args)
        elif isinstance(op, ast.Sub):
            return self._make_call('SUB', *node_args)
        elif isinstance(op, ast.Mult):
            return self._make_call('MUL', *node_args)
        elif isinstance(op, ast.Div):
            return self._make_call('DIV', *node_args) # non-integer division
        elif isinstance(op, ast.Mod):
            return self._make_call('MOD', *node_args)
        elif isinstance(op, ast.Pow):
            return self._make_call('POW', *node_args)
        elif isinstance(op, ast.LShift):
            return self._make_call('SHL', *node_args)
        elif isinstance(op, ast.RShift):
            return self._make_call('SHR', *node_args) # need types to decide SAR or SHR
        elif isinstance(op, ast.BitOr):
            return self._make_call('OR', *node_args)
        elif isinstance(op, ast.BitXor):
            return self._make_call('XOR', *node_args)
        elif isinstance(op, ast.BitAnd):
            return self._make_call('AND', *node_args)
        elif isinstance(op, ast.FloorDiv):
            return self._make_call('IDIV', *node_args) # integer division
        else:
            # if we reach here, then SyntaxCheck has not worked
            # properly OR we need to add support
            raise NotImplementedError(f"Don't support Python binary operator {op}")

    def visit_UnaryOp(self, node):
        node = self.generic_visit(node)

        # don't change boolean not
        if isinstance(node.op, ast.Not):
            return node

        op = node.op
        if isinstance(op, ast.Invert):
            return self._make_call('NOT', node, [node.operand])
        elif isinstance(op, ast.UAdd):
            return node # +a?
        elif isinstance(op, ast.USub):
            return self._make_call('NEG', node, [node.operand])
        else:
            # if we reach here, then SyntaxCheck has not worked
            # properly OR we need to add support
            raise NotImplementedError(f"Don't support Python unary operator {op}")

    def visit_Compare(self, node):
        node = self.generic_visit(node)

        assert len(node.ops) == 1 and len(node.comparators) == 1, f"Don't support chained comparisons"

        op = node.ops[0]
        node_args = (node, (node.left, node.comparators[0]))

        if isinstance(op, ast.Eq):
            return self._make_call('EQ', *node_args)
        elif isinstance(op, ast.NotEq):
            return self._make_call('NOTEQ', *node_args)
        elif isinstance(op, ast.Lt):
            return self._make_call('LT', *node_args)
        elif isinstance(op, ast.LtE):
            return self._make_call('LTE', *node_args)
        elif isinstance(op, ast.Gt):
            return self._make_call('GT', *node_args)
        elif isinstance(op, ast.GtE):
            return self._make_call('GTE', *node_args)
        else:
            # if we reach here, then SyntaxCheck has not worked
            # properly OR we need to add support
            # TODO: explore support for some variants of is/isnot?
            # TODO: maybe do in, not in
            raise NotImplementedError(f"Don't support Python comparison operator {op}")

