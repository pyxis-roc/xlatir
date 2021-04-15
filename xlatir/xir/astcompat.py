#!/usr/bin/env python3
#
# astcompat.py
#
# AST compatibility routines to handle AST differences between different Python3 AST versions

import ast
import sys

# this module exports a member called AC.
#
# Use AC.isNum to test for num like this: isinstance(node, ac.isNum)
# Use AC.value(node) to get the value of a constant node
# Use AC.setValue(node, value) to set the value of the node
# Use AC.mkConstant(value) to create a new AST node of the correct type
#
# This does not handle ast visitors or ast transformers.
#
# Recommend patching those visitors, transformers to handle both the
# hold classes and the new classes.

class Python36Compat:
    def __init__(self):
        # deprecated in 3.8: ast.Num, ast.Str, ast.Bytes, ast.NameConstant and ast.Ellipsis
        self.isNum = (ast.Num,)
        self.isStr = (ast.Str,)
        self.isNameConstant = (ast.NameConstant,)
        self.isConstant = (ast.Num, ast.Str, ast.Bytes, ast.NameConstant, ast.Ellipsis)

    def value(self, node):
        if isinstance(node, ast.Num):
            return node.n
        elif isinstance(node, ast.NameConstant):
            return node.value
        elif isinstance(node, ast.Str):
            return node.s
        else:
            raise NotImplementedError(f'Unhandled value class {node.__class__.__name__}')

    def set_value(self, node, value):
        if isinstance(node, ast.Num):
            node.n = value
        elif isinstance(node, ast.NameConstant):
            node.value = value
        else:
            raise NotImplementedError(f'Do not know how to set value of class {node.__class__.__name__}')

    def mk_constant(self, value):
        if isinstance(value, (int, float)):
            return ast.Num(n=value)
        elif isinstance(value, str):
            return ast.Str(s=value)
        elif value is None or value is True or value is False:
            return ast.NameConstant(value=value)
        else:
            raise NotImplementedError(f'Do not know how make constant {node.__class__.__name__}')

class Python38Compat:
    def __init__(self):
        self.isNum = (ast.Constant,)
        self.isStr = (ast.Constant,)
        self.isNameConstant = (ast.Constant,)
        self.isConstant = (ast.Constant,)

    def value(self, node):
        if isinstance(node, ast.Constant):
            return node.value
        else:
            raise NotImplementedError(f'Unhandled value class {node.__class__.__name__}')

    def set_value(self, node, value):
        if isinstance(node, ast.Constant):
            node.value = value
            if not hasattr(node, 'kind'): node.kind = None # 3.8 bug?
        else:
            raise NotImplementedError(f'Do not know how to set value of class {node.__class__.__name__}')

    def mk_constant(self, value):
        if isinstance(value, (int, str, float)) or value is None or value is True or value is False:
            n = ast.Constant(value=value)
            if not hasattr(n, 'kind'): n.kind = None # 3.8 bug
            return n
        else:
            raise NotImplementedError(f'Do not know how make constant {node.__class__.__name__}')

if sys.version_info.major == 3:
    if sys.version_info.minor < 8:
        AC = Python36Compat()
    elif sys.version_info.major < 9:
        AC = Python38Compat()
    else:
        # let higher versions opt-in
        pass
else:
    # we don't work with 2
    pass

