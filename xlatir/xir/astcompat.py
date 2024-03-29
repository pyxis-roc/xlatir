#!/usr/bin/env python3
#
# astcompat.py
#
# AST compatibility routines to handle AST differences between different Python3 AST versions
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT
#
# SPDX-Contributor: Sreepathi Pai
#

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

    def value(self, node, valchk = ()):
        # valchk is a list of types for ast.Num and ast.Str, but a list of values for ast.NameConstant
        # so (int,) for ast.Num will work,
        # and (None, True) will for ast.NameConstant

        if isinstance(node, ast.Num):
            v = node.n
            vok = isinstance(v, valchk) if len(valchk) > 0 else True
        elif isinstance(node, ast.NameConstant):
            v = node.value
            vok = v in valchk if len(valchk) > 0 else True
        elif isinstance(node, ast.Str):
            v = node.s
            vok = isinstance(v, valchk) if len(valchk) > 0 else True
        else:
            raise NotImplementedError(f'Unhandled value class {node.__class__.__name__}')

        if not vok:
            raise TypeError(f'{node} does not match expected type/values {valchk}')

        return v

    def set_value(self, node, value):
        if isinstance(node, ast.Num):
            node.n = value
        elif isinstance(node, ast.NameConstant):
            node.value = value
        else:
            raise NotImplementedError(f'Do not know how to set value of class {node.__class__.__name__}')

    def mk_constant(self, value):
        if value is None or value is True or value is False:
            return ast.NameConstant(value=value)
        elif isinstance(value, (int, float)):
            return ast.Num(n=value)
        elif isinstance(value, str):
            return ast.Str(s=value)
        else:
            raise NotImplementedError(f'Do not know how make constant {node.__class__.__name__}')

class Python38Compat:
    def __init__(self):
        self.isNum = (ast.Constant,)
        self.isStr = (ast.Constant,)
        self.isNameConstant = (ast.Constant,)
        self.isConstant = (ast.Constant,)

    def value(self, node, valchk = ()):
        if isinstance(node, ast.Constant):
            v = node.value
            if len(valchk):
                if v is None or v is True or v is False:
                    vok = v in valchk
                else:
                    vok = isinstance(v, valchk)

                if not vok:
                    raise TypeError(f'{node} does not match expected type/values {valchk}')

            return v
        else:
            raise NotImplementedError(f'Unhandled value class {node.__class__.__name__}')

    def set_value(self, node, value):
        if isinstance(node, ast.Constant):
            node.value = value
            if not hasattr(node, 'kind'): node.kind = None # 3.8 bug?
        else:
            raise NotImplementedError(f'Do not know how to set value of class {node.__class__.__name__}')

    def mk_constant(self, value):
        if isinstance(value, (int, str, float)) or (value is None) or (value is True) or (value is False):
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

