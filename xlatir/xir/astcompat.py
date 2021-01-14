#!/usr/bin/env python3
#
# astcompat.py
#
# AST compatibility routines to handle AST differences between different Python3 AST versions
#
# Need to handle: isinstance, ast.Visitor and ast.Transformer, as well as obtaining actual values.
#
# To handle `isinstance`, declare "Compat*" lists that identify the
# class that represents the original class. For example:
#
# python3.6: CompatNum = (ast.Num,)
# python3.8: CompatNum = (ast.Constant,)
#
# then in code always use: isinstance(node, CompatNum)
#
# To handle obtaining actual values, e.g. ast.Num.n vs
# ast.Constant.value, we'll use a set of wrapper classes and functions:
#
# python3.6: mkCompatNum(x: ast.Num) => wrapperCompatNum(x)
# python3.8: mkCompatNum(x: ast.Constant) => x
#
# where wrapperCompatNum(x) =>
# class (ast.Node):
#     def __init__(self, node):
#          self._node = node
#     @property
#     def value(): # uses forward-compatible attribute, i.e. ast.Constant.value instead of ast.Num.n
#         return self._node = node
#
#     note we only map existing attributes to new attributes (.n =>
#     .value), so no .kind on wrapperCompatNum().
#
# To handle the various visitors, we must handle generic_visit as well
# as visit properly. This means either the various wrapper* classes
# keep up with the AST or we override generic_visit and visit. TBD.
