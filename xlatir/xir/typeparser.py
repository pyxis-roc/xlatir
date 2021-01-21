#!/usr/bin/env python3
#
# typeparser.py
# XIR type declarations and annotations parser.

#
# TypeDeclaration := TypeVarDecl | ClassTypeDecl | AliasDecl
#
# TypeVarDecl := TypeVar '=' 'TypeVar' '(' '''' str '''' ')'  # ast.Assign
#
# AliasDecl := Var '=' TypeAnnotation # ast.Assign
#
# ClassTypeDecl := EnumDecl | DataTypeDecl

#
# TypeAnnotations :=

import ast
from .xirtyping import *
from .xirsrc import XIRSource, XIRSyntaxError
from typing import Union, Tuple

def expect(node: ast.AST, classes: Tuple[ast.AST], xsrc: XIRSource):
    if not isinstance(classes, tuple):
        classes = (classes, )

    if not isinstance(node, classes):
        raise xsrc._gen_syntax_error(f"Expecting {', '.join([x.__name__ for x in classes])}, found {node.__class__.__name__}", node)


# TypeDecl: Type = TypeConstructor()
# TypeAlias = TypeExpr
# TypeVar = TypeVar()
class AssignmentParser(object):
    """Assignment = TyVarDecl | AliasDecl

       tyvar = 'TypeVar' '(' '"' str '"' ')'"""

    tyvar_fn = 'TypeVar'

    def __init__(self, xsrc):
        self.xsrc = xsrc

    def parse_lhs(self, targets):
        if len(targets) > 1:
            raise xsrc._gen_syntax_error(f"TypeVar declarations cannot have multiple variables on LHS", node)
        expect(targets[0], ast.Name, self.xsrc)

        return targets[0].id

    def parse_tyvar(self, value):
        expect(value, ast.Call, self.xsrc)
        expect(value.func, ast.Name, self.xsrc)

        if value.func.id != self.tyvar_fn:
            raise self.xsrc._gen_syntax_error(f"RHS of TypeVar declaration must be call to {tyvar_function}")

        return self.tyvar_fn

    def maybe_tyvar(self, value):
        return isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id == self.tyvar_fn

    def parse_rhs(self, value):
        if self.maybe_tyvar(value):
            return self.parse_tyvar(value)
        elif isinstance(value, ast.Name):
            return TyConstant(value.id)
        else:
            raise self.xsrc._gen_syntax_error(f"Unrecognized RHS for assignment", value)

    def parse(self, node):
        expect(node, ast.Assign, self.xsrc)

        l = self.parse_lhs(node.targets)
        r = self.parse_rhs(node.value)

        if r == self.tyvar_fn:
            return TyVar(l)
        elif isinstance(r, TyTerm):
            return TyAlias(l, r)
        else:
            raise NotImplementedError

class TypeEnv(object):
    builtins = None
    type_constants = None
    type_vars = None
    type_aliases = None

    def __init__(self):
        self.builtins = set(['Callable'])
        self.type_constants = set()
        self.type_vars = {}
        self.type_aliases = {}

    def resolve(self, name):
        if name in self.type_constants or name in self.builtins:
            return TyConstant(name)
        elif name in self.type_vars:
            return TyVar(name)
        elif name in self.type_aliases:
            return self.type_aliases[name]
        else:
            raise KeyError(f"Not found in type environment: {name}")

# TypeExpr := TypeConstant | ArrayType | CallableType | TypeAlias | TypeVariable
#   TypeConstant, TypeAlias, TypeVariable are all ast.Name or ast.Constant (for None)
#
# # not supported by mypy, constant size arrays
# ArrayType := TypeExpr '[' dimension_size (',' dimension_size)* ']'
# CallableType := 'Callable' '[' '[' TypeExpr (',' TypeExpr ')'* ']' ',' TypeExpr ']'
#   ArrayType is ast.Subscript with TypeConstant and a tuple of ints
#   CallableType is ast.Subscript with TypeConstant('Callable') and a ast.List of arguments and a return TypeExpr
# dimension_size := [0-9]+
#    ast.Constant with value being a subtype of int
# TypeConstant := None | declared-types
#    ast.Name or ast.Constant
# TypeVariable := declared-type-variables
#    ast.Name
class TypeExprParser(ast.NodeVisitor):
    def visit_Name(self, node):
        try:
            return self._tyenv.resolve(node.id)
        except KeyError:
            raise self._xsrc._gen_syntax_error(f'Unrecognized name "{node.id}" in type expression. Not a type constant, variable or alias.', node)

    def visit_Constant(self, node):
        if isinstance(node.value, int):
            return node.value
        elif node.value is None:
            return TyConstant('void')

        raise self._xsrc._gen_syntax_error(f'Unexpected non-integer literal in type expression', node)

    def visit_List(self, node):
        return [self.visit(x) for x in node.elts]

    def visit_Tuple(self, node):
        return tuple([self.visit(x) for x in node.elts])

    def visit_Index(self, node):
        return self.visit(node.value)

    def visit_Subscript(self, node):
        l = self.visit(node.value)
        if isinstance(l, TyConstant):
            if isinstance(node.slice, ast.Slice):
                raise self._xsrc._gen_syntax_error(f'Cannot use slices in type expression')

            #AST 3.9 index...
            v = self.visit(node.slice)

            if isinstance(v, int):
                return TyArray(l, [v])
            elif isinstance(v, tuple):
                if l.value == 'Callable':
                    return TyApp(v[-1], v[0])
                else:
                    # TODO: could be multidimensional
                    raise self._xsrc._gen_syntax_error(f'Subscript on unknown type {l.value} in type expression', node)

        raise self._xsrc._gen_syntax_error(f'Unrecognized subscript type expression', node)

    def visit(self, node):
        if isinstance(node, (ast.Name, ast.Subscript, ast.Index, ast.Constant, ast.Tuple, ast.List)):
            return super(TypeExprParser, self).visit(node)
        else:
            raise self._xsrc._gen_syntax_error(f'Invalid ast node {node.__class__.__name__} in type expression', node)

    def parse(self, node: ast.AST, tyenv: TypeEnv, xsrc: XIRSource):
        self._xsrc = xsrc
        self._tyenv = tyenv
        return self.visit(node)
