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
#from .xirsrc import XIRSource, XIRSyntaxError
from typing import Union, Tuple
from collections import OrderedDict
from .astcompat import AC

def expect(node: ast.AST, classes: Tuple[ast.AST], xsrc):
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

    def maybe_class(self, value):
        if isinstance(value, ast.Subscript):
            if isinstance(value.value, ast.Name):
                # alias?
                if value.value.id in self.xsrc.tyenv.record_decls:
                    return True

        return False

    def parse_rhs(self, value):
        if self.maybe_tyvar(value):
            return self.parse_tyvar(value)
        elif isinstance(value, ast.Name):
            return TyConstant(value.id)
        elif self.maybe_class(value):
            return self._tep.parse(value, self.xsrc.tyenv, self.xsrc)
        else:
            raise self.xsrc._gen_syntax_error(f"Unrecognized RHS for assignment", value)

    def parse(self, node, tep):
        expect(node, ast.Assign, self.xsrc)
        self._tep = tep
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
        self.builtins = set(['Callable', 'Generic', 'Tuple']) # Tuple is deprecated and will be removed
        self.type_constants = set()
        self.type_vars = {}
        self.type_aliases = {}
        self.record_decls = {}

    # TODO: handle duplicate names

    def resolve(self, name):
        if name in self.type_constants or name in self.builtins:
            return TyConstant(name)
        elif name in self.type_vars:
            return TyVar(name)
        elif name in self.type_aliases:
            return self.type_aliases[name]
        else:
            raise KeyError(f"Not found in type environment: {name}")

    def merge(self, ote):
        #assert self.typing == od2t.typing, f"Different type classes"

        self.type_constants |= ote.type_constants

        for v in ote.type_vars:
            # duplicate type vars are usually not a problem
            if v in self.type_vars: continue
            self.type_vars[v] = ote.type_vars[v]

        for a in ote.type_aliases:
            if a in self.type_aliases:
                if self.type_aliases[a] == ote.type_aliases[a]:
                    continue

                # this means x = y and x = z in two different source files/libraries
                raise ValueError(f"Duplicate and differing type aliases {a}")
            else:
                self.type_aliases[a] = ote.type_aliases[a]


class RecordDeclParser(ast.NodeVisitor):
    def visit_Name(self, node):
        try:
            return self._tyenv.resolve(node.id)
        except KeyError:
            raise self._xsrc._gen_syntax_error(f'Unrecognized name "{node.id}" in type expression. Not a type constant, variable or alias.', node)

    def visit_AnnAssign(self, node):
        # only support 'x: type' at top level, no initializations
        if not isinstance(node.target, ast.Name):
            raise self._xsrc._gen_syntax_error(f'Field name must be a name, not {node.target.__class__.__name__}', node)

        if node.annotation is None:
            raise self._xsrc._gen_syntax_error(f'Missing type annotation for field member {node.target.id}', node)

        if node.value is not None:
            raise self._xsrc._gen_syntax_error(f'Initialization of field members not supported (field {node.target.id})', node)

        field = node.target.id
        field_type = self._tep.parse(node.annotation, self._tyenv, self._xsrc)

        #TODO: check allowed types
        return field, field_type

    def visit_ClassDef(self, node):
        # TODO: nested class defs?
        record_name = node.name
        # handle bases, the only base supported is Generic[]
        # disallow keywords
        # ignore decorators
        if len(node.bases) > 1:
            raise self._xsrc._gen_syntax_error(f'Do not support multiple bases for class definition {node}', node)
        elif len(node.bases) == 1:
            bt = self._tep.parse(node.bases[0], self._tyenv, self._xsrc)
        else:
            bt = None

        _fields = OrderedDict()
        for s in node.body:
            if isinstance(s, ast.AnnAssign):
                field, fty = self.visit(s)

                if field in _fields:
                    raise self._xsrc._gen_syntax_error(f'Duplicate field {node.target.id}', s)

                _fields[field] = fty
            elif isinstance(s, ast.ClassDef):
                raise NotImplementedError(f'Do not support nested class defs')
            elif isinstance(s, ast.FunctionDef):
                logging.debug(f'Ignoring FunctionDef in ClassDef')
            else:
                logging.debug(f'Ignoring {s} in ClassDef')
                pass

        return RecordDecl(record_name, _fields.items(), bt)

    def visit_FunctionDef(self, node):
        # functions in classes are uninterpreted
        self._level += 1
        self.generic_visit(node)
        self._level -= 1

    def parse(self, cdefnode, tyenv, xsrc, tyexprparser):
        self._xsrc = xsrc
        self._tyenv = tyenv
        self._tep = tyexprparser
        self._level = 0
        return self.visit(cdefnode)

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

    def _visit_Literal(self, node):
        value = AC.value(node)

        if isinstance(value, int):
            return value
        elif value is None:
            return TyConstant('void')

        raise self._xsrc._gen_syntax_error(f'Unexpected non-integer literal in type expression', node)

    def visit_NameConstant(self, node): # 3.6
        return self._visit_Literal(node)

    def visit_Num(self, node): # 3.6
        return self._visit_Literal(node)

    def visit_Constant(self, node):
        return self._visit_Literal(node)

    def visit_List(self, node):
        return [self.visit(x) for x in node.elts]

    def visit_Tuple(self, node):
        return tuple([self.visit(x) for x in node.elts])

    def visit_Index(self, node):
        return self.visit(node.value)

    def _parse_record(self, l, v, node):
        rd = self._tyenv.record_decls[l.value]

        if len(rd.generic_tyvars) != len(v):
            raise self._xsrc._gen_syntax_error(f'Incorrect number of type variables supplied for type annotation, expecting {len(rd.generic_tyvars)}, found {len(v)}', node)

        return rd.get_tyrecord(self._tyenv.record_decls, v)

    def visit_Subscript(self, node):
        l = self.visit(node.value)
        if not isinstance(l, TyConstant):
            raise self._xsrc._gen_syntax_error(f'Unrecognized subscript type expression {l}', node)

        if isinstance(node.slice, ast.Slice):
            raise self._xsrc._gen_syntax_error(f'Cannot use slices in type expression')

        #AST 3.9 index...
        v = self.visit(node.slice)

        if isinstance(v, int):
            return TyArray(l, [v])
        elif isinstance(v, tuple):
            if l.value == 'Callable':
                return TyApp(v[-1], v[0])
            elif l.value == 'Generic':
                if not all([isinstance(vv, TyVar) for vv in v]):
                    raise self._xsrc._gen_syntax_error(f'Generic must list only type variables', node)

                # the only place this should be used in in a ClassDef base, so return list
                # this can cause syntax errors ... Callable[Generic[T1]]?
                return v
            elif l.value in self._tyenv.record_decls:
                return self._parse_record(l, v, node)
            else:
                # TODO: could be multidimensional
                raise self._xsrc._gen_syntax_error(f'Subscript on unknown type {l.value} in type expression', node)
        elif isinstance(v, TyVar) or isinstance(v, TyConstant):
            if l.value == 'Generic':
                return [v] # normalize to list
            elif l.value in self._tyenv.record_decls:
                return self._parse_record(l, [v], node)
            else:
                raise self._xsrc._gen_syntax_error(f'Type variables only supported in Generic/Parametric classes', node)

        else:
            raise NotImplementedError(f'Unimplemented slice expression {node.slice}/{v}')



    def visit(self, node):
        if isinstance(node, (ast.Name, ast.Subscript, ast.Index, ast.Tuple, ast.List)) \
           or isinstance(node, AC.isConstant):
            return super(TypeExprParser, self).visit(node)
        else:
            raise self._xsrc._gen_syntax_error(f'Invalid ast node {node.__class__.__name__} in type expression', node)

    def parse(self, node: ast.AST, tyenv: TypeEnv, xsrc):
        self._xsrc = xsrc
        self._tyenv = tyenv
        return self.visit(node)

# function defs also specify a function type, but are syntactically different from function type expressions which use Callable

class FuncDefParser(object):
    def parse(self, fdefnode, tyenv, xsrc, tyexprparser = None, return_is_optional = False):
        if tyexprparser is None:
            tyexprparser = TypeExprParser()

        tep = tyexprparser

        if not return_is_optional and not fdefnode.returns:
            raise xsrc._gen_syntax_error(f'FunctionDef must have a return type', node)

        if fdefnode.returns:
            ret = tep.parse(fdefnode.returns, tyenv, xsrc)
            if isinstance(ret, tuple):
                # DEPRECATED
                ret = TyProduct(ret)
        else:
            ret = TyVar(f'fn_{f.name}_retval')

        arg_types = []
        poly_tydef = set(ret.get_typevars())
        for a in fdefnode.args.args:
            if a.annotation:
                t = tep.parse(a.annotation, tyenv, xsrc)
                poly_tydef |= set(t.get_typevars())
                arg_types.append(t)
            else:
                raise xsrc._gen_syntax_error(f'Argument {a.arg} must be annotated with type', a)

        if fdefnode.args.vararg is not None:
            # needed for min, max
            raise NotImplementedError(f"Don't support varargs in FunctionDef yet")

        fntype = TyApp(ret, arg_types)

        if len(poly_tydef):
            return PolyTyDef(list(poly_tydef), fntype)
        else:
            return fntype


class AppropriateParser(object):
    """Parser for global type declarations, calls the appropriate parser.
       Use this instead of the individual parsers, since its interface
       is less likely to change.
    """

    def __init__(self, tyenv, xsrc):
        self.tyenv = tyenv
        self.xsrc = xsrc
        self.ap = AssignmentParser(self.xsrc)
        self.tep = TypeExprParser()
        self.fdp = FuncDefParser()
        self.rp = RecordDeclParser()

    def parse(self, node):
        if isinstance(node, ast.Assign):
            return self.ap.parse(node, self.tep)
        elif isinstance(node, ast.FunctionDef):
            return self.fdp.parse(node, self.tyenv, self.xsrc, tyexprparser=self.tep)
        elif isinstance(node, ast.expr): # not the Expr statement
            return self.tep.parse(node, self.tyenv, self.xsrc)
        elif isinstance(node, ast.ClassDef):
            return self.rp.parse(node, self.tyenv, self.xsrc, self.tep)
        else:
            raise NotImplementedError(f"Don't know which parser to use for node {node}")
