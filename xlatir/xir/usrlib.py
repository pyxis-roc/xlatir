#!/usr/bin/env python3
#
# usrlib.py
# Support for user-defined libraries.
#
# Author: Sreepathi Pai
#
# Ultimately, we want to move support for intrinsics out of the
# compiler and into user-defined per-language libraries (which can
# include a standard set of XIR libraries, much like SMT-LIB theories).


import ast

XIR_DECL_ANNO = 'xirdecl'

def is_xir_declaration(node):
    def check_decl_deco(dl):
        for x in dl:
            if isinstance(x, ast.Name) and x.id == XIR_DECL_ANNO:
                return True

    def check_stub(f): # mypy style stubs
        if len(f.body) == 1 and isinstance(f.body[0], ast.Expr) \
           and isinstance(f.body[0].value, ast.Ellipsis):
            return True

    return isinstance(node, ast.FunctionDef) and \
        (check_decl_deco(node.decorator_list) or check_stub(node))

def is_xir_type_decl(node):
    if isinstance(node, ast.Assign):
        if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
            if node.value.func.id == 'TypeVar':
                return True
        elif isinstance(node.value, ast.Name):
            return True

    return False

def load_xir_declarations(srcfile):
    with open(srcfile, 'r') as f:
        src = ast.parse(f.read(), srcfile)

        out = []
        for l in src.body:
            if is_xir_declaration(l):
                out.append(l)
            elif is_xir_type_decl(l):
                out.append(l)

        return out

class Decl2Type(object):
    TypeConstants = set(['b1', 'u8',
                         'u16', 'b16', 's16',
                         'u32', 'b32', 's32',
                         'u64', 'b64', 's64',
                         'f32', 'f64',
                         'carryflag',
                         'bool',
                         'str',
                         'intptr_t'])

    TypeVars = None
    TypeAliases = None

    def __init__(self, typing):
        self.typing = typing # hack, for now
        self.TypeVars = {}
        self.TypeAliases = {}

    def py_type_expr_to_xirtype(self, expr):
        if isinstance(expr, ast.Name):
            if expr.id in self.TypeConstants:
                return self.typing.TyConstant(expr.id)
            elif expr.id in self.TypeAliases:
                return self.typing.TyConstant(self.TypeAliases[expr.id])
            elif expr.id in self.TypeVars:
                return self.typing.TyVar(expr.id)
            else:
                raise SyntaxError(f'Unknown type constant "{expr.id}"')
        elif isinstance(expr, ast.Tuple):
            return self.typing.TyProduct([self.py_type_expr_to_xirtype(t) for t in expr.elts])
        elif isinstance(expr, ast.Constant): # or could be ast.NamedConstant in older Python
            if expr.value is None:
                return self.typing.TyConstant('void')
            else:
                raise NotImplementedError(f'Unrecognized annotation Constant {expr.value}')
        elif isinstance(expr, ast.Subscript):
            # only support u32[N] where N is a literal constant
            assert isinstance(expr.slice, ast.Index), f"Unsupported: {expr.slice}"
            assert isinstance(expr.slice.value, ast.Constant), f"Unsupported size: {expr.slice.value}"
            ty = self.py_type_expr_to_xirtype(expr.value)
            return self.typing.TyArray(ty, [int(expr.slice.value.value)])
        else:
            raise NotImplementedError(f'Unrecognized annotation expression type {expr}')

    def from_FunctionDef(self, fdefnode):
        #TODO: SyntaxCheck to prohibit all other kinds of args

        if not fdefnode.returns:
            raise SyntaxError(f'FunctionDef must have a return type')

        ret = self.py_type_expr_to_xirtype(fdefnode.returns)
        arg_types = []
        poly_tydef = set()
        for a in fdefnode.args.args:
            if a.annotation:
                t = self.py_type_expr_to_xirtype(a.annotation)

                if isinstance(t, self.typing.TyVar):
                    poly_tydef.add(t.name)

                arg_types.append(t)
            else:
                raise SyntaxError(f'All arguments must be annotated with types')

        if fdefnode.args.vararg is not None:
            # needed for min, max
            raise NotImplementedError(f"Don't support varargs in FunctionDef yet")

        fntype = self.typing.TyApp(ret, arg_types)

        if len(poly_tydef):
            return self.typing.PolyTyDef(list(poly_tydef), fntype)
        else:
            return fntype

    def _gen_type_variable(self, var, decl):
        assert isinstance(var, ast.Name), var
        assert isinstance(decl, ast.Call) and isinstance(decl.func, ast.Name), decl

        if decl.func.id == 'TypeVar':
            if len(decl.args) == 1:
                #TODO: lookup what TypeVar's first argument actually means
                #TODO: separate type declarations in separate modules?
                if var.id not in self.TypeVars:
                    self.TypeVars[var.id] = None # for now
                else:
                    #f"Duplicate type variable: {var.id}"
                    pass
            else:
                # don't yet support x = TypeVar('x', str, bytes)
                raise NotImplementedError(f"Type restrictions on {var.id} not implemented yet")
        else:
            raise NotImplementedError(f"Don't know how to generate type variables from {decl.func.id}")

    def add_type_decl(self, node):
        if isinstance(node, ast.Assign):
            assert len(node.targets) == 1, f"Don't support multiple assignments {node}"
            assert isinstance(node.targets[0], ast.Name), f"Needs to be a name on LHS"

            if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
                if node.value.func.id == 'TypeVar':
                    self._gen_type_variable(node.targets[0], node.value)
            elif isinstance(node.value, ast.Name):
                if node.value.id in self.TypeConstants:
                    self.TypeAliases[node.targets[0].id] = node.value.id
                else:
                    raise SyntaxError(f"Unknown type constant {node.value.id} in alias {node.targets[0].id}")
            else:
                raise NotImplementedError(f"Don't know how to handle type declaration {node}")
        else:
            assert False
