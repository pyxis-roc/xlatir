#!/usr/bin/python3
#
# xirxlat.py
#
# Utilities for helping with translating XIR to other languages

from . import xir
import ast
from .xirtyping import *
from collections import OrderedDict

# The passing of actual arguments instead of just node in the xlat_*
# functions is meant to make things convenient. In case this doesn't
# work, a class where only the node is passed and the arguments are
# passed as lambdas returning a dictionary might be useful?

class Xlator(object):
    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor

    def get_declaration(self, node, declname = None):
        # must return a declaration
        raise NotImplementedError

    def get_native_type(self, xirty, declname = None):
        raise NotImplementedError

    def xlat_Name(self, name: str, node):
        raise NotImplementedError

    def xlat_NameConstant(self, value, vty, node):
        raise NotImplementedError

    def xlat_Attribute(self, value, attr: str, node):
        raise NotImplementedError

    def xlat_Subscript(self, var, varty, index, indexty, node):
        raise NotImplementedError

    def xlat_Str(self, s, node):
        raise NotImplementedError

    def xlat_Num(self, n, nty, node):
        raise NotImplementedError

    def xlat_BoolOp(self, op, opty, values, node):
        raise NotImplementedError

    def xlat_BinOp(self, op, opty, left, right, node):
        raise NotImplementedError

    def xlat_Compare(self, op, opty, left, right, node):
        raise NotImplementedError

    def xlat_UnaryOp(self, op, opty, value, node):
        raise NotImplementedError

    def xlat_IfExp(self, test, body, orelse, opty, node):
        raise NotImplementedError

    def xlat_If(self, test, body, orelse, node):
        raise NotImplementedError

    def xlat_For(self, target, range_start, range_end, body, node):
        raise NotImplementedError

    def xlat_Break(self, node):
        raise NotImplementedError

    def xlat_float_val(self, v, vty):
        raise NotImplementedError

    def xlat_float_compare(self, comparefn, constval, compareto):
        raise NotImplementedError

    def xlat_Call(self, fn, fnty, args, node):
        raise NotImplementedError

    def xlat_Pass(self, node):
        raise NotImplementedError

    def xlat_Return(self, v, vty, node):
        raise NotImplementedError

    def xlat_Assign(self, lhs, rhs, node): #TODO types?
        raise NotImplementedError

    def xlat_While(self, test, body, node):
        raise NotImplementedError

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        raise NotImplementedError

    def write_output(self, output, translations, defns):
        raise NotImplementedError

class XIRToX(ast.NodeVisitor):
    X = None # structured like a node visitor, except with xlat_X instead of visit_X

    def _get_type(self, tyterm):
        ty = xir.find(tyterm, self.types)
        if isinstance(ty, TyApp):
            ty = TyApp(self._get_type(ty.ret), [self._get_type(a) for a in ty.args])

        # TODO: other types
        assert isinstance(ty, TyTerm)
        return ty

    def _get_op_type(self, op, opty):
        if isinstance(opty, TyVar):
            opty = xir.find(opty, self.types)

        assert isinstance(opty, TyApp)
        arg_types = [self.X.get_native_type(self._get_type(a)) for a in opty.args]

        if len(arg_types) == 2:
            return (op, arg_types[0], arg_types[1])
        elif len(arg_types) == 1:
            return (op, arg_types[0])
        elif len(arg_types) > 2: # TODO: break this up?
            if op == '||' or op == '&&':
                return tuple([op] + arg_types)
            elif op == 'logical_op3' and len(arg_types) == 4:
                return tuple([op] + arg_types)
            elif op == 'FMA' and len(arg_types) == 3:
                return tuple([op] + arg_types)
            elif (op == 'FMA_ROUND' or op == 'FMA_ROUND_SATURATE') and len(arg_types) == 4:
                return tuple([op] + arg_types)
            elif op in (xir.ROUND_SAT_ARITH_FNS | xir.CARRY_ARITH_FNS) and len(arg_types) == 3:
                return tuple([op] + arg_types)
            elif (op.startswith('ReadByte_') or op == 'ReadByte') and len(arg_types) == 3:
                return tuple([op] + arg_types)

        raise NotImplementedError(f"Arguments of length {len(arg_types)} for {op}/{opty} not currently handled")

    def _get_float_val(self, node):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'float':
            assert isinstance(node.args[0], ast.Str), "Don't support non-str-const uses of float"
            x = node.args[0].s.lower()
            s = ''
            if x[0] == '-' or x[1] == '+':
                s = x[0] if x[0] == '-' else ''
                x = x[1:]

            assert x in ('inf', 'nan', '0.0'), f"Unrecognized value {x}"
            return True, s + x

        return False, None

    def visit_Name(self, node):
        if hasattr(self, 'fn') and self.fn:
            if isinstance(node.ctx, ast.Store):
                if node.id not in self.fn._xir_decls:
                    self.fn._xir_decls[node.id] = self.X.get_declaration(node)

        return self.X.xlat_Name(node.id, node)

    def visit_NameConstant(self, node):
        ty = self.X.get_native_type(self._get_type(node._xir_type))
        return self.X.xlat_NameConstant(node.value, ty, node)

    def visit_Attribute(self, node):
        #TODO decide whether to use . or ->
        # TODO: use visit
        return self.X.xlat_Attribute(self.visit(node.value), node.attr, node)

    def visit_Index(self, node):
        return self.visit(node.value)

    def visit_Subscript(self, node):
        #TODO decide whether to use . or ->
        # TODO: use visit
        var = self.visit(node.value)
        index = self.visit(node.slice)
        varty = self.X.get_native_type(self._get_type(node.value._xir_type))
        indexty = self.X.get_native_type(self._get_type(node.slice._xir_type))

        return self.X.xlat_Subscript(var, varty, index, indexty, node)

    def visit_Str(self, node):
        return self.X.xlat_Str(node.s, node)

    def visit_Constant(self, node):
        ty = self.X.get_native_type(self._get_type(node._xir_type))
        if isinstance(node.value, bool) or node.value is None: # must be checked before int!
            return self.X.xlat_NameConstant(node.value, ty, node)
        if isinstance(node.value, (int, float)):
            return self.X.xlat_Num(node.value, ty, node)
        elif isinstance(node.value, str):
            return self.X.xlat_Str(node.value, node)
        else:
            raise NotImplementedError(f'Constant of type={node.value} not handled')

    def visit_Num(self, node):
        ty = self.X.get_native_type(self._get_type(node._xir_type))
        return self.X.xlat_Num(node.n, ty, node)

    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.And):
            op = '&&'
        elif isinstance(node.op, ast.Or):
            op = '||'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_BoolOp(op, opty, [self.visit(v) for v in node.values], node)

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Mult):
            op = '*'
        elif isinstance(node.op, ast.BitAnd):
            op = '&'
        elif isinstance(node.op, ast.Add):
            op = '+'
        elif isinstance(node.op, ast.Sub):
            op = '-'
        elif isinstance(node.op, ast.Pow):
            op = '**'
        elif isinstance(node.op, ast.Mod):
            op = '%'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_BinOp(op, opty, self.visit(node.left), self.visit(node.right), node)

    def visit_Compare(self, node):
        assert len(node.ops) == 1, f"Not supported, more than op: {node.ops}"
        assert len(node.comparators) == 1, f"Not supported, more than one comparator: {node.ops}"

        if isinstance(node.ops[0], ast.Lt):
            op = '<'
        elif isinstance(node.ops[0], ast.Gt):
            op = '>'
        else:
            raise NotImplementedError(node.ops[0])

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_Compare(op, opty, self.visit(node.left),
                                   self.visit(node.comparators[0]), node)

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            op = '-'
        elif isinstance(node.op, ast.Not):
            op = '!' # logical not
        elif isinstance(node.op, ast.Invert):
            op = '~'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return self.X.xlat_UnaryOp(op, opty, self.visit(node.operand), node)

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_IfExp(self, node):
        opty = self._get_type(node._xir_type)

        opty = ('?:', self.X.get_native_type(opty.ret),
                self.X.get_native_type(opty.args[0]),
                self.X.get_native_type(opty.args[1]),
                self.X.get_native_type(opty.args[2]))

        return self.X.xlat_IfExp(self.visit(node.test),
                                 self.visit(node.body),
                                 self.visit(node.orelse),
                                 opty,
                                 node)

    def visit_If(self, node):
        return self.X.xlat_If(self.visit(node.test),
                              accumulate_body([self.visit(x) for x in node.body]),
                              accumulate_body([self.visit(x) for x in node.orelse]),
                              node)

    def visit_Break(self, node):
        return self.X.xlat_Break(node)

    def visit_Call(self, node):
        #TODO: this str is needed because the return values are from xlat_

        n = str(self.visit(node.func))

        if n == 'set_sign_bitWidth':
            return self.visit(node.args[0])
        elif n == 'int':
            return self.visit(node.args[0])
        elif n == 'set_value':
            return self.visit(node.args[2])
        elif n == 'float':
            _, v = self._get_float_val(node)
            assert v is not None, node.args[0]

            ty = self._get_type(node._xir_type)
            return self.X.xlat_float_val(v, self.X.get_native_type(ty.ret))
        elif n == 'FLOAT_COMPARE_EQ' or n == 'FLOAT_COMPARE_NOTEQ':
            _, v = self._get_float_val(node.args[1])
            assert v is not None, node.args[1]

            if v == 'inf' or v == '-inf':
                fn = "!isfinite"
            elif v == 'nan' or v == '-nan':
                fn = "isnan"

            return self.X.xlat_float_compare(n, v, self.visit(node.args[0]))

        #TODO: add the name of the function
        assert hasattr(node, '_xir_type'), f"Function {n} does not have _xir_type on node"

        fnty = self._get_op_type(n, node._xir_type)

        if hasattr(self.X, 'lib'):
            if hasattr(self.X.lib, n):
                fnxlat = getattr(self.X.lib, n)
                return fnxlat(n, fnty, [self.visit(a) for a in node.args[:len(fnty)-1]], node)

        return self.X.xlat_Call(n, fnty, [self.visit(a) for a in node.args[:len(fnty)-1]], node)

    def visit_Tuple(self, node):
        # this assumes that this will always be structure initialization
        return [self.visit(e) for e in node.elts]

    def visit_Return(self, node):
        if node.value:
            v = self.visit(node.value)
        else:
            v = None

        #TODO: embed struct name?
        return self.X.xlat_Return(v, self._retval_ty, node)

    def visit_Pass(self, node):
        return self.X.xlat_Pass(node)

    def visit_AnnAssign(self, node):
        assert node.simple == 1, "Not supported"

        if node.value is not None:
            return self.X.xlat_Assign(self.visit(node.target), self.visit(node.value), node)
        else:
            # handle just a type 'declaration'; x : u32
            return self.X.xlat_Pass(ast.Pass())

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Not supported"

        #TODO: types?
        return self.X.xlat_Assign(self.visit(node.targets[0]), self.visit(node.value), node)

    def visit_While(self, node):
        assert len(node.orelse) == 0, f"orelse for While node not supported"

        #TODO: type checking?
        test = self.visit(node.test)
        body = [self.visit(x) for x in node.body]

        return self.X.xlat_While(test, body, node)

    def visit_For(self, node):
        target = self.visit(node.target)
        assert isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name) and node.iter.func.id == "range"

        #TODO: check for ast.Num, but xir would've done this

        range_start = self.visit(node.iter.args[0])
        range_end = self.visit(node.iter.args[1])
        body = [self.visit(x) for x in node.body]

        return self.X.xlat_For(target, range_start, range_end, body, node)

    def visit_FunctionDef(self, node):
        # perhaps make this per block?
        self.fn = node

        node._xir_decls = {}
        args = []
        for a in node.args.args:
            t = self.X.get_declaration(a, declname=a.arg)
            node._xir_decls[a.arg] = None
            args.append(t)


        func = node.name
        declname = None
        if isinstance(self._get_type(node._xir_type.ret), TyProduct):
            if func.startswith("execute_"):
                # compat, anonymous
                declname = func[len('execute_'):]
            else:
                assert False # not supported in nonptx

        retval = self.X.get_native_type(node._xir_type.ret, declname)
        self._retval_ty = retval

        # order is important!
        body = accumulate_body([self.visit(s) for s in node.body if not isinstance(s, ast.Assert)])
        decls = [(v, t) for (v, t) in self.fn._xir_decls.items() if t is not None]

        out = self.X.xlat_FunctionDef(func, args, retval, decls, body, node)

        self.fn = None

        return out

    def visit_Assert(self, node):
        return None

    def translate(self, sem, types, tyenv):
        self.types = types
        self.tyenv = tyenv
        #TODO: handle this?
        self.defns = []
        return self.visit(sem)

def accumulate_body(stmts):
    """Allow statements to return a list of translations that are then folded into a single list"""
    out = []
    for s in stmts:
        if isinstance(s, list):
            out.extend(s)
        else:
            out.append(s)

    return out

class RecordInstantiation:
    def __init__(self, decl, instantiation):
        self.decl = decl
        self.inst = instantiation.copy()
        self.subst = decl.get_inst_subst(instantiation)
        self.suffix = tuple([x[1] for x in self.subst])
        self.subst = dict(self.subst)

        self.inst.name = f"{self.decl.name}_{'_'.join(self.suffix)}"

    @property
    def name(self):
        return self.inst.name

    def equivalent(self, o):
        if not isinstance(o, RecordInstantiation): return False
        if o.name != self.name: return False

        if o.decl.name != self.decl.name: return False

        for (of, ot), (sf, st) in zip(o.inst.fields_and_types, self.inst.fields_and_types):
            if not (ot == st): return False

        return True

    def __str__(self):
        return str(self.inst)

    __repr__ = __str__

class PolymorphicInst(ast.NodeVisitor):
    def __init__(self, translator):
        self._x2x = translator
        self._tyenv = None
        self._ty = None
        self.instantiations = {'records': OrderedDict()}
        self._ri = {}

    def find(self, ty):
        if isinstance(ty, TyRecord):
            ty = self._resolve_tyvars(ty)
            assert self._tyenv.is_generic_record(ty.name), f"{ty.name} is not a generic record, so can't find instantiation"
            decl = self._tyenv.record_decls[ty.name]
            suffix = [x[1] for x in decl.get_inst_subst(ty)]
            key = (decl.name, *suffix)
            return self._ri.get(key, None)

        return None

    def is_instantiation(self, ty):
        if isinstance(ty, TyRecord):
            return ty.name in self.instantiations['records']

        return False

    def add_instantiation(self, i):
        if isinstance(i, RecordInstantiation):
            x = self.instantiations['records']
            if i.inst.name in x:
                assert x[i.inst.name].equivalent(i), f"Instantiated record {i.inst.name} shares name with {x[i.inst.name]}, but is not equivalent"
            else:
                x[i.inst.name] = i
                key = (i.decl.name, *i.suffix)
                self._ri[key] = i
        else:
            raise NotImplementedError(f"Don't handle {i}")

    def _is_ground(self, ty):
        v = ty.get_typevars()
        return len(v) == 0

    def _resolve_tyvars(self, tyrec):
        out = []
        for f, t in tyrec.fields_and_types:
            if isinstance(t, TyRecord):
                raise NotImplementedError
            else:
                out.append((f, self._x2x._get_type(t)))

        return TyRecord(tyrec.name, out)

    def visit_Call(self, node):
        assert hasattr(node, '_xir_type')
        fty = self._x2x._get_type(node._xir_type)

        for pr in [fty.ret]:
            if isinstance(pr, TyRecord) and pr.name:
                if self._tyenv.is_generic_record(pr.name):
                    inst = self._resolve_tyvars(pr)
                    rd = self._tyenv.record_decls[inst.name]
                    if len(rd.generic_tyvars):
                        ity = RecordInstantiation(rd, inst)
                        self.add_instantiation(ity)

        self.generic_visit(node)

    def visit_Attribute(self, node):
        # TODO: this was checking node.value for _xir_type, but
        # xir.py sets the type on node, not node.value ...
        assert hasattr(node, '_xir_type')
        vty = self._x2x._get_type(node._xir_type)
        if isinstance(vty, TyRecord) and vty.name and self._tyenv.is_generic_record(vty.name):
            rd = self._tyenv.record_decls[vty.name]
            if len(rd.generic_tyvars):
                ity = RecordInstantiation(rd, vty)
                self.add_instantiation(ity)
        else:
            pass

        pass

        self.generic_visit(node)

    def get_instantiations(self, node, tyreps, tyenv):
        self._ty = tyreps
        self._tyenv = tyenv
        self._x2x.types = self._ty
        self.visit(node)
