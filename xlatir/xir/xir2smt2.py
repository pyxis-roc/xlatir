#!/usr/bin/env python3
#
# xir2smt.py
#
# Translate XIR to SMT2
#
# Author: Sreepathi Pai

import ast
from . import xir
from . import xirxlat
from .xirtyping import *
import textwrap
import os
import struct
from xlatir.smt2ast import *
import copy
from . import xirpeval
from collections import namedtuple
from xlatir.imp2func.passmgr import I2FConfig, InterPassContext, PassManager
from xlatir.imp2func.passes import *
from .astcompat import AC
from .xirlibsmt2 import XIRBuiltinLibSMT2

ROUND_MODES_SMT2 = {'rp': 'RTP', # positive inf
                    'rm': 'RTN', # negative inf
                    'rz': 'RTZ', # zero
                    'rn': 'RNE'} # nearest even, no support in PTX for RNA


DT = namedtuple('datatype', 'name constructor fields fieldtypes sort_cons')

DATA_TYPES_LIST = [DT('predpair', 'mk-pair', ('first', 'second'), ('pred', 'pred'), 'Pair'),
                   DT('cc_reg', 'mk-ccreg', ('cf',), ('carryflag',), 'CCRegister'),
                   DT('s16_carry', 'mk-pair', ('first', 'second'), ('s16', 'carryflag'), 'Pair'),
                   DT('u16_carry', 'mk-pair', ('first', 'second'), ('u16', 'carryflag'), 'Pair'),
                   DT('s32_carry', 'mk-pair', ('first', 'second'), ('s32', 'carryflag'), 'Pair'),
                   DT('u32_carry', 'mk-pair', ('first', 'second'), ('u32', 'carryflag'), 'Pair'),
                   DT('u64_carry', 'mk-pair', ('first', 'second'), ('u64', 'carryflag'), 'Pair'),
                   DT('s64_carry', 'mk-pair', ('first', 'second'), ('s64', 'carryflag'), 'Pair'),
                   DT('u32_cc_reg', 'mk-pair', ('first', 'second'), ('u32', 'cc_reg'), 'Pair'),
                   DT('s32_cc_reg', 'mk-pair', ('first', 'second'), ('s32', 'cc_reg'), 'Pair'),
                   DT('s64_cc_reg', 'mk-pair', ('first', 'second'), ('s64', 'cc_reg'), 'Pair'),
                   DT('u64_cc_reg', 'mk-pair', ('first', 'second'), ('u64', 'cc_reg'), 'Pair'),
                   ]

DATA_TYPES = dict([(dt.name, dt) for dt in DATA_TYPES_LIST])

FIELDS_TO_DT = dict([(dt.fieldtypes, Symbol(dt.name)) for dt in DATA_TYPES_LIST])

def bool_to_pred(x):
    return SExprList(Symbol("bool_to_pred"), x)

def pred_to_bool(x):
    return SExprList(Symbol("pred_to_bool"), x)

class SMT2lib(object):
    def __init__(self):
        self.xlib = []

    def add_lib(self, lib):
        lib.parent = self
        self.xlib.append(lib)

    def get_builtin(self):
        return XIRBuiltinLibSMT2()

    def can_xlat(self, n):
        for lib in self.xlib:
            if hasattr(lib, n) and not (n in lib.unsupported): return True

        return hasattr(self, n)

    def do_xlat(self, n, fnty, args, node):
        op = self._get_lib_op(fnty, node, n)
        assert not isinstance(op, str), f"Operator for {fnty} is a string"
        arglen = len(fnty) - 1
        return op(*args[:arglen])

    def _get_lib_op(self, fnty, node, n):
        xirty = node._xir_type if node is not None else None

        for lib in self.xlib:
            try:
                # this does first match
                lc = lib.dispatch(fnty, xirty)
                if isinstance(lc, str):
                    print(f"WARNING: {fnty} returns str from {lib.__class__.__name__}")
                return lc
            except KeyError:
                print(f"{lib.__class__.__name__}: keyerror: {fnty}")
            except NotImplementedError as e:
                print(f"{lib.__class__.__name__}: notimplemented: {fnty} ({e})")

        assert False, f"Couldn't find {fnty} in libraries"

def create_dag(statements, _debug_trace = False):
    # value numbering
    expr = {}
    values = {}

    def get_key(st):
        def _add_key(k):
            if k not in expr:
                expr[k] = len(expr) + 1
                values[len(expr)] = st

            return expr[k]

        if isinstance(st, SExprList):
            if is_call(st, "_xir_attr_ref"):
                # treat attr refs specially since they are a single variable
                return _add_key(str(st))
            else:
                # this is function application
                return tuple([get_key(v) for v in st.v])
        elif isinstance(st, (Symbol, Numeral, Decimal, Hexadecimal, Binary, String)):
            return _add_key(str(st))
        else:
            raise NotImplementedError(f"create_dag: Not implemented yet: {st}/{type(st)}")

    def reconstitute(k):
        if isinstance(k, tuple):
            return SExprList(*[reconstitute(v) for v in k])
        else:
            return values[k]

    if _debug_trace:
        print("STATEMENTS")
        for s in statements:
            print(s)

    # first, assign value numbers to the statements in the array
    out = []
    for s in statements:
        if isinstance(s, SExprList) and len(s.v) == 0: # pass
            continue

        if is_call(s, "="):
            # treat assignment specially
            k = get_key(s.v[2]) # value_key

            expr_key = str(s.v[1])
            expr[expr_key] = k

            if k in values:
                # update the value that a value number points to

                if isinstance(values[k], (Numeral, Decimal, Hexadecimal, Binary)):
                    # sanity check, but note this will change the depiction of the constant?
                    assert values[k].v == s.v[2].v, f"Two different constants have the same key {values[k]} and {s.v[2]}"
                    # this should never happen
                    assert str(values[k]) == str(s.v[2]), f"Same constant value, but different types! {str(values[k])} != {str(s.v[2])}"
                else:
                    if not isinstance(s.v[2], Symbol):
                        # values[k] is a Symbol, but RHS is not, so set it to a constant
                        values[k] = s.v[2].v
                    # elif not isinstance(s.v[1], Symbol):
                    #     TODO?
                    #     assert isinstance(s.v[1], SExprList) and s.v[1].v[0].v == "attr", f"LHS is not a symbol or write to a structure {s.v[1]}"
                    #     values[k] = s.v[2].v
                    else:
                        # both symbols, don't record
                        pass
            else:
                values[k] = s.v[1]
        else:
            k = get_key(s)

        out.append(k)

    # assume statement is return [maybe indicate more robustly?]
    retval = out[-1]

    if _debug_trace:
        print("EXPRESSIONS -> VALUES")
        for e, v in expr.items():
            print("\t", e, v)

        print("VALUES -> EXPRESSIONS")
        for v, e in values.items():
            print("\t", v, e)

        print("RETVAL", retval)
    #print(expr)
    #print(values)
    r = reconstitute(retval)
    #print(r)
    return r

def eliminate_xir_attr_ref(dag):
    if isinstance(dag, SExprList):
        if is_call(dag, "_xir_attr_ref"):
            return SExprList(Symbol(dag.v[1].v), dag.v[2])
        else:
            out = []
            for v in dag.v:
                vo = eliminate_xir_attr_ref(v)
                out.append(vo)

            return SExprList(*out)
    else:
        return dag

class SMT2Xlator(xirxlat.Xlator):
    desugar_boolean_xor = False
    name = "smt2"

    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor
        self.lib = SMT2lib()
        self._if_exp_recognizer = IfExpRecognizer()
        self._if_to_if_exp = IfToIfExp()
        self._array_fn = ArrayFn()
        self._ref_return_fixer = RefReturnFixer()
        self._tvndx = 0 # tmp variable suffixes
        self._use_imp2 = False
        self._label = 0
        self.lhs_types = {}
        self.gen_structs = {}

    def pre_xlat_transform(self, s):
        self._use_imp2 = False
        s = self._ref_return_fixer.fix_returns(s)

        self._if_exp_recognizer.visit(s)
        s = self._if_to_if_exp.visit(s)
        s = xirpeval.Unroll(s)

        ef = xirpeval.EvalFunc()
        s = ef.visit(s)

        s = self._array_fn.convert(s, 'extractAndZeroExt_4', 1, 4, 'na_extractAndZeroExt_4')
        s = self._array_fn.convert(s, 'extractAndZeroExt_2', 1, 2, 'na_extractAndZeroExt_2')
        s = self._array_fn.convert(s, 'extractAndSignExt_4', 1, 4, 'na_extractAndSignExt_4')
        s = self._array_fn.convert(s, 'extractAndSignExt_2', 1, 2, 'na_extractAndSignExt_2')

        s = dearrayify(s)
        BreakTarget().add_info(s)
        s = UnrollWhileLoop().visit(s)

        return s

    def get_label_prefix(self, suffix = ''):
        self._label += 1
        if self.x2x.fn:
            if suffix: suffix = '_' + suffix
            return f'{self.x2x.fn.name}_{self._label}{suffix}'
        else:
            return f'{suffix}{self._label}'

    def _add_record_inst(self, inst):
        name = inst.name
        cons = f"mk-{inst.decl.name}"
        fields = tuple([x[0] for x in inst.inst.fields_and_types])
        ftypes = tuple([x[1].get_suffix() for x in inst.inst.fields_and_types])
        sort_cons = inst.decl.name

        dt = DT(name, cons, fields, ftypes, sort_cons)

        if dt.name not in DATA_TYPES:
            DATA_TYPES_LIST.append(dt)
            DATA_TYPES[dt.name] = dt
            FIELDS_TO_DT[(ftypes, Symbol(dt.name))] = dt

    def _get_smt2_type(self, node, declname = None):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        if isinstance(ty, TyVar):
            t = xir.find(ty, self.x2x.types)
        else:
            t = ty

        if isinstance(t, TyPtr):
            pt = self._get_smt2_type(t.pty)

            if isinstance(t.pty, TyConstant) and pt.v == 'cc_reg':
                if declname:
                    return SExprList(Symbol(declname), pt.v)
                else:
                    return pt

            raise NotImplementedError(f"Support for pointer types {t} pointing to {pt}")
            return Symbol("ptr_{pt}")

        if isinstance(t, TyRecord):
            if self.x2x.tyenv.is_generic_record(t.name):
                # find instantiation
                inst = self.x2x.polyinst.find(t)
                assert inst is not None
                struct_name = inst.name
                self._add_record_inst(inst)
                self.gen_structs[inst.decl.name] = inst.decl
            else:
                struct_name = t.name
                self.gen_structs[struct_name] = t

            if not declname:
                return Symbol(struct_name)
            else:
                return SExprList(Symbol(declname), Symbol(struct_name))

        if isinstance(t, TyApp):
            arg_types = [self._get_smt2_type(x) for x in t.args]
            return SExprList(self._get_smt2_type(t.ret), *arg_types)

        if isinstance(t, TyProduct):
            #NOTE: this won't handle function pointers as return values
            elt_types = [self._get_smt2_type(x) for x in t.args]
            elt_names = [f"(out{k} {ty})" for k, ty in enumerate(elt_types)]

            field_types_key = tuple([e.v for e in elt_types])

            if field_types_key in FIELDS_TO_DT:
                return FIELDS_TO_DT[field_types_key]
            else:
                raise NotImplementedError(f"Type is TyProduct, but {field_types_key} not found in FIELDS_TO_DT")

        if isinstance(t, TyArray):
            elt_type = self._get_smt2_type(t.elt)
            assert len(t.sizes) == 1, f"Unsupported non-1D arrays: {t.sizes}"
            if str(elt_type) == "b1":
                # bitstrings
                return SExprList(Symbol("_"), Symbol("BitVec"), Decimal(t.sizes[0]))
            else:
                raise NotImplementedError(f"Don't support {elt_type} arrays in smt2")

        if not isinstance(t, TyConstant):
            if isinstance(t, TyVarLiteral):
                #print(t, " is a literal_type")
                return Symbol(f'literal_type{t}')

            assert isinstance(t, TyConstant), f"Non-TyConstant type: {t}"

        ty = t.value
        if ty == 'bool': ty = 'pred'

        if declname:
            return SExprList(Symbol(declname), Symbol(ty))
        else:
            return Symbol(ty)

    def get_declaration(self, node, declname = None):
        return self._get_smt2_type(node, declname)

    def get_native_type(self, xirty, declname = None):
        return self._get_smt2_type(xirty, declname)

    def xlat_Pass(self, node):
        return SExprList()

    def xlat_Name(self, name: str, node):
        if name.startswith("MACHINE_SPECIFIC_"):
            if name == "MACHINE_SPECIFIC_execute_lg2_negative_number":
                namety = self.get_native_type(self.x2x._get_type(node._xir_type))
                return self.xlat_float_val("nan", namety)
            elif name == "MACHINE_SPECIFIC_execute_rem_divide_by_zero_signed":
                namety = self.get_native_type(self.x2x._get_type(node._xir_type))
                width = int(namety.v[1:])
                return Hexadecimal((1 << width) - 1, width = width//4)
            elif name == "MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned":
                return Symbol(name) # lambda x: x
            elif name == "MACHINE_SPECIFIC_execute_rem_divide_by_neg":
                return Symbol(name) # lambda x, y: x % abs(y) ???
            elif name == "MACHINE_SPECIFIC_execute_div_divide_by_zero_integer":
                return Symbol(name)
            elif name == "MACHINE_SPECIFIC_execute_div_divide_by_zero_float":
                namety = self.get_native_type(self.x2x._get_type(node._xir_type))
                return self.xlat_float_val("nan", namety)
            else:
                raise NotImplementedError(f"Not implemented: Machine-specific value {name}")

        return Symbol(name)

    def xlat_NameConstant(self, value, vty, node):
        if node.value == True:
            return smt2_literal(1, vty.v)
        elif node.value == False:
            return smt2_literal(0, vty.v)
        elif node.value is None:
            return Symbol("None")

        raise NotImplementedError(f"NameConstant for value {value} not supported")

    #TODO: types?
    def xlat_Attribute(self, value, attr: str, node):
        if isinstance(node._xir_type, TyVar) and node._xir_type.name == "TY:cc_reg.cf":
            #cc_reg_type = self.x2x._get_type(TyVar("TY:cc_reg"))
            #is_ptr = isinstance(cc_reg_type, TyPtr)

            # this mirrors the selector syntax
            # (_xir_attr_ref field-name variable variable-type)
            return SExprList(Symbol("_xir_attr_ref"), String(attr), value, Symbol("cc_reg"))
            pass

        return SExprList(Symbol(attr), value)

    def xlat_Str(self, s, node):
        return String(s)

    def _smt2_literal(self, v, ty):
        return smt2_literal(v, ty.v)

    def xlat_Num(self, n, nty, node):
        return self._smt2_literal(n, nty)

    def xlat_BoolOp(self, op, opty, values, node):
        if opty[1].v == "pred":
            if op == "||":
                op = "bvor"
            elif op == "&&":
                op = "bvand"
        else:
            assert False, opty

        return SExprList(Symbol(op), *values)

    def xlat_BinOp(self, op, opty, left, right, node):
        return f'({left} {op} {right})'

    def xlat_Compare(self, op, opty, left, right, node):
        return f'({left} {op} {right})'

    def xlat_UnaryOp(self, op, opty, value, node):
        if op == '!':
            assert opty[1].v == 'pred', opty
            return SExprList(Symbol('bvnot'), value)
        elif op == '-':
            if opty[1].v in ('f32', 'f64'):
                return SExprList(Symbol('fp.neg'), value)
            else:
                return SExprList(Symbol('bvneg'), value)
        else:
            raise NotImplementedError(f"Unknown op {op}/{opty}")

    def xlat_IfExp(self, test, body, orelse, opty, node):
        if is_call(test, "bool_to_pred"):
            test = test.v[1]
        else:
            # TODO: handle this correctly, these are functions
            # operating on bitvectors but returning bool, as opposed to
            # bvor/bvand, etc.
# and test.v[0].v not in bool_returning_functions            bool_returning_functions = set(['=', 'bvuge', 'bvsge'])

            if isinstance(opty[2], Symbol) and opty[2].v == "pred":
                test = SExprList(Symbol("pred_to_bool"), test)

        return SExprList(Symbol("ite"), test, body, orelse)

    def _cast_to_bool(self, expr, ty):
        tyorig = ty
        if not isinstance(ty, TyConstant):
            if isinstance(ty, TyApp):
                tyorig = ty
                ty = ty.ret
                assert isinstance(ty, TyConstant), f"Return type for {expr} is not TyConstant {ty}"
            else:
                raise NotImplementedError(f"Unknown type for condition: {ty}")

        #print(expr, ty, tyorig)

        if ty.value == 'bool':
            if is_call(expr, "bool_to_pred"):
                expr = expr.v[1]

            if is_call(expr, "bvand") or is_call(expr, "bvor"):
                return pred_to_bool(expr)

            return expr

        if ty.value[0] in ('b', 'u', 's'):
            # integer
            width = int(ty.value[1:])
            assert (width % 4) == 0
            falsevalue = Hexadecimal(0, width = width // 4)
        else:
            raise NotImplementedError(f"Don't know what false values look like for {ty}")

        return SExprList(Symbol("not"), SExprList(Symbol("="), falsevalue, expr))

    def xlat_Subscript(self, var, varty, index, indexty, node):
        #TODO: if index a literal, we can simply use extract

        # (bool_to_pred (bvgt (bvand var (bvshl 1 index) ) 0)) for load
        # (bvand var (bvnot bit)) for store
        if is_call(varty, "_") and str(varty.v[1]) == 'BitVec':
            width = varty.v[2].v
            zero = shortest_bv(0, width)

            if indexty.v[0] in ('b', 'u', 's'): # TODO: make a predicate for this
                indexwidth = int(indexty.v[1:])
                one = shortest_bv(1, width)
                if indexwidth < width:
                    index = SExprList(SExprList(Symbol("_"),
                                                Symbol("zero_extend"),
                                                Decimal(width - indexwidth)),
                                      index)
                elif indexwidth > width:
                    #TODO: this could be problematic...
                    index = SExprList(SExprList(Symbol("_"),
                                                Symbol("extract"),
                                                Decimal(width-1),
                                                Decimal(0)),
                                      index)
            else:
                raise NotImplementedError(f'Unknown index type {indexty} in subscript')

            bit = SExprList(Symbol("bvshl"), one, index)

            if isinstance(node.ctx, ast.Load):
                out = bool_to_pred(SExprList(Symbol("not"),
                                             SExprList(Symbol("="), zero,
                                                       SExprList(Symbol("bvand"), var, bit))))
            else:
                out = (copy.deepcopy(var),
                       copy.deepcopy(index),
                       SExprList(Symbol("bvand"), var, SExprList(Symbol("bvnot"),
                                                                 bit)))
            return out
        else:
            raise NotImplementedError(f"Don't support {varty} for subscripts")

    def xlat_If(self, test, body, orelse, node):
        l = self.get_label_prefix("if")
        # cbranch (cond) truepart falsepart
        # truepart ends with branch to part after
        # falsepart ends with branch to part after
        self._use_imp2 = True

        cond = self._cast_to_bool(test, self.x2x._get_type(node.test._xir_type))
        true_label = f"if_{l}_true"

        if hasattr(node, '_xir_loop_id'):
            next_label = self._get_break_label(node._xir_loop_id)
        else:
            next_label = f"if_{l}_end"

        false_label = f"if_{l}_false" if len(orelse) else next_label

        out = [SExprList(Symbol("cbranch"), cond,
                         Symbol(true_label),
                         Symbol(false_label)),

               SExprList(Symbol("label"), Symbol(true_label))]

        out.extend(body)

        # if last statement is a break, don't add additional branch
        if len(body) and not is_call(body[-1], "branch"):
            out.append(SExprList(Symbol("branch"), Symbol(next_label)))

        out.append(SExprList(Symbol("label"), Symbol(false_label)))
        out.extend(orelse)

        if len(orelse):
            if not is_call(orelse[-1], "branch"):
                out.append(SExprList(Symbol("branch"), Symbol(next_label)))

        if false_label != next_label:
            out.append(SExprList(Symbol("label"), Symbol(next_label)))

        return out
        #raise NotImplemented("Don't support If in SMT2 yet")

    def _get_break_label(self, loop_id):
        if self.x2x.fn:
            lbl = f'{self.x2x.fn.name}_loop_break_{loop_id}'
        else:
            lbl = f'loop_break_{loop_id}'

        return lbl

    def xlat_Break(self, node):
        return SExprList(Symbol("branch"), Symbol(self._get_break_label(node._xir_loop_id)))
        #raise NotImplemented("Don't support Break loops in SMT2 yet")

    def xlat_float_val(self, v, vty):
        assert vty.v in ('f32', 'f64'), f"Unsupported float constant type {vty}"
        if vty.v == 'f32':
            vty = (Decimal(8), Decimal(24))
        elif vty.v == 'f64':
            vty = (Decimal(11), Decimal(53))

        if v == 'inf':
            return SExprList(Symbol("_"), Symbol("+oo"), *vty)
        elif v == '-inf':
            return SExprList(Symbol("_"), Symbol("-oo"), *vty)
        elif v == 'nan':
            return SExprList(Symbol("_"), Symbol("NaN"), *vty)
        elif v == '-nan':
            # TODO: FP theory *does* allow negative NaNs if using a raw format (i.e. fp)
            return SExprList(Symbol("_"), Symbol("NaN"), *vty)
        elif v == '0.0' or v == '+0.0':
            return SExprList(Symbol("_"), Symbol("+zero"), *vty)
        elif v == '-0.0':
            return SExprList(Symbol("_"), Symbol("-zero"), *vty)
        else:
            raise NotImplementedError(f"Unknown float constant {v}")

    def xlat_float_compare(self, comparefn, constval, compareto):
        if constval == 'inf' or constval == '-inf':
            fn = SExprList(Symbol("fp.isInfinite"), compareto)
        elif constval == 'nan' or constval == '-nan':
            fn = SExprList(Symbol("fp.isNaN"), compareto)

        if comparefn == 'FLOAT_COMPARE_NOTEQ':
            fn = SExprList(Symbol("not"), fn)

        return bool_to_pred(fn)

    def xlat_Call(self, fn, fnty, args, node):
        if fn.startswith('BITSTRING_') or fn.startswith('FROM_BITSTRING_'):
            return args[0]
        else:
            if fnty[0] in self.x2x.tyenv.record_decls:
                fn = "mk-" + fn

            arglen = len(fnty) - 1
            return SExprList(Symbol(fn), *args[:arglen])

    def xlat_Return(self, v, vty, node):
        if isinstance(v, list):
            return SExprList(Symbol("mk-pair"), *v)
        else:
            return v

    def _get_tmp_var(self):
        nv = Symbol(f"tmp_var_gen_{self._tvndx}")
        self._tvndx += 1
        return nv

    def record_type(self, var, ty):
        if self.x2x.fn.name not in self.lhs_types:
            self.lhs_types[self.x2x.fn.name] = {}

        self.lhs_types[self.x2x.fn.name][str(var)] = set([ty])

    def _handle_bitstring_assign(self, lhs, rhs, node):
        assert len(node.targets) == 1
        assert isinstance(lhs, tuple)

        var, index, lhsexpr = lhs
        if isinstance(node, ast.Assign):
            lhsty = self.get_native_type(node.targets[0].value._xir_type)
        else:
            lhsty = self.get_native_type(node.targets.value._xir_type)

        width = lhsty.v[2].v
        rhsexpr = SExprList(SExprList(Symbol("_"), Symbol("zero_extend"), Decimal(width - 1)),
                            rhs)

        rhsexpr = SExprList(Symbol("bvshl"), rhsexpr, index)

        return SExprList(Symbol("="), var, SExprList(Symbol("bvor"),
                                                     lhsexpr,
                                                     rhsexpr))

    def xlat_Assign(self, lhs, rhs, node):
        if isinstance(lhs, list):
            # deconstruct a assignment by first assigning to a temporary variable
            # and then deconstructing each individual field
            #  (a, b) = f()
            # is turned to
            #
            #   tmp = f()
            #   a = (first tmp)
            #   b = (second tmp)
            #

            # for some reason targets[X] does not have ._xir_type
            rhsty = self.get_native_type(node.value._xir_type)
            tv = self._get_tmp_var()
            out = [SExprList(Symbol("="), tv, rhs)]

            self.record_type(tv, rhsty.v[0])

            if rhsty.v[0].v not in DATA_TYPES:
                raise NotImplementedError(f"Don't know how to unpack {rhsty.v[0]}, not in DATA_TYPES")

            fields = DATA_TYPES[rhsty.v[0].v].fields
            fieldtypes = DATA_TYPES[rhsty.v[0].v].fieldtypes

            for ln, sel, fty in zip(lhs, fields, fieldtypes):
                out.append(SExprList(Symbol("="), ln, SExprList(Symbol(sel), tv)))
                self.record_type(ln, fty)

            return out
        elif isinstance(lhs, tuple):
            return self._handle_bitstring_assign(lhs, rhs, node)
        else:
            if is_call(lhs, "_xir_attr_ref"):
                out = [SExprList(Symbol("="), lhs, rhs)]
                #TODO: lhs type is weird for this ... s32 (cc_reg/cf)
                self.record_type(lhs, self.get_native_type(node.value._xir_type))

                dt = DATA_TYPES[lhs.v[3].v]
                var = lhs.v[2]
                reconstruct = [Symbol(dt.constructor)]
                for sel in dt.fields:
                    reconstruct.append(SExprList(Symbol("_xir_attr_ref"),
                                                 String(sel),
                                                 Symbol(var.v),
                                                 Symbol(dt.name)))

                out.append(SExprList(Symbol("="), Symbol(var.v), SExprList(*reconstruct)))
                self.record_type(var, Symbol(dt.name))
                return out
            else:
                if isinstance(node, ast.Assign):
                    pylhs = node.targets[0]
                    lhsty = self._get_smt2_type(node.targets[0])
                    self.record_type(lhs, lhsty)
                else:
                    # AugAssign
                    pylhs = node.target
                    lhsty = self._get_smt2_type(node.target)

                self.record_type(lhs, lhsty)

                return SExprList(Symbol("="), lhs, rhs)

    def xlat_While(self, test, body, node):
        raise NotImplemented("Don't support While loops in SMT2 yet")

    def _get_imp2func_pipeline(self, name, body, entry_fn, dump_cfg = False):
        config = I2FConfig(linear = True, name_prefix = name,
                           dump_cfg = dump_cfg, debug = False)

        config.error_on_non_exit_nodes = True

        pm = PassManager(config)
        pm.ctx.typed_backend = True
        pm.ctx.types = self.lhs_types[name]
        pm.ctx.statements = body
        pm.ctx.entry_fn = entry_fn
        pm.globalvars = set(list(ROUND_MODES_SMT2.values()) +
                            ['roundNearestTiesToEven', '-oo', '+oo',
                             'NaN', 'nan', '+zero', '-zero',
                             'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u16',
                             'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u32',
                             'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u64'])

        pm.add(InitBackendPass('smt2'))
        pm.add(AnnotationsPass())
        pm.add(CFGBuilderPass())
        pm.add(CFGUnreachableNodesPass(action='exit')) # we shouldn't be producing unreachable nodes?
        pm.add(CFGIdentifyNonExitingPass())
        pm.add(CFGHandleNonExitingPass(action='exit')) # we don't generate non-exiting nodes either
        pm.add(CFGMergeBranchExitNodesPass())

        if dump_cfg: pm.add(CFGDumperPass(f'cfg-{name}-initial.dot'))

        # convert to SSA form
        pm.add(PhasePass('CONVERTING TO SSA'))
        assemble_convert_to_SSA(pm)
        if dump_cfg: pm.add(CFGDumperPass(f'cfg-{name}-after-ssa.dot'))

        pm.add(PhasePass('CONVERTING TO FUNCTIONAL'))
        pm.add(ConvertSSAToFunctionalPass())

        return pm

    def _check_arg_types(self, node):
        for a in node.args.args:
            aty = self.x2x._get_type(a._xir_type)
            if isinstance(aty, TyApp):
                # waiting for: https://matryoshka-project.github.io/wait2018/slides/WAIT-2018-Fontaine-SMT-LIB-TIP.pdf

                raise NotImplementedError(f"Don't support higher-order functions in SMT-LIB2")

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        self._retval_ty = retval

        use_create_dag = not self._use_imp2

        self._check_arg_types(node)

        if use_create_dag:
            dag = create_dag(body, _debug_trace = False)
            expr = eliminate_xir_attr_ref(dag)

            #TODO: this should be done elsewhere
            output = SExprList(Symbol("define-fun"),
                               Symbol(name),
                               SExprList(*params),
                               Symbol(retval),
                               expr)
        else:
            for pty in params:
                self.record_type(pty.v[0], pty.v[1])

            self.lhs_types[name]['_retval'] = set([retval])
            body.insert(0, SExprList(Symbol("param"), *[pty.v[0] for pty in params]))
            body[-1] = SExprList(Symbol("return"), body[-1])
            pm = self._get_imp2func_pipeline(name, body, lambda x, y, z: (Symbol(name), SExprList(*params), Symbol(retval)))
            assert pm.run_all(), f"Conversion to SMT2 failed!"
            output = pm.ctx.backend.get_output()

        self._use_imp2 = False

        return [f"; :begin {name}", output, f"; :end {name}"]

    def _gen_datatypes(self):
        out = []
        for t in self.gen_structs:
            ty = self.gen_structs[t]
            if isinstance(ty, RecordDecl):
                name = ty.name
                par = len(ty.generic_tyvars)

                ft = []
                for (f, t) in ty.fields_and_types:
                    if isinstance(t, TyVar):
                        ft.append(SExprList(Symbol(f), Symbol(t.name)))
                    else:
                        ft.append(SExprList(Symbol(f), self._get_smt2_type(t)))

                cons = SExprList(Symbol(f"mk-{name}"), *ft)

                if par > 0:
                    cons = SExprList(Symbol("par"),
                                     SExprList(*[Symbol(t.name) for t in ty.generic_tyvars]),
                                     SExprList(cons))

                decl = SExprList(Symbol("declare-datatypes"),
                                 SExprList(SExprList(Symbol(name), Decimal(par))),
                                 SExprList(cons))

                out.append(decl)

        return "\n".join([str(s) for s in out])

    def _gen_constants(self):
        out = []
        for s in self.x2x.tyenv.constants:
            tv = self.x2x.tyenv.constants[s]
            st = self._get_smt2_type(tv[0])
            v = smt2_literal(AC.value(tv[1]), str(st))

            out.append(f"(define-fun {s} () {st} {v})")

        return "\n".join(out)

    def write_output(self, output, translations, defns, ptx = True):
        def include_file(inc, outf):
            inc = self.x2x.INC.locate(inc)

            with open(inc, "r") as incl:
                print(f"; begin-include {inc}", file=outf)
                print(incl.read(), file=outf)
                print(f"; end-include {inc}", file=outf)

        try:
            with open(output, "w") as f:
                print("(set-logic QF_FPBV)", file=f) # need to support arrays too
                print(self._gen_datatypes(), file=f)
                print("; :begin global", file=f)

                if "Pair" not in self.gen_structs:
                    # legacy
                    print("(declare-datatypes ( (Pair 2) ) ( (par (T1 T2) ( (mk-pair (first T1) (second T2)) )) ) )", file=f)

                if "CCRegister" not in self.gen_structs:
                    # legacy
                    print("(declare-datatypes ( (CCRegister 1) ) ((par (T1) ((mk-ccreg (cf T1))))))", file=f)

                #TODO: get rid of below too
                print(textwrap.dedent("""\
                (define-sort u8 () (_ BitVec 8))
                (define-sort b1 () (_ BitVec 1))
                (define-sort carryflag () b1)
                (define-sort pred () (_ BitVec 1))

                (define-fun bool_to_pred ((x Bool)) pred (ite x #b1 #b0))
                (define-fun pred_to_bool ((x pred)) Bool (= x #b1))
                """), file=f)

                for sz in [16, 32, 64, 128]:
                    for prefix in ['b', 's', 'u']:
                        print(f"(define-sort {prefix}{sz} () (_ BitVec {sz}))", file=f)

                for dt in DATA_TYPES_LIST:
                    #(define-sort predpair () (Pair pred pred))
                    print(f"(define-sort {dt.name} () ({dt.sort_cons} {' '.join(dt.fieldtypes)}))", file=f)

                for sz in [32, 64]:
                    print(f"(define-sort f{sz} () Float{sz})", file=f)

                print(self._gen_constants(), file=f)

                if ptx: #TODO
                    include_file("ptx_utils.smt2", f)
                    include_file("lop3_lut.smt2", f)
                    include_file("readbyte_prmt.smt2", f)
                    include_file("machine_specific.smt2", f)

                print("; :end global", file=f)


                for t in translations:
                    for tl in t:
                        print(str(tl), file=f)

                    print("\n", file=f)
        except:
            os.unlink(output)
            raise

class RefReturnFixer(ast.NodeVisitor):
    """Change all Return statements for functions accepting a ref
       parameter to also return that parameter."""

    REF_TYPES = set(["ConditionCodeRegisterRef"])
    REF_ANNOTATIONS = set(['cc_reg_ref'])

    def visit_Return(self, node):
        self._returns.append(node)

    def _is_anno_ref(self, annotation):
        if annotation is not None and isinstance(annotation, ast.Name):
            return annotation.id in self.REF_ANNOTATIONS

    def visit_FunctionDef(self, node):
        for a in node.args.args:
            if self._is_anno_ref(a.annotation):
                self._ref_args.append(ast.Name(a.arg, ast.Load()))

        self.generic_visit(node)

    #def visit_AnnAssign(self, node):
    #    if node.simple == 1:
    #        if self._is_anno_ref(a.annotation):
    #            self._ref_args.append(a.target)

    # this is deprecated
    def visit_Assign(self, node):
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if isinstance(node.value, ast.Call):
                call = node.value
                if isinstance(call.func, ast.Name) and call.func.id == "set_sign_bitWidth":

                    if call.args[2].s in self.REF_TYPES:
                        self._ref_args.append(node.targets[0])


    def fix_returns(self, node):
        self._ref_args = []
        self._returns = []

        self.visit(node)

        if len(self._ref_args):
            for r in self._returns:
                r.value = ast.Tuple(elts=[r.value] + self._ref_args, ctx = ast.Load())

        return node

class BreakTarget(ast.NodeVisitor):
    """Add branch metadata to break statements"""

    def visit_While(self, node):
        self.loop_id += 1
        myid = self.loop_id
        self.loops.append(myid)
        self.breaks.append(False)
        self.generic_visit(node)

        self.loops.pop()
        has_break = self.breaks.pop()
        if has_break:
            node._xir_loop_id = myid

    def visit_Break(self, node):
        self.breaks[-1] = True
        node._xir_loop_id = self.loops[-1]

    def add_info(self, node):
        self.loop_id = 0
        self.breaks = []
        self.loops = []
        self.visit(node)

class IfExpRecognizer(ast.NodeVisitor):
    def visit_If(self, node):
        for s in [node.body, node.orelse]:
            if s is not None and len(s) == 1:
                if isinstance(s[0], ast.Assign):
                    # add to leaves
                    self._leaves.append(s[0])
                elif isinstance(s[0], ast.If):
                    return self.visit(s[0])
                # possibly handle pass as well
                else:
                    return False
            else:
                return False

        return True

    def _check_assigns(self, l):
        out = set()
        for a in l:
            if len(a.targets) == 1:
                if isinstance(a.targets[0], ast.Name):
                    out.add(a.targets[0].id)

        return len(out) == 1, out

    def visit_FunctionDef(self, node):
        for s in node.body:
            # support only top-level Ifs
            if isinstance(s, ast.If):
                self._leaves = []
                if self.visit(s):
                    assign_ok, assignment_to = self._check_assigns(self._leaves)
                    s._if_exp = (self.visit(s) and assign_ok, assignment_to.pop())

class IfToIfExp(ast.NodeTransformer):
    _in_if_exp = False

    def visit_Assign(self, node):
        if self._in_if_exp:
            return node.value

        return node

    def visit_If(self, node):
        toplevel = None
        if hasattr(node, '_if_exp') and node._if_exp[0]:
            toplevel = node._if_exp[1]
            self._in_if_exp = True

        if self._in_if_exp:
            test = node.test
            assert len(node.orelse) > 0, f"No else found when converting to IfExp: this means tests are not exhaustive for: {ast.dump(node)}"

            body = self.visit(node.body[0])
            orelse = self.visit(node.orelse[0])
            #print(ast.dump(test), "\n", ast.dump(body), "\n", ast.dump(orelse))
            node = ast.IfExp(test, body, orelse)
        else:
            node = self.generic_visit(node)

        if toplevel is not None:
            self._in_if_exp = False
            node = ast.Assign([ast.Name(id=toplevel, ctx=ast.Store())], node)

        return node

class ArrayFn(ast.NodeTransformer):
    """Transform functions that return arrays of constant size into
       assignments to individual elements

       e.g. extractAndZeroExt_4(x, num1) to
            num1[0] = extractAndZeroExt_4(x, 0)
            ...
            num1[3] = extractAndZeroExt_4(x, 3)
"""

    def visit_Expr(self, node):
        if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == self._array_fn:
            return self.visit(node.value)

        return node

    def visit_FunctionDef(self, node):
        self._converted = False
        self._arrays = set()
        node = self.generic_visit(node)

        if self._converted:
            # assists dearrayification
            out = []
            for v, sz in self._arrays:
                initializer = ast.List([AC.mk_constant(0)]*sz, ast.Load())
                node.body.insert(0, ast.Assign([ast.Name(v, ast.Store())], initializer))

        return node

    def visit_Call(self, node):
        if isinstance(node.func, ast.Name) and node.func.id == self._array_fn:
            self._converted = True

            out = []

            self._arrays.add((node.args[self._array_arg_idx].id, self._array_sz))

            for i in range(self._array_sz):
                call = copy.deepcopy(node)
                call.func.id = self._array_fn_rename
                call.args[self._array_arg_idx] = AC.mk_constant(i)

                out.append(ast.Assign([ast.Subscript(node.args[self._array_arg_idx],
                                                    ast.Index(AC.mk_constant(i)),
                                                    ast.Store())],
                                      call))

            return out

        return node

    def convert(self, node, array_fn, array_arg_idx, array_sz, array_fn_rename = None):
        self._array_fn = array_fn
        self._array_arg_idx = array_arg_idx
        self._array_sz = array_sz
        if array_fn_rename is None: array_fn_rename = array_fn
        self._array_fn_rename = array_fn_rename

        return self.visit(node)

class UnrollWhileLoop(ast.NodeTransformer):
    def visit_While(self, node):
        if not hasattr(node, '_xir_unroll_factor'):
            return node

        test = self.visit(node.test)
        body = [self.visit(s) for s in node.body]

        if len(node.orelse) > 0:
            raise NotImplementedError(f"Don't know how to unroll While loops with orelse {node.orelse}")

        unroll_factor = node._xir_unroll_factor
        unrolled = ast.If(test, body, [])
        orig = unrolled

        for i in range(unroll_factor - 1):
            body = unrolled.body
            body.append(copy.deepcopy(unrolled))
            unrolled = body[-1]

        if hasattr(node, '_xir_loop_id'):
            orig._xir_loop_id = node._xir_loop_id

        return orig

def dearrayify(s):
    # we need this here because we convert array functions to
    # non-array-functions.
    daf = xirpeval.Dearrayification()
    return daf.dearrayify(s)

def test_ArrayFn():
    import astunparse

    code = """
def test():
    extractAndZeroExt_4(x, num1)
"""

    i = ast.parse(code)
    t = ArrayFn()
    o = t.convert(i, 'extractAndZeroExt_4', 1, 4)

    print(astunparse.unparse(o))

def test_IfToIfExp():
    import astunparse

    code1 = """
def x():
    if ISNAN(src1):
        tmp_dst = src2
    elif ISNAN(src2):
        tmp_dst = src1
    else:
        tmp_dst = (src1 if GT(src1, src2) else src2)
    """

    code2 = """
def x():
    if ISNAN(src1):
        tmp_dst = src2
    """

    code3 = """
def x():
    if ISNAN(src1):
        tmp_dst = src2
    else:
        tmp_dst = src1
    """

    for c in [code1, code2, code3]:
        mod = ast.parse(c)
        v = IfExpRecognizer()
        v.visit(mod)

        t = IfToIfExp()
        mod2 = t.visit(mod)

        print(astunparse.unparse(mod2))

