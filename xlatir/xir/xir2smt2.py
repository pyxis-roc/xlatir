#!/usr/bin/env python3
#
# xir2smt.py
#
# Translate XIR to SMT2
#
# Author: Sreepathi Pai

import ast
import xir
import xirxlat
from xirtyping import *
import textwrap
import os
import struct
from smt2ast import *

ROUND_MODES_SMT2 = {'rp': 'RTP', # positive inf
                    'rm': 'RTN', # negative inf
                    'rz': 'RTZ', # zero
                    'rn': 'RNE'} # nearest even, no support in PTX for RNA


def bool_to_pred(x):
    return SExprList(Symbol("bool_to_pred"), x)

def generic_round(fn, nargs):
    if nargs == 2:
        return lambda x, y, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x, y)
    elif nargs == 3:
        return lambda x, y, z, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x, y, z)
    else:
        raise NotImplementedError(f"nargs={nargs} not implemented")

def RCP(ty, x, rm = Symbol('rn')):
    if ty == 'f32':
        exp = 8
        signi = 24
    elif ty == 'f64':
        exp = 11
        signi = 53
    else:
        raise NotImplementedError(f"Unknown type for rcp {ty}")

    return SExprList(Symbol("fp.div"),
                     Symbol(ROUND_MODES_SMT2[rm.v]),
                     SExprList(SExprList(Symbol("_"), Symbol("to_fp"), Decimal(exp), Decimal(signi)),
                               Symbol(ROUND_MODES_SMT2['rn']),
                               Hexadecimal(1, width=(exp+signi)//4)),
                     x)


XIR_TO_SMT2_OPS = {('ADD', '*', '*'): lambda x, y: SExprList(Symbol("bvadd"), x, y),
                   ('ADD', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.add"),
                                                                     Symbol("roundNearestTiesToEven"), # TODO
                                                                     x, y),
                   ('SUB', '*', '*'): lambda x, y: SExprList(Symbol("bvsub"), x, y),
                   ('SUB', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.sub"),
                                                                     Symbol("roundNearestTiesToEven"), # TODO
                                                                     x, y),

                   ('MUL', '*', '*'): lambda x, y: SExprList(Symbol("bvmul"), x, y),
                   ('MUL', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.mul"),
                                                                     Symbol("roundNearestTiesToEven"),
                                                                     x, y),

                   ('DIV', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvudiv"), x, y),
                   ('DIV', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvsdiv"), x, y),
                   ('DIV', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.div"),
                                                                     Symbol("roundNearestTiesToEven"),
                                                                     x, y),
                   ('RCP_ROUND', 'f32', 'str'): lambda x, m: RCP('f32', x, m),
                   ('RCP_ROUND', 'f64', 'str'): lambda x, m: RCP('f64', x, m),
                   ('RCP', 'f32'): lambda x: RCP('f32', x, Symbol('rn')),

                   ('REM', '*', '*'): '%',

                   ('SHR', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvlshr"), x, y),
                   ('SHR', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvashr"), x, y),

                   ('SHL', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvshl"), x, y),
                   ('SHL', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvshl"), x, y),


                   ('GT', 'unsigned', 'unsigned'): lambda x, y: bool_to_pred(SExprList(Symbol('bvugt'), x, y)),
                   ('GT', 'signed', 'signed'): lambda x, y: bool_to_pred(SExprList(Symbol('bvsgt'), x, y)),
                   ('GT', 'float', 'float'): lambda x, y: bool_to_pred(SExprList(Symbol('fp.gt'), x, y)),

                   ('LT', 'unsigned', 'unsigned'): lambda x, y: bool_to_pred(SExprList(Symbol('bvult'), x, y)),
                   ('LT', 'signed', 'signed'): lambda x, y: bool_to_pred(SExprList(Symbol('bvslt'), x, y)),
                   ('LT', 'float', 'float'): lambda x, y: bool_to_pred(SExprList(Symbol('fp.lt'), x, y)),

                   ('NOTEQ', 'unsigned', 'unsigned'): lambda x, y: bool_to_pred(SExprList(Symbol("not"), SExprList("=", x, y))),
                   ('NOTEQ', 'signed', 'signed'): lambda x, y: bool_to_pred(SExprList(Symbol("not"), SExprList("=", x, y))),
                   ('NOTEQ', 'float', 'float'): lambda x, y: bool_to_pred(SExprList(Symbol("not"), SExprList("fp.eq", x, y))),


                   ('GTE', 'unsigned', 'unsigned'): lambda x, y: bool_to_pred(SExprList(Symbol('bvuge'), x, y)),
                   ('GTE', 'signed', 'signed'): lambda x, y: bool_to_pred(SExprList(Symbol('bvsge'), x, y)),
                   ('GTE', 'float', 'float'): lambda x, y: bool_to_pred(SExprList(Symbol('fp.geq'), x, y)),

                   ('EQ', '*', '*'): lambda x, y: bool_to_pred(SExprList(Symbol("="), x, y)),

                   ('MIN', 'float', 'float'): 'fminf',
                   ('MAX', 'float', 'float'): 'fmaxf',

                   ('FTZ', 'f32'): lambda x: SExprList(Symbol('FTZ_f32'), x),
                   ('FTZ', 'f64'): lambda x: SExprList(Symbol('FTZ_f64'), x),

                   ('MIN', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("ite"),
                                                                           SExprList(Symbol("bvult"), x, y), x, y),
                   ('MIN', 'signed', 'signed'): lambda x, y: SExprList(Symbol("ite"),
                                                                           SExprList(Symbol("bvslt"), x, y), x, y),
                   #('MIN', 'double', 'double'): 'fmin',
                   #('MAX', 'double', 'double'): 'fmax',
                   ('MAX', '*', '*'): 'MAX',

                   ('min', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("ite"),
                                                                           SExprList(Symbol("bvult"), x, y), x, y),
                   ('min', 'signed', 'signed'): lambda x, y: SExprList(Symbol("ite"),
                                                                           SExprList(Symbol("bvslt"), x, y), x, y),


                   ('AND', '*', '*'): lambda x, y: SExprList(Symbol('bvand'), x, y),
                   ('OR', '*', '*'): lambda x, y: SExprList(Symbol('bvor'), x, y),
                   ('XOR', '*', '*'): lambda x, y: SExprList(Symbol('bvxor'), x, y),
                   ('NOT', '*'): lambda x: SExprList(Symbol('bvnot'), x),

                   ('booleanOp_xor', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvxor"), x, y),
                   ('booleanOp_xor', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvxor"), x, y),

                   ('booleanOp_xor', 'pred', 'pred'): lambda x, y: SExprList(Symbol("bvxor"), x, y),

                   ('compare_eq', '*', '*'): lambda x, y: SExprList(Symbol('='), x, y),
                   ('compare_eq', 'float', 'float'): lambda x, y: SExprList(Symbol('fp.eq'), x, y),
                   ('compare_ne', '*', '*'): lambda x, y: SExprList(Symbol("not"),
                                                                    SExprList(Symbol('='), x, y)),
                   ('compare_ne', 'float', 'float'): lambda x, y: SExprList(Symbol("not"),
                                                                    SExprList(Symbol('fp.eq'), x, y)),

                   # the unordered versions use the same as below
                   ('compare_lt', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol('bvult'), x, y),
                   ('compare_lt', 'signed', 'signed'): lambda x, y: SExprList(Symbol('bvslt'), x, y),
                   ('compare_lt', 'float', 'float'): lambda x, y: SExprList(Symbol('fp.lt'), x, y),

                   ('compare_le', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol('bvule'), x, y),
                   ('compare_le', 'signed', 'signed'): lambda x, y: SExprList(Symbol('bvsle'), x, y),
                   ('compare_le', 'float', 'float'): lambda x, y: SExprList(Symbol('fp.leq'), x, y),

                   ('compare_gt', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol('bvugt'), x, y),
                   ('compare_gt', 'signed', 'signed'): lambda x, y: SExprList(Symbol('bvsgt'), x, y),
                   ('compare_gt', 'float', 'float'): lambda x, y: SExprList(Symbol('fp.gt'), x, y),

                   ('compare_ge', '*', '*'): '>=', # for signed and unsigned (see set)

                   ('compare_lo', 'uint32_t', 'uint32_t'): '<', # for unsigned (see set)
                   ('compare_ls', 'uint32_t', 'uint32_t'): '<=', # for unsigned (see set)
                   ('compare_hi', 'uint32_t', 'uint32_t'): '>', # for unsigned (see set)
                   ('compare_hs', 'uint32_t', 'uint32_t'): '>=', # for unsigned (see set)

                   ('compare_lo', 'uint16_t', 'uint16_t'): '<', # for unsigned (see set)
                   ('compare_ls', 'uint16_t', 'uint16_t'): '<=', # for unsigned (see set)
                   ('compare_hi', 'uint16_t', 'uint16_t'): '>', # for unsigned (see set)
                   ('compare_hs', 'uint16_t', 'uint16_t'): '>=', # for unsigned (see set)

                   ('compare_lo', 'uint64_t', 'uint64_t'): '<', # for unsigned (see set)
                   ('compare_ls', 'uint64_t', 'uint64_t'): '<=', # for unsigned (see set)
                   ('compare_hi', 'uint64_t', 'uint64_t'): '>', # for unsigned (see set)
                   ('compare_hs', 'uint64_t', 'uint64_t'): '>=', # for unsigned (see set)

                   ('compare_num', 'f32', 'f32'): '()', # for type checking only
                   ('compare_num', 'f64', 'f64'): '()',  # for type checking only

                   ('compare_nan', 'f32', 'f32'): '()', # for type checking only
                   ('compare_nan', 'f64', 'f64'): '()',  # for type checking only

                   ('POW', 'float', 'float'): 'powf',
                   ('POW', 'double', 'double'): 'pow',

                   ('set_memory', '*', '*'): 'set_memory',
                   ('logical_op3', 'uint32_t', 'uint32_t', 'uint32_t', 'uint8_t'): 'logical_op3',

                   ('ABSOLUTE', 's32'): lambda x: SExprList(Symbol('abs_s32'), x),
                   ('ABSOLUTE', 's64'): lambda x: SExprList(Symbol('abs_s64'), x),
                   ('ABSOLUTE', 's16'): lambda x: SExprList(Symbol('abs_s16'), x),

                   ('ABSOLUTE', 'f32'): lambda x: SExprList(Symbol("fp.abs"), x),
                   ('ABSOLUTE', 'f64'): lambda x: SExprList(Symbol("fp.abs"), x),

                   ('ROUND', '*'): lambda x: x, # TODO
                   ('ADD_SATURATE', 's32', 's32'): lambda x, y: SExprList(Symbol('ADD_SATURATE_s32'),
                                                                          x, y),
                   ('SUB_SATURATE', 's32', 's32'): lambda x, y: SExprList(Symbol('SUB_SATURATE_s32'),
                                                                          x, y),

                   ('SATURATE', 'f32'): lambda x: SExprList(Symbol('SATURATE_f32'), x),
                   ('SATURATE', 'f64'): lambda x: SExprList(Symbol('SATURATE_f64'), x),

                   ('ADD_ROUND', '*', '*', '*'): generic_round('fp.add', 2),
                   ('SUB_ROUND', '*', '*', '*'): generic_round('fp.sub', 2),
                   ('MUL_ROUND', '*', '*', '*'): generic_round('fp.mul', 2),
                   ('DIV_ROUND', '*', '*', '*'): generic_round('fp.div', 2),
                   ('FMA_ROUND', '*', '*', '*', '*'): generic_round('fp.fma', 3)
}

class SMT2lib(object):
    def _normalize_types(self, ty, builtin = True):
        if builtin:
            if ty.v[0] == "b" or ty.v[0] == "u":
                return "unsigned"
            elif ty.v[0] == "s":
                return "signed"
            elif ty.v[0] == "f":
                return "float"

        return str(ty)

    def _get_op(self, fnty, generic = False, builtin = True):
        fnty2 = tuple([fnty[0]] + [self._normalize_types(ty,
                                                         builtin = builtin)
                                   for ty in fnty[1:]])

        if fnty2 not in XIR_TO_SMT2_OPS and generic:
            fnty2 = tuple([fnty[0]] + ['*'] * (len(fnty)-1))

        assert fnty2 in XIR_TO_SMT2_OPS, f"{fnty} [{fnty2}] not in XIR_TO_SMT2_OPS"
        return XIR_TO_SMT2_OPS[fnty2]

    def _nie(self, *args, **kwargs):
        raise NotImplementedError(args[0])

    def _do_fnop_builtin(self, n, fnty, args, node):
        """For functions that are built-in to a logic [i.e. they are generic]"""
        arglen = len(fnty) - 1
        op = self._get_op(fnty, generic = True)
        return op(*args[:arglen])

    def _do_fnop(self, n, fnty, args, node):
        """For functions that are user-defined and don't have generic capabilities"""

        arglen = len(fnty) - 1
        op = self._get_op(fnty, builtin = False)
        return op(*args[:arglen])

    POW = _nie
    MIN = _do_fnop_builtin
    MAX = _nie
    set_memory = _nie
    FTZ = _do_fnop
    #logical_op3 = _nie
    min = _do_fnop_builtin
    ABSOLUTE = _do_fnop
    ROUND = _do_fnop_builtin # should be _do_fnop after implementation
    SATURATE = _do_fnop
    NOT = _do_fnop_builtin
    booleanOp_xor = _do_fnop_builtin

    ADD_ROUND = _do_fnop_builtin
    SUB_ROUND = _do_fnop_builtin
    MUL_ROUND = _do_fnop_builtin
    DIV_ROUND = _do_fnop_builtin
    FMA_ROUND = _do_fnop_builtin
    RCP_ROUND = _do_fnop # because we want different routines for f32/f64 even though fp.div is builtin
    RCP = _do_fnop # approx

    def _do_fnop_sat(self, n, fnty, args, node):
        if fnty[1].v == 's32':
            return self._do_fnop(n, fnty, args, node)
        else:
            wosat = n[:-len("_SATURATE")]
            assert hasattr(self, wosat), f"Unable to find non-saturating {wosat} version of {n}"
            wosat_fnty = tuple([wosat] + list(fnty[1:]))
            wosatcode = getattr(self, wosat)(wosat, wosat_fnty, args, node)

            sat_fnty = ('SATURATE', fnty[1])

            # pass none since we don't really have a saturate node (but maybe we should?)
            return self.SATURATE('SATURATE', sat_fnty, [wosatcode], None)

    ADD_ROUND_SATURATE = _do_fnop_sat
    SUB_ROUND_SATURATE = _do_fnop_sat
    MUL_ROUND_SATURATE = _do_fnop_sat
    DIV_ROUND_SATURATE = _do_fnop_sat

    ADD_SATURATE = _do_fnop_sat
    SUB_SATURATE = _do_fnop_sat
    MUL_SATURATE = _do_fnop_sat
    DIV_SATURATE = _do_fnop_sat

    def subnormal_check(self, n, fnty, args, node):
        return bool_to_pred(SExprList(Symbol("fp.isSubnormal"), *args))

    GTE = _do_fnop_builtin
    GT = _do_fnop_builtin
    LT = _do_fnop_builtin
    LTE = _nie
    EQ = _do_fnop_builtin
    NOTEQ = _do_fnop_builtin

    OR = _do_fnop_builtin
    AND = _do_fnop_builtin
    XOR = _do_fnop_builtin
    SHR = _do_fnop_builtin
    SHL = _do_fnop_builtin

    ADD = _do_fnop_builtin
    SUB = _do_fnop_builtin
    MUL = _do_fnop_builtin
    DIV = _do_fnop_builtin


    def ISNAN(self, n, fnty, args, mode):
        #TODO: check types
        return bool_to_pred(SExprList(Symbol("fp.isNaN"), *args))

    def _do_compare_unordered(self, n, fnty, args, node):
        assert n[-1] == 'u' # unordered
        n = n[:-1]

        fnty2 = (n, fnty[1], fnty[2])
        x = getattr(self, n)(n, fnty2, args, node)

        if is_call(x, "bool_to_pred"):
            x = x.v[1]

        a1 = args[0]
        a2 = args[1]

        return bool_to_pred(SExprList(Symbol("or"),
                                      SExprList(Symbol("fp.isNaN"), a1),
                                      SExprList(Symbol("fp.isNaN"), a2),
                                      x))

    compare_equ = _do_compare_unordered
    compare_neu = _do_compare_unordered
    compare_ltu = _do_compare_unordered
    compare_leu = _do_compare_unordered
    compare_gtu = _do_compare_unordered
    compare_geu = _do_compare_unordered

    def _do_compare(self, n, fnty, args, node):
        op = self._get_op(fnty, generic=True)

        return bool_to_pred(op(args[0], args[1]))

    def _do_compare_2(self, n, fnty, args, node):
        fnty2 = tuple([fnty[0]] + [self._normalize_types(ty) for ty in fnty[1:]])

        op = n[-2:]
        if op in ('lt', 'le', 'gt', 'ge'):
            assert fnty[1].v == fnty[2].v, f"Incorrect type signature for compare {fnty}"
            if fnty2[1] == "unsigned":
                op = "bvu" + op
            elif fnty2[1] == "signed":
                op = "bvs" + op
            elif fnty2[1] == "float":
                op = "fp." + op
                if op[-1] == "e": op += "q" # le -> leq, ge -> geq
        elif op in ('lo', 'ls', 'hi', 'hs'):
            xlat = {'lo': 'lt', 'ls': 'le', 'hi': 'gt', 'hs': 'ge'}
            op = "bvu" + xlat[op]
        else:
            raise NotImplementedError(f"Unknown comparison operator {op}")

        return bool_to_pred(SExprList(Symbol(op), args[0], args[1]))

    compare_eq = _do_compare
    compare_ne = _do_compare
    compare_lt = _do_compare_2
    compare_le = _do_compare_2
    compare_gt = _do_compare_2
    compare_ge = _do_compare_2
    compare_lo = _do_compare_2
    compare_ls = _do_compare_2
    compare_hi = _do_compare_2
    compare_hs = _do_compare_2

    def compare_nan(self, n, fnty, args, node):
        assert (n, fnty[1].v, fnty[2].v) in XIR_TO_SMT2_OPS, f"Incorrect type for {n} {fnty}"

        return bool_to_pred(SExprList(Symbol("or"),
                                      SExprList(Symbol("fp.isNaN"), args[0]),
                                      SExprList(Symbol("fp.isNaN"), args[1])))

    def compare_num(self, n, fnty, args, node):
        assert (n, fnty[1].v, fnty[2].v) in XIR_TO_SMT2_OPS, f"Incorrect type for {n} {fnty}"

        return bool_to_pred(SExprList(Symbol("not"),
                                      SExprList(Symbol("or"),
                                                SExprList(Symbol("fp.isNaN"), args[0]),
                                                SExprList(Symbol("fp.isNaN"), args[1]))))

def is_call(sexpr, func):
    return isinstance(sexpr, SExprList) and isinstance(sexpr.v[0], Symbol) and (sexpr.v[0].v == func)

def create_dag(statements):
    # value numbering
    expr = {}
    values = {}
    def get_key(st):
        if isinstance(st, SExprList):
            return tuple([get_key(v) for v in st.v])
        elif isinstance(st, (Symbol, Numeral, Decimal, Hexadecimal, Binary)):
            k = str(st)
            if k not in expr:
                expr[k] = len(expr) + 1
                values[len(expr)] = st

            return expr[k]
        else:
            raise NotImplementedError(f"create_dag: Not implemented yet: {st}/{type(st)}")

    def reconstitute(k):
        if isinstance(k, tuple):
            return SExprList(*[reconstitute(v) for v in k])
        else:
            return values[k]


    # first, assign value numbers to the statements in the array
    out = []
    for s in statements:
        if is_call(s, "="):
            # treat assignment specially
            k = get_key(s.v[2])
            expr[str(s.v[1])] = k
            if k in values:
                if not isinstance(values[k], Symbol):
                    assert values[k].v == s.v[2].v, f"Two different constants have the same key {values[k]} and {s.v[2]}"
                else:
                    # values[k] is a Symbol, but RHS is not, so set it to a constant
                    if not isinstance(s.v[2], Symbol):
                        values[k] = s.v[2].v
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

    #print(expr)
    #print(values)
    r = reconstitute(retval)
    #print(r)
    return r

class SMT2Xlator(xirxlat.Xlator):
    desugar_boolean_xor = False

    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor
        self.lib = SMT2lib()
        self._if_exp_recognizer = IfExpRecognizer()
        self._if_to_if_exp = IfToIfExp()

    def pre_xlat_transform(self, s):
        self._if_exp_recognizer.visit(s)
        s = self._if_to_if_exp.visit(s)
        return s

    def _get_smt2_type(self, node, declname = None):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        t = xir.find(ty, self.x2x.types)

        if isinstance(t, TyPtr):
            pt = self._get_c_type(t.pty)
            return f"{pt} *"

        if isinstance(t, TyApp):
            arg_types = [self._get_smt2_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for fn ptrs"
            return f"{self._get_c_type(t.ret)} (*{declname})({', '.join(arg_types)})"

        if isinstance(t, TyProduct):
            #NOTE: this won't handle function pointers as return values
            elt_types = [self._get_smt2_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for product types"
            elt_names = [f"(out{k} {ty})" for k, ty in enumerate(elt_types)]
            assert elt_types[0].v == "pred" and elt_types[1].v == "pred"
            return Symbol("predpair")

        if not isinstance(t, TyConstant):
            if isinstance(t, TyVarLiteral):
                return Symbol('literal_type')

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

    def xlat_Name(self, name: str, node):
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
        return f'{value}.{attr}'

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

    def xlat_If(self, test, body, orelse, node):
        raise NotImplemented("Don't support If loops in SMT2 yet")

    def xlat_Break(self, node):
        raise NotImplemented("Don't support Break loops in SMT2 yet")

    def xlat_float_val(self, v):
        if v == 'inf':
            return "INFINITY" # since C99
        elif v == '-inf':
            return "-INFINITY" # since C99
        elif v == 'nan':
            return "NAN" # since C99, but could also use nan()?
        elif v == '-nan':
            return "-NAN"
        elif v == '-0.0' or v == '0.0':
            return v
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
        arglen = len(fnty) - 1
        return SExprList(Symbol(fn), *args[:arglen])

    def xlat_Return(self, v, vty, node):
        if isinstance(v, list):
            return SExprList(Symbol("mk-pair"), *v)
        else:
            return v

    def xlat_Assign(self, lhs, rhs, node):
        return SExprList(Symbol("="), lhs, rhs)

    def xlat_While(self, test, body, node):
        raise NotImplemented("Don't support While loops in SMT2 yet")

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        self._retval_ty = retval

        expr = create_dag(body)

        #TODO: this should be done elsewhere
        output = SExprList(Symbol("define-fun"),
                           Symbol(name),
                           SExprList(*params),
                           Symbol(retval),
                           expr)

        return output

    def write_output(self, output, translations, defns):
        def include_file(inc, outf):
            with open(os.path.join(os.path.dirname(__file__), inc), "r") as incl:
                print(f"; begin-include {inc}", file=outf)
                print(incl.read(), file=outf)
                print(f"; end-include {inc}", file=outf)

        with open(output, "w") as f:
            print("(set-logic QF_FPBV)", file=f) # need to support arrays too

            print(textwrap.dedent("""\
            ; :begin global
            (declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))
            (define-sort u8 () (_ BitVec 8))
            (define-sort pred () (_ BitVec 1))

            (define-fun bool_to_pred ((x Bool)) pred (ite x #b1 #b0))
            (define-fun pred_to_bool ((x pred)) Bool (= x #b1))
            (define-sort predpair () (Pair pred pred))
            """), file=f)

            for sz in [16, 32, 64]:
                for prefix in ['b', 's', 'u']:
                    print(f"(define-sort {prefix}{sz} () (_ BitVec {sz}))", file=f)

            for sz in [32, 64]:
                print(f"(define-sort f{sz} () Float{sz})", file=f)

            include_file("ptx_utils.smt2", f)
            include_file("lop3_lut.smt2", f)

            print("; :end global", file=f)


            for t in translations:
                if is_call(t, "define-fun"):
                    print(f"; :begin {t.v[1]}", file=f)

                print(str(t), file=f)

                if is_call(t, "define-fun"):
                    print(f"; :end {t.v[1]}", file=f)

                print("\n", file=f)

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

