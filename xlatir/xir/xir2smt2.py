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
import copy
import xirpeval
from collections import namedtuple
import imp2func_ssa

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

def generic_round(fn, nargs):
    if nargs == 1:
        return lambda x, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x)
    elif nargs == 2:
        return lambda x, y, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x, y)
    elif nargs == 3:
        return lambda x, y, z, m: SExprList(Symbol(fn), Symbol(ROUND_MODES_SMT2[m.v]), x, y, z)
    else:
        raise NotImplementedError(f"nargs={nargs} not implemented")

def truncate(width):
    return lambda x: SExprList(SExprList(Symbol('_'), Symbol('extract'),
                                         Decimal(width - 1), Decimal(0)), x)

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

def extract_cf(x):
    # actually do a proper type check?
    return SExprList(SExprList(Symbol("_"), Symbol("extract"), Decimal(0), Decimal(0)), x)

XIR_TO_SMT2_OPS = {('ADD', '*', '*'): lambda x, y: SExprList(Symbol("bvadd"), x, y),
                   ('ADD_CARRY', 'u16', 'u16', 'u16'): lambda x, y, z: SExprList(Symbol("ADD_CARRY_u16"), x, y, extract_cf(z)),
                   ('ADD_CARRY', 's16', 's16', 's16'): lambda x, y, z: SExprList(Symbol("ADD_CARRY_u16"), x, y, extract_cf(z)),

                   ('ADD_CARRY', 'u32', 'u32', 'u32'): lambda x, y, z: SExprList(Symbol("ADD_CARRY_u32"), x, y, extract_cf(z)),
                   ('ADD_CARRY', 's32', 's32', 's32'): lambda x, y, z: SExprList(Symbol("ADD_CARRY_u32"), x, y, extract_cf(z)), # it is always u32

                   ('ADD_CARRY', 'u64', 'u64', 'u64'): lambda x, y, z: SExprList(Symbol("ADD_CARRY_u64"), x, y, extract_cf(z)),
                   ('ADD_CARRY', 's64', 's64', 's64'): lambda x, y, z: SExprList(Symbol("ADD_CARRY_u64"), x, y, extract_cf(z)), # it is always u64


                   ('ADD', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.add"),
                                                                     Symbol("roundNearestTiesToEven"), # TODO
                                                                     x, y),
                   ('SUB', '*', '*'): lambda x, y: SExprList(Symbol("bvsub"), x, y),

                   ('SUB_CARRY', 'u32', 'u32', 'u32'): lambda x, y, z: SExprList(Symbol("SUB_CARRY_u32"), x, y, extract_cf(z)),
                   ('SUB_CARRY', 's32', 's32', 's32'): lambda x, y, z: SExprList(Symbol("SUB_CARRY_u32"), x, y, extract_cf(z)), # it is always u32

                   ('SUB_CARRY', 'u64', 'u64', 'u64'): lambda x, y, z: SExprList(Symbol("SUB_CARRY_u64"), x, y, extract_cf(z)),
                   ('SUB_CARRY', 's64', 's64', 's64'): lambda x, y, z: SExprList(Symbol("SUB_CARRY_u64"), x, y, extract_cf(z)), # it is always u64

                   ('SUB', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.sub"),
                                                                     Symbol("roundNearestTiesToEven"), # TODO
                                                                     x, y),

                   ('MUL', '*', '*'): lambda x, y: SExprList(Symbol("bvmul"), x, y),
                   ('MUL', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.mul"),
                                                                     Symbol("roundNearestTiesToEven"),
                                                                     x, y),

                   ('MUL24', 's32', 's32'): lambda x, y: SExprList(Symbol("MUL24_s32"), x, y),
                   ('MUL24', 'u32', 'u32'): lambda x, y: SExprList(Symbol("MUL24_u32"), x, y),

                   ('MULWIDE', 's16', 's16'): lambda x, y: SExprList(Symbol("MULWIDE_s16"), x, y),
                   ('MULWIDE', 'u16', 'u16'): lambda x, y: SExprList(Symbol("MULWIDE_u16"), x, y),

                   ('MULWIDE', 's32', 's32'): lambda x, y: SExprList(Symbol("MULWIDE_s32"), x, y),
                   ('MULWIDE', 'u32', 'u32'): lambda x, y: SExprList(Symbol("MULWIDE_u32"), x, y),

                   ('MULWIDE', 's64', 's64'): lambda x, y: SExprList(Symbol("MULWIDE_s64"), x, y),
                   ('MULWIDE', 'u64', 'u64'): lambda x, y: SExprList(Symbol("MULWIDE_u64"), x, y),

                   ('DIV', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvudiv"), x, y),
                   ('DIV', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvsdiv"), x, y),
                   ('DIV', 'float', 'float'): lambda x, y: SExprList(Symbol("fp.div"),
                                                                     Symbol("roundNearestTiesToEven"),
                                                                     x, y),
                   ('RCP_ROUND', 'f32', 'str'): lambda x, m: RCP('f32', x, m),
                   ('RCP_ROUND', 'f64', 'str'): lambda x, m: RCP('f64', x, m),
                   ('RCP', 'f32'): lambda x: RCP('f32', x, Symbol('rn')),

                   ('REM', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvurem"), x, y),
                   # TODO: investigate since this could be bvsmod and is machine-specific
                   ('REM', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvsrem"), x, y),

                   ("MACHINE_SPECIFIC_execute_rem_divide_by_neg", "signed", "signed"): lambda x, y: SExprList(Symbol("bvsrem"), x, SExprList(Symbol("bvneg"), y)), # this is probably the same as bvsrem?

                   ('SHR', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvlshr"), x, y),
                   ('SHR', 'signed', 'unsigned'): lambda x, y: SExprList(Symbol("bvashr"), x, y),

                   # to avoid casts
                   ('SHR', 'unsigned', 'signed'): lambda x, y: SExprList(Symbol("bvlshr"), x, y),
                   ('SHR', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvashr"), x, y),

                   ('SAR', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvashr"), x, y),
                   ('SAR', 'signed', 'unsigned'): lambda x, y: SExprList(Symbol("bvashr"), x, y),

                   # to avoid casts
                   ('SAR', 'unsigned', 'signed'): lambda x, y: SExprList(Symbol("bvashr"), x, y),
                   ('SAR', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvashr"), x, y),

                   ('SHL', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvshl"), x, y),
                   ('SHL', 'signed', 'unsigned'): lambda x, y: SExprList(Symbol("bvshl"), x, y),

                   # to avoid casts
                   ('SHL', 'unsigned', 'signed'): lambda x, y: SExprList(Symbol("bvshl"), x, y),
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

                   ('LOG2', 'f32'): lambda x: SExprList(Symbol("log2_f32"), x),
                   ('LOG2', 'f64'): lambda x: SExprList(Symbol("log2_f64"), x),

                   ('POW', 'f32', 'f32'): lambda x, y: SExprList(Symbol("pow_f32"), x, y),
                   ('POW', 'f64', 'f64'): lambda x, y: SExprList(Symbol("pow_f64"), x, y),

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
                   ('FMA_ROUND', '*', '*', '*', '*'): generic_round('fp.fma', 3),

                   ('SQRT_ROUND', 'f32', 'str'): generic_round('sqrt_round_f32', 1),
                   ('SQRT_ROUND', 'f64', 'str'): generic_round('sqrt_round_f64', 1),

                   ('SQRT', 'f32'): lambda x: SExprList(Symbol('sqrt_f32'), x),
                   ('SQRT', 'f64'): lambda x: SExprList(Symbol('sqrt_f64'), x),

                   ('SINE', 'f32'): lambda x: SExprList(Symbol('sin_f32'), x),
                   ('SINE', 'f64'): lambda x: SExprList(Symbol('sin_f64'), x),

                   ('COSINE', 'f32'): lambda x: SExprList(Symbol('cos_f32'), x),
                   ('COSINE', 'f64'): lambda x: SExprList(Symbol('cos_f64'), x),

                   # this mirrors machine-specific, but should probably outsource to smt2 file
                   ("MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned", "*"): lambda x: x,

                   ("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer", "u16"): lambda _: Symbol("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u16"),
                   ("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer", "u32"): lambda _: Symbol("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u32"),
                   ("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer", "u64"): lambda _: Symbol("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u64"),

                   # these still point to uX for convenience
                   ("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer", "s16"): lambda _: Symbol("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u16"),
                   ("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer", "s32"): lambda _: Symbol("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u32"),
                   ("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer", "s64"): lambda _: Symbol("MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u64"),

                   ("zext_64", 'b32'): lambda x: SExprList(SExprList(Symbol('_'),
                                                                     Symbol('zero_extend'),
                                                                     Decimal(32)), x),

                   ("sext_16", 'b16'): lambda x: x,
                   ("sext_16", 'u16'): lambda x: x,
                   ("sext_16", 's16'): lambda x: x,

                   ("sext_32", 'b32'): lambda x: x,
                   ("sext_32", 'u32'): lambda x: x,
                   ("sext_32", 's32'): lambda x: x,

                   ("sext_64", 'b64'): lambda x: x,
                   ("sext_64", 'u64'): lambda x: x,
                   ("sext_64", 's64'): lambda x: x,

                   ("truncate_16", '*'): truncate(16),
                   ("truncate_32", '*'): truncate(32),
                   ("truncate_64", '*'): truncate(64),
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

    POW = _do_fnop
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
    SQRT_ROUND = _do_fnop
    RCP = _do_fnop # approx
    LOG2 = _do_fnop
    SQRT = _do_fnop
    SINE = _do_fnop
    COSINE = _do_fnop
    MUL24 = _do_fnop
    MULWIDE = _do_fnop

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
    FMA_ROUND_SATURATE = _do_fnop_sat

    ADD_SATURATE = _do_fnop_sat
    SUB_SATURATE = _do_fnop_sat
    MUL_SATURATE = _do_fnop_sat
    DIV_SATURATE = _do_fnop_sat

    def subnormal_check(self, n, fnty, args, node):
        return bool_to_pred(SExprList(Symbol("fp.isSubnormal"), *args))

    def _do_SHIFT(self, n, fnty, args, node):
        assert fnty[1].v[0] in ('u', 'b', 's'), fnty[1].v[0]
        assert fnty[2].v[0] in ('u', 'b', 's'), fnty[2].v[0]

        width1 = int(fnty[1].v[1:])
        width2 = int(fnty[2].v[1:])

        if width1 == width2:
            return self._do_fnop_builtin(n, fnty, args, node)
        else:
            # PTX requires shift amount be a unsigned 32-bit value for
            # the shr/shl instructions. SMT2 requires that the shift
            # argument be the same type as first argument.

            if width1 > width2:
                # source argument bigger than shift, so enlarge shift
                args[1] = SExprList(SExprList(Symbol("_"), Symbol("zero_extend"),
                                              Decimal(width1-width2)), args[1])
            else:
                # source argument smaller than shift, so truncate shift
                args[1] = SExprList(SExprList(Symbol("_"), Symbol("extract"),
                                              Decimal(width1-1), Decimal(0)), args[1])

            return self._do_fnop_builtin(n, fnty, args, node)

    GTE = _do_fnop_builtin
    GT = _do_fnop_builtin
    LT = _do_fnop_builtin
    LTE = _nie
    EQ = _do_fnop_builtin
    NOTEQ = _do_fnop_builtin

    OR = _do_fnop_builtin
    AND = _do_fnop_builtin
    XOR = _do_fnop_builtin
    SHR = _do_SHIFT
    SHL = _do_SHIFT
    SAR = _do_SHIFT

    ADD = _do_fnop_builtin
    ADD_CARRY = _do_fnop
    SUB_CARRY = _do_fnop
    SUB = _do_fnop_builtin
    MUL = _do_fnop_builtin
    DIV = _do_fnop_builtin
    REM = _do_fnop_builtin

    zext_64 = _do_fnop
    truncate_16 = _do_fnop_builtin
    truncate_32 = _do_fnop_builtin
    truncate_64 = _do_fnop_builtin

    # TODO: check for use as a sign indicator and strip such uses (i.e. output width == input width)
    sext_16 = _do_fnop
    sext_32 = _do_fnop
    sext_64 = _do_fnop

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

    MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned = _do_fnop_builtin
    MACHINE_SPECIFIC_execute_rem_divide_by_neg = _do_fnop_builtin
    MACHINE_SPECIFIC_execute_div_divide_by_zero_integer = _do_fnop

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

    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor
        self.lib = SMT2lib()
        self._if_exp_recognizer = IfExpRecognizer()
        self._if_to_if_exp = IfToIfExp()
        self._array_fn = ArrayFn()
        self._ref_return_fixer = RefReturnFixer()
        self._tvndx = 0 # tmp variable suffixes

        self.lhs_types = {}

    def pre_xlat_transform(self, s):
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

        return s

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

        self.lhs_types[self.x2x.fn.name][str(var)] = ty

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
                self.record_type(lhs, self._get_smt2_type(node.targets[0]))
                return SExprList(Symbol("="), lhs, rhs)

    def xlat_While(self, test, body, node):
        raise NotImplemented("Don't support While loops in SMT2 yet")

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        self._retval_ty = retval

        use_create_dag = True

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
            #for s in body:
            #    print(s)

            self.lhs_types[name]['_retval'] = retval
            body[-1] = SExprList(Symbol("return"), body[-1])
            backend = imp2func_ssa.SMT2Output(self.lhs_types[name],
                                              entry_fn = lambda x, y, z: (Symbol(name), SExprList(*params), Symbol(retval)))
            glb = set(list(ROUND_MODES_SMT2.values()) + ['roundNearestTiesToEven', '-oo', '+oo',
                                                         'NaN', 'nan', '+zero', '-zero',
                                                         'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u16',
                                                         'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u32',
                                                         'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer_u64'])

            imp2func_ssa.convert_to_functional(body, glb, backend, linear = True, name_prefix = name)
            output = backend.get_output()

        return [f"; :begin {name}", output, f"; :end {name}"]

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
            (declare-datatypes (T1) ((CCRegister (mk-ccreg (cf T1)))))

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

            include_file("ptx_utils.smt2", f)
            include_file("lop3_lut.smt2", f)
            include_file("readbyte_prmt.smt2", f)
            include_file("machine_specific.smt2", f)

            print("; :end global", file=f)


            for t in translations:
                for tl in t:
                    print(str(tl), file=f)

                print("\n", file=f)

class RefReturnFixer(ast.NodeVisitor):
    """Change all Return statements for functions accepting a ref
       parameter to also return that parameter."""

    REF_TYPES = set(["ConditionCodeRegisterRef"])

    def visit_Return(self, node):
        self._returns.append(node)

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
                initializer = ast.List([ast.Num(0)]*sz, ast.Load())
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
                call.args[self._array_arg_idx] = ast.Num(i)

                out.append(ast.Assign([ast.Subscript(node.args[self._array_arg_idx],
                                                    ast.Index(ast.Num(i)),
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

