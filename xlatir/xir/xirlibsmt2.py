#!/usr/bin/env python3

from .xirlib import XIRBuiltinLib
from xlatir.smt2ast import *

try:
    from functools import singledispatchmethod # 3.8+
except ImportError:
    from singledispatchmethod import singledispatchmethod

class SMT2Type:
    pass

class SMT2BasicType(SMT2Type): # i.e., not a C-like struct
    pass

class SMT2Float(SMT2BasicType):
    pass

class f32(SMT2Float):
    w = 32
    pass

class f64(SMT2Float):
    w = 64
    pass

class BV(SMT2BasicType):
    w = None
    pass

class Signed(BV):
    pass

class Unsigned(BV):
    pass

class b1(Unsigned):
    w = 1
    pass

class u8(Unsigned):
    w = 8
    pass

class u16(Unsigned):
    w = 16
    pass

class u32(Unsigned):
    w = 32
    pass

class u64(Unsigned):
    w = 64
    pass

class u128(Unsigned):
    w = 128
    pass

class s8(Signed):
    w = 8
    pass

class s16(Signed):
    w = 16
    pass

class s32(Signed):
    w = 32
    pass

class s64(Signed):
    w = 64
    pass

class s128(Signed):
    w = 128
    pass

class pred(SMT2BasicType):
    w = 1
    pass

SINGLETONS = {
    'f32': f32(),
    'f64': f64(),

    'u8': u8(),
    'u16': u16(),
    'u32': u32(),
    'u64': u64(),
    'u128': u128(),

    'b1': b1(),
    'b8': u8(),
    'b16': u16(),
    'b32': u32(),
    'b64': u64(),

    's8': s8(),
    's16': s16(),
    's32': s32(),
    's64': s64(),
    's128': s128(),

    'pred': pred(),
}

def bool_to_pred(x):
    return SExprList(Symbol("bool_to_pred"), x)

def pred_to_bool(x):
    return SExprList(Symbol("pred_to_bool"), x)

def BinOp(name):
    return lambda x, y: SExprList(Symbol(name), x, y)

def UnOp(name):
    return lambda x: SExprList(Symbol(name), x)

def FPBinOp(name, roundingmode):
    return lambda x, y: SExprList(Symbol(name), Symbol(roundingmode), x, y)

def BoolBinOp(name):
    fn = BinOp(name)
    return lambda x, y: bool_to_pred(fn(x, y))

def BoolNotBinOp(name):
    fn = BinOp(name)
    return lambda x, y: bool_to_pred(SExprList(Symbol("not"), fn(x, y)))

class XIRBuiltinLibSMT2(XIRBuiltinLib):
    type_dict = dict(SINGLETONS)

    @singledispatchmethod
    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD({aty}, {bty}) not implemented.")

    # 3.6/singledispatchmethod doesn't seem to read the type annotations on args?
    # 3.8 handles this fine
    @ADD.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOp("bvadd")

    @ADD.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return FPBinOp("fp.add", "roundNearestTiesToEven")

    @singledispatchmethod
    def SUB(self, aty, bty):
        raise NotImplementedError(f"SUB({aty}, {bty}) not implemented.")

    @SUB.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOp("bvsub")

    @SUB.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return FPBinOp("fp.sub", "roundNearestTiesToEven")

    @singledispatchmethod
    def MUL(self, aty, bty):
        raise NotImplementedError(f"MUL({aty}, {bty}) not implemented.")

    @MUL.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOp("bvmul")

    @MUL.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return FPBinOp("fp.mul", "roundNearestTiesToEven")

    @singledispatchmethod
    def DIV(self, aty, bty):
        raise NotImplementedError(f"DIV (or IDIV)({aty}, {bty}) not implemented.")

    @DIV.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BinOp("bvudiv")

    @DIV.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BinOp("bvsdiv")

    @DIV.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return FPBinOp("fp.div", "roundNearestTiesToEven")

    @singledispatchmethod
    def IDIV(self, aty, bty):
        raise NotImplementedError(f"IDIV({aty}, {bty}) not implemented.")

    @IDIV.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BinOp("bvudiv")

    @IDIV.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BinOp("bvsdiv")

    @singledispatchmethod
    def REM(self, aty, bty):
        raise NotImplementedError(f"REM({aty}, {bty}) not implemented.")

    @REM.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BinOp("bvurem")

    @REM.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BinOp("bvsrem")

    # TODO: investigate since this could be bvsmod and is machine-specific
    MOD = REM

    def _do_SHIFT(self, aty, bty, fn):
        assert isinstance(aty, BV)
        assert isinstance(bty, BV)

        width1 = aty.w
        width2 = bty.w

        if width1 == width2:
            return fn
        else:
            # PTX requires shift amount be a unsigned 32-bit value for
            # the shr/shl instructions. SMT2 requires that the shift
            # argument be the same type as first argument.

            if width1 > width2:
                # source argument bigger than shift, so enlarge shift
                a1 = lambda y: SExprList(SExprList(Symbol("_"), Symbol("zero_extend"),
                                              Decimal(width1-width2)), y)
            else:
                # source argument smaller than shift, so truncate shift
                a1 = lambda y: SExprList(SExprList(Symbol("_"), Symbol("extract"),
                                                   Decimal(width1-1), Decimal(0)), y)

            return lambda x, y: fn(x, a1(y))

    @singledispatchmethod
    def SHR(self, aty, bty):
        raise NotImplementedError(f"SHR({aty}, {bty}) not implemented.")

    @SHR.register(Unsigned)
    def _(self, aty: Unsigned, bty: BV):
        return self._do_SHIFT(aty, bty, BinOp("bvlshr"))

    @SHR.register(Signed)
    def _(self, aty: Signed, bty: BV):
        return self._do_SHIFT(aty, bty, BinOp("bvashr"))

    @singledispatchmethod
    def SHL(self, aty, bty):
        raise NotImplementedError(f"SHL({aty}, {bty}) not implemented.")

    @SHL.register(BV)
    def _(self, aty: BV, bty: BV):
        return self._do_SHIFT(aty, bty, BinOp("bvshl"))

    @singledispatchmethod
    def GT(self, aty, bty):
        raise NotImplementedError(f"GT({aty}, {bty}) not implemented.")

    @GT.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BoolBinOp("bvugt")

    @GT.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BoolBinOp("bvsgt")

    @GT.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BoolBinOp("fp.gt")

    @singledispatchmethod
    def LT(self, aty, bty):
        raise NotImplementedError(f"LT({aty}, {bty}) not implemented.")

    @LT.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BoolBinOp("bvult")

    @LT.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BoolBinOp("bvslt")

    @LT.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BoolBinOp("fp.lt")

    @singledispatchmethod
    def LTE(self, aty, bty):
        raise NotImplementedError(f"LTE({aty}, {bty}) not implemented.")

    @LTE.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BoolBinOp("bvule")

    @LTE.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BoolBinOp("bvsle")

    @LTE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BoolBinOp("fp.leq")

    @singledispatchmethod
    def NOTEQ(self, aty, bty):
        raise NotImplementedError(f"NOTEQ({aty}, {bty}) not implemented.")

    @NOTEQ.register(BV)
    def _(self, aty: BV, bty: BV):
        return BoolNotBinOp("=")

    @NOTEQ.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BoolNotBinOp("fp.eq") # TODO: not fp.eq is not exactly correct?

    @singledispatchmethod
    def GTE(self, aty, bty):
        raise NotImplementedError(f"GTE({aty}, {bty}) not implemented.")

    @GTE.register(Unsigned)
    def _(self, aty: Unsigned, bty: Unsigned):
        return BoolBinOp("bvuge")

    @GTE.register(Signed)
    def _(self, aty: Signed, bty: Signed):
        return BoolBinOp("bvsge")

    @GTE.register(SMT2Float)
    def _(self, aty: SMT2Float, bty: SMT2Float):
        return BoolBinOp("fp.geq")


    @singledispatchmethod
    def EQ(self, aty, bty):
        raise NotImplementedError(f"EQ({aty}, {bty}) not implemented.")

    @EQ.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BoolBinOp("=")

    @singledispatchmethod
    def OR(self, aty, bty):
        raise NotImplementedError(f"OR({aty}, {bty}) not implemented.")

    @OR.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOp("bvor")

    @OR.register(pred)
    def _(self, aty: pred, bty: pred):
        return BinOp("bvor")

    @singledispatchmethod
    def XOR(self, aty, bty):
        raise NotImplementedError(f"XOR({aty}, {bty}) not implemented.")

    @XOR.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOp("bvxor")

    @XOR.register(pred)
    def _(self, aty: pred, bty: pred):
        return BinOp("bvxor")

    @singledispatchmethod
    def AND(self, aty, bty):
        raise NotImplementedError(f"AND({aty}, {bty}) not implemented.")

    @AND.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOp("bvand")

    @AND.register(pred)
    def _(self, aty: pred, bty: pred):
        return BinOp("bvand")

    @singledispatchmethod
    def NOT(self, aty):
        raise NotImplementedError(f"NOT({aty}) not implemented.")

    # order of registration doesn't matter?
    @NOT.register(pred)
    def _(self, aty: pred):
        return UnOp("bvnot") # TODO

    @NOT.register(BV)
    def _(self, aty: BV):
        return UnOp("bvnot") # TODO

    def get_dispatch_types(self, fnty, xirty):
        # x is a Symbol
        return [fnty[0]] + [self.type_dict[str(x)] for x in fnty[1:]]

