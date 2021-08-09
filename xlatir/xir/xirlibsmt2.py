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
    pass

class f64(SMT2Float):
    pass

class BV(SMT2BasicType):
    pass

class Signed(BV):
    pass

class Unsigned(BV):
    pass

class u8(Unsigned):
    pass

class u16(Unsigned):
    pass

class u32(Unsigned):
    pass

class u64(Unsigned):
    pass

class s8(Signed):
    pass

class s16(Signed):
    pass

class s32(Signed):
    pass

class s64(Signed):
    pass

class pred(SMT2BasicType):
    pass

SINGLETONS = {
    'float': f32(),
    'double': f64(),

    'u8': u8(),
    'u16': u16(),
    'u32': u32(),
    'u64': u64(),

    's8': s8(),
    's16': s16(),
    's32': s32(),
    's64': s64(),

    'pred': pred(),
}

def BinOp(name):
    return lambda x, y: SExprList(Symbol(name), x, y)

def FPBinOp(name, roundingmode):
    return lambda x, y: SExprList(Symbol(name), Symbol(roundingmode), x, y)


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


    @SUB.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("-")

    @singledispatchmethod
    def MUL(self, aty, bty):
        raise NotImplementedError(f"MUL({aty}, {bty}) not implemented.")

    @MUL.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("*")

    @singledispatchmethod
    def DIV(self, aty, bty):
        raise NotImplementedError(f"DIV({aty}, {bty}) not implemented.")

    @DIV.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("/")

    @singledispatchmethod
    def IDIV(self, aty, bty):
        raise NotImplementedError(f"IDIV({aty}, {bty}) not implemented.")

    @IDIV.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOpInfix("/")

    @singledispatchmethod
    def REM(self, aty, bty):
        raise NotImplementedError(f"REM({aty}, {bty}) not implemented.")

    @REM.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOpInfix("%")

    @singledispatchmethod
    def MOD(self, aty, bty):
        raise NotImplementedError(f"MOD({aty}, {bty}) not implemented.")

    @MOD.register(BV)
    def _(self, aty: BV, bty: BV):
        return BinOpInfix("%")

    @singledispatchmethod
    def SHR(self, aty, bty):
        raise NotImplementedError(f"SHR({aty}, {bty}) not implemented.")

    # TODO: why unsigned?
    @SHR.register(Unsigned)
    def _(self, aty: Unsigned, bty: u32):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, u32):
            return FnCall("SHR", 2)
        else:
            return BinOpInfix(">>")

    # this mimics the original dictionary, but makes little sense?
    @SHR.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix(">>")

    @singledispatchmethod
    def SHL(self, aty, bty):
        raise NotImplementedError(f"SHL({aty}, {bty}) not implemented.")

    @SHL.register(Unsigned)
    def _(self, aty: Unsigned, bty: u32):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, u32):
            return FnCall("SHL", 2)
        else:
            return BinOpInfix("<<")

    # this mimics the original dictionary, but makes little sense?
    @SHL.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("<<")

    @singledispatchmethod
    def GT(self, aty, bty):
        raise NotImplementedError(f"GT({aty}, {bty}) not implemented.")

    @GT.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix(">")

    @singledispatchmethod
    def LT(self, aty, bty):
        raise NotImplementedError(f"LT({aty}, {bty}) not implemented.")

    @LT.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("<")

    @singledispatchmethod
    def LTE(self, aty, bty):
        raise NotImplementedError(f"LTE({aty}, {bty}) not implemented.")

    @LTE.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("<=")

    @singledispatchmethod
    def NOTEQ(self, aty, bty):
        raise NotImplementedError(f"NOTEQ({aty}, {bty}) not implemented.")

    @NOTEQ.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("!=")

    @singledispatchmethod
    def GTE(self, aty, bty):
        raise NotImplementedError(f"GTE({aty}, {bty}) not implemented.")

    @GTE.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix(">=")

    @singledispatchmethod
    def EQ(self, aty, bty):
        raise NotImplementedError(f"EQ({aty}, {bty}) not implemented.")

    @EQ.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("==")

    @singledispatchmethod
    def OR(self, aty, bty):
        raise NotImplementedError(f"OR({aty}, {bty}) not implemented.")

    @OR.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("|")

    @singledispatchmethod
    def XOR(self, aty, bty):
        raise NotImplementedError(f"XOR({aty}, {bty}) not implemented.")

    @XOR.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("^")

    @singledispatchmethod
    def AND(self, aty, bty):
        raise NotImplementedError(f"AND({aty}, {bty}) not implemented.")

    @AND.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType, bty: SMT2BasicType):
        return BinOpInfix("&")

    @singledispatchmethod
    def NOT(self, aty):
        raise NotImplementedError(f"NOT({aty}) not implemented.")

    # order of registration doesn't matter?
    @NOT.register(pred)
    def _(self, aty: pred):
        return UnOpPrefix("!")

    @NOT.register(SMT2BasicType)
    def _(self, aty: SMT2BasicType):
        return UnOpPrefix("~")

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [self.type_dict[x] for x in fnty[1:]]

