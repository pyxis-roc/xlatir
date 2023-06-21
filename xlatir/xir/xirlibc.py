#!/usr/bin/env python3
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT
#
# SPDX-Contributor: Sreepathi Pai
#

from .xirlib import XIRBuiltinLib

try:
    from functools import singledispatchmethod # 3.8+
except ImportError:
    from singledispatchmethod import singledispatchmethod

class CType:
    pass

class CBasicType(CType):
    pass

class CFP(CBasicType):
    pass

class c_float(CFP):
    pass

class double(CFP):
    pass

class CInteger(CBasicType):
    pass

class CSigned(CInteger):
    pass

class CUnsigned(CInteger):
    pass

class uint8_t(CUnsigned):
    pass

class uint16_t(CUnsigned):
    pass

class uint32_t(CUnsigned):
    pass

class uint64_t(CUnsigned):
    pass


class int8_t(CSigned):
    pass

class int16_t(CSigned):
    pass

class int32_t(CSigned):
    pass

class int64_t(CSigned):
    pass

class c_bool(CBasicType):
    pass

# this needs to reflect XIR_TO_C_TYPES in xir2c.py

SINGLETONS = {
    'float': c_float(),
    'double': double(),

    'uint8_t': uint8_t(),
    'uint16_t': uint16_t(),
    'uint32_t': uint32_t(),
    'uint64_t': uint64_t(),

    'int8_t': int8_t(),
    'int16_t': int16_t(),
    'int32_t': int32_t(),
    'int64_t': int64_t(),

    'unsigned int': c_bool(), # TODO
    'BIT_T': CUnsigned(),
    'my_int128_t': CSigned(),
    'my_uint128_t': CSigned(),
}

def BinOpInfix(op):
    return lambda x, y: f"({x} {op} {y})"

def UnOpPrefix(op):
    return lambda x: f"{op}({x})"

def FnCall(fn, nargs):
    def cc(*args):
        assert len(args) == nargs, f"{fn}: Expecting {nargs} arguments, got {len(args)}"
        return f"{fn}({', '.join(args[:nargs])})"

    return cc

def CastOp(op):
    return lambda x: f"(({op}) {x})"

class XIRBuiltinLibC(XIRBuiltinLib):
    type_dict = dict(SINGLETONS)

    @singledispatchmethod
    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD({aty}, {bty}) not implemented.")

    # 3.6/singledispatchmethod doesn't seem to read the type annotations on args?
    # 3.8 handles this fine
    @ADD.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("+")


    @singledispatchmethod
    def SUB(self, aty, bty):
        raise NotImplementedError(f"SUB({aty}, {bty}) not implemented.")


    @SUB.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("-")

    @singledispatchmethod
    def MUL(self, aty, bty):
        raise NotImplementedError(f"MUL({aty}, {bty}) not implemented.")

    @MUL.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("*")

    @singledispatchmethod
    def DIV(self, aty, bty):
        raise NotImplementedError(f"DIV({aty}, {bty}) not implemented.")

    @DIV.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("/")

    @singledispatchmethod
    def IDIV(self, aty, bty):
        raise NotImplementedError(f"IDIV({aty}, {bty}) not implemented.")

    @IDIV.register(CInteger)
    def _(self, aty: CInteger, bty: CInteger):
        return BinOpInfix("/")

    @singledispatchmethod
    def REM(self, aty, bty):
        raise NotImplementedError(f"REM({aty}, {bty}) not implemented.")

    @REM.register(CInteger)
    def _(self, aty: CInteger, bty: CInteger):
        return BinOpInfix("%")

    @singledispatchmethod
    def MOD(self, aty, bty):
        raise NotImplementedError(f"MOD({aty}, {bty}) not implemented.")

    @MOD.register(CInteger)
    def _(self, aty: CInteger, bty: CInteger):
        return BinOpInfix("%")

    @singledispatchmethod
    def SHR(self, aty, bty):
        raise NotImplementedError(f"SHR({aty}, {bty}) not implemented.")

    # TODO: why unsigned?
    @SHR.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return FnCall("SHR", 2)
        else:
            return BinOpInfix(">>")

    # this mimics the original dictionary, but makes little sense?
    @SHR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix(">>")

    @singledispatchmethod
    def SHL(self, aty, bty):
        raise NotImplementedError(f"SHL({aty}, {bty}) not implemented.")

    @SHL.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return FnCall("SHL", 2)
        else:
            return BinOpInfix("<<")

    # this mimics the original dictionary, but makes little sense?
    @SHL.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("<<")

    @singledispatchmethod
    def GT(self, aty, bty):
        raise NotImplementedError(f"GT({aty}, {bty}) not implemented.")

    @GT.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix(">")

    @singledispatchmethod
    def LT(self, aty, bty):
        raise NotImplementedError(f"LT({aty}, {bty}) not implemented.")

    @LT.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("<")

    @singledispatchmethod
    def LTE(self, aty, bty):
        raise NotImplementedError(f"LTE({aty}, {bty}) not implemented.")

    @LTE.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("<=")

    @singledispatchmethod
    def NOTEQ(self, aty, bty):
        raise NotImplementedError(f"NOTEQ({aty}, {bty}) not implemented.")

    @NOTEQ.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("!=")

    @singledispatchmethod
    def GTE(self, aty, bty):
        raise NotImplementedError(f"GTE({aty}, {bty}) not implemented.")

    @GTE.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix(">=")

    @singledispatchmethod
    def EQ(self, aty, bty):
        raise NotImplementedError(f"EQ({aty}, {bty}) not implemented.")

    @EQ.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("==")

    @singledispatchmethod
    def OR(self, aty, bty):
        raise NotImplementedError(f"OR({aty}, {bty}) not implemented.")

    @OR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("|")

    @singledispatchmethod
    def XOR(self, aty, bty):
        raise NotImplementedError(f"XOR({aty}, {bty}) not implemented.")

    @XOR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("^")

    @singledispatchmethod
    def AND(self, aty, bty):
        raise NotImplementedError(f"AND({aty}, {bty}) not implemented.")

    @AND.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return BinOpInfix("&")

    @singledispatchmethod
    def NOT(self, aty):
        raise NotImplementedError(f"NOT({aty}) not implemented.")

    # order of registration doesn't matter?
    @NOT.register(c_bool)
    def _(self, aty: c_bool):
        return UnOpPrefix("!")

    @NOT.register(CBasicType)
    def _(self, aty: CBasicType):
        return UnOpPrefix("~")

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [self.type_dict[x] for x in fnty[1:]]

