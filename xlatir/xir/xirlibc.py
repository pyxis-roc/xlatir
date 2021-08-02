#!/usr/bin/env python3

from .xirlib import XIRBuiltinLib

try:
    from functools import singledispatchmethod # 3.8+
except ImportError:
    from singledispatchmethod import singledispatchmethod

class CType:
    pass

class CBasicType(CType):
    pass

class c_float(CBasicType):
    pass

class double(CBasicType):
    pass

class uint16_t(CBasicType):
    pass

class uint32_t(CBasicType):
    pass

class uint64_t(CBasicType):
    pass


class int16_t(CBasicType):
    pass

class int32_t(CBasicType):
    pass

class int64_t(CBasicType):
    pass


_SINGLETONS = {
    'float': c_float(),
    'double': double(),

    'uint16_t': uint16_t(),
    'uint32_t': uint32_t(),
    'uint64_t': uint64_t(),

    'int16_t': int16_t(),
    'int32_t': int32_t(),
    'int64_t': int64_t(),

}

class XIRBuiltinLibC(XIRBuiltinLib):
    @singledispatchmethod
    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD({aty}, {bty}) not implemented.")

    # 3.6/singledispatchmethod doesn't seem to read the type annotations on args?
    @ADD.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "+"


    @singledispatchmethod
    def SUB(self, aty, bty):
        raise NotImplementedError(f"SUB({aty}, {bty}) not implemented.")


    @singledispatchmethod
    def MUL(self, aty, bty):
        raise NotImplementedError(f"MUL({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def DIV(self, aty, bty):
        raise NotImplementedError(f"DIV({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def IDIV(self, aty, bty):
        raise NotImplementedError(f"IDIV({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def REM(self, aty, bty):
        raise NotImplementedError(f"REM({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def MOD(self, aty, bty):
        raise NotImplementedError(f"MOD({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def SHR(self, aty, bty):
        raise NotImplementedError(f"SHR({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def SHL(self, aty, bty):
        raise NotImplementedError(f"SHL({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def GT(self, aty, bty):
        raise NotImplementedError(f"GT({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def LT(self, aty, bty):
        raise NotImplementedError(f"LT({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def LTE(self, aty, bty):
        raise NotImplementedError(f"LTE({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def NOTEQ(self, aty, bty):
        raise NotImplementedError(f"NOTEQ({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def GTE(self, aty, bty):
        raise NotImplementedError(f"GTE({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def EQ(self, aty, bty):
        raise NotImplementedError(f"EQ({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def OR(self, aty, bty):
        raise NotImplementedError(f"OR({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def XOR(self, aty, bty):
        raise NotImplementedError(f"XOR({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def AND(self, aty, bty):
        raise NotImplementedError(f"AND({aty}, {bty}) not implemented.")

    @singledispatchmethod
    def NOT(self, aty):
        raise NotImplementedError(f"NOT({aty}) not implemented.")

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [_SINGLETONS[x] for x in fnty[1:]]

