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

class uint16_t(CUnsigned):
    pass

class uint32_t(CUnsigned):
    pass

class uint64_t(CUnsigned):
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

    'uint16_t': uint16_t(),
    'uint32_t': uint32_t(),
    'uint64_t': uint64_t(),

    'int16_t': int16_t(),
    'int32_t': int32_t(),
    'int64_t': int64_t(),

    'unsigned int': c_bool(), # TODO
    'BIT_T': CUnsigned(),
    'my_int128_t': CSigned(),
    'my_uint128_t': CSigned(),
}

class XIRBuiltinLibC(XIRBuiltinLib):
    type_dict = dict(SINGLETONS)

    @singledispatchmethod
    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD({aty}, {bty}) not implemented.")

    # 3.6/singledispatchmethod doesn't seem to read the type annotations on args?
    # 3.8 handles this fine
    @ADD.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "+"


    @singledispatchmethod
    def SUB(self, aty, bty):
        raise NotImplementedError(f"SUB({aty}, {bty}) not implemented.")


    @SUB.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "-"

    @singledispatchmethod
    def MUL(self, aty, bty):
        raise NotImplementedError(f"MUL({aty}, {bty}) not implemented.")

    @MUL.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "*"

    @singledispatchmethod
    def DIV(self, aty, bty):
        raise NotImplementedError(f"DIV({aty}, {bty}) not implemented.")

    @DIV.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "/"

    @singledispatchmethod
    def IDIV(self, aty, bty):
        raise NotImplementedError(f"IDIV({aty}, {bty}) not implemented.")

    @IDIV.register(CInteger)
    def _(self, aty: CInteger, bty: CInteger):
        return "/"

    @singledispatchmethod
    def REM(self, aty, bty):
        raise NotImplementedError(f"REM({aty}, {bty}) not implemented.")

    @REM.register(CInteger)
    def _(self, aty: CInteger, bty: CInteger):
        return "%"

    @singledispatchmethod
    def MOD(self, aty, bty):
        raise NotImplementedError(f"MOD({aty}, {bty}) not implemented.")

    @MOD.register(CInteger)
    def _(self, aty: CInteger, bty: CInteger):
        return "%"

    @singledispatchmethod
    def SHR(self, aty, bty):
        raise NotImplementedError(f"SHR({aty}, {bty}) not implemented.")

    @SHR.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return "SHR"
        else:
            return ">>"

    # this mimics the original dictionary, but makes little sense?
    @SHR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return ">>"

    @singledispatchmethod
    def SHL(self, aty, bty):
        raise NotImplementedError(f"SHL({aty}, {bty}) not implemented.")

    @SHL.register(CUnsigned)
    def _(self, aty: CUnsigned, bty: uint32_t):
        # dispatch on second argument doesn't quite mimic '*', '*'
        # TODO: eliminate >>?
        if isinstance(bty, uint32_t):
            return "SHL"
        else:
            return "<<"

    # this mimics the original dictionary, but makes little sense?
    @SHL.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "<<"

    @singledispatchmethod
    def GT(self, aty, bty):
        raise NotImplementedError(f"GT({aty}, {bty}) not implemented.")

    @GT.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return ">"

    @singledispatchmethod
    def LT(self, aty, bty):
        raise NotImplementedError(f"LT({aty}, {bty}) not implemented.")

    @LT.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "<"

    @singledispatchmethod
    def LTE(self, aty, bty):
        raise NotImplementedError(f"LTE({aty}, {bty}) not implemented.")

    @LTE.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "<="

    @singledispatchmethod
    def NOTEQ(self, aty, bty):
        raise NotImplementedError(f"NOTEQ({aty}, {bty}) not implemented.")

    @NOTEQ.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "!="

    @singledispatchmethod
    def GTE(self, aty, bty):
        raise NotImplementedError(f"GTE({aty}, {bty}) not implemented.")

    @GTE.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return ">="

    @singledispatchmethod
    def EQ(self, aty, bty):
        raise NotImplementedError(f"EQ({aty}, {bty}) not implemented.")

    @EQ.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "=="

    @singledispatchmethod
    def OR(self, aty, bty):
        raise NotImplementedError(f"OR({aty}, {bty}) not implemented.")

    @OR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "|"

    @singledispatchmethod
    def XOR(self, aty, bty):
        raise NotImplementedError(f"XOR({aty}, {bty}) not implemented.")

    @XOR.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "^"

    @singledispatchmethod
    def AND(self, aty, bty):
        raise NotImplementedError(f"AND({aty}, {bty}) not implemented.")

    @AND.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "&"

    @singledispatchmethod
    def NOT(self, aty):
        raise NotImplementedError(f"NOT({aty}) not implemented.")

    # order of registration doesn't matter?
    @NOT.register(c_bool)
    def _(self, aty: c_bool):
        return "!"

    @NOT.register(CBasicType)
    def _(self, aty: CBasicType):
        return "~"

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [self.type_dict[x] for x in fnty[1:]]

