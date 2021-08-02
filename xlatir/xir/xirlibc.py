#!/usr/bin/env python3

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


_SINGLETONS = {
    'float': c_float(),
    'double': double(),
    'uint16_t': uint16_t(),
}


class XIRLib:
    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD not implemented.")

    def get_dispatch_types(self, fnty, xirty):
        raise NotImplementedError

    def dispatch(self, fnty, xirty):
        fn = fnty[0]

        if not hasattr(self, fn):
            raise KeyError(f"Function {fn} not supported in XIRLib")

        dty = self.get_dispatch_types(fnty, xirty)

        assert hasattr(self, dty[0]), f"No method {dty[0]} in {self.__class__.__name__}"

        m = getattr(self, dty[0])
        print(m)
        return m(*dty[1:])

class XIRLibC(XIRLib):
    @singledispatchmethod
    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD({aty}, {bty}) not implemented.")

    # 3.6/singledispatchmethod doesn't seem to read the type annotations on args?
    @ADD.register(CBasicType)
    def _(self, aty: CBasicType, bty: CBasicType):
        return "+"

    def get_dispatch_types(self, fnty, xirty):
        return [fnty[0]] + [_SINGLETONS[x] for x in fnty[1:]]

