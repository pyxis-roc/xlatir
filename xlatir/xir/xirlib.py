#
# xirlib.py
#
# Provides compiler support for user-defined libraries that are needed
# to compile function calls in XIR code to the backend.
#
#
# To develop a new user-defined library, create a subclass of XIRLib
# that will form the abstract base class for that library. Then,
# instantiate it for each backend.
#

class XIRLib:
    """Generic library implementation.

       This is used by a user-defined library to specialize functions
       based on the types of arguments.
    """
    unsupported = set()

    def tychk(self, v, type_):
        if not isinstance(v, type_):
            raise TypeError(f"Expecting type {type_}, found {type(v)}")

    def get_dispatch_types(self, fnty, xirty):
        raise NotImplementedError

    def dispatch(self, fnty, xirty):
        fn = fnty[0]

        if not hasattr(self, fn):
            raise KeyError(f"Function {fn} not supported in {self.__class__.__name__}")

        try:
            dty = self.get_dispatch_types(fnty, xirty)
        except KeyError as e:
            assert False, f"Type {e} not found in {fnty} when getting dispatch types"

        assert hasattr(self, dty[0]), f"No method {dty[0]} in {self.__class__.__name__}"

        m = getattr(self, dty[0])
        return m(*dty[1:])


class MultilibDispatcher:
    def __init__(self):
        self.xlib = []

    def add_lib(self, lib):
        lib.parent = self
        self.xlib.append(lib)

    def can_xlat(self, n):
        for lib in self.xlib:
            if hasattr(lib, n) and not (n in lib.unsupported): return True

        return False

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

    def get_builtin(self):
        raise NotImplementedError


class XIRBuiltinLib(XIRLib):
    """Abstract base class for the XIR Builtin Library."""

    unsupported = frozenset()

    def ADD(self, aty, bty):
        raise NotImplementedError(f"ADD not implemented.")

    def SUB(self, aty, bty):
        raise NotImplementedError(f"SUB not implemented.")

    def DIV(self, aty, bty):
        raise NotImplementedError(f"DIV not implemented.")

    def IDIV(self, aty, bty):
        raise NotImplementedError(f"IDIV not implemented.")

    def MOD(self, aty, bty):
        raise NotImplementedError(f"MOD not implemented.")

    def POW(self, aty, bty):
        raise NotImplementedError(f"POW not implemented.")


    def SHL(self, aty, bty):
        raise NotImplementedError(f"SHL not implemented.")

    def SHR(self, aty, bty):
        raise NotImplementedError(f"SHR not implemented.")


    def OR(self, aty, bty):
        raise NotImplementedError(f"OR not implemented.")

    def XOR(self, aty, bty):
        raise NotImplementedError(f"XOR not implemented.")

    def AND(self, aty, bty):
        raise NotImplementedError(f"AND not implemented.")

    def NOT(self, aty):
        raise NotImplementedError(f"NOT not implemented.")


    def EQ(self, aty):
        raise NotImplementedError(f"EQ not implemented.")

    def NOTEQ(self, aty):
        raise NotImplementedError(f"NOTEQ not implemented.")

    def LT(self, aty):
        raise NotImplementedError(f"LT not implemented.")

    def LTE(self, aty):
        raise NotImplementedError(f"LTE not implemented.")

    def GT(self, aty):
        raise NotImplementedError(f"GT not implemented.")

    def GTE(self, aty):
        raise NotImplementedError(f"GTE not implemented.")


    def abs(self, aty):
        raise NotImplementedError(f"abs not implemented.")

    def bool(self, aty):
        raise NotImplementedError(f"bool not implemented.")


    # TODO: return type?
    def MUL(self, aty, bty):
        raise NotImplementedError(f"MUL not implemented.")
