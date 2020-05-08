#!/usr/bin/env python3
#
# smt2ast.py
#
# A simple, stand-alone SMT-LIBv2 AST for Python
#
# Author: Sreepathi Pai

class SExpr(object):
    pass

class Numeral(SExpr):
    def __init__(self, v):
        self.v = v

    def __str__(self):
        return str(self.v)

    __repr__ = __str__

class Decimal(SExpr):
    def __init__(self, v):
        self.v = v

    def __str__(self):
        return str(self.v)

    __repr__ = __str__

class Hexadecimal(SExpr):
    def __init__(self, v, width = 0):
        self.v = v
        self.width = width

    def __str__(self):
        if self.width > 0:
            return f"#x{self.v:0{self.width}x}"
        else:
            return f"#x{self.v:x}"

    __repr__ = __str__

class Binary(SExpr):
    def __init__(self, v, width = 0):
        self.v = v
        self.width = width

    def __str__(self):
        if self.width > 0:
            return f"#b{self.v:0{self.width}b}"
        else:
            return f"#b{self.v:b}"

    __repr__ = __str__

class String(SExpr):
    def __init__(self, v):
        self.v = v
        self._qv = v.replace('"', '""')

    def __str__(self):
        return f'"{self._qv}"'

    __repr__ = __str__

class Symbol(SExpr):
    def __init__(self, v):
        self.v = v

    def __str__(self):
        return f'{self.v}'

    __repr__ = __str__

class QuotedSymbol(SExpr):
    def __init__(self, v):
        self.v = v

    def __str__(self):
        return f'|{self.v}|'

    __repr__ = __str__

class Keyword(SExpr): # not exactly an atom
    def __init__(self, symbol):
        self.v = symbol

    def __str__(self):
        return f':{self.v}'

    __repr__ = __str__

class SExprList(SExpr):
    def __init__(self, *args):
        self.v = args

    def __str__(self):
        return f'({" ".join([str(e) for e in self.v])})'

    __repr__ = __str__

def smt2_literal(v, ty):
    if ty == 'pred':
        assert v == 1 or v == 0, f"Wrong value for pred: {v}"
        return Binary(v, 1)
    elif ty in ('u8', 'u16', 'u32', 'u64',
                's16', 's32', 's64',
                'b16', 'b32', 'b64'):
        signed = ty[0] == 's'
        width = int(ty[1:])

        if not signed:
            assert v >= 0, f"Unsigned types {ty} can't have negative values {v}"
        else:
            while v < 0:
                v += 2**width

        return Hexadecimal("{v:0{width//4}x}")
    elif ty in ('f32', 'f64'):
        xlat = {'f32': (1, 8, 23),
                'f64': (1, 11, 52)}

        # TODO: handle f16
        int_fmt_str = "I" if ty == 'f32' else 'Q'
        flt_fmt_str = "f" if ty == 'f32' else 'd'
        bit_fmt = xlat[ty]

        b = struct.unpack(f'{int_fmt_str}', struct.pack(f'{flt_fmt_str}', v))[0]

        s = 0
        out = []
        for w in reversed(bit_fmt):
            if w % 4 == 0:
                out.append(Hexadecimal((b & 2**w - 1), width = w//4))
            else:
                out.append(Binary(b & 2**w - 1, width = w))

            b >>= w

        return SExprList(Symbol("fp"), *reversed(out))
    else:
        raise NotImplementedError(f"Don't yet handle literals of type {ty}/{v}")
