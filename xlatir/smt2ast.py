#!/usr/bin/env python3
#
# smt2ast.py
#
# A simple, stand-alone SMT-LIBv2 AST for Python
#
# Author: Sreepathi Pai
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT

import struct # for smt2_literal
import re # for parser

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

def shortest_bv(value, width):
    if width % 4 == 0:
        return Hexadecimal(value, width // 4)
    else:
        return Binary(value, width)

class String(SExpr):
    def __init__(self, v):
        self.v = v
        self._qv = v.replace('"', '""')

    def __str__(self):
        return f'"{self._qv}"'

    __repr__ = __str__

class Comment(SExpr):
    def __init__(self, v):
        self.v = v
        assert v[-1] in ('\n', '\r'), f"Comment must include line break"

    def __str__(self):
        return f'; {self.v}'

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
        self.v = list(args)

    def __str__(self):
        return f'({" ".join([str(e) for e in self.v])})'

    __repr__ = __str__

def is_call(sexpr, func):
    return isinstance(sexpr, SExprList) and (len(sexpr.v) > 0 and isinstance(sexpr.v[0], Symbol) and (sexpr.v[0].v == func))

def smt2_literal(v, ty, fp_as_bv=False):
    #TODO: remove all PTX-specific literals or accept a custom transformations
    if ty == 'pred':
        assert not isinstance(v, bool) and (v == 1 or v == 0), f"Wrong value for pred: {v}"
        return Binary(v, 1)
    elif ty == 'cc_reg':
        assert not isinstance(v, bool) and (v == 1 or v == 0), f"Wrong value for cc_reg: {v}"
        return SExprList(Symbol("mk-ccreg"), Binary(v, 1))
    elif ty == 'carryflag':
        assert not isinstance(v, bool) and (v == 1 or v == 0), f"Wrong value for carryflag: {v}"
        return Binary(v, 1)
    elif ty in ('u8', 'u16', 'u32', 'u64', 'u128',
                's16', 's32', 's64', 's128',
                'b16', 'b32', 'b64', 'b1'):
        signed = ty[0] == 's'
        width = int(ty[1:])

        if not signed:
            assert v >= 0, f"Unsigned types {ty} can't have negative values {v}"
        else:
            while v < 0:
                v += 2**width

        return shortest_bv(v, width)
    elif ty in ('f32', 'f64'):
        xlat = {'f32': (1, 8, 23),
                'f64': (1, 11, 52)}

        # TODO: handle f16
        int_fmt_str = "I" if ty == 'f32' else 'Q'
        flt_fmt_str = "f" if ty == 'f32' else 'd'
        bit_fmt = xlat[ty]

        b = struct.unpack(f'{int_fmt_str}', struct.pack(f'{flt_fmt_str}', v))[0]

        if fp_as_bv:
            return Hexadecimal(b, 8 if ty == "f32" else 16)
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

def from_smt2_literal(value, ty):
    if not isinstance(value, SExprList):
        if ty[0] == "s":
            #TODO: does not seem possible to get this from smt2
            w = int(ty[1:])
            t = 2 ** (w - 1) - 1
            if value.v > t:
                value.v = -(2**w - value.v)

            return value.v
        else:
            return value.v # this is the value

    if is_call(value, "mk-pair"):
        return (from_smt2_literal(value.v[1], ty[0]), from_smt2_literal(value.v[2], ty[1]))

    if is_call(value, "mk-ccreg"):
        return from_smt2_literal(value.v[1], "b1")

    if is_call(value, "mkTuple"):
        return tuple([from_smt2_literal(v, t) for v, t in zip(value.v[1:], ty)])

    if len(value.v) and isinstance(value.v[0], SExprList) and is_call(value.v[0], "as"):
        # TODO: rewrite as a constructor ...
        cons = value.v[1]
        values = []
        if isinstance(ty, (list, tuple)): # TODO: examine 'as' to determine how to deal with arguments
            for v, t in zip(value.v[1:], ty):
                values.append(from_smt2_literal(v, t))

            return tuple(values)
        else:
            return from_smt2_literal(value.v[1], ty)

    if is_call(value, "_"):
        if value.v[1].v == "-oo":
            return float("-inf")
        elif value.v[1].v == "+oo":
            return float("+inf")
        elif value.v[1].v == "+zero":
            return 0.0
        elif value.v[1].v == "-zero":
            return -0.0
        elif value.v[1].v == "NaN": # unfortunately smtlib doesn't handle negative NaN?
            return float("nan")
        elif value.v[1].v.startswith("bv"):
            val = int(value.v[1].v[2:])
            if ty[0] == "s":
                w = int(ty[1:])
                t = 2 ** (w - 1) - 1
                if val > t:
                    val = -(2**w - val)
                return val
            else:
                return val  # this is the value
        else:
            raise NotImplementedError(f"Can't handle _ [{value}]")

    if is_call(value, "fp"):
        sign = value.v[1]
        exp = value.v[2]
        significand = value.v[3]

        sw = significand.width if isinstance(significand, Binary) else significand.width * 4
        expw = exp.width if isinstance(exp, Binary) else exp.width * 4
        total = sw + expw + 1

        intv = (sign.v << (expw + sw)) + (exp.v << (sw)) + significand.v

        if total == 32:
            int_fmt_str = "I"
            flt_fmt_str = "f"
        elif total == 64:
            int_fmt_str = "Q"
            flt_fmt_str = "d"
        else:
            raise NotImplementedError(f"Can't handle {total}-bit float literals (exp: {expw} significand: {sw})")

        floatv = struct.unpack(flt_fmt_str, struct.pack(int_fmt_str, intv))[0]
        #print(intv, value, floatv, floatv.hex())
        return floatv

    raise NotImplementedError(f"from_smt2_literal: Can't handle sexpr {value}")

class SMT2Parser(object):
    @staticmethod
    def tokenize(smt2str):
        # based on the example in the re docs
        tokens = [('STRING', '"[^"]*"'),
                  ('COMMENT', r';.*$'),
                  ('DECIMAL', r'\d\d+'), # order important # TODO: \d.0*\d
                  ('NUMERAL', r'\d'),
                  ('HEX', r'#x[A-Fa-f0-9]+'),
                  ('BINARY', r'#b[01]+'),
                  ('LPAREN', r'\('),
                  ('RPAREN', r'\)'),
                  ('SIMPLE_SYMBOL', r'[-~!@$%^&*_+=<>.?A-Za-z/][-~!@$%^&*_+=<>.?\w/]*'), # \w includes digits, this means first character can't be non-ascii letter
                  ('QUOTED_SYMBOL', r'\|[^\\\|]+\|'),
                  ('WHITESPACE', r'[\t\r\n ]+'), # TODO: 9, 10, 13, 32
                  ('KEYWORD', r':[^\d][-~!@$%^&*_+=<>.?\w/]+'),
                  ('MISMATCH', r'.'),
        ]

        tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in tokens)

        last_str = None
        for m in re.finditer(tok_regex, smt2str, flags=re.M):
            token = m.lastgroup
            match = m.group()

            if last_str is not None and token != 'STRING':
                yield ('STRING', last_str)
                last_str = None

            if token == 'MISMATCH':
                raise ValueError(f"Mismatch {match}")
            elif token == 'STRING':
                if not last_str is None:
                    last_str += match[1:] # drop double "
                else:
                    last_str = match
            elif token == 'WHITESPACE':
                pass
            else:
                yield (token, match)

    @staticmethod
    def parse(smt2str, comments = False):
        token_stream = SMT2Parser.tokenize(smt2str)

        out = []
        try:
            while True:
                tkn, match = next(token_stream)
                if tkn == "COMMENT":
                    continue
                elif tkn == "LPAREN":
                    out.append(SMT2Parser.parse_sexpr(token_stream, comments))
                else:
                    a = SMT2Parser.parse_atom(tkn, match)
                    if not comments and isinstance(a, Comment): continue
                    out.append(a)
        except StopIteration:
            pass

        return out

    @staticmethod
    def parse_sexpr(token_stream, comments = False):
        out = []
        try:
            while True:
                tkn, match = next(token_stream)
                if tkn == "RPAREN":
                    return SExprList(*out)
                elif tkn == "LPAREN":
                    out.append(SMT2Parser.parse_sexpr(token_stream, comments))
                else:
                    a = SMT2Parser.parse_atom(tkn, match)
                    if not comments and isinstance(a, Comment): continue
                    out.append(SMT2Parser.parse_atom(tkn, match))
        except StopIteration:
            raise ValueError("Ran out of input when parsing SExpr")

    @staticmethod
    def parse_atom(tkn, match):
        if tkn == "DECIMAL":
            return Decimal(int(match))
        elif tkn == "NUMERAL":
            return Numeral(int(match))
        elif tkn == "HEX":
            return Hexadecimal(int(match[2:], base=16), width=len(match)-2)
        elif tkn == "BINARY":
            return Binary(int(match[2:], base=2), width=len(match)-2)
        elif tkn == "SIMPLE_SYMBOL":
            return Symbol(match)
        elif tkn == "QUOTED_SYMBOL":
            return QuotedSymbol(match)
        elif tkn == "KEYWORD":
            return Keyword(match[1:])
        elif tkn == "COMMENT":
            # drop comments for now
            return Comment(match[1:] + '\n') # TODO: use actual EOL character?
        elif tkn == "STRING":
            return String(match[1:-1])
        else:
            raise NotImplementedError(f"Unknown token {tkn} '{match}'")

if __name__ == "__main__":
    import sys
    sys.setrecursionlimit(2500)
    with open(sys.argv[1], "r") as f:
        p = SMT2Parser.parse(f.read())
        for pl in p:
            print(pl)
