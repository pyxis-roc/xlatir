#!/usr/bin/env python3

import ast
import xir
import xirxlat
from xirtyping import *
import textwrap
import os

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


XIR_TO_SMT2_OPS = {('ADD', '*', '*'): '+',
                   ('SUB', '*', '*'): '-',
                   ('MUL', '*', '*'): '*',
                   ('DIV', '*', '*'): '/', # signed division
                   ('REM', '*', '*'): '%',

                   ('SHR', '*', '*'): '>>', # signed shr
                   ('SHL', '*', '*'): '<<', #

                   ('GT', '*', '*'): '>',
                   ('LT', '*', '*'): '<',
                   ('NOTEQ', '*', '*'): '!=',
                   ('GTE', '*', '*'): '>=',
                   ('EQ', '*', '*'): '==',

                   ('MIN', 'float', 'float'): 'fminf',
                   ('MAX', 'float', 'float'): 'fmaxf',

                   ('FTZ', 'f32'): lambda x: SExprList(Symbol('FTZ_f32'), x),
                   ('FTZ', 'f64'): lambda x: SExprList(Symbol('FTZ_f64'), x),

                   ('MIN', 'double', 'double'): 'fmin',
                   ('MAX', 'double', 'double'): 'fmax',
                   ('MAX', '*', '*'): 'MAX',
                   ('min', '*', '*'): 'ptx_min', # this is varargs, but restrict it to 2?

                   ('AND', '*', '*'): '&',
                   ('OR', '*', '*'): '|',
                   ('XOR', '*', '*'): '^',
                   ('NOT', '*'): '~',

                   ('booleanOp_xor', 'signed', 'signed'): lambda x, y: SExprList(Symbol("bvxor"), x, y),
                   ('booleanOp_xor', 'unsigned', 'unsigned'): lambda x, y: SExprList(Symbol("bvxor"), x, y),

                   ('booleanOp_xor', 'pred', 'pred'): lambda x, y: SExprList(Symbol("bvxor"), x, y),

                   ('compare_eq', '*', '*'): lambda x, y: SExprList(Symbol('='), x, y),
                   ('compare_ne', '*', '*'): lambda x, y: SExprList(Symbol("not"),
                                                                    SExprList(Symbol('='), x, y)),

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

                ('compare_num', 'float', 'float'): '()', # for type checking only
                   ('compare_num', 'double', 'double'): '()',  # for type checking only

                ('compare_nan', 'float', 'float'): '()', # for type checking only
                   ('compare_nan', 'double', 'double'): '()',  # for type checking only

                ('POW', 'float', 'float'): 'powf',
                   ('POW', 'double', 'double'): 'pow',

                ('set_memory', '*', '*'): 'set_memory',
                   ('logical_op3', 'uint32_t', 'uint32_t', 'uint32_t', 'uint8_t'): 'logical_op3',

                ('ABSOLUTE', 'int32_t'): 'abs',
                   ('ABSOLUTE', 'int64_t'): 'labs', # depends on 64-bit model
                   ('ABSOLUTE', 'int16_t'): 'abs',
                   ('ABSOLUTE', 'float'): 'fabsf',
                   ('ABSOLUTE', 'double'): 'fabs',
                   ('ROUND', '*'): '', # TODO
                   ('SATURATE', 'int32_t'): '', #TODO
                   ('SATURATE', '*'): 'SATURATE', # not for int!
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
        raise NotImplementedError

    def _do_fnop_builtin(self, n, fnty, args, node):
        arglen = len(fnty) - 1
        op = self._get_op(fnty)
        return op(*args[:arglen])

    def _do_fnop(self, n, fnty, args, node):
        arglen = len(fnty) - 1
        op = self._get_op(fnty, builtin = False)
        return op(*args[:arglen])

    POW = _nie
    MIN = _nie
    MAX = _nie
    set_memory = _nie
    FTZ = _do_fnop
    logical_op3 = _nie
    min = _nie
    ABSOLUTE = _nie
    ROUND = _nie
    SATURATE = _nie
    NOT = _nie
    booleanOp_xor = _do_fnop_builtin

    def subnormal_check(self, n, fnty, args, node):
        return f"(bool_to_pred (fp.is_Subnormal args))"

    GTE = _nie
    GT = _nie
    LT = _nie
    LTE = _nie
    EQ = _nie
    NOTEQ = _nie

    OR = _nie
    AND = _nie
    XOR = _nie
    SHR = _nie
    SHL = _nie

    ADD = _nie
    SUB = _nie
    MUL = _nie
    DIV = _nie

    def _do_compare_unordered(self, n, fnty, args, node):
        assert n[-1] == 'u' # unordered
        n = n[:-1]

        assert opkey in XIR_TO_SMT2_OPS, f"Missing operator {fnty}"

        a1 = args[0]
        a2 = args[1]

        return f"(bool_to_pred (or (fp.isNaN {a1}) (fp.isNaN {a2}) ({XIR_TO_SMT2_OPS[opkey]} {a1} {a2})))"

    compare_equ = _do_compare_unordered
    compare_neu = _do_compare_unordered
    compare_ltu = _do_compare_unordered
    compare_leu = _do_compare_unordered
    compare_gtu = _do_compare_unordered
    compare_geu = _do_compare_unordered

    def _do_compare(self, n, fnty, args, node):
        op = self._get_op(fnty, generic=True)

        return SExprList(Symbol("bool_to_pred"), op(args[0], args[1]))

    compare_eq = _do_compare
    compare_ne = _do_compare
    compare_lt = _do_compare
    compare_le = _do_compare
    compare_gt = _do_compare
    compare_ge = _do_compare
    compare_lo = _do_compare
    compare_ls = _do_compare
    compare_hi = _do_compare
    compare_hs = _do_compare

    def compare_nan(self, n, fnty, args, node):
        assert fnty in XIR_TO_SMT2_OPS, f"Incorrect type for {n}"
        return f"(bool_to_pred (or (fp.isNaN {args[0]}) (fp.isNaN {args[1]})))"

    def compare_num(self, n, fnty, args, node):
        assert fnty in XIR_TO_SMT2_OPS, f"Incorrect type for {n}"
        return f"(bool_to_pred (not (or (fp.isNaN {args[0]}) (fp.isNaN {args[1]}))))"

def is_call(sexpr, func):
    return isinstance(sexpr, SExprList) and isinstance(sexpr.v[0], Symbol) and (sexpr.v[0].v == func)

def create_dag(statements):

    # value numbering
    expr = {}
    values = {}
    def get_key(st):
        if isinstance(st, SExprList):
            return tuple([get_key(v) for v in st.v])
        elif isinstance(st, (Symbol, Numeral, Decimal, Hexadecimal, Binary)):
            k = str(st)
            if k not in expr:
                expr[k] = len(expr) + 1
                values[len(expr)] = st

            return expr[k]
        else:
            raise NotImplementedError(f"create_dag: Not implemented yet: {st}/{type(st)}")

    def reconstitute(k):
        if isinstance(k, tuple):
            return SExprList(*[reconstitute(v) for v in k])
        else:
            return values[k]


    # first, assign value numbers to the statements in the array
    out = []
    for s in statements:
        if is_call(s, "="):
            # treat assignment specially
            k = get_key(s.v[2])
            expr[str(s.v[1])] = k
            values[k] = s.v[1]
        else:
            k = get_key(s)

        out.append(k)

    # assume statement is return [maybe indicate more robustly?]
    retval = out[-1]

    #print(expr)
    #print(values)
    return reconstitute(retval)

class SMT2Xlator(xirxlat.Xlator):
    desugar_boolean_xor = False

    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor
        self.lib = SMT2lib()

    def _get_smt2_type(self, node, declname = None):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        t = xir.find(ty, self.x2x.types)

        if isinstance(t, TyPtr):
            pt = self._get_c_type(t.pty)
            return f"{pt} *"

        if isinstance(t, TyApp):
            arg_types = [self._get_smt2_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for fn ptrs"
            return f"{self._get_c_type(t.ret)} (*{declname})({', '.join(arg_types)})"

        if isinstance(t, TyProduct):
            #NOTE: this won't handle function pointers as return values
            elt_types = [self._get_smt2_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for product types"
            elt_names = [f"(out{k} {ty})" for k, ty in enumerate(elt_types)]

            return f"struct retval_{declname} {{ {'; '.join(elt_names)};  }}"

        if not isinstance(t, TyConstant):
            if isinstance(t, TyVarLiteral):
                return f'literal_type'

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

    def xlat_Name(self, name: str, node):
        return Symbol(name)

    def xlat_NameConstant(self, value, node):
        if node.value == True:
            return Numeral(1)
        elif node.value == False:
            return Numeral(0)
        elif node.value is None:
            return Symbol("None")

        raise NotImplementedError(f"NameConstant for value {value} not supported")

    #TODO: types?
    def xlat_Attribute(self, value, attr: str, node):
        return f'{value}.{attr}'

    def xlat_Str(self, s, node):
        return String(s)

    def _smt2_literal(self, v, ty):
        if ty.v == 'pred':
            assert v == 1 or v == 0, f"Wrong value for pred: {v}"
            return Binary(v, 1)
        else:
            raise NotImplementedError(f"Don't yet handle literals of type {ty}/{v}")

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
        assert opty[1].v == 'pred', opty
        return SExprList(Symbol('bvnot'), value)

    def xlat_IfExp(self, test, body, orelse, node):
        if is_call(test, "bool_to_pred"):
            test = test.v[1]

        return SExprList(Symbol("ite"), test, body, orelse)

    def xlat_If(self, test, body, orelse, node):
        raise NotImplemented("Don't support If loops in SMT2 yet")

    def xlat_Break(self, node):
        raise NotImplemented("Don't support Break loops in SMT2 yet")

    def xlat_float_val(self, v):
        if v == 'inf':
            return "INFINITY" # since C99
        elif v == '-inf':
            return "-INFINITY" # since C99
        elif v == 'nan':
            return "NAN" # since C99, but could also use nan()?
        elif v == '-nan':
            return "-NAN"
        elif v == '-0.0' or v == '0.0':
            return v
        else:
            raise NotImplementedError(f"Unknown float constant {v}")

    def xlat_float_compare(self, comparefn, constval, compareto):
        if constval == 'inf' or constval == '-inf':
            fn = "!isfinite"
        elif constval == 'nan' or constval == '-nan':
            fn = "isnan"

        return f"{'!' if comparefn == 'FLOAT_COMPARE_NOTEQ' else ''}{fn}({compareto})"

    def xlat_Call(self, fn, fnty, args, node):
        arglen = len(fnty) - 1
        return SExprList(fn, *args[:arglen])

    def xlat_Return(self, v, vty, node):
        return v

    def xlat_Assign(self, lhs, rhs, node):
        return SExprList(Symbol("="), lhs, rhs)

    def xlat_While(self, test, body, node):
        raise NotImplemented("Don't support While loops in SMT2 yet")

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        self._retval_ty = retval

        expr = create_dag(body)

        #TODO: this should be done elsewhere
        output = SExprList(Symbol("define-fun"),
                           Symbol(name),
                           SExprList(*params),
                           Symbol(retval),
                           expr)

        output = str(output)

        return output

    def write_output(self, output, translations, defns):
        with open(output, "w") as f:
            print("(set-logic QF_FPBV)", file=f) # need to support arrays too

            print(textwrap.dedent("""\
            (define-sort u8 () (_ BitVec 8))
            (define-sort pred () (_ BitVec 1))

            (define-fun bool_to_pred ((x Bool)) pred (ite x #b1 #b0))
            (define-fun pred_to_bool ((x pred)) Bool (= x #b1))

            """), file=f)

            for sz in [16, 32, 64]:
                for prefix in ['b', 's', 'u']:
                    print(f"(define-sort {prefix}{sz} () (_ BitVec {sz}))", file=f)

            for sz in [32, 64]:
                print(f"(define-sort f{sz} () Float{sz})", file=f)


            with open(os.path.join(os.path.dirname(__file__), "ptx_utils.smt2"), "r") as incl:
                print(incl.read(), file=f)

            print("\n\n".join(translations), file=f)

