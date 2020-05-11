#!/usr/bin/env python3

import argparse
import xir
import ast
import extract_ex_semantics
from xirtyping import *
import os
import xirxlat

XIR_TO_C_TYPES = {'b8': 'uint8_t',
                  'b16': 'uint16_t',
                  'b32': 'uint32_t',
                  'b64': 'uint64_t',
                  'u8': 'uint8_t',
                  'u16': 'uint16_t',
                  'u32': 'uint32_t',
                  'u64': 'uint64_t',
                  's8': 'int8_t',
                  's16': 'int16_t',
                  's32': 'int32_t',
                  's64': 'int64_t',
                  'f32': 'float',
                  'f64': 'double',
                  'pred': 'uint32_t', #TODO
                  # not part of ptx
                  'intptr_t': 'intptr_t',
                  'void': 'void',
                  'bool': 'unsigned int', #TODO
                  'cc_reg': 'struct cc_register',
                  }

#TODO: Rewrite this
XIR_TO_C_OPS = {('ADD', '*', '*'): '+',
                ('SUB', '*', '*'): '-',
                ('MUL', '*', '*'): '*',
                ('DIV', '*', '*'): '/',
                ('REM', '*', '*'): '%',

                ('SHR', '*', '*'): '>>',
                ('SHL', '*', '*'): '<<',

                ('GT', '*', '*'): '>',
                ('LT', '*', '*'): '<',
                ('NOTEQ', '*', '*'): '!=',
                ('GTE', '*', '*'): '>=',
                ('EQ', '*', '*'): '==',

                ('MIN', 'float', 'float'): 'fminf',
                ('MAX', 'float', 'float'): 'fmaxf',

                ('FTZ', 'float'): 'FTZ',
                ('FTZ', 'double'): 'FTZ',

                ('MIN', 'double', 'double'): 'fmin',
                ('MAX', 'double', 'double'): 'fmax',
                ('MAX', '*', '*'): 'MAX',
                ('min', '*', '*'): 'ptx_min', # this is varargs, but restrict it to 2?

                ('AND', '*', '*'): '&',
                ('OR', '*', '*'): '|',
                ('XOR', '*', '*'): '^',
                ('NOT', '*'): '~',

                ('compare_eq', '*', '*'): '==',
                ('compare_ne', '*', '*'): '!=',

                # the unordered versions use the same as below
                ('compare_lt', '*', '*'): '<', # for signed and unsigned (see set)
                ('compare_le', '*', '*'): '<=', # for signed and unsigned (see set)
                ('compare_gt', '*', '*'): '>', # for signed and unsigned (see set)
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

class Clib(object):
    def _do_fnop(self, n, fnty, args, node):

        arglen = len(fnty) - 1

        if fnty not in XIR_TO_C_OPS:
            opkey = tuple([n] + ['*'] * arglen) # contains arity info
        else:
            opkey = fnty

        assert opkey in XIR_TO_C_OPS, f"Missing operator {fnty}"

        return f"{XIR_TO_C_OPS[opkey]}({', '.join([a for a in args[:arglen]])})"

    POW = _do_fnop
    MIN = _do_fnop
    MAX = _do_fnop
    set_memory = _do_fnop
    FTZ = _do_fnop
    logical_op3 = _do_fnop
    min = _do_fnop
    ABSOLUTE = _do_fnop
    ROUND = _do_fnop
    SATURATE = _do_fnop
    NOT = _do_fnop # because not is a prefix op

    def subnormal_check(self, n, fnty, args, node):
        return f"(fpclassify({args[0]}) == FP_SUBNORMAL)"

    def _do_infix_op(self, n, fnty, args, node):
        arglen = len(fnty) - 1
        assert arglen == 2, f"Not supported {n}/{fnty} for infix op"

        if fnty not in XIR_TO_C_OPS:
            opkey = tuple([n] + ['*'] * arglen) # contains arity info
        else:
            opkey = fnty

        assert opkey in XIR_TO_C_OPS, f"Missing operator {fnty}"

        return f"({args[0]} {XIR_TO_C_OPS[opkey]} {args[1]})"

    GTE = _do_infix_op
    GT = _do_infix_op
    LT = _do_infix_op
    LTE = _do_infix_op
    EQ = _do_infix_op
    NOTEQ = _do_infix_op

    OR = _do_infix_op
    AND = _do_infix_op
    XOR = _do_infix_op
    SHR = _do_infix_op
    SHL = _do_infix_op

    ADD = _do_infix_op
    SUB = _do_infix_op
    MUL = _do_infix_op
    DIV = _do_infix_op

    def _do_compare_unordered(self, n, fnty, args, node):
        assert n[-1] == 'u' # unordered
        n = n[:-1]

        if fnty in XIR_TO_C_OPS:
            opkey = fnty
        else:
            opkey = (n, '*', '*')

        assert opkey in XIR_TO_C_OPS, f"Missing operator {fnty}"

        a1 = args[0]
        a2 = args[1]

        return f"isnan({a1}) || isnan({a2}) || (({a1}) {XIR_TO_C_OPS[opkey]} ({a2}))"

    compare_equ = _do_compare_unordered
    compare_neu = _do_compare_unordered
    compare_ltu = _do_compare_unordered
    compare_leu = _do_compare_unordered
    compare_gtu = _do_compare_unordered
    compare_geu = _do_compare_unordered

    def _do_compare(self, n, fnty, args, node):
        if fnty not in XIR_TO_C_OPS:
            fnty = (fnty[0], '*', '*')

        assert fnty in XIR_TO_C_OPS, f"Missing operator translation {fnty}"

        return f"({args[0]} {XIR_TO_C_OPS[fnty]} {args[1]})"

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
        assert fnty in XIR_TO_C_OPS, f"Incorrect type for {n}"
        return f"(isnan({args[0]}) || isnan({args[1]}))"

    def compare_num(self, n, fnty, args, node):
        assert fnty in XIR_TO_C_OPS, f"Incorrect type for {n}"
        return f"!(isnan({args[0]}) || isnan({args[1]}))"

class CXlator(xirxlat.Xlator):
    desugar_boolean_xor = True

    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor
        self.lib = Clib()

    def pre_xlat_transform(self, s):
        return s

    def _get_c_type(self, node, declname = None):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        t = xir.find(ty, self.x2x.types)

        if isinstance(t, TyPtr):
            pt = self._get_c_type(t.pty)
            return f"{pt} *"

        if isinstance(t, TyApp):
            arg_types = [self._get_c_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for fn ptrs"
            return f"{self._get_c_type(t.ret)} (*{declname})({', '.join(arg_types)})"

        if isinstance(t, TyProduct):
            #NOTE: this won't handle function pointers as return values
            elt_types = [self._get_c_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for product types"
            elt_names = [f"{ty} out{k}" for k, ty in enumerate(elt_types)]

            return f"struct retval_{declname} {{ {'; '.join(elt_names)};  }}"

        if not isinstance(t, TyConstant):
            if isinstance(t, TyVarLiteral):
                return f'literal_type'

            assert isinstance(t, TyConstant), f"Non-TyConstant type: {t}"

        if declname:
            return f"{XIR_TO_C_TYPES[t.value]} {declname}"
        else:
            return XIR_TO_C_TYPES[t.value]

    def get_declaration(self, node, declname = None):
        return self._get_c_type(node, declname)

    def get_native_type(self, xirty, declname = None):
        return self._get_c_type(xirty, declname)

    def xlat_Name(self, name: str, node):
        return name

    def xlat_NameConstant(self, value, vty, node):
        if node.value == True:
            return "1"
        elif node.value == False:
            return "0"
        elif node.value is None:
            return "None"

        raise NotImplementedError(f"NameConstant for value {value} not supported")

    #TODO: types?
    def xlat_Attribute(self, value, attr: str, node):
        return f'{value}.{attr}'

    def xlat_Str(self, s, node):
        return s

    def xlat_Num(self, n, nty, node):
        return str(n)

    def xlat_BoolOp(self, op, opty, values, node):
        return "(" + f" {op} ".join(values) + ")"

    def xlat_BinOp(self, op, opty, left, right, node):
        return f'({left} {op} {right})'

    def xlat_Compare(self, op, opty, left, right, node):
        return f'({left} {op} {right})'

    def xlat_UnaryOp(self, op, opty, value, node):
        return f'({op}{value})'

    def xlat_IfExp(self, test, body, orelse, opty, node):
        return f"({test} ? {body} : {orelse})"

    def xlat_If(self, test, body, orelse, node):
        body = ["\t\t" + x + ";" for x in body]
        if orelse:
            orelse = ["\t\t" + x + ";" for x in orelse]
        else:
            orelse = None

        out = [f'if ({test}) {{']
        out.extend(body)
        if orelse:
            out.append('\t} else {')
            out.extend(orelse)
        out.append('\t}')

        return '\n'.join(out)

    def xlat_Break(self, node):
        return "break\n"

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
        return f"{fn}({', '.join(args[:arglen])})"

    def xlat_Return(self, v, vty, node):
        if isinstance(v, list):
            vty = vty[:vty.index("{")]
            v = f"{vty} _retval = {{ {', '.join(v)} }};\n\treturn _retval"
            return v
        elif v is not None:
            return f"return {v}"
        else:
            return f"return"

    def xlat_Assign(self, lhs, rhs, node):
        return f"{lhs} = {rhs}"

    def xlat_While(self, test, body, node):
        body = ["\t\t" + x + ";" for x in body]

        return f"while({test}) {{" + "\n" + "\n".join(body) + "\n}"

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        body = "\n\t".join([s + ";" for s in body])
        decls = "\n\t".join([f"{t} {v};" for (v, t) in decls])

        if retval.startswith("struct "):
            self.x2x.defns.append(retval + ";")
            retval = retval[:retval.index("{")]

        self._retval_ty = retval
        self.x2x.defns.append(f"{retval} {name} ({', '.join(params)});")

        output = f"""
{retval} {name} ({', '.join(params)}) {{
        {decls}

        {body}
}}"""

        return output

    def write_output(self, output, translations, defns):
        write_output(output, translations, defns)


# For now, use strings instead of returning an AST?
class XIRToC(ast.NodeVisitor):
    def _get_c_type(self, node, declname = None):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        t = xir.find(ty, self.types)

        if isinstance(t, TyPtr):
            pt = self._get_c_type(t.pty)
            return f"{pt} *"

        if isinstance(t, TyApp):
            arg_types = [self._get_c_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for fn ptrs"
            return f"{self._get_c_type(t.ret)} (*{declname})({', '.join(arg_types)})"

        if isinstance(t, TyProduct):
            #NOTE: this won't handle function pointers as return values
            elt_types = [self._get_c_type(x) for x in t.args]
            assert declname is not None, "declname must be provided for product types"
            elt_names = [f"{ty} out{k}" for k, ty in enumerate(elt_types)]

            return f"struct retval_{declname} {{ {'; '.join(elt_names)};  }};"

        if not isinstance(t, TyConstant):
            if isinstance(t, TyVarLiteral):
                return f'literal_type'

            assert isinstance(t, TyConstant), f"Non-TyConstant type: {t}"

        if declname:
            return f"{XIR_TO_C_TYPES[t.value]} {declname}"
        else:
            return XIR_TO_C_TYPES[t.value]

    def _get_type(self, tyterm):
        return xir.find(tyterm, self.types)

    def visit_Name(self, node):
        if hasattr(self, 'fn') and self.fn:
            if isinstance(node.ctx, ast.Store):
                if node.id not in self.fn._xir_decls:
                    self.fn._xir_decls[node.id] = self._get_c_type(node)

        return node.id

    def visit_NameConstant(self, node):
        if node.value == True:
            return "1"
        elif node.value == False:
            return "0"
        elif node.value is None:
            return "None"

    def visit_Attribute(self, node):
        #TODO decide whether to use . or ->
        return f'{self.visit(node.value)}.{node.attr}'

    def visit_Str(self, node):
        return f'"{node.s}"'

    def visit_Num(self, node):
        return f'{node.n}'

    def _get_op_type(self, op, opty):
        print(op, opty)
        opty = xir.find(opty, self.types)
        assert isinstance(opty, TyApp)
        arg_types = [self._get_c_type(self._get_type(a)) for a in opty.args]

        if len(arg_types) == 2:
            return (op, arg_types[0], arg_types[1])
        elif len(arg_types) == 1:
            return (op, arg_types[0])
        else:
            raise NotImplementedError

    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.And):
            op = ' && '
        elif isinstance(node.op, ast.Or):
            op = ' || '
        else:
            raise NotImplementedError(node.op)

        return op.join([f'({self.visit(v)})' for v in node.values])

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Mult):
            op = '*'
        elif isinstance(node.op, ast.BitAnd):
            op = '&'
        elif isinstance(node.op, ast.Add):
            # TODO: ptx integer wrapping semantics?
            op = '+'
        elif isinstance(node.op, ast.Sub):
            # TODO: ptx integer wrapping semantics?
            op = '-'
        elif isinstance(node.op, ast.Pow):
            # TODO: ptx integer wrapping semantics?
            if isinstance(node.left, ast.Num) and node.left.n == 2:
                return f"(1 << {self.visit(node.right)})"
            else:
                op = '**'
        elif isinstance(node.op, ast.Mod):
            # TODO: ptx integer wrapping semantics?
            op = '%'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return f'({self.visit(node.left)} {op} {self.visit(node.right)})'

    def visit_Compare(self, node):
        assert len(node.ops) == 1, f"Not supported, more than op: {node.ops}"
        assert len(node.comparators) == 1, f"Not supported, more than one comparator: {node.ops}"

        if isinstance(node.ops[0], ast.Lt):
            op = '<'
        elif isinstance(node.ops[0], ast.Gt):
            op = '>'
        else:
            raise NotImplementedError(node.ops[0])

        opty = self._get_op_type(op, node._xir_type)

        return f'({self.visit(node.left)} {op} {self.visit(node.comparators[0])})'

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub):
            op = '-'
        elif isinstance(node.op, ast.Not):
            op = '!' # logical not
        elif isinstance(node.op, ast.Invert):
            op = '~'
        else:
            raise NotImplementedError(node.op)

        opty = self._get_op_type(op, node._xir_type)

        return f'({op}{self.visit(node.operand)})'

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_IfExp(self, node):
        return f"{self.visit(node.test)} ? {self.visit(node.body)} : {self.visit(node.orelse)}"

    def visit_If(self, node):
        test = self.visit(node.test)
        body = ["\t\t" + self.visit(x) + ";" for x in node.body]
        if node.orelse:
            orelse = ["\t\t" + self.visit(x) + ";" for x in node.orelse]
        else:
            orelse = None

        out = [f'if({test}) {{']
        out.extend(body)
        #out.append("\t}")
        if orelse:
            out.append('\t} else {')
            out.extend(orelse)

        out.append('\t}')

        return '\n'.join(out)

    def visit_Break(self, node):
        return "break\n"

    def _get_float_val(self, node):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'float':
            assert isinstance(node.args[0], ast.Str), "Don't support non-str-const uses of float"
            x = node.args[0].s.lower()
            s = ''
            if x[0] == '-' or x[1] == '+':
                s = x[0] if x[0] == '-' else ''
                x = x[1:]

            assert x in ('inf', 'nan', '0.0'), f"Unrecognized value {x}"
            return True, s + x

        return False, None

    def visit_Call(self, node):
        n = self.visit(node.func)
        if n == 'set_sign_bitWidth':
            return self.visit(node.args[0])
        elif (n in xir.ARITH_FNS or n in xir.BITWISE_FNS) and n not in ('POW', 'MIN', 'MAX', 'NOT'): #binary only
            op, t1, t2 = self._get_op_type(n, node._xir_type)

            if (op, t1, t2) in XIR_TO_C_OPS:
                opkey = (op, t1, t2)
            else:
                opkey = (n, '*', '*')

            assert opkey in XIR_TO_C_OPS, opkey

            # returnin ASTs would make this so much nicer ...
            return f"({self.visit(node.args[0])} {XIR_TO_C_OPS[opkey]} {self.visit(node.args[1])})"
        elif n in xir.COMPARE_FNS:
            op, t1, t2 = self._get_op_type(n, node._xir_type)
            assert (n, '*', '*') in XIR_TO_C_OPS

            opkey = (n, '*', '*')
            # returnin ASTs would make this so much nicer ...
            return f"({self.visit(node.args[0])} {XIR_TO_C_OPS[opkey]} {self.visit(node.args[1])})"
        elif n in xir.COMPARE_PTX:
            if n not in set(['compare_equ', 'compare_neu',
                             'compare_ltu', 'compare_leu',
                             'compare_gtu', 'compare_geu',
                             'compare_num', 'compare_nan']):
                op, t1, t2 = self._get_op_type(n, node._xir_type)
                if (n, t1, t2) in XIR_TO_C_OPS:
                    opkey = (n, t1, t2)
                else:
                    opkey = (n, '*', '*')

                assert opkey in XIR_TO_C_OPS, (n, t1, t2)

                # returnin ASTs would make this so much nicer ...
                return f"({self.visit(node.args[0])} {XIR_TO_C_OPS[opkey]} {self.visit(node.args[1])})"
            elif n in ('compare_num', 'compare_nan'):
                op, t1, t2 = self._get_op_type(n, node._xir_type)
                assert (op, t1, t2) in XIR_TO_C_OPS, f"Incorrect type for {n}"

                if n == 'compare_nan':
                    return f"isnan({self.visit(node.args[0])}) || isnan({self.visit(node.args[1])})"
                elif n == 'compare_num':
                    return f"!(isnan({self.visit(node.args[0])}) || isnan({self.visit(node.args[1])}))"
            else:
                assert n[-1] == 'u' # unordered
                n = n[:-1]
                op, t1, t2 = self._get_op_type(n, node._xir_type)
                if (n, t1, t2) in XIR_TO_C_OPS:
                    opkey = (n, t1, t2)
                else:
                    opkey = (n, '*', '*')

                assert opkey in XIR_TO_C_OPS, (n, t1, t2)
                a1 = self.visit(node.args[0])
                a2 = self.visit(node.args[1])

                return f"isnan({a1}) || isnan({a2}) || (({a1}) {XIR_TO_C_OPS[opkey]} ({a2}))"
        elif n in 'POW':
            opkey = self._get_op_type(n, node._xir_type)
            assert opkey in XIR_TO_C_OPS, f"Missing {opkey}"
            return f"{XIR_TO_C_OPS[opkey]}({self.visit(node.args[0])}, {self.visit(node.args[1])})"
        elif n in ('MIN', 'MAX'):
            opkey = self._get_op_type(n, node._xir_type)
            if opkey not in XIR_TO_C_OPS:
                assert (opkey[0], '*', '*') in XIR_TO_C_OPS, f"Missing {opkey}"
                opkey = (opkey[0], '*', '*')

            return f"{XIR_TO_C_OPS[opkey]}({self.visit(node.args[0])}, {self.visit(node.args[1])})"
        elif n == 'ISNAN':
            return f"isnan({self.visit(node.args[0])})"
        elif n == 'set_memory':
            return f"set_memory({self.visit(node.args[0])}, {self.visit(node.args[1])})"
        elif n == 'int':
            return self.visit(node.args[0])
        elif n == 'set_value':
            return self.visit(node.args[2])
        elif n == 'ABSOLUTE':
            #TODO: C is undefined for max neg int
            opkey = self._get_op_type(n, node._xir_type)
            return f"{XIR_TO_C_OPS[opkey]}({self.visit(node.args[0])})"
        elif n == 'NOT':
            op, _ = self._get_op_type(n, node._xir_type)

            return f"{XIR_TO_C_OPS[(op, '*')]}({self.visit(node.args[0])})"
        elif n == 'ROUND':
            #TODO: use fesetenv before the operation!
            return self.visit(node.args[0])
        elif n == 'FTZ':
            #TODO: implement force to zero
            return f"FTZ({self.visit(node.args[0])})"
        elif n == 'SATURATE':
            op, t1 = self._get_op_type(n, node._xir_type)
            if t1 == 'float' or t1 == 'double':
                return f"SAT({self.visit(node.args[0])})"
            #TODO: saturate for s32 should be ADD_SAT
            return self.visit(node.args[0])
        elif n == 'subnormal':
            #TODO: actually implement subnormal, which seems to be the same as FTZ?
            return self.visit(node.args[0])
        elif n == 'subnormal_check':
            return f"fpclassify({self.visit(node.args[0])}) == FP_SUBNORMAL"
        elif n == 'min':
            #TODO: actually implement a min function, a macro will not cut it
            return f"ptx_min({self.visit(node.args[0])}, {self.visit(node.args[1])})"
        elif n == 'float':
            _, v = self._get_float_val(node)
            assert v is not None, node.args[0]

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
        elif n == 'FLOAT_COMPARE_EQ' or n == 'FLOAT_COMPARE_NOTEQ':
            _, v = self._get_float_val(node.args[1])
            assert v is not None, node.args[1]

            if v == 'inf' or v == '-inf':
                fn = "!isfinite"
            elif v == 'nan' or v == '-nan':
                fn = "isnan"

            return f"{'!' if n == 'FLOAT_COMPARE_NOTEQ' else ''}{fn}({self.visit(node.args[0])})"
        elif n == "logical_op3":
            return f"logical_op3({', '.join([self.visit(a) for a in node.args[:-1]])})"

        args = [str(self.visit(a)) for a in node.args]
        return f"{n}({', '.join(args)})"

    def visit_Tuple(self, node):
        # this assumes that this will always be structure initialization
        return f"{{ {', '.join([self.visit(e) for e in node.elts])} }}"

    def visit_Return(self, node):
        if node.value:
            if isinstance(node.value, ast.Tuple):
                return f"struct retval_{self.fn.name[len('execute_'):]} _retval = {self.visit(node.value)};\n\treturn _retval"
            else:
                return f"return {self.visit(node.value)}"
        else:
            return "return"

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Not supported"

        return f"{self.visit(node.targets[0])} = {self.visit(node.value)}"

    def visit_While(self, node):
        assert len(node.orelse) == 0

        test = self.visit(node.test)
        body = ["\t\t" + self.visit(x) + ";" for x in node.body]

        return f"while({test}) {{" + "\n" + "\n".join(body) + "\n}"

    def visit_FunctionDef(self, node):
        # perhaps make this per block?
        self.fn = node

        node._xir_decls = {}
        args = []
        for a in node.args.args:
            t = self._get_c_type(a, declname=a.arg)
            node._xir_decls[a.arg] = None
            args.append(t)

        out = []
        for s in node.body:
            out.append(str(self.visit(s)) + ";")

        body = "\n\t".join(out)
        decls = "\n\t".join([f"{t} {v};" for v, t in self.fn._xir_decls.items() if t is not None])


        func = node.name
        retval = self._get_c_type(node._xir_type.ret,
                                  func[len('execute_'):] if isinstance(self._get_type(node._xir_type.ret), TyProduct) else None)
        if retval.startswith("struct "):
            self.defns.append(retval)
            retval = retval[:retval.index("{")]

        self.defns.append(f"{retval} {func} ({', '.join(args)});")

        #TODO: return a C AST?
        output = f"""
{retval} {func} ({', '.join(args)}) {{
        {decls}
        {body}
}}"""
        self.fn = None

        return output

    def translate(self, sem, types):
        self.types = types
        self.defns = []
        return self.visit(sem)

debug_exclude = set(['execute_ld_param_u64',
                     'execute_ld_param_u16',
                     'execute_ld_param_u32',
                     'execute_ld_param_f32',
                     'execute_ld_param_f64',
                     'execute_cvta_to_global_u64',

                     'execute_mad_wide_u16',
                     'execute_mad_wide_s16',
                     'execute_mad_wide_s32',
                     'execute_mad_wide_u32',
                     'execute_mad_wide_s64',
                     'execute_mad_wide_u64',

                     'execute_bfind_b32', # while
                     'execute_bfind_s32',
                     'execute_bfind_u32',
                     'execute_bfind_u64',
                     'execute_bfind_s64', # type error
                     'execute_bfind_shiftamt_s32',
                     'execute_bfind_shiftamt_s64',
                     'execute_bfe_u32', # bitwise, and type error, uses multiplication to get strings of length X
                     'execute_bfe_s32', # bitwise, and type error
                     'execute_bfe_s64', # bitwise, and type error
                     'execute_bfe_u64',
                     'execute_fns_unsigned_s32',
                     'execute_fns_unsigned_b32',
                     'execute_fns_signed_s32',
                     'execute_fns_signed_s32',
                     'execute_bfi_b32', # type errors, binary strings?
                     'execute_bfi_b64', # type errors, binary strings?
                     'execute_dp4a_u32_u32', # type errors, not using right sign
                     'execute_dp4a_u32_s32', # type errors, not using right sign
                     'execute_dp4a_s32_u32', # type errors, not using right sign [also array type]
                     'execute_dp4a_s32_s32', # type errors, not using right sign [also array type]
                     'execute_dp2a_lo_u32_u32', # type errors, not using right sign [also array type]
                     'execute_dp2a_lo_s32_s32', # type errors, not using right sign [also array type]
                     'execute_dp2a_lo_u32_s32', # type errors, not using right sign [also array type]
                     'execute_dp2a_lo_s32_u32', # type errors, not using right sign [also array type]
                     'execute_dp2a_hi_u32_u32', # type errors, not using right sign [also array type]
                     'execute_dp2a_hi_s32_s32', # type errors, not using right sign [also array type]
                     'execute_dp2a_hi_u32_s32', # type errors, not using right sign [also array type]
                     'execute_dp2a_hi_s32_u32', # type errors, not using right sign [also array type]
                     'execute_mov_s32',
                     'execute_prmt_f4e_b32', # array type
                     'execute_prmt_b4e_b32', # array type
                     'execute_prmt_rc8_b32', # array type
                     'execute_prmt_ecl_b32', # array type
                     'execute_prmt_ecr_b32', # array type
                     'execute_prmt_rc16_b32', # array type

                     'execute_rem_u16',
                     'execute_rem_u32',
                     'execute_rem_u64',

                     'execute_rem_s16',
                     'execute_rem_s32',
                     'execute_rem_s64',

                     'execute_lg2_approx_f32', # no support for LOG
                     'execute_lg2_approx_ftz_f32', # no support for LOG

]) # temporary

def write_output(outfile, translations, defns):
    header = os.path.basename(outfile)[:-2] + ".h"
    print(f"Writing {outfile}")
    with open(outfile, "w") as f:
        f.write("#include <stdlib.h>\n")
        f.write("#include <stdint.h>\n")
        f.write("#include <math.h>\n")
        f.write(f'#include "{header}"\n')
        f.write('#include "ptxc_utils.h"\n')
        f.write("\n\n".join(translations))

    print(f"Writing {header}")
    with open(os.path.join(os.path.dirname(outfile), header), "w") as f:
        f.write("#include <stdlib.h>\n\n")
        f.write("#include <stdint.h>\n\n")
        f.write("#include <math.h>\n\n")
        f.write('#include "lop3_lut.h"\n')
        f.write("struct cc_register { int cf;};\n")
        f.write("#define ptx_min(a, b) ((a) > (b) ? (b) : (a))") # TODO: actually implement a min
        f.write('\n')
        f.write("\n".join(defns))


if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert XIR semantics to C")
    p.add_argument('semfile', help="File containing executable semantics")
    p.add_argument('ptxinsn', nargs="+", help="PTX instruction in underscore form (e.g. add_u16)")
    p.add_argument("-o", dest="output", help="Output instruction")

    args = p.parse_args()
    gl, semantics = extract_ex_semantics.load_execute_functions(args.semfile)


    if len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all':
        args.ptxinsn = [k[len("execute_"):] for k in semantics if k not in debug_exclude]

    translator = XIRToC()
    out = []
    out_defns = []
    rp = xir.RewritePythonisms()

    for pi in args.ptxinsn:
        sem = semantics["execute_" + pi]
        #if pi.startswith('setp_q'): continue
        rp.visit(sem)
        ast.dump(sem)
        ty = xir.infer_types(sem)
        out.append(translator.translate(sem, ty))
        out_defns.extend(translator.defns)

    if args.output:
        write_output(args.output, out, out_defns)
    else:
        print("\n\n".join(out))
