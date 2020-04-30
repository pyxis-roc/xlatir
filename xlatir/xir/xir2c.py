#!/usr/bin/env python3

import argparse
import xir
import ast
import extract_ex_semantics
from xirtyping import *
import os

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
                  }

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

                ('AND', '*', '*'): '&',
                ('OR', '*', '*'): '|',
                ('XOR', '*', '*'): '^',

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

                ('ABSOLUTE', 'int32_t'): 'abs',
                ('ABSOLUTE', 'int64_t'): 'labs', # depends on 64-bit model
                ('ABSOLUTE', 'int16_t'): 'abs',
                ('ABSOLUTE', 'float'): 'fabsf',
                ('ABSOLUTE', 'double'): 'fabs'}

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

        if not isinstance(t, TyConstant):
            if t.name == 'TY:cc_reg':
                return f'struct cc_register {declname}'

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

            assert x in ('inf', 'nan'), "Unrecognized value {x}"
            return True, s + x

        return False, None

    def visit_Call(self, node):
        n = self.visit(node.func)
        if n == 'set_sign_bitWidth':
            return self.visit(node.args[0])
        elif (n in xir.ARITH_FNS or n in xir.BITWISE_FNS) and n not in ('POW',): #binary only
            # right now, since operators are not differentiated by type in C, this is okay
            # but we may need it for half, etc.
            op, t1, t2 = self._get_op_type(n, node._xir_type)
            assert (n, '*', '*') in XIR_TO_C_OPS, (n, '*', '*')

            opkey = (n, '*', '*')
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
        elif n == 'POW':
            opkey = self._get_op_type(n, node._xir_type)
            assert opkey in XIR_TO_C_OPS, f"Missing {opkey}"
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
            else:
                raise NotImplementedError(f"Unknown float constant {v}")
        elif n == 'FLOAT_COMPARE_EQ' or n == 'FLOAT_COMPARE_NOTEQ':
            _, v = self._get_float_val(node.args[1])
            assert v is not None, node.args[1]

            if v == 'inf' or v == '-inf':
                fn = "isfinite"
            elif v == 'nan' or v == '-nan':
                fn = "isnan"

            return f"{'!' if n == 'FLOAT_COMPARE_NOTEQ' else ''}{fn}({self.visit(node.args[0])})"

        args = [str(self.visit(a)) for a in node.args]
        return f"{n}({', '.join(args)})"

    def visit_Return(self, node):
        if node.value:
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


        retval = self._get_c_type(node._xir_type.ret)

        func = node.name

        self.defns.append(f"{retval} {func} ({', '.join(args)});")

        #TODO: return a C AST?
        output = f"""\
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

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert XIR semantics to C")
    p.add_argument('semfile', help="File containing executable semantics")
    p.add_argument('ptxinsn', nargs="+", help="PTX instruction in underscore form (e.g. add_u16)")
    p.add_argument("-o", dest="output", help="Output instruction")

    args = p.parse_args()
    semantics = extract_ex_semantics.load_execute_functions(args.semfile)

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
                         'execute_lop3_b32', # immLut type
                         'execute_prmt_f4e_b32', # array type
                         'execute_prmt_b4e_b32', # array type
                         'execute_prmt_rc8_b32', # array type
                         'execute_prmt_ecl_b32', # array type
                         'execute_prmt_ecr_b32', # array type
                         'execute_prmt_rc16_b32', # array type
                         'execute_setp_q.*', # multiple return values
                         'execute_lg2_approx_f32', # no support for LOG
                         'execute_lg2_approx_ftz_f32', # no support for LOG

    ]) # temporary

    if len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all':
        args.ptxinsn = [k[len("execute_"):] for k in semantics if k not in debug_exclude]

    translator = XIRToC()
    out = []
    out_defns = []
    rp = xir.RewritePythonisms()

    for pi in args.ptxinsn:
        sem = semantics["execute_" + pi]
        if pi.startswith('setp_q'): continue
        rp.visit(sem)
        ast.dump(sem)
        ty = xir.infer_types(sem)
        out.append(translator.translate(sem, ty))
        out_defns.extend(translator.defns)

    if args.output:
        header = os.path.basename(args.output)[:-2] + ".h"
        print(f"Writing {args.output}")
        with open(args.output, "w") as f:
            f.write("#include <stdlib.h>\n")
            f.write("#include <stdint.h>\n")
            f.write("#include <math.h>\n")
            f.write(f'#include "{header}"\n')
            f.write(f'#include "ptxc_utils.h"\n')
            f.write("\n\n".join(out))

        print(f"Writing {header}")
        with open(os.path.join(os.path.dirname(args.output), header), "w") as f:
            f.write("#include <stdlib.h>\n\n")
            f.write("#include <stdint.h>\n\n")
            f.write("#include <math.h>\n\n")
            f.write("struct cc_register { int cf;};\n")
            f.write("#define ptx_min(a, b) ((a) > (b) ? (b) : (a))") # TODO: actually implement a min
            f.write('\n')
            f.write("\n".join(out_defns))
    else:
        print("\n\n".join(out))
