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
                  # temporary until we find a better way
                  'str': 'str'
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
                ('LOG2', 'float'): 'log2f',
                ('LOG2', 'double'): 'log2',
                ('MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned', '*'): '', #unsigned only!

                ('FTZ', 'float'): 'FTZ',
                ('FTZ', 'double'): 'FTZ',

                ('FMA', 'float', 'float', 'float'): 'FMA',
                ('FMA', 'double', 'double', 'double'): 'FMA',

                ('SINE', 'float'): 'sinf',
                ('SINE', 'double'): 'sin',

                ('COSINE', 'float'): 'cosf',
                ('COSINE', 'double'): 'cos',

                ('MIN', 'double', 'double'): 'fmin',
                ('MAX', 'double', 'double'): 'fmax',
                ('MAX', '*', '*'): 'MAX',
                ('min', '*', '*'): 'MIN', # this is varargs, but restrict it to 2?
                ('MIN', '*', '*'): 'MIN',

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
                ('SQRT', 'float'): 'sqrtf',
                ('SQRT', 'double'): 'sqrt',

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

                ('ADD_SATURATE', 'int32_t', 'int32_t'): 'ADD_SATURATE_s32',
                ('SUB_SATURATE', 'int32_t', 'int32_t'): 'SUB_SATURATE_s32',

                ('ADD_ROUND', '*', '*', '*'): 'ADD_ROUND',
                ('RCP_ROUND', '*', '*'): 'RCP_ROUND',
                ('MUL_ROUND', '*', '*', '*'): 'MUL_ROUND',
                ('SUB_ROUND', '*', '*', '*'): 'SUB_ROUND',
                ('DIV_ROUND', '*', '*', '*'): 'DIV_ROUND',
                ('FMA_ROUND', '*', '*', '*', '*'): 'FMA_ROUND',
                ('SQRT_ROUND', '*', '*'): 'SQRT_ROUND',
                ('zext_64', '*'): 'uint64_t'

}

class Clib(object):
    ROUND_MODES = {'rp': 'FE_UPWARD',  # to positive infinity
                   'rn': 'FE_TONEAREST', # towards nearest even
                   'rz': 'FE_TOWARDZERO', # towards zero
                   'rm': 'FE_DOWNWARD'} # to negative infinity

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
    LOG2 = _do_fnop
    MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned = _do_fnop
    COSINE = _do_fnop
    SINE = _do_fnop

    set_memory = _do_fnop
    FTZ = _do_fnop
    logical_op3 = _do_fnop
    min = _do_fnop
    ABSOLUTE = _do_fnop
    ROUND = _do_fnop
    SATURATE = _do_fnop
    NOT = _do_fnop # because not is a prefix op

    def _do_fnop_round(self, n, fnty, args, node):
        arglen = len(fnty) - 1

        if fnty not in XIR_TO_C_OPS:
            opkey = tuple([n] + ['*'] * arglen) # contains arity info
        else:
            opkey = fnty

        assert opkey in XIR_TO_C_OPS, f"Missing operator {fnty}"

        roundMode = self.ROUND_MODES[args[arglen-1][1:-1]]
        return f"{XIR_TO_C_OPS[opkey]}({', '.join([a for a in args[:arglen-1]])}, {roundMode})"

    def _do_fnop_sat(self, n, fnty, args, node):
        if fnty[1] == 'int32_t':
            return self._do_fnop(n, fnty, args, node)
        else:
            wosat = n[:-len("_SATURATE")]
            assert hasattr(self, wosat), f"Unable to find non-saturating {wosat} version of {n}"
            wosatcode = getattr(self, wosat)(wosat, fnty, args, node)

            #TODO: actually perform a lookup - this is when passing ASTs would be better?
            return f"SATURATE({wosatcode})"

    ADD_ROUND = _do_fnop_round
    SUB_ROUND = _do_fnop_round
    MUL_ROUND = _do_fnop_round
    DIV_ROUND = _do_fnop_round
    FMA_ROUND = _do_fnop_round
    RCP_ROUND = _do_fnop_round
    SQRT_ROUND = _do_fnop_round

    ADD_SATURATE = _do_fnop_sat
    ADD_ROUND_SATURATE = _do_fnop_sat
    SUB_SATURATE = _do_fnop_sat
    SUB_ROUND_SATURATE = _do_fnop_sat
    MUL_SATURATE = _do_fnop_sat
    MUL_ROUND_SATURATE = _do_fnop_sat
    FMA_ROUND_SATURATE = _do_fnop_sat

    def ISNAN(self, n, fnty, args, mode):
        #TODO: check types
        return f"isnan({args[0]})"

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
    REM = _do_infix_op

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


    def _do_cast(self, n, fnty, args, node):
        if fnty not in XIR_TO_C_OPS:
            opkey = tuple([n] + ['*'] * len(args))
        else:
            opkey = fnty

        assert opkey in XIR_TO_C_OPS, f"Missing operator {fnty}"

        return f"(({XIR_TO_C_OPS[opkey]}) {args[0]})"

    zext_64 = _do_cast

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

        if isinstance(t, TyArray):
            elt_type = self._get_c_type(t.elt)
            assert len(t.sizes) == 1, f"Unsupported non-1D arrays: {t.sizes}"
            return f"{elt_type} {declname}[{t.sizes[0]}]"

        if not isinstance(t, TyConstant):
            if isinstance(t, TyVarLiteral):
                return f'literal_type'

            assert isinstance(t, TyConstant), f"Non-TyConstant type: {t}"

        if declname:
            return f"{XIR_TO_C_TYPES[t.value]} {declname}"
        else:
            return XIR_TO_C_TYPES[t.value]

    def get_declaration(self, node, declname = None):
        if isinstance(self.x2x._get_type(node._xir_type), TyArray):
            declname = node.id

        return self._get_c_type(node, declname)

    def get_native_type(self, xirty, declname = None):
        return self._get_c_type(xirty, declname)

    def xlat_Name(self, name: str, node):
        if name.startswith("MACHINE_SPECIFIC_"):
            if name == "MACHINE_SPECIFIC_execute_lg2_negative_number":
                return "NAN"
            elif name == "MACHINE_SPECIFIC_execute_rem_divide_by_zero_signed":
                return "-1"
            elif name == "MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned":
                return "MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned" # lambda x: x
            else:
                raise NotImplementedError(f"Not implemented: Machine-specific value {name}")

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
        return repr(s)

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

    def xlat_Subscript(self, var, varty, index, indexty, node):
        return f"{var}[{index}]"

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

    def xlat_For(self, target, range_start, range_end, body, node):
        body = ["\t\t" + x + ";" for x in body]

        return f"for({target} = {range_start}; {target} < {range_end}; {target}++) {{" + "\n" + "\n".join(body) + "\n}"

    def xlat_FunctionDef(self, name, params, retval, decls, body, node):
        body = "\n\t".join([s + ";" for s in body])
        decls = "\n\t".join([f"{t} {v};" if "[" not in t else t + ";" for (v, t) in decls]) #TODO: fix this hack for arrays

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
        f.write('#include "readbyte_prmt.h"\n')
        f.write("struct cc_register { int cf;};\n")

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
