#!/usr/bin/env python3

import argparse
from . import xir
import ast
from .xirtyping import *
import os
from . import xirxlat
from .astcompat import AC
from .xirlibc import XIRBuiltinLibC

XIR_TO_C_TYPES = {'b8': 'uint8_t',
                  'b16': 'uint16_t',
                  'b32': 'uint32_t',
                  'b64': 'uint64_t',
                  'u8': 'uint8_t',
                  'u16': 'uint16_t',
                  'u32': 'uint32_t',
                  'u64': 'uint64_t',
                  'u128': 'my_uint128_t',
                  's8': 'int8_t',
                  's16': 'int16_t',
                  's32': 'int32_t',
                  's64': 'int64_t',
                  's128': 'my_int128_t',
                  'f32': 'float',
                  'f64': 'double',
                  'pred': 'uint32_t', #TODO
                  # not part of ptx
                  'intptr_t': 'intptr_t',
                  'void': 'void',
                  'bool': 'unsigned int', #TODO
                  'cc_reg': 'struct cc_register',
                  'cc_reg_ref': 'struct cc_register *',
                  'b1': 'BIT_T', # NOT REALLY, but used as a indicator
                  # temporary until we find a better way
                  'str': 'str',
                  'carryflag': 'int',
                  }

class Clib(object):
    def __init__(self):
        self.xlib = []

    def add_lib(self, lib):
        lib.parent = self
        self.xlib.append(lib)

    def get_builtin(self):
        return XIRBuiltinLibC()

    def can_xlat(self, n):
        for lib in self.xlib:
            if hasattr(lib, n): return True

        return False

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
            except NotImplementedError:
                print(f"{lib.__class__.__name__}: notimplemented: {fnty}")

        assert False, f"Couldn't find {fnty} in libraries"

    def do_xlat(self, n, fnty, args, node):
        op = self._get_lib_op(fnty, node, n)
        assert not isinstance(op, str), f"Don't support legacy string value {op} returned by lookup for {fnty}"
        arglen = len(fnty) - 1
        return op(*args[:arglen])

class CXlator(xirxlat.Xlator):
    desugar_boolean_xor = True
    name = "c"

    def __init__(self, x2x):
        self.x2x = x2x # parent ast.NodeVisitor
        self.lib = Clib()
        self.gen_structs = {}

    def pre_xlat_transform(self, s):
        return s

    def _get_c_type(self, node, declname = None):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        if isinstance(ty, TyVar):
            t = xir.find(ty, self.x2x.types)
        else:
            t = ty

        if isinstance(t, TyPtr):
            pt = self._get_c_type(t.pty)

            if isinstance(t.pty, TyConstant) and pt == 'cc_reg':
                if not declname:
                    return "struct cc_register *"
                else:
                    return f"struct cc_register * {declname}"

            return f"{pt} * {declname}"

        if isinstance(t, TyRecord):
            if self.x2x.tyenv.is_generic_record(t.name):
                # find instantiation
                inst = self.x2x.polyinst.find(t)
                assert inst is not None
                struct_name = inst.name
                self.gen_structs[struct_name] = inst.inst # we need the specific instantiation, since otherwise the typevars in T are "global"
            else:
                struct_name = t.name
                self.gen_structs[struct_name] = t # TODO

            if not declname:
                return f"struct {struct_name}"
            else:
                return f"struct {struct_name} {declname}"


        if isinstance(t, TyApp):
            arg_types = [self._get_c_type(x) for x in t.args]
            ret_type = self._get_c_type(t.ret)
            if ret_type == "BIT_T":
                # TODO: why do bitarray accesses show up as fnptrs? [or actually other way around?]
                return ret_type
            else:
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
            if elt_type == "BIT_T":
                # bitstrings
                return f"bitstring{t.sizes[0]}_t"
            else:
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
                return name # lambda x: x
            elif name == "MACHINE_SPECIFIC_execute_rem_divide_by_neg":
                return name # lambda x, y: x % abs(y)
            elif name == "MACHINE_SPECIFIC_execute_div_divide_by_zero_integer":
                return name
                #width = int(self.x2x.get_type(node._xir_type).name[1:])
                #return str(2**width-1)
            elif name == "MACHINE_SPECIFIC_execute_div_divide_by_zero_float":
                return "NAN" # shouldn't the FP unit do this?
            else:
                raise NotImplementedError(f"Not implemented: Machine-specific value {name}")

        return name

    def xlat_NameConstant(self, value, vty, node):
        if AC.value(node) == True:
            return "1"
        elif AC.value(node) == False:
            return "0"
        elif AC.value(node) is None:
            return "None"

        raise NotImplementedError(f"NameConstant for value {value} not supported")

    #TODO: types?
    def xlat_Attribute(self, value, attr: str, node):
        is_ptr = False
        if isinstance(node._xir_type, TyVar) and node._xir_type.name == "TY:cc_reg.cf":
            cc_reg_type = self.x2x._get_type(TyVar("TY:cc_reg"))
            is_ptr = isinstance(cc_reg_type, TyPtr)

        return f'{value}{"->" if is_ptr else "."}{attr}'

    def xlat_Str(self, s, node):
        return repr(s)

    def xlat_Num(self, n, nty, node):
        if nty == 'uint64_t':
            return str(n) + "UL"
        elif nty == 'int64_t':
            return str(n) + "L"
        elif nty == 'uint32_t':
            return str(n) + "U"
        else:
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

    def xlat_float_val(self, v, vty):
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
        if constval == 'inf':
            fn = lambda x: f"(isinf({x}) == 1)"
        elif constval == '-inf':
            fn = lambda x: f"(isinf({x}) == -1)"
        elif constval == 'nan' or constval == '-nan':
            fn = lambda x: f"isnan({x})"
        elif constval == '-0.0':
            fn = lambda x: f"(fpclassify({x}) == FP_ZERO && signbit({x}))"
        else:
            raise NotImplementedError(f"Unknown float value in comparison {constval}")

        return f"{'!' if comparefn == 'FLOAT_COMPARE_NOTEQ' else ''}{fn(compareto)}"

    def xlat_Subscript(self, var, varty, index, indexty, node):
        if varty.startswith('bitstring'):
            if isinstance(node.ctx, ast.Load):
                suffix = 'UL' if varty == 'bitstring64_t' else ''
                return f"((({var} & (1{suffix} << {index})) == (1{suffix} << {index})))" # return 1 or 0
            else:
                return (var, index)
        else:
            return f"{var}[{index}]"

    def xlat_Pass(self, node):
        return ";"

    def xlat_Call(self, fn, fnty, args, node):
        arglen = len(fnty) - 1

        if fnty[0] in self.x2x.tyenv.record_decls:
            ret_ty = self.x2x._get_type(node._xir_type).ret
            struct_ty = self._get_c_type(ret_ty)

            return f"(({struct_ty}) {{{', '.join(args[:arglen])}}})" # C compound literal, C99

        if fn.startswith("BITSTRING_") or fn.startswith("FROM_BITSTRING_"):
            return args[0]
        else:
            return f"{fn}({', '.join(args[:arglen])})"

    def xlat_Return(self, v, vty, node):
        if isinstance(v, list):
            # this should no longer be required?

            if "{" in vty:
                # compat, we used anonymous structs for Tuples
                vty = vty[:vty.index("{")]
            else:
                pass

            v = f"{vty} _retval = {{ {', '.join(v)} }};\n\treturn _retval"
            return v
        elif v is not None:
            return f"return {v}"
        else:
            return f"return"

    def xlat_Assign(self, lhs, rhs, node):
        if isinstance(lhs, tuple):
            lhs_type = self._get_c_type(node.targets[0]._xir_type)
            assert isinstance(node.targets[0], ast.Subscript) and lhs_type == "BIT_T"
            var, index = lhs

            bstype = self._get_c_type(node.targets[0].value._xir_type)
            bssuffix = "UL" if bstype == 'bitstring64_t' else ''
            # index is evaluated twice ...

            # note: rhs also has type bit, necessitating the coercion
            return f"{var} = ({var} & ~(1{bssuffix} << {index})) | ((({bstype}) ({rhs})) << ({index}))"
        else:
            # yes, this will pass lists through and fail to compile.
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
            if "{" in retval:
                # compat, anonymous TyProduct handling
                retval = retval[:retval.index("{")]
            else:
                pass

        self._retval_ty = retval
        self.x2x.defns.append(f"{retval} {name} ({', '.join(params)});")

        output = f"""
{retval} {name} ({', '.join(params)}) {{
        {decls}

        {body}
}}"""

        return output

    def xlat_struct_gen(self):
        out = []
        for s in self.gen_structs:
            out.append(f"struct {s} {{")
            for f, t in self.gen_structs[s].fields_and_types:
                ct = self._get_c_type(t)
                out.append(f"    {ct} {f};")
            out.append(f"}};")
        return out

    def xlat_constant_gen(self):
        out = []
        for s in self.x2x.tyenv.constants:
            tv = self.x2x.tyenv.constants[s]
            ct = self._get_c_type(tv[0])
            out.append(f"const {ct} {s} = {AC.value(tv[1])};")

        return out

    def write_output(self, output, translations, defns, ptx = True):
        structs = self.xlat_struct_gen()
        constants = self.xlat_constant_gen()

        if ptx:
            write_output_ptx(output, translations, structs + constants + defns)
        else:
            write_output_general(output, translations, structs + constants + defns)

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

def write_output_ptx(outfile, translations, defns):
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

def write_output_general(outfile, translations, defns):
    # non-ptx write_output
    header = os.path.basename(outfile)[:-2] + ".h"
    print(f"Writing {outfile}")
    with open(outfile, "w") as f:
        f.write("#include <stdlib.h>\n")
        f.write("#include <stdint.h>\n")
        f.write("#include <math.h>\n")
        f.write(f'#include "{header}"\n')
        f.write("\n\n".join(translations))

    print(f"Writing {header}")
    with open(os.path.join(os.path.dirname(outfile), header), "w") as f:
        f.write("#include <stdlib.h>\n\n")
        f.write("#include <stdint.h>\n\n")
        f.write("#include <math.h>\n\n")
        f.write('\n')
        f.write("\n".join(defns))
