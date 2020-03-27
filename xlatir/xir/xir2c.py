#!/usr/bin/env python3

import argparse
import xir
import ast
import extract_ex_semantics
from xirtyping import *

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
                  }

XIR_TO_C_OPS = {('add', '*', '*'): '+'}

# For now, use strings instead of returning an AST?
class XIRToC(ast.NodeVisitor):
    def _get_c_type(self, node):
        if isinstance(node, ast.AST):
            ty = node._xir_type
        else:
            ty = node

        t = xir.find(ty, self.types)
        assert isinstance(t, TyConstant), f"Non-TyConstant type: {t}"

        return XIR_TO_C_TYPES[t.value]

    def _get_type(self, tyterm):
        return xir.find(tyterm, self.types)

    def visit_Name(self, node):
        if hasattr(self, 'fn') and self.fn:
            if isinstance(node.ctx, ast.Store):
                if node.id not in self.fn._xir_decls:
                    self.fn._xir_decls[node.id] = self._get_c_type(node)

        return node.id

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
        else:
            raise NotImplementedError

    def visit_Call(self, node):
        n = self.visit(node.func)
        if n == 'set_sign_bitWidth':
            return self.visit(node.args[0])
        elif n == 'add':
            # right now, since operators are not differentiated by type in C, this is okay
            # but we may need it for half, etc.
            op, t1, t2 = self._get_op_type(n, node._xir_type)
            assert (n, '*', '*') in XIR_TO_C_OPS

            # returnin ASTs would make this so much nicer ...
            return f"({self.visit(node.args[0])} + {self.visit(node.args[1])})"

        args = [str(self.visit(a)) for a in node.args]
        return f"{n}({', '.join(args)})"

    def visit_Return(self, node):
        return f"return {self.visit(node.value)}"

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Not supported"

        return f"{self.visit(node.targets[0])} = {self.visit(node.value)}"

    def visit_FunctionDef(self, node):
        # perhaps make this per block?
        self.fn = node

        node._xir_decls = {}

        out = []
        for s in node.body:
            out.append(str(self.visit(s)) + ";")

        body = "\n\t".join(out)
        decls = "\n\t".join([f"{t} {v};" for v, t in self.fn._xir_decls.items()])

        args = [f"{self._get_c_type(a)} {a.arg}" for a in node.args.args]
        retval = self._get_c_type(node._xir_type.ret)

        func = node.name

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
        return self.visit(sem)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Convert XIR semantics to C")
    p.add_argument('semfile', help="File containing executable semantics")
    p.add_argument('ptxinsn', nargs="+", help="PTX instruction in underscore form (e.g. add_u16)")
    p.add_argument("-o", dest="output", help="Output instruction")

    args = p.parse_args()
    semantics = extract_ex_semantics.load_execute_functions(args.semfile)

    if len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all':
        args.ptxinsn = [k[len("execute_"):] for k in semantics]

    translator = XIRToC()
    out = []
    for pi in args.ptxinsn:
        sem = semantics["execute_" + pi]
        ast.dump(sem)
        ty = xir.infer_types(sem)
        out.append(translator.translate(sem, ty))

    if args.output:
        with open(args.output, "w") as f:
            f.write("#include <stdint.h>\n\n")
            f.write("\n\n".join(out))
    else:
        print("\n\n".join(out))
