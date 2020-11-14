#!/usr/bin/env python3
#
# xir.py
#
# eXtensible, Xlation (translation) IR for semantics. Converting the
# semantics expressed in the Python-like IR into other languages. Also
# includes utilities like type inference and loop unrolling.
#
# Author: Sreepathi Pai
#
# TODO: Move this into a separate package gpurosetta?

import ast
import extract_ex_semantics
import argparse
from collections import namedtuple
import astunparse
from xirtyping import *
import itertools

Def_GenericCompare = PolyTyDef(["gamma"], TyApp(TyConstant('bool'),
                                                [TyVar("gamma"), TyVar("gamma")]))

Def_GenericBinOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"),
                                              [TyVar("gamma"), TyVar("gamma")]))

Def_GenericRoundUnaryOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"),
                                                     [TyVar("gamma"), TyConstant('str')]))

Def_GenericRoundBinOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"),
                                                   [TyVar("gamma"), TyVar("gamma"),
                                                    TyConstant('str')]))

# through trickery in the unifier, carryflag will become gamma.
Def_GenericCarryBinOp = PolyTyDef(["gamma1"], TyApp(TyProduct([TyVar("gamma1"),
                                                               TyConstant("carryflag")]),
                                                    [TyVar("gamma1"), TyVar("gamma1"),
                                                     TyVar("gamma1")]))


Def_MulOp = PolyTyDef(["gamma_out", "gamma_in"], TyApp(TyVar("gamma_out"),
                                                       [TyVar("gamma_in"), TyVar("gamma_in")]))

# returns a 2's complement bit vector
Def_Mul24 = PolyTyDef(["gamma"], TyApp(TyConstant("u64"),
                                       [TyVar("gamma"), TyVar("gamma")]))

Def_FMAOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"),
                                       [TyVar("gamma"), TyVar("gamma"), TyVar("gamma")]))

Def_FMARoundOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"),
                                            [TyVar("gamma"), TyVar("gamma"), TyVar("gamma"), TyConstant("str")]))


Def_ShiftOps = PolyTyDef(["gamma_in", "gamma_shift"], TyApp(TyVar("gamma_in"),
                                                          [TyVar("gamma_in"),
                                                           TyVar("gamma_shift")]))

Def_ShiftOps_Literal = PolyTyDef(["gamma_in"], TyApp(TyVar("gamma_in"),
                                                     [TyVar("gamma_in"),
                                                      TyVar("gamma_in")]))

Def_GenericUnaryOp = PolyTyDef(["gamma"], TyApp(TyVar("gamma"), [TyVar("gamma")]))

Def_IfExp = PolyTyDef(["if_gamma"], TyApp(TyVar("if_gamma"),
                                          [TyConstant('bool'),
                                           TyVar("if_gamma"),
                                           TyVar("if_gamma")]))


VARARGS_FNS = set(['min'])

ROUND_SAT_ARITH_FNS = set(['ADD_ROUND', 'SUB_ROUND', 'MUL_ROUND', 'DIV_ROUND', 'FMA_ROUND', 'SQRT_ROUND', 'RCP_ROUND',  'ADD_ROUND_SATURATE',  'SUB_ROUND_SATURATE', 'MUL_ROUND_SATURATE', 'FMA_ROUND_SATURATE'])

SAT_ARITH_FNS = set(['ADD_SATURATE', 'SUB_SATURATE', 'MUL_SATURATE', 'DIV_SATURATE'])

CARRY_ARITH_FNS = set(['ADD_CARRY', 'SUB_CARRY'])

MACHINE_SPECIFIC_FNS = set(["MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned",
                            "MACHINE_SPECIFIC_execute_rem_divide_by_neg",
                            "MACHINE_SPECIFIC_execute_div_divide_by_zero_integer"])

ARITH_FNS = set(['ADD', 'SUB', 'MUL', 'DIV', 'DIV_FULL', 'DIV_APPROX', 'POW', 'REM', 'MIN', 'MAX', 'FMA', 'MUL24', 'MULWIDE', 'LOG2', 'EXP2', 'RCP', 'RSQRT', 'SINE', 'COSINE', 'COPYSIGN']) | SAT_ARITH_FNS | ROUND_SAT_ARITH_FNS | CARRY_ARITH_FNS | MACHINE_SPECIFIC_FNS

BITWISE_FNS = set(['AND', 'SHR', 'SAR', 'OR', 'SHL', 'XOR', 'NOT'])
COMPARE_FNS = set(['GT', 'LT', 'LTE', 'NOTEQ', 'GTE', 'EQ'])
FLOAT_FNS = set(['ROUND', 'FTZ', 'SATURATE', 'ABSOLUTE', 'ISNAN', 'SQRT', 'RCP']) #also unary
COMPARE_PTX = set(['compare_eq','compare_equ','compare_ge','compare_geu',
                   'compare_gt','compare_gtu','compare_hi','compare_hs','compare_le','compare_leu',
                   'compare_lo','compare_ls','compare_lt','compare_ltu','compare_nan','compare_ne',
                   'compare_neu','compare_num'])

BOOLEAN_OP_PTX = set(['booleanOp_and', 'booleanOp_or', 'booleanOp_xor'])

TYPE_DECLS = {'MULWIDE': {('u16', 'u16'): 'u32',
                          ('s16', 's16'): 's32',
                          ('u32', 'u32'): 'u64',
                          ('s32', 's32'): 's64',
                          ('u64', 'u64'): 'u128',
                          ('s64', 's64'): 's128',
                          }}

class HandleXIRHints(ast.NodeTransformer):
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name) and node.func.id.startswith('_xir_'):
            n = node.func.id
            if n == '_xir_unroll':
                assert isinstance(node.args[0], ast.Num), node.args[0]
                self._unroll_factor = node.args[0].n
                return ast.Pass()
            else:
                raise NotImplementedError(f"Unknown XIR hint: {n}")

        return node

    def visit_While(self, node):
        if self._unroll_factor is not None:
            node._xir_unroll_factor = self._unroll_factor
            self._unroll_factor = None

        return node

    def handle_hints(self, node):
        self._unroll_factor = None
        self.visit(node)

class RewritePythonisms(ast.NodeTransformer):
    desugar_boolean_xor = True
    def _is_float_constant_constructor(self, n):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'float':
            if isinstance(n.args[0], ast.Str):
                return n.args[0].s.lower() in ("nan",
                                               "+nan",
                                               "-nan",
                                               "+nan",
                                               "+inf",
                                               "inf",
                                               "-inf",
                                               "-0.0")
        return False

    # TODO: handle machine_specific

    def _add_rounding(self, n):
        if isinstance(n.func, ast.Name) and "_ROUND" in n.func.id: #TODO: make a full list?
            assert isinstance(n.args[-1], ast.Str), f"Expecting last argument of ROUND function to be a string"
            roundModifier = n.args.pop().s
            n.func.id = n.func.id.replace('_ROUND', '_ROUND_' + roundModifier)

    def cvt_machine_specific(self, node):
        def get_keys(msn, keys=None):
            if isinstance(msn, ast.Subscript):
                if isinstance(msn.value, ast.Name) and msn.value.id == 'machine_specific':
                    assert isinstance(msn.slice.value, ast.Str), f"Don't support {msn.slice}"
                    v = msn.slice.value.s
                    keys.append(v)
                    return True
                elif isinstance(msn.value, ast.Subscript):
                    if get_keys(msn.value, keys):
                        assert isinstance(msn.slice.value, ast.Str), f"Don't support {msn.slice}"
                        v = msn.slice.value.s
                        keys.append(v)
                        return True
                    else:
                        return False
                else:
                    return False
            else:
                return False

        k = []
        if get_keys(node, k):
            return ast.Name("MACHINE_SPECIFIC_" + "_".join(k), node.ctx)
        else:
            return node

    def visit_Subscript(self, node):
        if isinstance(node.value, ast.Subscript):
            return self.cvt_machine_specific(node)

        return self.generic_visit(node)

    SUFFIX_FNS = {'compare': (2, ast.Str),
                  'zext': (1, ast.Num),
                  'ReadByte': (0, (ast.Str, ast.NameConstant)),
                  'truncate': (1, ast.Num),
                  'sext': (1, ast.Num),
                  }

    def add_fn_suffix(self, node):
        argid, arg_type = self.SUFFIX_FNS[node.func.id]
        arg = node.args[argid]

        assert isinstance(arg, arg_type), f"{node.func.id} does not have {arg_type} as argument #{argid}, actual type is {type(arg)}"
        if isinstance(arg, ast.Str):
            suffix = arg.s
        elif isinstance(arg, ast.Num):
            suffix = str(arg.n)
        elif isinstance(arg, ast.NameConstant):
            if arg.value is None:
                suffix = ''
            else:
                raise NotImplementedError(f"Don't support NamedConstant with value = {arg.value}")
        else:
            raise NotImplementedError(f"Don't support {arg_type} as suffix")

        node.func.id = node.func.id + ('_' + suffix if suffix else '')
        del node.args[argid]
        self.generic_visit(node)
        return node

    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id in self.SUFFIX_FNS:
                return self.add_fn_suffix(node)
            elif node.func.id.startswith('extractAndSignOrZeroExt'):
                assert isinstance(node.args[2], ast.Num) and node.args[2].n == 32
                assert isinstance(node.args[1], ast.NameConstant) and node.args[1].value in (True, False)
                # This is not necessary, but could simplify implementations?
                if node.args[1].value == False:
                    node.func.id = "extractAndZeroExt" + node.func.id[len("extractAndSignOrZeroExt"):]
                elif node.args[1].value == True:
                    node.func.id = "extractAndSignExt" + node.func.id[len("extractAndSignOrZeroExt"):]
                else:
                    assert False, f"Unsupported {node.args[1].value}"

                node.args = node.args[0:1] # this will happen before Assign
            elif node.func.id in ROUND_SAT_ARITH_FNS:
                if node.func.id == 'FMA_ROUND' or node.func.id == 'FMA_ROUND_SATURATE':
                    node.args.insert(3, node.args[-1])
                    node.args.pop()
                elif node.func.id in ('RCP_ROUND', 'SQRT_ROUND'):
                    node.args.insert(1, node.args[-1])
                    node.args.pop()
                else:
                    node.args.insert(2, node.args[-1])
                    node.args.pop()

            elif node.func.id == 'booleanOp':
                assert isinstance(node.args[2], ast.Str)
                if node.args[2].s == 'and':
                    node = ast.BoolOp(op=ast.And(), values=[node.args[0], node.args[1]])
                elif node.args[2].s == 'or':
                    node = ast.BoolOp(op=ast.Or(), values=[node.args[0], node.args[1]])
                elif node.args[2].s == 'xor':
                    if self.desugar_boolean_xor:
                        # ugly but this is boolean xor: a'b + ab'
                        node = ast.BoolOp(op=ast.Or(),
                                          values=[ast.BoolOp(op=ast.And(),
                                                             values=[ast.UnaryOp(ast.Not(),
                                                                                 node.args[0]),
                                                                     node.args[1]]),

                                                  ast.BoolOp(op=ast.And(),
                                                             values=[node.args[0],
                                                                     ast.UnaryOp(ast.Not(),
                                                                                 node.args[1])]),
                                          ])
                    else:
                        node.func.id = 'booleanOp_' + node.args[2].s
                        node.args.pop()

                return node
            elif node.func.id == 'EQ' or node.func.id == 'NOTEQ':
                if self._is_float_constant_constructor(node.args[1]):
                    return ast.Call(func=ast.Name(f"FLOAT_COMPARE_{node.func.id}", ast.Load()),
                                    args=[node.args[0], node.args[1]],
                                    keywords={})
            elif node.func.id == 'float':
                if not isinstance(node.args[0], ast.Str):
                    return node.args[0] # don't support float as a type cast
            else:
                node = self.generic_visit(node)
        else:
            node = self.generic_visit(node)

        return node

    def visit_Assign(self, node):
        # rewrite extractAnd*Ext so that we can support languages that don't support returning arrays
        node = self.generic_visit(node)

        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if isinstance(node.value, ast.Call):
                if isinstance(node.value.func, ast.Name) and node.value.func.id.startswith('extractAnd'):
                    rhs = node.value
                    rhs.args.append(node.targets[0])
                    return ast.Expr(rhs)

        return node

class TypeEqnGenerator(ast.NodeVisitor):
    def __init__(self):
        self.type_variables = {}
        self.equations = []
        self.call_types = [] # track function call and argument types
        self.ret = 0
        self.literal_index = 0
        self.fn = None

    def generate_type_variable(self, name, literal=None):
        assert name not in self.type_variables

        if literal is None:
            ty = TyVar(f"TY:{name}")
        else:
            ty = TyVarLiteral(f"TY:{name}", literal)
            self.literal_index += 1 # same-valued literals don't necessarily have the same type

        self.type_variables[name] = ty
        return ty

    def get_or_gen_ty_var(self, name, literal = None):
        if name not in self.type_variables:
            return self.generate_type_variable(name, literal)

        return self.type_variables[name]

    def visit_Attribute(self, node):
        if isinstance(node.value, ast.Name) and node.value.id == 'cc_reg':
            if node.attr == 'cf':
                # TODO: connect cc_reg's type to cc_reg.cf type without messing up carryflag
                node._xir_type = self.get_or_gen_ty_var('cc_reg.cf')
                return node._xir_type

        raise NotImplementedError(f"Attribute node {node} not handled")

    def visit_For(self, node):
        assert len(node.orelse) == 0, f"Don't support orelse on For node"

        tty = self.visit(node.target)
        ity = self.visit(node.iter)
        self.equations.append(TyEqn(tty, ity))

        for s in node.body:
            self.visit(s)

    def anno_to_type(self, anno):
        if anno == 'pred': # TODO: width?
            ty = TyConstant("bool")
        elif anno == 'cc_reg_ref':
            ty = TyPtr(TyConstant("cc_reg"))
        else:
            ty = TyConstant(anno)

        return ty

    def visit_FunctionDef(self, node):
        for a in node.args.args:
            t = self.get_or_gen_ty_var(a.arg)
            a._xir_type = t
            if a.annotation is not None:
                aty = self.anno_to_type(a.annotation.id)
                self.equations.append(TyEqn(t, aty))

        ret = self.get_or_gen_ty_var(f"fn_{node.name}_retval")
        fnty = TyApp(ret, [a._xir_type for a in node.args.args])
        node._xir_type = fnty

        # not supported
        assert node.args.vararg is None
        assert node.args.kwarg is None

        self.fn = node
        x = self.generic_visit(node)
        self.fn = None
        return x

    def visit_Tuple(self, node):
        return TyProduct([self.visit(e) for e in node.elts])

    def visit_Return(self, node):
        if node.value:
            tyv = self.visit(node.value)
        else:
            tyv = TyConstant('void')

        #TODO: multiple return values need a product type
        self.equations.append(TyEqn(tyv, self.fn._xir_type.ret))

    def _generate_poly_call_eqns(self, fn, args, typedef):
        ret = self.get_or_gen_ty_var(f"ret{self.ret}")
        fnt = self.get_or_gen_ty_var(f"{fn}{self.ret}") # this is polymorphic ops

        subst = {}
        for uqv in typedef.uqvars:
            uqt = self.get_or_gen_ty_var(f"{uqv}{self.ret}")
            subst[uqv] = uqt.name

        self.ret += 1

        arg_types = [self.visit(a) for a in args]
        app = TyApp(ret, arg_types)
        defty = typedef.get(subst)

        self.equations.append(TyEqn(fnt, app))
        self.equations.append(TyEqn(app, defty))
        self.call_types.append((fn, fnt, app))
        return ret, fnt, defty, app

    def visit_Compare(self, node):
        # not supported
        assert len(node.ops) == 1, node
        assert len(node.comparators) == 1, node

        if isinstance(node.ops[0], ast.Lt):
            fn = f'op_Lt'
        elif isinstance(node.ops[0], ast.Gt):
            fn = f'op_Gt'
        else:
            raise NotImplementedError(f"Unknown compare operator: {node.ops[0]}")

        args = [node.left, node.comparators[0]]
        ret, fnt, defty, app = self._generate_poly_call_eqns(fn, args,
                                                             Def_GenericCompare)

        node._xir_type = fnt

        return ret

    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.Or):
            fn = f'op_BoolOr'
        elif isinstance(node.op, ast.And):
            fn = f'op_BoolAnd'
        else:
            raise NotImplementedError(f"Unknown binary operator: {node.op}")


        tyd = PolyTyDef([], TyApp(TyConstant("bool"), [TyConstant("bool")]*len(node.values)))
        ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.values, tyd)
        node._xir_type = fnt

        return ret

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Add):
            fn = f'op_Add'
        elif isinstance(node.op, ast.Mult):
            fn = f'op_Mult'
        elif isinstance(node.op, ast.Sub):
            fn = f'op_Sub'
        elif isinstance(node.op, ast.Pow):
            fn = f'op_Pow'
        elif isinstance(node.op, ast.Mod):
            fn = f'op_Mod'
        elif isinstance(node.op, ast.BitAnd):
            fn = f'op_BitAnd'
        else:
            raise NotImplementedError(f"Unknown binary operator: {node.op}")

        ret, fnt, _, _ = self._generate_poly_call_eqns(fn, [node.left, node.right],
                                                       Def_GenericBinOp)
        node._xir_type = fnt

        return ret

    def visit_Str(self, node):
        ty =  self.get_or_gen_ty_var(f"{node.s}_{self.literal_index}", literal=node.s)
        node._xir_type = ty
        return ty

    def visit_Num(self, node):
        #TODO: more nuanced?
        ty =  self.get_or_gen_ty_var(f"{node.n}_{self.literal_index}", literal=node.n)
        node._xir_type = ty
        return ty

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_NameConstant(self, node):
        if node.value == True or node.value == False:
            ty = TyConstant("bool")
        elif node.value is None:
            ty = TyConstant("None")
        else:
            return None

        node._xir_type = ty
        return ty

    def visit_Index(self, node):
        ty = self.visit(node.value)
        node._xir_type = ty
        return ty

    def visit_Subscript(self, node):
        vty = self.visit(node.value)

        if isinstance(node.slice, ast.Index):
            sty = self.visit(node.slice)
        else:
            raise NotImplementedError(f"Don't support non-Index array indices for {node.value}")


        aet = self.get_or_gen_ty_var(f"array_elt_type{self.ret}")
        self.ret += 1

        # TODO: this is really the function call for [], so it must be []: vty * sty -> set
        node._xir_type = TyApp(aet, [sty])

        self.equations.append(TyEqn(vty, TyArray(aet, ['?'])))
        self.equations.append(TyEqn(sty, TyConstant('s32')))

        return aet

    def visit_UnaryOp(self, node):
        self.generic_visit(node)

        if isinstance(node.op, ast.USub):
            fn = f'op_USub'
        elif isinstance(node.op, ast.Not):
            fn = f'op_Not'
        elif isinstance(node.op, ast.Invert):
            fn = f'op_Invert'
        else:
            raise NotImplementedError(f"Unknown unary operator: {node.op}")

        ret, fnt, _, app = self._generate_poly_call_eqns(fn, [node.operand], Def_GenericUnaryOp)
        node._xir_type = fnt

        return ret

    def visit_Call(self, node):
        def _set_fn_node_type(node, fnt):
            node._xir_type = fnt
            if isinstance(node.func, ast.Name):
                # "allow" polymorphism by having each call site use different type variables
                node.func._xir_type = fnt

        def _get_ty_from_fn_call(vararg, signarg, tyarg, widtharg):
            if isinstance(vararg, ast.Name):
                v = vararg.id
            elif isinstance(vararg, ast.Num): # allow some literals? e.g. brev?
                v = self.visit(vararg)
            else:
                raise NotImplementedError(f"Non-literal and non-Name first arguments to set_sign_bitWidth not supported")

            assert isinstance(signarg, ast.NameConstant)
            sign = signarg.value

            assert isinstance(tyarg, ast.Str) # changes in 3.8?
            ty = tyarg.s

            assert isinstance(widtharg, ast.Num) # changes in 3.8?
            width = widtharg.n

            if ty == 'Integer':
                # 8 is for immLut, 128 is for MULWIDE
                assert width in (8, 16, 32, 64, 128), f"Invalid width {width} for Integer"
                fullty = f"{'s' if sign else 'u'}{width}"
            elif ty == 'Float':
                assert width == 32, f"Invalid width {width} for float"
                fullty = f"f{width}"
            elif ty == 'Double':
                assert width == 64, f"Invalid width {width} for double"
                fullty = f"f{width}"
            elif ty == 'Binary':
                assert width in (16, 32, 64), f"Invalid width {width} for Binary"
                fullty = f"b{width}"
            elif ty == 'Pred':
                assert width == 1 , f"Invalid width {width} for Pred"
                fullty = "bool"
            elif ty == 'ConditionCodeRegister':
                fullty = "cc_reg"
            elif ty == "ConditionCodeRegisterRef":
                fullty = TyPtr(TyConstant("cc_reg"))
            else:
                assert False, f"Unrecognized type: {ty}"

            return v, fullty

        fn_name_ty = self.visit(node.func)
        fn = node.func.id if isinstance(node.func, ast.Name) else None

        if fn == 'set_sign_bitWidth':
            v, fullty = _get_ty_from_fn_call(node.args[0], node.args[1],
                                             node.args[2], node.args[3])

            if not isinstance(v, TyTerm):
                tv = self.get_or_gen_ty_var(v)
            else:
                tv = v

            if isinstance(fullty, str):
                self.equations.append(TyEqn(tv, TyConstant(fullty)))
            else:
                self.equations.append(TyEqn(tv, fullty))

            return tv
        elif fn == 'set_value':
            v, fullty = _get_ty_from_fn_call(node.args[2], node.args[0],
                                             node.args[3], node.args[1])
            tv = self.get_or_gen_ty_var(v)
            self.equations.append(TyEqn(tv, TyConstant(fullty)))
            return tv
        elif fn in COMPARE_PTX:
            #TODO: support bool and pred
            # tv = self.get_or_gen_ty_var(fn)
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                           PolyTyDef(["gamma"],
                                                                     TyApp(TyConstant('bool'),
                                                                           [TyVar("gamma"),
                                                                            TyVar("gamma")])))
            _set_fn_node_type(node, fnt)

            return ret
        elif fn in BOOLEAN_OP_PTX:
            # tv = self.get_or_gen_ty_var(fn)
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                           PolyTyDef([],
                                                                     TyApp(TyConstant('bool'),
                                                                           [TyConstant("bool"),
                                                                            TyConstant("bool")])))
            _set_fn_node_type(node, fnt)

            return ret

        elif fn in ARITH_FNS or fn in BITWISE_FNS:
            #note: call is: add(a, b, 'Integer', 16), so there is type information we're not using?
            if fn == 'MULWIDE':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                               Def_MulOp)
            elif fn == 'MUL24':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                               Def_Mul24)
            elif fn == 'FMA':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:3],
                                                               Def_FMAOp)
            elif fn == 'FMA_ROUND' or fn == 'FMA_ROUND_SATURATE':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:4],
                                                               Def_FMARoundOp)
            elif fn == 'RCP_ROUND' or fn == 'SQRT_ROUND':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                               Def_GenericRoundUnaryOp)
            elif fn == "SHR" or fn == "SHL" or fn == "SAR":
                if isinstance(node.args[1], ast.Num):
                    tydecl = Def_ShiftOps_Literal
                else:
                    tydecl = Def_ShiftOps

                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                               tydecl)
            elif fn == "NOT" or fn == "RCP" or fn == "LOG2" or fn == "MACHINE_SPECIFIC_execute_rem_divide_by_zero_unsigned" or fn in ('SINE', 'COSINE') or fn == 'EXP2' or fn == 'RSQRT':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, [node.args[0]],
                                                               Def_GenericUnaryOp)
            elif fn in ROUND_SAT_ARITH_FNS:
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:3],
                                                               Def_GenericRoundBinOp)
            elif fn in CARRY_ARITH_FNS:
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:3],
                                                               Def_GenericCarryBinOp)
            elif fn == 'MACHINE_SPECIFIC_execute_div_divide_by_zero_integer':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:1],
                                                               Def_GenericUnaryOp)
            else:
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:2],
                                                               Def_GenericBinOp)

            _set_fn_node_type(node, fnt)

            return ret
        elif fn in VARARGS_FNS:
            if fn == 'min':
                ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                               PolyTyDef(["gamma"],
                                                                         TyApp(TyVar("gamma"),
                                                                               [TyVar("gamma")]*len(node.args))))
            else:
                raise NotImplementedError(f"Function {fn} not implemented")

            _set_fn_node_type(node, fnt)

            return ret
        elif fn in COMPARE_FNS:
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           Def_GenericCompare)

            _set_fn_node_type(node, fnt)

            return ret
        elif fn in FLOAT_FNS:
            # note: saturate also carries a type, but not a width ...
            argty = self.visit(node.args[0])
            if fn != "ISNAN":
                retty = argty
            else:
                retty = TyConstant("bool")

            _set_fn_node_type(node, TyApp(retty, [argty]))
            return retty
        elif fn == 'set_memory':
            # don't use _generate_poly_call, since this is a variable...
            sm_var = self.get_or_gen_ty_var(fn)
            addrty = self.visit(node.args[0])
            sm_ty = TyApp(TyConstant('void'), [TyConstant('intptr_t'), self.visit(node.args[1])])

            self.equations.append(TyEqn(sm_var, sm_ty))
            self.equations.append(TyEqn(addrty, TyConstant('intptr_t')))

            _set_fn_node_type(node, sm_ty)
            return sm_ty
        elif fn == 'logical_op3':
            res, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:4],
                                                           PolyTyDef([],
                                                                     TyApp(TyConstant('b32'),
                                                                           [TyConstant('b32'),
                                                                            TyConstant('b32'),
                                                                            TyConstant('b32'),
                                                                            TyConstant('u8')])))
            _set_fn_node_type(node, fnt)
            return res
        elif fn == 'subnormal_check':
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, [node.args[0]],
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyConstant('bool'),
                                                                           [TyVar('gamma')]))
                                                           )

            _set_fn_node_type(node, fnt)
            return ret
        elif fn == 'int':
            # int is not treated as a cast
            # fold this into RewritePythonisms?
            return self.visit(node.args[0])
        elif fn == 'zext_64':
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyConstant('u64'),
                                                                           [TyVar('gamma')])
                                                           ))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn.startswith('sext'):
            width = int(fn[fn.rfind("_")+1:])
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyConstant(f's{width}'),
                                                                           [TyVar('gamma')])
                                                           ))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn.startswith('truncate_'):
            width = int(fn[fn.rfind("_")+1:])
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyConstant(f'u{width}'),
                                                                           [TyVar('gamma')])
                                                           ))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn.startswith('ReadByte_') or fn == 'ReadByte':
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyConstant('u32'), # u8
                                                                           [TyConstant('b32'),
                                                                            TyConstant('b64'),
                                                                            TyConstant('b32')])
                                                                     ))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn.startswith('extractAndZeroExt') or fn.startswith('extractAndSignExt'):
            arraysz = int(fn[fn.rindex("_")+1:])
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef([''],
                                                                     TyApp(TyConstant('void'),
                                                                           [TyConstant('u32'),
                                                                            TyArray(TyConstant('u32'),
                                                                                    [arraysz])])))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn.startswith('na_extractAndZeroExt') or fn.startswith('na_extractAndSignExt'):
            # the na versions are non-array versions
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyVar('u32'),
                                                                           [TyConstant('u32'),
                                                                            TyConstant('u8')])))
            _set_fn_node_type(node, fnt)
            return ret

        elif fn == 'range':
            if len(node.args) != 2:
                # though we should support step...
                raise NotImplementedError(f"range with {len(node.args)} not supported")

            if not (isinstance(node.args[0], ast.Num) and isinstance(node.args[1], ast.Num)):
                raise NotImplementedError(f"range with non-constant arguments not supported")

            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args,
                                                           PolyTyDef(['gamma'],
                                                                     TyApp(TyConstant('s32'),
                                                                           [TyConstant('s32'),
                                                                            TyConstant('s32')])))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn == 'float':
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args, Def_GenericUnaryOp)
            _set_fn_node_type(node, fnt)
            return ret
        elif fn == 'BITSTRING':
            assert isinstance(node.args[3], ast.Num), f"BITSTRING needs a constant size: {node.args[3]}"
            arraysz = node.args[3].n
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:1],
                                                           PolyTyDef([''],
                                                                     TyApp(TyArray(TyConstant('b1'),
                                                                                   [arraysz]),
                                                                           [TyConstant(f'b{arraysz}')])))
            _set_fn_node_type(node, fnt)
            return ret
        elif fn == 'FROM_BITSTRING':
            assert isinstance(node.args[1], ast.Num), f"FROM_BITSTRING needs a constant size: {node.args[1]}"
            arraysz = node.args[1].n
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, node.args[:1],
                                                           PolyTyDef([''],
                                                                     TyApp(TyConstant(f'b{arraysz}'),
                                                                           [TyArray(TyConstant('b1'),
                                                                                    [arraysz])])))
            _set_fn_node_type(node, fnt)
            return ret

        fnt = self.get_or_gen_ty_var(f'unknown_fn_{fn if fn else ""}{self.ret}')
        self.ret += 1

        self.generic_visit(node)
        #node._xir_type = fnt
        return fnt

    def visit_IfExp(self, node):
        ret, fnt, depty, _ = self._generate_poly_call_eqns("if_exp",
                                                           [node.test, node.body, node.orelse],
                                                           Def_IfExp)

        node._xir_type = fnt

        #self.equations.append(TyEqn(depty.args[1], depty.args[2]))
        #self.equations.append(TyEqn(fnt.ret, fnt.args[1]))

        return ret

    def visit_Name(self, node):
        v = self.get_or_gen_ty_var(node.id)
        node._xir_type = v
        return v

    def visit_Assign(self, node):
        assert len(node.targets) == 1, "Multiple targets in assign not supported"

        lhs = self.visit(node.targets[0])
        rhs = self.visit(node.value)

        self.equations.append(TyEqn(lhs, rhs))
        # no return because this is a statement

    def visit_AnnAssign(self, node):
        assert node.simple == 1 # TODO

        lhs = self.visit(node.target)
        lhsty = self.anno_to_type(node.annotation.id)
        self.equations.append(TyEqn(lhs, lhsty))

        if node.value is not None:
            rhs = self.visit(node.value)
            self.equations.append(TyEqn(lhs, rhs))

    def visit_Assert(self, node):
        # assert nodes are not type checked
        pass

    def visit_While(self, node):
        assert len(node.orelse) == 0 # not supported

        test = self.visit(node.test)
        for s in node.body:
            self.visit(s)

        self.equations.append(TyEqn(test, TyConstant('bool')))

def infer_types(insn_sem, type_decls = None):
    # generate type equations
    print(astunparse.unparse(insn_sem))
    print(ast.dump(insn_sem))
    eqg = TypeEqnGenerator()
    eqg.visit(insn_sem)
    reps = {}
    #print(eqg.type_variables)
    #print(eqg.equations)

    #for eq in eqg.equations:
    #    print(eq)

    for eq in eqg.equations:
        print(eq)
        if not unify(eq.lhs, eq.rhs, reps):
            for k, v in reps.items():
                print(f"\t{k}: {v}")
            assert False, f"Failed to unify: {eq}"

    if type_decls is not None:
        reps = types_from_decls(eqg, reps, type_decls)

    print("****")
    for v in reps:
        if not isinstance(v, (TyArray, TyProduct)):
            print(v, reps[v])
        else:
            print(v, reps[v], find(reps[v], reps))

    #print("OUT FROM infer", reps)

    return reps

def types_from_decls(eqg, reps, type_decls):
    inct = eqg.call_types
    changed = True

    while changed and len(inct):
        out = []
        changed = False
        for ct in inct:
            fn, fnt, app = ct

            if fn in type_decls:
                arg_reps = [find(x, reps) for x in app.args]
                arg_types = tuple([x.value if isinstance(x, TyConstant) else '?' for x in arg_reps])
                ret_rep = find(app.ret, reps)
                print("==>", fn, fnt, app)
                print("   ", ret_rep, arg_types)

                if arg_types not in type_decls[fn]:
                    if '?' in arg_types: # we don't the types of some arguments
                        out.append(ct)
                    else:
                        print(f"WARNING: No type declaration for {fn}: {' * '.join(arg_types)} found. Either a type declaration is missing or there is a type error in the arguments.")

                    continue

                if isinstance(ret_rep, TyConstant):
                    assert ret_rep.value == type_decls[fn][arg_types], f"{fn}: {' * '.join(arg_types)} -> {ret_rep.value} is invalid, return type must be '{type_decls[fn][arg_types]}'"
                else:
                    if not unify(app.ret, TyConstant(type_decls[fn][arg_types]), reps):
                        assert False, f"Failed to unify from declaration {fn}: {' * '.join(arg_types)} -> {type_decls[fn][arg_types]}"
                    else:
                        print("    return-type", find(app.ret, reps))
                        changed = True

        inct = out

    return reps

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Run various bits of xir on a semantic")
    p.add_argument('semfile', help="File containing executable semantics for XIR")
    p.add_argument('task', help="Task to perform", choices=['types'])
    p.add_argument('ptxinsn', nargs="+", help="PTX instruction in underscore form (e.g. add_u16)")

    args = p.parse_args()
    gl, semantics = extract_ex_semantics.load_execute_functions(args.semfile)

    rp = RewritePythonisms()

    if args.task == 'types':
        if len(args.ptxinsn) == 1 and args.ptxinsn[0] == 'all':
            args.ptxinsn = [k[len("execute_"):] for k in semantics]

        for pi in args.ptxinsn:
            sem = semantics["execute_" + pi]
            rp.visit(sem)

            infer_types(semantics["execute_" + pi], type_decls = TYPE_DECLS)
            print(f"**** TYPES OKAY {pi}")

