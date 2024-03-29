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
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT


import ast
import argparse
from collections import namedtuple
import astunparse
from .xirtyping import *
import itertools
import logging
from .typeparser import AppropriateParser
from .astcompat import AC
from .xirtyerrors import SubsTy

logger = logging.getLogger(__name__)

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
                                                     TyConstant("carryflag")]))


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

BITWISE_FNS = set(['AND', 'SHR', 'SAR', 'OR', 'SHL', 'XOR', 'NOT', 'SHR_LIT', 'SAR_LIT', 'SHL_LIT'])
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
                assert len(node.args) == 2, f"_xir_unroll requires two arguments"
                assert isinstance(node.args[1], ast.Num), f"_xir_unroll second argument must be a numeric literal, not {node.args[1]}"

                # left over from when _xir_unroll was a standalone hint
                self._unroll_factor = node.args[1].n
                return node.args[0]
            else:
                raise NotImplementedError(f"Unknown XIR hint: {n}")

        return node

    def visit_While(self, node):
        # should be okay since we never transform this node
        self.generic_visit(node)

        if self._unroll_factor is not None:
            node._xir_unroll_factor = self._unroll_factor
            self._unroll_factor = None

        return node

    def handle_hints(self, node):
        self._unroll_factor = None
        self.visit(node)

class RewritePythonisms(ast.NodeTransformer):
    desugar_boolean_xor = True
    elim_x_value = False
    add_fn_suffixes = False

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

    # unused, delete after verification
    # def _add_rounding(self, n):
    #     if isinstance(n.func, ast.Name) and "_ROUND" in n.func.id: #TODO: make a full list?
    #         assert isinstance(n.args[-1], ast.Str), f"Expecting last argument of ROUND function to be a string"
    #         roundModifier = n.args.pop().s
    #         n.func.id = n.func.id.replace('_ROUND', '_ROUND_' + roundModifier)

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
                if self.add_fn_suffixes:
                    return self.add_fn_suffix(node)
                else:
                    return node
            elif node.func.id.startswith('extractAndSignOrZeroExt'):
                # TODO: get rid of this
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
                # TODO: get rid of this
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
                # TODO: get rid of this
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
            elif node.func.id == 'int':
                return node.args[0] # don't support int as a type cast
            elif node.func.id == 'range':
                if len(node.args) != 2:
                    # though we should support step...
                    raise NotImplementedError(f"range with {len(node.args)} not supported")

                if not (isinstance(node.args[0], ast.Num) and isinstance(node.args[1], ast.Num)):
                    raise NotImplementedError(f"range with non-constant arguments not supported")
            elif node.func.id in ('SHL', 'SHR', 'SAR'):
                # TODO: get rid of this
                node = self.generic_visit(node)
                #TODO: the greater than is because of PTX...
                assert len(node.args) >= 2, f"{node.func.id} needs two arguments" 
                if isinstance(node.args[1], ast.Num):
                    node.func.id = node.func.id + "_LIT"
            elif node.func.id == 'BITSTRING':
                node = self.generic_visit(node)
                assert isinstance(node.args[3], ast.Num), f"BITSTRING needs a constant size: {node.args[3]}"
                node.func.id += "_" + str(node.args[3].n)
            elif node.func.id == 'FROM_BITSTRING':
                node = self.generic_visit(node)
                assert isinstance(node.args[1], ast.Num), f"FROM_BITSTRING needs a constant size: {node.args[1]}"
                node.func.id += "_" + str(node.args[1].n)
            elif self.elim_x_value and node.func.id == 'set_value':
                # TODO: get rid of this
                # ptx relies on set_value to set type on argument, once
                # type annotations are on _global_*, we can get rid of self.noptx
                # get rid of set_value, since it's not needed
                return node.args[2]
            elif self.elim_x_value and node.func.id == 'get_value':
                node = self.generic_visit(node)
                # get rid of get_value, since it's not needed
                return node.args[2]
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
    def __init__(self, user_decls = None, trim_args_ptxcompat = False):
        self.type_variables = {}
        self.equations = []
        self.call_types = [] # track function call and argument types
        self.ret = 0
        self.literal_index = 0
        self.fn = None
        self.declarations = {} if user_decls is None else user_decls
        self.local_decls = {} # for local declarations, TODO: replace declarations and local declarations with a proper scoped declarations implementation
        self.stats = {'totalfns': 0, 'usrlibfns': 0, 'unkfns': 0}
        self.typedecl = None # deprecated
        self.typeenv = None
        self.xsrc = None
        self._appp = None

        # disregard excess arguments (sign, type, width annotations) when generating type equations
        self.trim_args_ptxcompat = trim_args_ptxcompat
        self.ptx_compat = self.trim_args_ptxcompat

    def set_src_info(self, xsrc, typeenv):
        self.xsrc = xsrc
        self.typeenv = typeenv
        self._appp = AppropriateParser(self.typeenv, self.xsrc)

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
            # PTX compat
            if node.attr == 'cf':
                # TODO: connect cc_reg's type to cc_reg.cf type without messing up carryflag
                node._xir_type = self.get_or_gen_ty_var('cc_reg.cf')
                return node._xir_type
        else:
            vty = self.visit(node.value)

            assert isinstance(vty, TyVar)
            aty = self.get_or_gen_ty_var(f'{vty.name}.{node.attr}')
            node._xir_type = aty

            rty = TyRecord(None, [(node.attr, aty)])
            self.equations.append(TyEqn(vty, rty))

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
        # This needs to be separated out into a common type annotation parser
        if isinstance(anno, ast.Name):
            if anno.id == 'pred': # TODO: width?
                ty = TyConstant("bool")
            elif anno.id == 'cc_reg_ref':
                ty = TyPtr(TyConstant("cc_reg"))
            else:
                if self.typedecl and anno.id in self.typedecl.TypeAliases:
                    ty = TyConstant(self.typedecl.TypeAliases[anno.id])
                else:
                    #TODO: only allow a list!
                    ty = TyConstant(anno.id)
        elif isinstance(anno, ast.Subscript):
            if isinstance(anno.value, ast.Name) and anno.value.id == 'Callable':
                if isinstance(anno.slice.value, ast.Tuple) and len(anno.slice.value.elts) == 2:
                    argtypes = anno.slice.value.elts[0]
                    ret = anno.slice.value.elts[1]

                    assert isinstance(argtypes, ast.List), f"Expecting List as first argument of Callable (... not supported)"
                    assert isinstance(ret, AC.isNameConstant) or isinstance(ret, ast.Name), f"Expecting constant/name as return type"

                    argtypes = [self.anno_to_type(a) for a in argtypes.elts]
                    ret = self.anno_to_type(ret)
                    ty = TyApp(ret, argtypes)
                else:
                    raise SyntaxError(f"Callable syntax incorrect: {anno}")
            else:
                raise NotImplementedError(f"Unimplemented subscript type: {ast.dump(anno)}")
        elif isinstance(anno, AC.isNameConstant):
            assert AC.value(anno) is None, f"Only None supported in type: {anno}"
            ty = TyConstant('void')
        else:
            raise NotImplementedError(f"Don't know how to handle type annotation {anno}/{anno.__class__}")

        return ty

    def anno_to_type_2(self, anno):
        ty = self._appp.parse(anno)
        if isinstance(ty, TyConstant):
            if ty.value == 'pred':
                return TyConstant('bool')
            elif ty.value == 'cc_reg_ref':
                return TyPtr(TyConstant('cc_reg')) # PTXism

        return ty

    def visit_FunctionDef(self, node):
        self.local_decls = {}

        for a in node.args.args:
            t = self.get_or_gen_ty_var(a.arg)
            a._xir_type = t
            if a.annotation is not None:
                aty = self.anno_to_type_2(a.annotation)
                if isinstance(aty, TyApp):
                    assert a.arg not in self.local_decls, f"Duplicate local declaration for argument {a.arg}"
                    #TODO: this doesn't work now because it is parsed incorrectly
                    if any([isinstance(x, TyVar) for x in aty.args]) or isinstance(aty.ret, TyVar):
                        raise NotImplementedError(f'Do not support type variables (type literals only) in Callable')

                    self.local_decls[a.arg] = aty

                self.equations.append(TyEqn(t, aty))

        ret = self.get_or_gen_ty_var(f"fn_{node.name}_retval")
        fnty = TyApp(ret, [a._xir_type for a in node.args.args])
        node._xir_type = fnty

        if node.returns:
            rty = self.anno_to_type_2(node.returns)
            self.equations.append(TyEqn(ret, rty))

        # not supported
        assert node.args.vararg is None
        assert node.args.kwarg is None

        node._xir_return = False

        self.fn = node
        #x = self.generic_visit(node) # this visits annotations too ...
        #print("x == ", x)
        for x in node.body:
            self.visit(x)

        self.fn = None

        if not node._xir_return:
            logging.debug(f'Function {node.name} has no return statement, returning void')
            self.equations.append(TyEqn(node._xir_type.ret, TyConstant('void')))

        return None

    def visit_Tuple(self, node):
        if self.ptx_compat:
            return TyProduct([self.visit(e) for e in node.elts])
        else:
            raise SyntaxError(f"Tuples are not supported")


    def visit_Return(self, node):
        if node.value:
            tyv = self.visit(node.value)
        else:
            tyv = TyConstant('void')

        #TODO: multiple return values need a product type
        self.equations.append(TyEqn(tyv, self.fn._xir_type.ret))
        self.fn._xir_return = True

    def _generate_poly_call_eqns(self, fn, args, typedef):
        ret = self.get_or_gen_ty_var(f"ret{self.ret}")
        fnt = self.get_or_gen_ty_var(f"{fn}:{self.ret}") # this is polymorphic ops

        subst = {}
        for uqv in typedef.uqvars:
            uqt = self.get_or_gen_ty_var(f"{uqv}:{self.ret}")
            subst[uqv] = uqt.name

        self.ret += 1

        arg_types = [self.visit(a) for a in args]

        if isinstance(typedef.typedef, TyApp):
            assert len(arg_types) == len(typedef.typedef.args), f"Number of parameters in typedef ({len(typedef.typedef.args)}) for {fn} does not match those in call ({len(args)})"
        else:
            raise NotImplementedError(f'Do not know how to handle PolyTyDef without TyApp')

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
        assert False, f"Should not occur in XIR"

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

    def _visit_Literal(self, node):
        value = AC.value(node)

        if value is True or value is False:
            ty = TyConstant("bool")
        elif value is None:
            ty = TyConstant("None")
        elif isinstance(value, (str, int, float)):
            ty =  self.get_or_gen_ty_var(f"{value}_{self.literal_index}", literal=value)
        else:
            raise NotImplementedError(f"Unknown literal {node} with value {value}")
            return None

        node._xir_type = ty
        return ty

    def visit_Str(self, node): # 3.6
        return self._visit_Literal(node)

    def visit_Num(self, node): # 3.6
        return self._visit_Literal(node)

    def visit_Constant(self, node):
        return self._visit_Literal(node)

    def visit_Expr(self, node):
        return self.visit(node.value)

    def visit_NameConstant(self, node): # 3.6
        return self._visit_Literal(node)

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
        #assert False, f"Should not happen in XIR" # can happen since xir supports 'not'

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

        self.stats['totalfns'] += 1

        if fn not in self.declarations and fn not in self.local_decls:
            logger.warning(f"Missing declaration: {fn}")
        else:
            if fn in self.local_decls:
                declty = self.local_decls[fn]
            else:
                declty = self.declarations[fn]

            if isinstance(declty, TyApp):
                #TODO: local_decls can't be polymorphic yet ...
                declty = PolyTyDef([], declty.copy())
            elif isinstance(declty, PolyTyDef):
                pass
            else:
                raise NotImplementedError(f'Do not handle declaration type {declty} for {fn}')

            args = node.args[:len(declty.typedef.args)] if self.trim_args_ptxcompat else node.args
            ret, fnt, _, _ = self._generate_poly_call_eqns(fn, args, declty)
            _set_fn_node_type(node, fnt)
            if fn in self.local_decls:
                logging.info(f'local decl: {fn}')
            else:
                logging.info(f'usrlib: {fn}')
                self.stats['usrlibfns'] += 1
            return ret

        fnt = self.get_or_gen_ty_var(f'unknown_fn_{fn if fn else ""}{self.ret}')
        self.ret += 1
        self.stats['unkfns'] += 1
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

        if node.id in self.typeenv.constants:
            self.equations.append(TyEqn(v, self.typeenv.constants[node.id][0]))

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
        lhsty = self.anno_to_type_2(node.annotation)
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

def infer_types(insn_sem, type_decls = None, user_decls = None, stats = None, noptx = False, typeenv = None, xsrc = None):
    # generate type equations
    print(astunparse.unparse(insn_sem))
    print(ast.dump(insn_sem))
    eqg = TypeEqnGenerator(user_decls = user_decls, trim_args_ptxcompat = not noptx)

    if typeenv or xsrc:
        assert xsrc is not None, f"xsrc must be specified if typeenv is specified"
        assert typeenv is not None, f"typeenv must be specified if xsrc is specified"
        eqg.set_src_info(xsrc, typeenv)

    eqg.visit(insn_sem)

    if stats is not None:
        for k, v in eqg.stats.items():
            stats[k] = stats.get(k, 0) + v

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

            dbgty = SubsTy()
            print("***** TYPED AST")
            print(astunparse.unparse(dbgty.rewrite(insn_sem, reps)))
            assert False, f"Failed to unify: {eq}"

    if False:
        # for debugging
        dbgty = SubsTy()
        print("***** TYPED AST")
        print(astunparse.unparse(dbgty.rewrite(insn_sem, reps)))
        assert False, f"Test failed to unify: {eq}"

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

def get_record_decl(recordty, typeenv):
    def match(t1, t2):
        # this is really a "silent" unify

        if isinstance(t1, TyConstant) and isinstance(t2, TyConstant):
            return t1 == t2
        elif (isinstance(t1, TyVar) or isinstance(t2, TyVar)):
            assert False, f'Cannot resolve type variables in get_record_decl: {t1}, {t2}'
        else:
            # neither of them is a TyVar
            raise NotImplementedError(f"Can't match {t1} and {t2}")

            #elif isinstance(t1, TyProduct) and isinstance(t2, TyProduct):
            #return len(t1.args) == len(t2.args) and all([match(x, y) for x, y in zip(t1.args, t2.args)])

    if recordty.name is not None:
        assert recordty.name in typeenv.type_constants, f'Unknown record type "{recordty.name}"'
        return TyConstant(recordty.name)

    # find all records containing the fields
    rfields = dict(recordty.fields_and_types)
    candidates = []

    rd = typeenv.record_decls
    for r in rd:
        if all([f in rd[r].field_names for f in rfields]):
            candidates.append(rd[r])

    # weed out based on types
    candidates2 = []
    for crd in candidates:
        crdf = dict(crd.fields_and_types)
        if all([match(crdf[f], rfields[f]) for f in rfields]):
            candidates2.append(crd)

    if len(candidates2) == 0:
        print(f"Unable to find record declaration for {recordty}")
    elif len(candidates2) > 1:
        print(f"ERROR: Multiple record declarations match {recordty}: {candidates2}")
        return None
    else:
        return candidates2[0]

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
