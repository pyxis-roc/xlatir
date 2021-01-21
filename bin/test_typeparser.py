#!/usr/bin/env python3

from xlatir.xir.typeparser import *
from xlatir.xir.xirsrc import *
from xlatir.xir.xirtyping import *

import ast

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description='Load declarations and parse using typeparser constructs')
    p.add_argument('xirimp', help='XIR library')

    args = p.parse_args()

    xs = XIRSource()
    xs.load(args.xirimp)

    te = TypeEnv()
    ap = AssignmentParser(xs)
    te.type_constants.add('b1')
    te.type_constants.add('u8')
    te.type_constants.add('u16')
    te.type_constants.add('u32')
    te.type_constants.add('u64')
    te.type_constants.add('b16')
    te.type_constants.add('b32')
    te.type_constants.add('b64')
    te.type_constants.add('s16')
    te.type_constants.add('s32')
    te.type_constants.add('s64')
    te.type_constants.add('f32')
    te.type_constants.add('f64')
    te.type_constants.add('carryflag')
    te.type_constants.add('cc_reg_ref')
    te.type_constants.add('cc_reg')
    te.type_constants.add('bool')
    te.type_constants.add('pred')
    te.type_constants.add('intptr_t')
    for s in xs.ast.body:
        if isinstance(s, ast.Assign):
            try:
                a = ap.parse(s)
                if isinstance(a, TyAlias):
                    te.type_aliases[a.name] = a.value
                else:
                    te.type_vars[a.name] = a
            except XIRSyntaxError as e:
                print(e)
        elif isinstance(s, ast.FunctionDef):
            tep = TypeExprParser()
            print(ast.dump(s))
            for a in s.args.args:
                print("annotation", tep.parse(a.annotation, te, xs))

            for st in s.body:
                # only handles top-level statements for now
                if isinstance(st, ast.AnnAssign):
                    print(ast.dump(st))
                    print("assign-annotation", tep.parse(st.annotation, te, xs))
