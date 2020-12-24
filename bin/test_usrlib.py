#!/usr/bin/env python3

from xlatir.xir.usrlib import *

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description='Load declarations and generate xirtyping constructs')
    p.add_argument('xirimp', help='XIR/Imp library')

    args = p.parse_args()

    decls = load_xir_declarations(args.xirimp)
    d2t = Decl2Type()
    for d in decls:
        print(d2t.from_FunctionDef(d))
