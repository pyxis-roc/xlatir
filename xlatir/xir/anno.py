#!/usr/bin/env python3
#
# anno.py
#
# XIR annotations/decorators for use in xir code.
#
# Since these are checked for syntactic equivalence, they _must_ be
# used thus:
#
# from xlatxir.xir.anno import *

def xirmacro(f):
    """Indicate that a function is an XIR macro.

       If the function contains a single expression, it is an expression macro.

       Otherwise it is treated as a statement macro."""

    return f

def xirdecl(f):
    """Indicate that the function should be treated as declaration of a
       user-defined library function and made available during type
       checking to other functions.

       You can also use mypy stub syntax instead of this decl.

       def fn(a: somety) -> othertype: ...
    """

    return f

def xirignore(f):
    """Indicate that the function should be ignored during translation."""

    return f
