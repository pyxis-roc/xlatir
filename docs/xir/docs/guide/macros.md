<!--
SPDX-FileCopyrightText: 2021,2023 University of Rochester

SPDX-License-Identifier: MIT
-->

# XIR Macros

Unlike Python, XIR supports macros to prevent repetitive work. While
XIR Macros remain syntactically Python, they have no equivalent in
Python. There is a recent proposal for Python Macros [PEP638] and we
_may_ adopt that syntax in the future.

The `xirconvert.py` utility acts as a preprocessor to expand the
macros used in your specifications.

## Definition

XIR macros are written as Python functions with an `@xirmacro`
decorator. There are three main kinds of macros. Although macros can
"call" other macros, recursion is not supported.

Both expression macros and statement macros are purely syntactic.

Template macros support partial evaluation, but provide limited
support for typing so polymorphic dispatch may not work.

XIR macros work by replacing macro arguments with the _AST structures_
provided as arguments.

### Expression Macros

An expression macro expands into a Python expression. It consists of a
macro definition that contains only one expression. It must be used in
an expression context.

```python
@xirmacro
def mmax(a, b):
    a if a > b else b
```

This can be used as a normal function call:

```python
def use_mmax(x: b32, y: b32):
    return mmax(x+1, y)
```

which will expand to (using `xirconvert.py --xm`):

```python
def use_mmax(x: b32, y: b32):
    return (ADD(x, 1) if GT(a, b) else y)
```

Note here that Python operators were converted to XIR function
calls. This isn't inherent to the macro implementation, but rather a
side-effect of `xirconvert.py`.

### Statement Macros

A statement macro expands into a block of Python statements. It must
be invoked in a statement context.

```python
@xirmacro
def generic_cond_branch(a, b, op, pc, offset):
    if op(a, b):
        pc += offset

    return pc
```

This can be used as follows:

```python
def branch_lte(a, b, pc, offset):
    generic_cond_branch(a, b, LTE, pc, offset)

def branch_gt(a, b, pc, offset):
    generic_cond_branch(a, b, GT, pc, offset)
```

This will expand to:

```python
def branch_lte(a, b, pc, offset):
    if LTE(a, b):
        pc = ADD(pc, offset)
    return pc

def branch_gt(a, b, pc, offset):
    if GT(a, b):
        pc = ADD(pc, offset)
    return pc
```

Note that macro definitions and calls must be syntactically valid
Python before substitution, so more sophisticated token manipulation
is not possible.

### Template Macros

[Still in design phases, not implemented]

Template macros generate function definitions. In addition, they will
support partial evaluation.

Template macros are defined exactly like statement or expression
macros, but they are invoked at the global level:

```python
@xirmacro
def generic_cond_fn(a: T, b: T, op, pc, offset):
    if op(a, b):
        pc += offset
    return pc

branch_lte = generic_cond_fn(op = LTE, T = s32)
```

This should yield:

```python
def branch_lte(a: s32, b: s32, pc, offset):
    if LTE(a, b):
        pc += offset
    return pc
```

TODO: maybe template macros should be defined like decorators returning a function?
This would significantly ease handling of template parameters vs
function parameters. So the above would be:

```python
@xirmacro
def generic_cond_fn(fn, T, op):
    def fn(a: T, b: T, pc, offset):
        if op(a, b):
            pc += offset
        return pc

generic_cond_fn(branch_lte, s32, LTE)
```

and would yield the same output.

## Bugs

The most serious bug that can be encountered with the current
`xirmacros.py` implementation is unintentional capture of variables in
the calling context.

## Design Thoughts

TODO.

use global to identify variables that should not be changed

rename all local variables to MACRO_coord_[varname]

use eval to indicate stuff that should be evaled?

use format strings to enable quasi-quoting/multi-stage?


