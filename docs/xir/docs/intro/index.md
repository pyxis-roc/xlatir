# Introduction to the XIR Specification Language

The XIR Specification Language is used to specify the semantics of
instructions. The syntax for XIR is a strict subset of Python 3,
however its semantics are different. These differences are summarized
below.

### XIR is typed

XIR is a typed language, with *one type per variable*. Developers do not
need to specify the type for each variable, since XIR uses type
inference. The only expected type annotations are on the arguments
to a function.

```python
def EBPF_MUL(a: b32, b: b32):
    return MUL(a, b)
```

The type annotations are mostly a _subset_ of the mypy type
syntax, but include non-mypy constructs as well. TODO: document these.

For those familiar with type inference in other languages, literals in
XIR do _not_ have a default type. In certain circumstances, this may
require type hints to be specified:

```python
a: u32 = 0
```

XIR should be able to infer the types for everything else. TODO: type inference documentation.

For now, XIR supports a set of types derived from the PTX types. In
the near future, it will allow the specification of custom types.

### XIR does not support Python arithmetic and bitwise operators

Specifications cannot use the the Python operators `+`, `-`,
etc. Instead, they must call functions instead:

  - `ADD` for +
  - `MUL` for *
  - and so on.

The full list of functions is in `xirbuiltins.pyi`. However, since it
is very inconvenient to use these functions manually, it is
recommended instead that specifications be developed in two-step
process. In the first step, the specification is written using normal
Python syntax, and in the second step the XIR is produced using the
`xirconvert.py` tool.


### XIR syntax is a proper subset of Python

XIR does not support all Python constructs. The `xirconvert.py` tool
can perform a syntax check and alert you to unsupported syntax.

### XIR supports macros

Unlike Python, XIR supports [syntactic macros](../macros) to ease the work of semantics engineering.
