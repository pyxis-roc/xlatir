<!--
SPDX-FileCopyrightText: 2021,2023 University of Rochester

SPDX-License-Identifier: MIT
-->

# Compiler Libraries

By default, a function call in XIR is translated into a function call by the compiler backend (i.e. C or SMT2).
A _compiler library_ allows a IR designer to hook into the backend and control the translation of function calls.
This feature is used by the `xirbuiltins.pyi` library to translate function calls like `ADD(a, b)` to `a + b` in C or `(fp.add a b)` in SMT2, for example.

To use this feature for your own IR, you need to:

   1. Define a compiler library implementation in _Python_ (since the XIR compiler is built in Python) for each backend.
   2. Load the implementation during translation of XIR programs.


## Defining a compiler library

A compiler library is a Python module that contains:

   1. A `Lib` class that descends from `xlatir.xir.xirlib.XIRLib`.
   2. A function called `get_libs` that returns instantiations of the `Lib` classes.

A simple and complete example would be the following code:

```python
from xlatir.xir.xirlib import XIRLib

class SomeLibC(XIRLib):
      def get_dispatch_types(self, fnty, xirty):
          return fnty

      def BINARYFN(self, aty, bty):
          if aty == 'uint32_t':
              return lambda x, y: f"BF_u32({x}, {y})"
          else:
              return NotImplementedError(f"BINARYFN({aty}, {bty}) not implemented.")

def get_libs(backend):
    if backend == "c":
        return [SomeLibC()]

    return []
```

This code will override the C translation of `BINARYFN`.
The C backend (in `xir2c.py`) will examine the libraries loaded looking for a method called `BINARYFN`.
The types of the arguments (here, `aty` and `bty`) are then passed to this method, if found.
The method must return a function, an _AST constructor_, with the same number of arguments as the function being translated.

The argument to the AST constructor will be the ASTs of each of the function's arguments and the return value must be an AST itself specifying the translation.
The structure of ASTs depends on the backend. For the C backend, ASTs are currently plain Python strings.
So the AST constructor for the C backend is a function that returns a string when given strings for each of its arguments.

In the example above, `BINARYFN` examines the types and if the type is `uint32_t`, it translates it to `BF_u32`, otherwise it prevents the translation by raising a `NotImplementedError`.
The `BF_u32` AST constructor is a lambda function with two (string) arguments that returns a string as well.

The `get_dispatch_types` function allows you to convert the types used by the backend (i.e. strings in the C backend) to alternative forms for more advanced implementations.
In this example, the function is a no-op, returning the input function type.

Concisely, the class translates function calls based on types of the arguments in the XIR source code.


## Loading the compiler library

To load and use the library, use the `-b` flag on `xir2x.py`.

```shell
xir2x.py -b /path/to/module ...
```

The library for XIR builtins is loaded automatically. You can override this library, see the `xir2x.py` command-line documentation.

Multiple libraries can be specified, and are looked up in the order they were specified on the
command line, and the first successful translation is used by the compiler.

Note: `xir2x.py` always loads the XIR builtin library first, so it cannot be overriden.

## Implementation design of a compiler library

Using some new Python features (specifically, `singledispatch`), it is possible to let Python do the type-based dispatch instead of cluttering up the code with `if` statements.

Look at the implementation of the XIR builtins library in `xirlibc.py` or in the PTX XIR specification (in `ptxlib.py` and `ptxlibc.py`).

## Limitations

Currently, only the C backend supports compiler libraries. The SMT2 backend will soon follow.

