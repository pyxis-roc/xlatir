# The Translatable Intermediate Representation (XIR)

XIR, packaged as Python package `xlatir`, is a restricted dialect of
Python a la RPython. The primary purpose of XIR is to serve as a
vehicle for specification of instruction set semantics that can be
translated to other languages. Currently translations to C and SMT-LIB
are supported.

XIR is still in heavy development, and in particular, bears vestiges
of the time it was used to develop instruction set semantics for the
PTX GPU virtual ISA. Eventually, XIR will become more general purpose.

To install:

```
  python3 setup.py develop --user
```

Note: this does not yet install the binaries into some `bin` directory
accessible from the path.


## XIR dialects

There are several XIR dialects. All of them are syntactically
compatible with Python3. However, some dialects of XIR support
additional features like macros and templates which make them
semantically incompatible with Python3. The tool `xirconvert.py` can
convert programs written in these dialects to the plain XIR dialect
which strives to be semantically compatible with Python3.

## Libraries

Plain XIR does not support any Python operators beyond (AST) `Call`,
`Subscript`, and `Attribute` (see `xirsyntax.py` for the definitive
syntax definition).

Therefore, all operations such as addition, subtraction must be
performed using function calls. Since XIR is typed, declarations for
these functions are provided by a "standard library" (`xirstdlib.pyi`)
that accompanies XIR. For the most part, these declarations uses
mypy-style type annotations. However, there are extensions (e.g. for
constant-size array declarations) that are not recognized by mypy.

Additional functionality beyond standard operators can be added by
defining ISA-specific libraries.

Currently the supported base types are hardcoded (see
`xlatir.xir.usrlib`) and cannot be specified by the user, though
mypy-style aliases are supported and strongly encouraged.

It is intended that the semantics for library functions be
user-definable. Currently, this is not the case.


## Examples

A simple definition: [eBPF in XIR](https://github.com/pyxis-roc/ebpf-xir).

The PTX definition in XIR -- TODO.

