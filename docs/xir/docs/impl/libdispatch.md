# Introduction

XIR functions are translated to native functions based on the name of
the function and its types:

```
('ADD', 'f32', 'f32')

```

This usually gets sent in as:
```
('ADD', 'float', 'float')
```

to CLib and SMTLib for dispatch from `xirxlat.visit_Call`

CLib and SMTLib usually look up a dictionary to figure out the actual
call based on the types and return an expression.

What we want to support is a user-extensible library with the same
functionality.

## xirclib and xirsmtlib

For xirstdlib compilation.


## ptxclib and ptxsmtlib

For ptxstdlib compilation.

## Specifying lookups

Currently:

('ADD', '*', '*') = '+'




