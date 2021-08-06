# Types in XIR

This is preliminary documentation on using types in XIR.

## Built-in types (or Type Constants)

As vestiges of PTX, the following types are supported in XIR right now.

  - `uX`, unsigned X-bit integer, where X is one of 8, 16, 32, 64, 128
  - `sX`, signed X-bit integer.
  - `bX`, unsigned X-bit bitvectors, interchangeable with `uX`.
  - `f32`, 32-bit floating point
  - `f64`, 64-bit floating point

## Type Variables

The standard Python `typing.TypeVar` syntax can be used to create type variables:

```python
T = TypeVar('T')
```

XIR ignores _all_ arguments to `TypeVar`. It only looks at the LHS of
the assignment and recognizes it as a type variable in all type
expressions from now on.

## Polymorphism

The use of type variables permits declaring polymorphic functions:

```python
def ADD(a: T, b: T) -> T: ...
```

Not that the types of *each* call of `ADD` are resolved independently.

Currently, the XIR backends cannot compile polymorphic functions
except those in libraries, and even then the only polymorphic
functions supported are those that are in `xirbuiltins.pyi` and
`ptxlib.pyi`. Support for monomorphizing polymorphic functions will be
added in later versions of the XIR compiler.

## Type Casting

XIR does not perform implicit type casts. All type casts must be explicit.

There are no type casting functions provided by default, you should
specify them as part of your standard library.

Here are some definitions of type casting functions used in the PTX definition:

```python
def zext_32(a: T) -> u32: ...

def sext_32(a: T) -> s32: ...

def truncate_32(a: T) -> b32: ...
```

Currently, the compilers recognize the above functions as "special"
and make sure the value of `T` makes sense (i.e. its width is less
than or equal to `T` for the extension functions, and greater than or
equal to `T` for the `truncate` function). This will change in the
future to support user-defined constraints on type casting functions
that you define.

## Type Expressions

Type expressions are used to denote a particular type. The syntax is a
subset of mypy, with a few non-compatible additions.


```
TypeExpr := TypeConstant | ArrayType | CallableType | TypeAlias | TypeVariable

# not supported by mypy, constant size arrays
ArrayType := TypeExpr '[' dimension_size (',' dimension_size)* ']'

CallableType := 'Callable' '[' '[' TypeExpr (',' TypeExpr ')'* ']' ',' TypeExpr ']'

dimension_size := [0-9]+

TypeConstant := None | declared-types

TypeVariable := declared-type-variables
```

Currently, the compiler does not support multi-dimensional arrays.


## Type Aliases

A type alias is like a `typedef` in C. It is specified as follows:

```python
alias = type
```

A type is a valid type expression used in a type annotation.

Note: type aliases have a similar syntax to specifying globals. For example:

```
T = 1
A = T
```

declares `T` and `A` to be global constants, however `A = T` is also
(syntactically) a type alias.

In such cases, the default rule is to parse `A = T` as a type alias
and if it fails (because `T` is not a type expression), to _silently_
treat it as a global. Currently none of the backends support globals,
but when they do this will probably be fixed.

## Creating New Types

[Still in design phase, not implemented]

To create new types, the plan is to use syntax like below:

```python
b32 = BitVector(32)
```

To make parsing easier and distinguish easily between type aliases,
globals, etc., we might want to use syntax like this:

```python
b32: type = BitVector(32)
```

where `BitVector` is XIR internal type metaclass.  This is different
from mypy which uses `NewType`.


### Product data types

Currently, the XIR compilers will create a product data type whenever
they encounter 2-element tuples in the definitions:

```python
return (a, b)
```

Depending on the types of `a` and `b` this will instantiate a subtype of `Pair` (in the SMT backend) or a particular named structure (in the C backend).

This is deprecated and will be removed, especially since the following syntax is _not_ supported in XIR:

```python
x = (a, b)
y = x[0]
```

### Structures

XIR allows definitions of structures like so:

```python
class ArithWithCarry(Generic[T]):
    sum: T
    carry: b1
```

Then:

```python
class u32_carry(ArithWithCarry[u32]):
    pass

def ADD_CARRY_u32(a: u32, b: u32) -> u32_carry:
    # accesses will use attribute notation
    #
    # if x is of type u32_carry:
    #
    # x.sum, x.carryflag
    #
    return u32_carry(sum, carryflag)

```

Read more in the [documentation on classes](../classes).

### Recursive Data Types

Currently, recursive data types are not supported.

### Unions

Currently, unions are not supported.
