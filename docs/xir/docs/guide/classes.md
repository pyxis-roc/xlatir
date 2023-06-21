<!--
SPDX-FileCopyrightText: 2021,2023 University of Rochester

SPDX-License-Identifier: MIT
-->

# XIR Classes

XIR supports the Python `class` syntax to specify datatypes similar to
records and structures in other languages.

However, XIR classes are very simple. They cannot be nested or
recursive. They do not support inheritance.

## Basic Structures

The basic XIR structure syntax looks like this:

```python
class Pt:
    x: b32
    y: b32
```

This creates a structure called `Pt` with two members in it `x` and
`y`. You cannot use initializers. While `Pt` can contain methods, they
will be ignored by XIR.

## Using Structures

In declarations, just specify the name of the class.

```python
def get_x(p: Pt) -> b32:
    return p.x
```

You will use Python's dot operator (`.`) to access members of a class.

You can create values using the standard class invocation:

```python
def get_pt(x: b32, y: b32) -> Pt:
    return Pt(x, y)
```

## Generic/Polymorphic Structures

XIR also supports generic classes:

```python
def Pt(Generic[T1]):
    x: T1
    y: T1
```

This creates a class that is parameterized over a type variable
`T1`. You can use it as follows:

```python
def get_x(p: Pt[T]) -> T:
    return p.x
```

During type inference, this will instantiate `T` to a particular type.

The C backend for XIR does not support polymorphic types, so the class
will be monomorphized to `Pt_u32` for example for `Pt[u32]`.

The SMT-LIB backend will generate both a parameteric datatype for `Pt`
as well as an instantiation `Pt_u32` for example.

## Legacy `Pair` is Deprecated

The legacy version of XIR used for specifying PTX would automatically
convert Python tuples into a `Pair` class. This feature is deprecated
and will go away.
