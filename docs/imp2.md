# Imperative to Functional v2

The `imp2func_ssa` (or `imp2func2` or simply `imp2`) package converts
"imperative" code (without side effects) to functional code. The first
version of this package could only handle basic blocks (no control
flow) and used value numbering to produce an expression tree. This
version can handle control flow, and is based on the article by Appel
[1]. The basic idea is to convert branches to function calls, using a
correspondence between branches and functions surfaced by SSA
phi-functions.

The imperative code is passed in as a list of list of S-expressions,
whose syntax is documented below. Additional information on the types
of variables, and the names of global variables may need to be
provided. As output, the package can produce Python3 code in
functional form, as well as SMT2-LIB code.

The produced functional code can be in _nested_ form, with variables
implicitly passed between functions as part of the enclosing scope, or
in _linear_ form with variables passed explicitly as
parameters. Notably, some backends (e.g. SMT2-LIB) do not support the
nested form and will always produce linear form.

The `imp2` package can be used from the command-line or through its
API. However, as of this release, a Python package is not provided.

# Example Usage

Here is an example input to `imp2func_ssa`:

```
(global PT RZ)
(param z x x2)
(type x2 (_ BitVec 32))
(type x (_ BitVec 32))
(type z (_ BitVec 32))
(label lbl0008)
(= r1 c_0x0_0x20)
(label lbl0010)
(= R6 c_0x0_0x158)
(label lbl0018)
(= R7 c_0x0_0x15c)
(label lbl0028)
(= R6 z)
(label lbl0030)
(= R2 c_0x0_0x148)
(label lbl0038)
(= R3 c_0x0_0x14c)
(label lbl0048)
(= R10 x)
(type R10 (_ BitVector 32))
(label lbl0050)
(= R4 c_0x0_0x150)
(label lbl0058)
(= R5 c_0x0_0x154)
(label lbl0068)
(= P0 (FSETP.GE.AND PT R6 RZ PT))
(type P0 (_ BitVec 1))
(label lbl0070)
(cbranch (= P0 #b1) lbl0080 lbl0078)
(label lbl0078)
(cbranch (= P0 #b0) lbl0078_1 lbl0080)
(label lbl0078_1)
(= R10 x2)
(label lbl0080)
(label lbl0088)
(= R8 c_0x0_0x140)
(label lbl0090)
(= R9 c_0x0_0x144)
(label lbl0098)
(= R10 1)
(type R10 (_ BitVec 64))
(return R10)
(label lbl00a8)
(label lbl00b0)
(branch lbl00b0)
(label lbl00b8)
(branch lbl00b8)
```

Here are several things worth noting:

  1. Each line or statement is an S-expression.
  2. The `global` statement, if present, must be the first statement in the
     input and denotes symbols that are imported from the global
     scope.
  3. The `param` statement lists the order of parameters for the entry
     function for the linear form. If it appears, it must be the first
     statement or immediately follow the `global` statement.
  4. The `type` statement provides a mechanism to provide inline type
     information about the symbol specified in the second
     argument. The type is opaque to `imp2`. Only the SMT2 backend
     makes use of this information, so far.
  5. The `label` statement identifies branch targets, for loops and conditionals.
  6. The assignment `=` statement assigns the value of an expression to a variable.
  7. The `cbranch` statement specifies a conditional branch.
  8. The `branch` statement specifies an unconditional branch.
  9. The `return` statement specifies a value to return.

Note the example contains two unreachable loops.

To compile this to functional form, you would run:
```
imp2func_ssa.py example.xir --backend python --linear --prefix example
```

which will yield the linear form:
```
def lbl0078_1(): # let_levels=[], captured_params=[]
  return lbl0080()

def lbl0078(P0_0): # let_levels=[], captured_params=['P0_0']
  return lbl0078_1() if (P0_0 == 0b0) else lbl0080()

def example_EXIT(_retval_0): # let_levels=[], captured_params=['_retval_0']
  return(_retval_0)

def lbl0080(): # let_levels=[['R10_2'], ['_retval_0']], captured_params=[]
  R10_2 = 1
  _retval_0 = R10_2
  return example_EXIT(_retval_0)

def example_label_2(P0_0): # let_levels=[], captured_params=['P0_0']
  return lbl0080() if (P0_0 == 0b1) else lbl0078(P0_0)

def example_label_1(z, x, x2): # let_levels=[['R6_1', 'R10_0'], ['P0_0']], captured_params=['z', 'x', 'x2']
  R6_1 = z
  R10_0 = x
  P0_0 = FSETP.GE.AND(PT, R6_1, RZ, PT)
  return example_label_2(P0_0)

def example_START(z, x, x2): # let_levels=[], captured_params=['z', 'x', 'x2']
  return example_label_1(z, x, x2)
```

Or alternatively, the nested form obtained using `imp2func_ssa.py example.xir --backend python  --prefix example`:

```
def example_START(): # let_levels=[], captured_params=['x2', 'x', 'z']
  def example_label_1(): # let_levels=[['R6_1', 'R10_0'], ['P0_0']], captured_params=['x2', 'x', 'z']
    R6_1 = z
    R10_0 = x
    P0_0 = FSETP.GE.AND(PT, R6_1, RZ, PT)
    def example_label_2(): # let_levels=[], captured_params=['P0_0']
      def lbl0078(): # let_levels=[], captured_params=['P0_0']
        def lbl0078_1(): # let_levels=[], captured_params=[]
          return lbl0080()

        return lbl0078_1() if (P0_0 == 0b0) else lbl0080()

      def lbl0080(): # let_levels=[['R10_2'], ['_retval_0']], captured_params=[]
        R10_2 = 1
        _retval_0 = R10_2
        def example_EXIT(): # let_levels=[], captured_params=['_retval_0']
          return(_retval_0)

        return example_EXIT()

      return lbl0080() if (P0_0 == 0b1) else lbl0078()

    return example_label_2()

  return example_label_1()
```

Using `--backend smt2` will produce SMT2 form, which implies `--linear`.

# Statement Reference

## The no-op `()` statement

Syntax: `()`

The `()` is the no-op statement and will be ignored.

## The `global` statement

Syntax: `(global symbol1 symbol2 ...)`

The symbols listed after `global` are treated as global references --
not as parameters. Usually, these are common symbols you define and
use.

Note this also includes symbols from an SMT2-LIB theory. So, for
example, the symbols `+oo`, `RTP`, etc. from floating point must also
be included if you use them.

In the future, SMT2-LIB theory symbols may be automatically
supported. Patches are welcome.

## The `param` statement

Syntax `(param param1 param2 ...)`

Specifies the order of parameters in the entry function of the linear
form.

Note the API provides a more generic way to build the entry function,
including more complex naming mechanisms.

## The `type` statement

Syntax: `(type symbol typeexpr)`

Specifies the type of `symbol` as `typeexpr`.

Must appear _after_ the first write to `symbol` unless the symbol is a
parameter.

Types can also be specified via the API.

The `type` statement was introduced to handle specification of types
for variables whose types may change during execution. This is not
ideal, but can be found in some ISAs that use the same register names
to store floating point and integer valued variables.

The `imp2` package requires that a variable have the same type in all
the nodes of the CFG it dominates. Importantly, it will refuse to
compile if the definitions that reach a `phi` statement have different
types.

Note that `imp2` uses the SSA form where writes that are dead beyond
their basic blocks do not place `phi` functions in dominance frontier
nodes. A future implementation may also elide `phi` functions for
writes that are dead at their dominance frontier.

## The assignment statement

### Basic form

Syntax: `(= symbol expr)`

Assigns expression to symbol. The kinds of expressions supported are defined by each backend.

### Deconstructing form

There is no form of `=` which allows assignments to multiple
variables. You must instead break up the assignment thus:

```
(= a_b (f ..))
(= a (first a_b))
(= b (second a_b))
```

### Attribute write form

If you have a variable that has a product type (data-type) and you
want to update only a field, you must use the following form:

```
(= (_xir_attr_ref "member2" variable variable-data-type) expr)
(= variable (mk-type (_xir_attr_ref "member1" variable variable-data-type) (_xir_attr_ref "member2" variable variable-data-type)))
```

In this example, the `member2` field is updated to `expr` by the first
statement, and then the variable is reconstructed using the values of
the other fields using the type's constructor `mk-type`.

This syntax is subject to change in the future.

## Labels

Syntax: `(label symbol)`

Identifies a label as a target for `branch` and `cbranch`. These are
also used as names of the functions generated, however the `imp2`
package might assign its own generated labels.


## Conditional branches

Syntax: `(cbranch expr label_true label_false)`

Evaluates `expr` and jumps to `label_true` if true, `label_false` otherwise.

Unlike most ISAs, `cbranch` does not fallthrough. Both labels must be
specified.

## Unconditional Branches

Syntax: `(branch label)`

Jumps to `label` unconditionally.

## Return

Syntax: `(return expr)`

Returns `expr` as the value of the code.

The type of `expr` will be inferred, especially if `expr` is a symbol,
but this is not always possible. In this case, specify the type using
`(type _retval typeexpr)` *once* at the top of the input.

The symbol `_retval` is reserved for use by `imp2`.

# Implementation Notes and Limitations

The backends return strings as outputs. In the future, they may return
native ASTs.

Currently, the code produced by `imp2` for basic blocks is "worse"
than `imp1`'s `create_dag` function. This will be fixed in the future.

The code currently does not try to minimize the number of functions
produced for a given control-flow graph.

Loops are not handled correctly by the SMT2 backend.


## SMT2 backend

Since `define-fun-rec` is not well supported and often inhibits model
finding, the SMT2 backend will avoid using it if it can. This is
always possible in a loop-free control-flow graph.

It will revert to using `define-fun-rec` if it detects reachable loops
in the CFG. Note, however, this functionality is currently broken.


[1] Andrew W. Appel, "[SSA is Functional Programming](https://www.cs.princeton.edu/~appel/papers/ssafun.pdf)", ACM SIGPLAN Notices, 1998
