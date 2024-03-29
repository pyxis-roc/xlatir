#
# xirbuiltin.pyi
#
# Provides the type declarations for standard XIR/Imp functionality
# that replaces Python functionality.
#
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT
#
# SPDX-Contributor: Sreepathi Pai

from typing import TypeVar, List

T = TypeVar('T')
T1 = TypeVar('T1')
T2 = TypeVar('T2')

# Add | Sub | Mult | Div | Mod | Pow
def ADD(a: T, b: T) -> T: ...
def SUB(a: T, b: T) -> T: ...

# allow result to be of a different (usually wider) type for MUL
def MUL(a: T1, b: T1) -> T2: ...

def DIV(a: T, b: T) -> T: ...
def IDIV(a: T, b: T) -> T: ... #TODO: restrict to integer types?
def MOD(a: T, b: T) -> T: ...
def POW(a: T, b: T) -> T: ...

Tshift = TypeVar('Tshift')

# keep the types for value and shift different, and let backends patch
# up type issues for now -- smt-lib requires both to be of the same
# width, for example.

# Currently when a literal is supplied for s, it is set to the same
# type as T in the old code, possibly best implemented as SHL_LIT and
# SHR_LIT? Or make this into a generic rule?

# LShift | RShift
def SHL(v: T, s: Tshift) -> T: ...
def SHR(v: T, s: Tshift) -> T: ...

# BitOr | BitXor | BitAnd
def OR(v: T, s: T) -> T: ...
def XOR(v: T, s: T) -> T: ...
def AND(v: T, s: T) -> T: ...

# Invert
def NOT(v: T) -> T: ...

# Eq | NotEq | Lt | LtE | Gt | GtE
def EQ(a: T, b: T) -> bool: ...
def NOTEQ(a: T, b: T) -> bool: ...
def LT(a: T, b: T) -> bool: ...
def LTE(a: T, b: T) -> bool: ...
def GT(a: T, b: T) -> bool: ...
def GTE(a: T, b: T) -> bool: ...

# builtins
def abs(v: T) -> T: ...
def bool(v: T) -> bool: ...
#def max(*args: List[T]) -> T: ...
# max, min, pow?

# sext, zext and truncate
