#!/usr/bin/env python3
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT


import xlatir.xir.xirlibc as xirlibc

def test_NOT():
    x = xirlibc.XIRBuiltinLibC()
    a1 = xirlibc.c_float()
    print(x.NOT(a1))

    a1 = xirlibc.c_bool()
    print(x.NOT(a1))

    a1 = xirlibc.uint32_t()
    print(x.NOT(a1))

def test_ADD():
    x = xirlibc.XIRBuiltinLibC()
    a1 = xirlibc.c_float()
    a2 = xirlibc.c_float()
    assert x.ADD(a1, a2) == "+"

if __name__ == "__main__":
    test_ADD()
    test_NOT()
