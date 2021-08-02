#!/usr/bin/env python3

import xlatir.xir.xirlibc as xirlibc

def test_ADD():
    x = xirlibc.XIRLibC()
    a1 = xirlibc.c_float()
    a2 = xirlibc.c_float()
    print(x.ADD(a1, a2))

if __name__ == "__main__":
    test_ADD()
