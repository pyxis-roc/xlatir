# Welcome to the XIR documentation

The Translatable Intermediate Representation (XIR) project is a toolkit for the specification of instruction-set semantics.
The goal is to produce interpreters, verifiers, test suites, etc. from a single easy-to-write specification.
XIR was developed to specify the instruction set semantics for NVIDIA's virtual ISA called PTX.
It is now being used to specify other instruction sets as well.

XIR is a work in progress, with features being added on as-needed basis. Please create an issue on GitHub if you encounter shortcomings.

## Installation

Clone the [xlatir package](https://github.com/pyxis-roc/xlatir) from
GitHub and run `python3 setup.py develop --user`.


## Getting Started with XIR

XIR syntax is a strict subset of Python, but its semantics are subtly different. Read the [Introduction to XIR](intro/) to understand the differences.


## XIR Reference

  * [XIR Classes](classes)
