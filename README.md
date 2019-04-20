# VFCR - Virtual Function Call Resolver
---
[![GRC Lab IIT Bombay](https://img.shields.io/badge/GRC%20Lab-IIT%20Bombay-blue.svg)](http://www.cse.iitb.ac.in/grc/) 
___

### What is it?

It is a LLVM out-of-tree pass, that used flow-sensitive, demand-driven bi-directional alias analysis for resolving virtual function calls in C++.

### What it does?

It tries to reduce the number of element in the callee set of a virtual function call.

### How to use it?

Dependecy: https://github.com/reSHARMA/LLVM-IR-Plus-Plus 
Use it directly with opt 

> I'll update this readme with more details soon! 
