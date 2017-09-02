# Project Roadmap

## Immediate fixes

* [DONE] Do not generate spurious loads, which are later unused
    - [DONE] Implement visitor for statements
* Make rule querying uniform (no more canonicalize fiddling)
* Support for pointer types
* Type inference for ghosts (right now it's a dummy int)

## Synthesis machinery

* Support for inductive predicates
* Support for conditionals
* Third-party functions

## Infrastructure

* Interpreter for imperative programs
* Randomized tesing (via ScalaCheck) based on specifications
* Simple SL-based analysis (i.e., bi-abduction etc)
* Integration with the existing tools for spatial reasoning:
    - Infer (Calcagno et al.)
    - CVC4 (Tinelli et al.)
    - Grasshopper (Wies et al.)
    - Cyclist (Brotherston et al.) 