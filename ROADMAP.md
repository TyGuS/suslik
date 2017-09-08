# Project Roadmap

## Immediate fixes and extensions

* Treatment for points-to assertions with offsets
* Interpreter for imperative programs

## More expressive SL

* Inductive predicates
    - [DONE] Syntax for the predicate definitions
    - Parser for definitions
    - Predicate occurrences in spatial formulas
    - Enhance parser for spatial formulas
    - Synthesis rules for list-like stuff
    - Higher-order predicates

## Synthesis machinery

* Support for inductive predicates
* Support for conditionals
* Third-party functions

## Infrastructure

* Randomized testing (via ScalaCheck) based on specifications
* Simple SL-based analysis (i.e., bi-abduction etc)
* Integration with the existing tools for spatial reasoning:
    - Infer (Calcagno et al.)
    - CVC4 (Tinelli et al.)
    - Grasshopper (Wies et al.)
    - Cyclist (Brotherston et al.) 
    
## Completed

* [DONE] Do not generate spurious loads, which are later unused
    - [DONE] Implement visitor for statements
* [DONE] Support for pointer types
* [DONE] Make rule querying uniform (no more canonicalize fiddling)
* [DONE] Type inference for ghosts (right now it's a dummy int)
