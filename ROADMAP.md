# Project Roadmap

## Immediate fixes and extensions

* Add a flag to control logging output? [Ilya]
* Change representation of SFormula to a list of chunks
* Get rid of types (for now)? Maybe two types: loc and int?
* Pick logic for locations and implement proper subsumption of spatial formulas
* Proper syntax for declarations (function signatures, inductive predicates, etc)
* (Fix the parser for pointers to pointer)
* Interpreter for imperative programs

## More expressive SL

* Inductive predicates
    - [DONE] Syntax for the predicate definitions
    - [DONE] Parser for definitions
    - [DONE] Predicate occurrences in spatial formulas
    - [DONE] Enhance parser for spatial formulas
    - Synthesis rules for list-like stuff
      - What are the simples examples?
      - Perhaps, the simplest is deallocation, 
        so we need implementation for `free()`
    - Higher-order list predicates

## Synthesis machinery

* Alloc and free rules
* Connect to pure synthesizer
* Rule for inductive predicates
* Rule for recursive calls
* Rule for calls

## Infrastructure

* Randomized testing (via ScalaCheck) based on specifications
* Simple SL-based analysis (i.e., bi-abduction etc)
* Integration with the existing tools for spatial reasoning:
    - Infer (Calcagno et al.)
    - CVC4 (Tinelli et al.)
    - Grasshopper (Wies et al.)
    - Cyclist (Brotherston et al.) 
    
## Benchmarks

* Destructors
* Examples from natural synthesis paper
* Persistent memory examples (?)
* Something with a complex data structure (snaphottable tree?)
* Something with concurrency
    
## Completed

* [DONE] Do not generate spurious loads, which are later unused
    - [DONE] Implement visitor for statements
* [DONE] Support for pointer types
* [DONE] Make rule querying uniform (no more canonicalize fiddling)
* [DONE] Type inference for ghosts (right now it's a dummy int)
* [DONE] Treatment for points-to assertions with offsets