# Synthetic Separation Logic

[![Build Status](https://api.travis-ci.org/TyGuS/suslik.svg?branch=borrows)](https://travis-ci.org/TyGuS/suslik)
[![License](https://img.shields.io/badge/License-BSD%202--Clause-orange.svg)](https://raw.githubusercontent.com/TyGuS/suslik/master/LICENSE)
[![DOI](https://zenodo.org/badge/101061595.svg)](https://zenodo.org/badge/latestdoi/101061595)

Synthesis of Heap-Manipulating Programs from Separation Logic
Specifications

<p align="center">
  <a href = "http://comcom.csail.mit.edu/comcom/#SuSLik"><img src="https://github.com/TyGuS/suslik/blob/master/misc/suslik-logo.png" width="150" height="150"></a>
  </p>

## Theory Behind the Tool

The details of Synthetic Separation Logic can be found in the
[accompanying draft paper](https://arxiv.org/pdf/1807.07022.pdf).

## Usage

The easiest way to try out examples is via the [online demo](http://comcom.csail.mit.edu/comcom/#SuSLik). 

Otherwise, check the building instructions below.

## Setup and Build

### Requirements 

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
* [Scala Build Tool](https://www.scala-sbt.org/), `sbt` (version >=1.1.6)
* [Z3 SMT solver](https://github.com/Z3Prover/z3)
* [Scala](https://www.scala-lang.org/download/) (version >= 2.12.6) - to run the standalone artifact

### Building and Testing the Project

To compile and run the entire test suite (and see some cool synthesis results), execute from the root folder of the project:

```
sbt test
```

### Compiling the Executables

Just run the following from your command line: 

```
sbt assembly
```

As the result, an executable `JAR`-file will be produced, so you can run it as explained below.

## Synthesizing Programs from SL Specifications

Alternatively, once you have built the artifact via `sbt assembly`, you can run 
it as a standalone application (given that the runnable `scala` is in your path).

### Case Studies

At the moment, many interesting case studies can be found in the folder
`$PROJECT_ROOT/examples`. More examples
and benchmarks related to the paper on SSL  are in the folders
`paper-examples` and `paper-benchmarks` under `$PROJECT_ROOT/src/test/resources/synthesis`.

Each set of case studies is in a single folder (e.g., `copy`). The
definitions of inductive predicates and auxiliary function
specifications (lemmas) are given in the single `.def`-file, typically
present in each such folder. For instance, in `examples`, it is
`predicates.def`, whose contents are as follows:

```
predicate lseg(loc x, set s) {
|  x == 0        => { s =i {} ; emp }
|  not (x == 0)  => { s =i {v} ++ s1 ; [x, 2] ** x :-> v ** (x + 1) :-> nxt ** lseg(nxt, s1) }
}

predicate lseg2(loc x, set s) {
|  x == 0        => { s =i {} ; emp }
|  not (x == 0)  => { s =i {v} ++ s1 ; [x, 3] ** x :-> v ** (x + 1) :-> v + 1 ** (x + 2) :-> nxt ** lseg2(nxt, s1) }
}

...
```

The remaining files (`*.syn`) are the actual examples, each
structured in the following format:

```
<A textual comment about what capability of the synthesizer is being assessed.>
#####
<Hoare-style specification of the synthesized procedure in SL>
#####
<Optional expected result>
```

For example, `examples/listcopy.syn` is defined as follows:

```
Copy a linked list

#####

{true ; r :-> x ** lseg(x, 0, S)}
void listcopy(loc r)
{true ; r :-> y ** lseg(x, 0, S) ** lseg(y, 0, S) }

#####

```

### Trying the Synthesis with the Case Studies

To run the synthesis for a specific case study from a specific folder,
execute the following script:

```
suslik fileName [options]
```
where the necessary arguments and options are

```
  fileName                 a synthesis file name (the file under the specified folder, called filename.syn)
  -r, --trace <value>      print the entire derivation trace; default: true
  -t, --timeout <value>    timeout for the derivation; default (in milliseconds): 300000 (5 min)
  -d, --depth <value>      derivation depth; default: 100
  -a, --assert <value>     check that the synthesized result against the expected one; default: true
  -c, --maxCloseDepth <value>
                           maximum unfolding depth in the post-condition; default: 1
  -o, --maxOpenDepth <value>
                           maximum unfolding depth in the pre-condition; default: 1
  -b, --branchAbduction <value>
                           abduce conditional branches; default: false
  --commute <value>        only try commutative rule applications in one order; default: true
  --phased <value>         split rules into unfolding and flat phases; default: true
  --fail <value>           enable early failure rules; default: true
  --invert <value>         enable invertible rules; default: true
  --imm <value>            enable reasoning with RO annotations; default: true   
  --prioImm <value>        prioritize immutable heaps for unification when multiple candidates exist; default: false
  -s, --printStats <value> print synthesis stats; default: true
  -e, --printEnv <value>   print synthesis context; default: false
  -f, --printFail <value>  print failed rule applications; default: false
  -g, --tags <value>       print predicate application tags in derivations; default: false
  -l, --log <value>        log results to a csv file; default: true
  --logFile <value>        log results to a given csv file; default: stats.csv
  --help                   prints this usage text

```

Once the synthesis is done execution statistics will be available in `stats.csv`.

For instance, to synthesize `$PROJECT_ROOT/examples/listcopy.syn` and see the derivation trace, run

```
suslik examples/listcopy.syn
```

to get the following result:

```
void listcopy (loc r) {
  let x2 = *r;
  if (x2 == 0) {
  } else {
    let v2 = *x2;
    let nxt2 = *(x2 + 1);
    *r = nxt2;
    listcopy(r);
    let y12 = *r;
    let y2 = malloc(2);
    *(x2 + 1) = y12;
    *r = y2;
    *(y2 + 1) = nxt2;
    *y2 = v2;
  }
}
```

For running benchmarks or examples from the accompanying paper, run, e.g.,
```
suslik src/test/resources/synthesis/paper-benchmarks/sll/sll-append.syn
``` 

### Trying the Read-Only Annotations

The inductive predicate definitions use de Bruijn-style notation for borrows 
inside their clauses. For example:

```
predicate lseg(loc x, loc y, set s) {
|  x == y        => { s =i {} ; emp }
|  not (x == y)  => { s =i {v} ++ s1 ;
                      [[x, 2]]@0 ** [x :-> v]@1 ** [(x + 1) :-> nxt]@2 ** lseg(nxt, y, s1)[0,1,2] }
}

...
```

The list copy synthesis problem can now be annotated as follows:

```
Copy a linked list with immutable annotations constraints

#####

{true ; r :-> x ** lseg(x, 0, s)[I@a,I@b,I@c]}
void listcopy_v2(loc r)
{true ; r :-> y ** lseg(x, 0, s)[I@a,I@b,I@c] ** lseg(y, 0, s)[M,M,M] }

#####

```

where `M` stands for mutable permission, and 
`I@a` stands for read-only (immutable) permission with the borrow stored in variable `a`.
A mutable points-to is denoted by `z :-> k`, while its immutable counterpart
is denoted by `[z :-> k]@I@a`. A mutable block is denoted by `[x, 2]`, and its 
immutable version is `[[x, 2]]@I@a`.

The read-only annotations are only present in the assertions language. 
The synthesized program doesn't contain such annotations, but their effect can be noticed
in the generated program where no mutation occurs if so is specified: 

```
void listcopy_v2 (loc r) {
  let x2 = *r;
  if (x2 == 0) {
  } else {
    let v2 = *x2;
    let nxt2 = *(x2 + 1);
    *r = nxt2;
    listcopy(r);
    let y12 = *r;
    let y2 = malloc(2);
    *r = y2;
    *(y2 + 1) = nxt2;
    *y2 = v2;
  }
}
```

In comparison, the `listcopy` example 
synthesised earlier contains a spurious write statement `*(x2 + 1) = y12;`, absent in 
`listcopy_v2`. The reasoning using immutability annotation can be switched on or off 
using the `--imm` flag as explained above.

## Reproducing the Evaluation Results (for RO)

Running the performance eval (averages 3 runs of the benchmarks) outputs 
the results in the  `evaluation-utils/stats-performance.csv` file:

```
python3 evaluation-imm.py --performance --n 3
```
 
 
Running the robustness eval:
```
python3 evaluation-imm.py --robustnessUSsll
python3 evaluation-imm.py --robustnessUSsrtl
python3 evaluation-imm.py --robustnessUStree
```
 outputs: `evaluation-utils/robustness-sll.csv`,
    `evaluation-utils/robustness-srtl.csv`, and 
   `evaluation-utils/robustness-tree.csv`, respectively. 


The `evaluation-imm.py` program must be launched from the project's main directory.
