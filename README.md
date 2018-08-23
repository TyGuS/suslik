# Synthetic Separation Logic

[![Build Status](https://travis-ci.org/TyGuS/suslik.svg?branch=master)](https://travis-ci.org/TyGuS/suslik)
[![License](https://img.shields.io/badge/License-BSD%202--Clause-orange.svg)](https://raw.githubusercontent.com/TyGuS/suslik/master/LICENSE)

Synthesis of Heap-Manipulating Programs from Separation Logic
Specifications

<p align="center">
  <a href = "http://comcom.csail.mit.edu/comcom/#SuSLik"><img src="https://github.com/TyGuS/suslik/blob/master/misc/suslik-logo.png" width="150" height="150"></a>
  </p>

## Theory Behind the Tool

The details of Synthetic Separation Logic cand be found in the
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
suslik [options] folder goalName
```
where the necessary arguments and options are

```
  folder                   a folder with the predicate definitions, lemmas, and synthesis goal file
  goalName                 a test case name (the file under the specified folder, called goalName.syn)
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
  -s, --printStats <value> print synthesis stats; default: true
  -e, --printEnv <value>   print synthesis context; default: false
  -f, --printFail <value>  print failed rule applications; default: false
  -g, --tags <value>       print predicate application tags in derivations; default: false
  -l, --log <value>        log results to a csv file; default: true
  --help                   prints this usage text

```

Once the synthesis is done execution statistics will be available in `stats.csv`.

For instance, to synthesize `$PROJECT_ROOT/examples/listcopy.syn` and see the derivation trace, run

```
suslik examples listcopy
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

If you are going to synthesize case studies from the provided set, you may only type the folder under 
`$PROJECT_ROOT/src/test/resources/` (i.e., without the full prefix of the path), e.g.:

```
suslik paper-examples 17-listcopy -r true
```

or 

```
suslik examples swap -r false -t 800
```
 
