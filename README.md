# SynSL

[![Build Status](https://travis-ci.org/TyGuS/synsl.svg?branch=master)](https://travis-ci.org/TyGuS/synsl)
[![License](https://img.shields.io/badge/License-BSD%202--Clause-orange.svg)](https://raw.githubusercontent.com/TyGuS/synsl/master/LICENSE)

Synthesis of Heap-Manipulating Programs from Separation Logic Specifications

## Setup and Build

### Requirements 

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
* [Scala Build Tool](https://www.scala-sbt.org/), `sbt` (version >=1.1.6)
* [Z3 SMT solver](https://github.com/Z3Prover/z3)

### Building the Project

To compile and run the entire test suite, execute from the root folder of the project:

```
sbt test
```

## Synthesizing Programs from SL Specifications

### Case Studies

At the moment, many interesting case studies can be found in the folder
`$PROJECT_ROOT/src/test/resources/synthesis`.

Each set of case studies is in a single folder (e.g., `copy`). The definitions
of inductive predicates and auxiliary function specifications (lemmas) are given
in the single `.def`-file, typically present in each such folder. For instance,
in `paper-examples`, it is `predicates.def`, whose contents are as follows:

```
predicate lseg(loc x, loc y, set s) {
|  x == y        => { s =i {} ; emp }
|  not (x == y)  => { s =i {v} ++ s1 ; [x, 2] ** x :-> v ** (x + 1) :-> nxt ** lseg(nxt, y, s1) }
}

predicate lseg2(loc x, set s) {
|  x == 0        => { s =i {} ; emp }
|  not (x == 0)  => { s =i {v} ++ s1 ; [x, 3] ** x :-> v ** (x + 1) :-> v + 1 ** (x + 2) :-> nxt ** lseg2(nxt, s1) }
}
```

The remaining files (`*.syn`) are the test cases, each
structured in the following format:

```
<A textual comment about what capability of the synthesizer is being assessed.>
#####
<Hoare-stule specification of the synthesized procedure>
#####
<Expected result>
```

For example, `paper-examples/19-listcopy.syn` is defined as follows:

```
Example (19) from the paper (listcopy)

#####

{true ; r :-> x ** lseg(x, 0, S)}
void listcopy(loc r)
{true ; r :-> y ** lseg(x, 0, S) ** lseg(y, 0, S) }

#####

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
    *y2 = v2;
    *(y2 + 1) = nxt2;
    *r = y2;
    *(x2 + 1) = y12;
  }
}
```

### Trying the Synthesis with the Case Studies

To run the synthesis for a specific case study from `src/test/resources/synthesis`,
execute the following script:

```
sbt "test:runMain org.tygus.synsl.synthesis.SynthesisTestRunner folder testname [[printTrace] [checkResult]]"
```

* `folder` - a folder under `src/test/resources/synthesis`
* `testname` - the name of a file in that folder, without the `.syn` extension

The last two input arguments are  optional boolean flags:

* `printTrace` - print the entire derivation trace. Default: `true`.
* `checkResult` - check that the synthesized result matches what's in the last part of the test file. Default: `false`.

For instance, to synthesize `paper-examples/19-listcopy.syn`, run

```
sbt "test:runMain org.tygus.synsl.synthesis.SynthesisTestRunner paper-examples 19-listcopy"
```

You can add your own folders and test cases into that folder.

## Troubleshooting

Coming soon.
