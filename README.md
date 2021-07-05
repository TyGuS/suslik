# Synthetic Separation Logic

[![License](https://img.shields.io/badge/License-BSD%202--Clause-orange.svg)](https://raw.githubusercontent.com/TyGuS/suslik/master/LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1482573.svg)](https://doi.org/10.5281/zenodo.1482573)

Synthesis of Heap-Manipulating Programs from Separation Logic Specifications

<p align="center">
  <a href = "http://comcom.csail.mit.edu/comcom/#SuSLik"><img src="https://github.com/TyGuS/suslik/blob/master/misc/suslik-logo.png" width="150" height="150"></a>
</p>

## Theory Behind the Tool and Corresponding Development Snapshots

The details of Synthetic Separation Logic and its extensions can be found in the following published research papers:

* **[Structuring the Synthesis of Heap-Manipulating Programs](https://dl.acm.org/doi/10.1145/3290385)**  
    Nadia Polikarpova and Ilya Sergey. POPL'19.
  - [Artifact, 10 Nov 2018](https://doi.org/10.5281/zenodo.1482574)
* **[Concise Read-Only Specifications for Better Synthesis of Programs with Pointers](https://link.springer.com/chapter/10.1007/978-3-030-44914-8_6)**  
  Andreea Costea, Amy Zhu, Nadia Polikarpova, and Ilya Sergey. ESOP'20.
  - [Artifact, 29 Jan 2020](https://doi.org/10.5281/zenodo.3630045)
* **[Cyclic Program Synthesis](https://doi.org/10.1145/3453483.3454087)**  
  Shachar Itzhaky, Hila Peleg, Nadia Polikarpova, Reuben Rowe, and Ilya Sergey. PLDI'21
  - [Artifact, 11 Apr 2021](https://doi.org/10.5281/zenodo.4679743)
* **[Certifying the Synthesis of Heap-Manipulating Programs](https://doi.org/10.1145/3473589)**
  Yasunari Watanabe, Kiran Gopinathan, George Pîrlea, Nadia Polikarpova, and Ilya Sergey. ICFP'21
  - [Artifact, 21 May 2021](http://doi.org/10.5281/zenodo.5005829)
  
## Benchmark Statistics

The most up to date statistics on the benchmarks can be found under the folder `cav21-artifact`:

* `stats_all.csv` contains all benchmarks associated with the CAV'21 tutorial 
  **Deductive Synthesis of Programs with Pointers: Techniques, Challenges, Opportunities**
* `gen-table-all.py` is a script that generates the LaTeX table with the results (requires Python 2.7 to run)   

## Online Interface

The easiest way to try out basic examples is via the [online demo](http://comcom.csail.mit.edu/comcom/#SuSLik). 

However, this will only work with examples of the first version of the tool (0.1, of 10 Nov 2018). For later versions
and more advanced examples please check the artifacts referred above or follow the building instructions below. 

## Setup and Build

### Requirements 

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
* [Scala Build Tool](https://www.scala-sbt.org/), `sbt` (version >=1.1.6)
* [Z3 SMT solver](https://github.com/Z3Prover/z3) (version >= 4.8.9)
* [CVC4 SMT solver](https://cvc4.github.io/), version 1.7 (precise version is important!)
* [Cyclist Theorem Prover](http://www.cyclist-prover.org/installation)
* [Scala](https://www.scala-lang.org/download/) (version >= 2.12.6) - to run the standalone artifact

### Compiling the Executables

Just run the following from your command line: 

```
sbt assembly
```

As the result, an executable `.jar`-file will be produced, so you can run it as explained below.

### Generating Latest Benchmark Results

Run from the command line

```
sbt "testOnly org.tygus.suslik.synthesis.ChallengeTests"
```

Alternatively, you can run the test suite `ChallengeTests` from an IDE.  

In both cases, this will run the most complete suite, generating the file `stats.csv` in the root of the project with all
the benchmark data.

### Testing the Project

To run the entire test suite, execute from the root folder of the project:

```
sbt test
```

## Synthesizing Programs from SL Specifications

Alternatively, once you have built the artifact via `sbt assembly`, you can run 
it as a standalone application (given that the runnable `scala` is in your path).

### Case Studies

At the moment, many interesting case studies can be found in the folder
`$PROJECT_ROOT/examples`. More examples
and benchmarks can be found under `$PROJECT_ROOT/src/test/resources/synthesis/all-benchmarks`.

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
./suslik fileName [options]
```
where the necessary arguments and options are

```
  fileName                 a synthesis file name (the file under the specified folder, called filename.syn)
  -r, --trace <value>      print the entire derivation trace; default: false
  -t, --timeout <value>    timeout for the derivation; default (in milliseconds): 300000 (5 min)
  -a, --assert <value>     check that the synthesized result against the expected one; default: false
  -c, --maxCloseDepth <value>
                           maximum unfolding depth in the post-condition; default: 1
  -o, --maxOpenDepth <value>
                           maximum unfolding depth in the pre-condition; default: 1
  -f, --maxCallDepth <value>
                           maximum call depth; default: 1
  -x, --auxAbduction <value>
                           abduce auxiliary functions; default: false
  --topLevelRecursion <value>
                           allow top-level recursion; default: true
  -b, --branchAbduction <value>
                           abduce conditional branches; default: false
  --maxGuardConjuncts <value>
                           maximum number of conjuncts in an abduced guard; default: 2
  --phased <value>         split rules into unfolding and flat phases; default: true
  -d, --dfs <value>        depth first search; default: false
  --bfs <value>            breadth first search (ignore weights); default: false
  --delegate <value>       delegate pure synthesis to CVC4; default: true
  -i, --interactive <value>
                           interactive mode; default: false
  -s, --printStats <value>
                           print synthesis stats; default: false
  -p, --printSpecs <value>
                           print specifications for synthesized functions; default: false
  -e, --printEnv <value>   print synthesis context; default: false
  --printFail <value>      print failed rule applications; default: false
  -l, --log <value>        log results to a csv file; default: false
  -j, --traceToJsonFile <value>
                           dump entire proof search trace to a json file; default: none
  --memo <value>           enable memoization; default: true
  --lexi <value>           use lexicographic termination metric (as opposed to total size); default: false
  --certTarget <value>           set certification target; default: none (options: htt | vst | iris)
  --certDest <value>             specify the directory in which to store the certificate file; default: none
  --certHammerPure <value>       use hammer to solve pure lemmas instead of admitting them (HTT only); default: false
  --certSetRepr <value>          use SSReflect's perm_eq to represent set equality (HTT only); default: false
  --help                   prints this usage text

```

Once the synthesis is done execution statistics will be available in `stats.csv`.

For instance, to synthesize `$PROJECT_ROOT/examples/listcopy.syn` and see the derivation trace, run

```
./suslik examples/listcopy.syn
```

to get the following result:

```
void listcopy (loc r) {
  let x = *r;
  if (x == 0) {
  } else {
    let v = *x;
    let n = *(x + 1);
    *r = n;
    listcopy(r);
    let y1 = *r;
    let y = malloc(2);
    *r = y;
    *(y + 1) = y1;
    *y = v;
  }
}
```

For running advanced examples from the accompanying test suite, execute, e.g.,
```
./suslik src/test/resources/synthesis/all-benchmarks/sll/append.syn
``` 

## Certification

Please refer to `certification.md` for information on certifying the synthesis results.
