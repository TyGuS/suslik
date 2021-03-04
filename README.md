# PLDI 2021 Artifact

## Getting Started

This artifact is distirbuted as a VirtualBox VM image. We use [VirtualBox 6.1](https://www.virtualbox.org/wiki/Downloads).

Open the image in VirtualBox, start the VM, and gog in with 
```
user: osboxes
password: osboxes.org
```

Here is a quick test if the artifact is working (this should take *less than a minute*).
Open terminal and execute:
```
cd ~/suslik
python2 evaluation.py --tiny
```

This should produce the following output (times might differ slightly):
```
Running src/test/resources/synthesis/cyclic-benchmarks/sll/free2.syn 1.8s
Running src/test/resources/synthesis/cyclic-benchmarks/multi-list/free.syn 1.8s
Running src/test/resources/synthesis/cyclic-benchmarks/tree/free2.syn 3.6s
Running src/test/resources/synthesis/cyclic-benchmarks/rose-tree/free.syn 1.7s
``` 

## Step by Step Instructions

These instructions detail how to:

1. Reproduce the results reported in Sec 5, Table 1 (evaluating Cypress on benchmarks with _complex recursion_)
2. Reproduce the results reported in Appendix C, Table 1 (evaluating Cypress on benchmarks with _simple recursion_)
3. Run Cypress on individual synthesis problems
4. Rebuild Cypress from sources inside the VM

### Structure of the Artifact

The source code for this artifact can be found in the [pldi21-artifact](https://github.com/TyGuS/suslik/tree/pldi21-artifact) branch of the SuSLik github repository.

Inside the VM, the code is located in `~/suslik`. Inside this directory:
- `evaluation.py` is the Python script to replicate the evaluation in the paper
- `src/test/resources/synthesis/cyclic-benchmarks` contains the benchmarks with complex recursion
- `src/test/resources/synthesis/simple-benchmarks` contains the benchmarks with simple recursion
- `src/main/scala/org/tygus/suslik` contains the source code of Cypress

### Reproducing Evaluation Results

#### Complex Benchmarks

To reproduce the results on _complex benchmarks_ (as defined in Sec 5), execute:
```
cd ~/suslik
python2 evaluation.py
```
This will run Cypress on all benchmarks from Table 1 (Sec 5), apart from benchmark 5 `intersection`, which is reported there as failing (see more details below).
This should take approximately *five minutes*.

After the script terminates, it will create two output files in `~/suslik`:
- `complex.csv` contains results reported in Table 1
- `all_resutls` contains the synthesized programs

To inspect the results in a table form, you can execute:
```
pretty_csv complex.csv
```

#### Simple Benchmarks

To reproduce the results on _simple benchmarks_, execute:
```
cd ~/suslik
python2 evaluation.py --simple
```
This will run Cypress on all benchmarks from Appendix C, apart from the really long running benchmark `BST: delete root` (see more details below).
This should take approximately *five minutes*.

After the script terminates, it will create two output files in `~/suslik`:
- `simple.csv` contains Cypress results reported in Appendix C, Table 1 (For SusLik results, see the [suslik paper](https://cseweb.ucsd.edu/~npolikarpova/publications/suslik.pdf))
- `all_resutls` contains the synthesized programs

To inspect the results in a table form, you can execute:
```
pretty_csv simple.csv
```

#### Comparing Execution Times

We noticed roughly a *2x overhead* of running Cypress inside the VM
(hence, you should expect synthesis times to be twice as long as those reported in the paper).

In addition, the synthesis times reported by the script are measured by Cypress itself
and do not account for the JVM start-up time,
which is a constant overhead for each benchmark.
For the paper, we ran the whole evaluation in a single JVM instance, using the scala testing framework,
which avoids this startup overhead.
For the purposes of artifact evaluation, we provide a Python script instead,
which has the overhead but offers more flexibility and transparancy.
To observe the behavior without the constant overhead, you can run scala tests for complex benchmarks using:
```
sbt testOnly org.tygus.suslik.synthesis.CyclicBenchmarks
```
and for simple benchmarks using
```
sbt testOnly org.tygus.suslik.synthesis.SimpleBenchmarks
```
Note, however, that this will run all benchmarks from eiter category, including the long-running ones (see discussion below).

#### Long-Running Benchmarks

Executing:
```
cd ~/suslik
python2 evaluation.py --all
```
will execute all benchmarks, that is, both complex and simple, including the longer-running benchmarks `instersection` and `BST: delete root`, mentioned above.
This might take *upto an hour*.
This will generate output files: 
- `complex.csv`
- `simple.csv`
- `all_results` with all the synthesized programs

We have excluded these two long-running benchmarks from the normal script modes for convenience,
because these are the only benchmarks that take over a minute to run natively (so, over two minutes on the VM).
In particular, `instersection` takes 4 min,
and `BST: delete root` takes ~45 mins to finish on the VM.

The benchmark `intersection` needs a clarification, which we have made to reviewers during the rebuttal.
Originally, we have a tried the following _destructive_ specification for this benchmark:
```
{ r :-> x ** ulist(x, s1) ** ulist(y, s2) }
void intersect (loc r, loc y)
{ r :-> z ** ulist(z, s1 * s2) }
```
This version of the benchmark fails, as reported in the submitted version of the paper
because of the limitation on the class of auxiliaries that Cypress can generate.
However, after the submission we realized that Cypress can actually handle the following version of this benchmark,
where one of the original lists is preserved by the procedure:
```
{ r :-> x ** ulist(x, s1) ** ulist(y, s2) }
void intersect (loc r, loc y)
{ r :-> z ** ulist(z, s1 * s2) ** ulist(y, s2) }
```
This version allows Cypress to first recurse on the tail of `x`,
and then check whether the head of `x` is present in `y` and hence whether it should be included in the intersection.
This is the version of `intersect` included in the artifact (and this is the version we intend to present in the camera-ready);
it can be synthesized in two minutes on native hardware (and in four minutes on the VM)

## Setup and Build

### Requirements 

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
* [Scala Build Tool](https://www.scala-sbt.org/), `sbt` (version >=1.1.6)
* [Z3 SMT solver](https://github.com/Z3Prover/z3)
* [CVC4 SMT solver](https://cvc4.github.io/), version 1.7
* [Cyclist Theorem Prover](http://www.cyclist-prover.org/installation)
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
  -t, --timeout <value>    timeout for the derivation; default (in milliseconds): 120000 (2 min)
  -d, --depth <value>      derivation depth; default: 100
  -a, --assert <value>     check that the synthesized result against the expected one; default: false
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
  -p, --printSpecs <value> print specifications for synthesized functions; default: false
  -e, --printEnv <value>   print synthesis context; default: false
  -f, --printFail <value>  print failed rule applications; default: false
  -g, --tags <value>       print predicate application tags in derivations; default: false
  -l, --log <value>        log results to a csv file; default: true
  -x, --auxAbduction <value>
                           abduce auxiliary functions; default: false 
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

### Certification

See the file [certification.md](certification.md) for instructions on certifying the synthesis results. 
