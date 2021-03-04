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
- `all_results` contains the synthesized programs

To inspect the results in a table form, you can execute:
```
pretty_csv complex.csv
```

The text file `all_results` should contain the same synthesized code as reported in Appendix C.
In addition to the code itself, for your information we also print out the inferred specifications of the auxiliary functions,
however those might contain internal _cardinatlity variables_ and assertions over those 
(see line 417 in the paper for an explanation of what they are).

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

### Running on Individual Benchmarks

To run Cypress on `file.syn`, you can execute `suslik file.syn` from `~/suslik`.
For example, to run the tree flattening example from the intro, execute:
```
suslik src/test/resources/synthesis/cyclic-benchmarks/tree/flatten.syn
```
(Note that due to changes to the cost function, 
the solution Cypress currently synthesizes is different from the one presented in the Overview, 
but is nevertheless correct).

### Rebuilding from Source on the VM

To build Cypress from scratch in a new location `<dir>` on our VM, execute:
```
cd <dir>
git clone git@github.com:TyGuS/suslik.git .
git checkout pldi21-artifact
sbt assembly
```

## Building Cypress from Sources

This section contains instructions on building Cypress from sources _outside the VM_.
Note that Cypress has a lot of prerequisites, so this process is quite time-consuming.

Cypress can be built on Linux, Mac, or on Windows under WSL.

### Prerequisites 

To build Cypress:

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
* [Scala Build Tool](https://www.scala-sbt.org/) `sbt`, version >=1.1.6
* [Z3 SMT solver](https://github.com/Z3Prover/z3), version >=4.8.7
* [CVC4 SMT solver](https://cvc4.github.io/), version 1.7
* [Cyclist Theorem Prover](http://www.cyclist-prover.org/installation)

To run the evaluation script:

* Python 2.7
* `colorama` package

### Building the Project

Once all the prerequisites have been installed, you can build a `jar` by running from the root directory of the repo:
```
sbt assembly
```

To run the `jar` on an input file `file.syn`, execute the following from the root directory of the repo:

```
java -jar ./target/scala-2.12/suslik.jar file.syn
```

