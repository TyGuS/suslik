# SynSL

Synthesis of heap-manipulating programs from Separation Logic specs

## Setup and Build

### Requirements 

* JDK 1.8
* `sbt` (version >0.13.0)
*  `CVC4` SMT solver (version 1.5), available [here](http://cvc4.cs.stanford.edu/web/)
*  `Z3` SMT solver, available [here](https://github.com/Z3Prover/z3)

### Compiling malformed dependencies

In order to use `scalasmt`, its dependency `expect-for-scala-1.0.2-SNAPSHOT` needs to be installed manually as follows:

```
git clone git@bitbucket.org:franck44/expect-for-scala.git
git checkout cbf01454c35612e8fe43688330da240df3e18fbb .
sbt publishLocal
```


### Building the project

To compile and run the test suitetest, execute from the root folder of the project:

```
sbt test
```

