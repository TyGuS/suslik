# Certified Synthesis

Generation of correctness certificates for synthesized programs. Currently, we support Coq as the certification backend.

## Coq

### Requirements

- [Coq](https://coq.inria.fr/) (>= "8.9.0" & < "8.12~")
- [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.11~")
- [FCSL PCM library](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")
- [HTT](https://github.com/TyGuS/htt)

### Building Definitions and Proofs

For Coq requirements available on [OPAM](https://opam.ocaml.org/doc/Install.html), we recommend installing with it:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-htt
```

Before verifying a generated Coq certificate, make sure to compile the predefined tactics by running `make clean && make` in the directory `certification/coq`. Each generated Coq certificate adds this physical directory to the load path of Coq, and then maps it to the logical directory `SSL`.

### Running Synthesis with Certification

Add the following flags to run synthesis with certification.

- `--certTarget <value>`: Currently supports value `coq`.
- `--certDest <value>` (optional): Specifies the directory in which to generate a certificate file. Logs output to console if not provided.

For example, the following command produces a Coq certificate of the specification `listfree.syn`, and logs its contents to the console.

```bash
./suslik examples/listfree.syn --assert false --certTarget coq
```

By providing the `--certDest` flag, SuSLik writes out this certificate as a file to the specified directory. The following example command writes a Coq certificate named `listfree.v` to the project root directory.

```bash
./suslik examples/listfree.syn --assert false --certTarget coq --certDest .
```

### Viewing The Trace

This package extracts the successful derivations from the synthesis process into a tree structure, for post-hoc access to information needed for certification.

A standalone representation of this tree can be printed via the the following flags.

- `--printTree <value>`: Set to `true` to enable printing.
- `--treeDest <value>` (optional): Specifies the path to output the tree as a file. If not provided, logs output to console instead. 

For example, the following command logs the tree to a file called `trace.out` in the project root directory.

```bash
./suslik examples/listfree.syn --assert false --printTree true --treeDest trace.out
```
