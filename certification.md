# Certified Synthesis

Generation of correctness certificates for synthesized programs. Currently, we support HTT as the certification backend.

## HTT

### Examples

Visit the [`ssl-htt`](https://github.com/yasunariw/ssl-htt) repository to see examples of generated certificates.

### Requirements

- [Coq](https://coq.inria.fr/) (>= "8.10.0" & < "8.12~")
- [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.11~")
- [FCSL PCM library](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")
- [HTT](https://github.com/TyGuS/htt)
- [CoqHammer](https://coqhammer.github.io)
- [SSL-HTT](https://github.com/TyGuS/ssl-htt)

### Building Definitions and Proofs

We recommend installing with [OPAM](https://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes
opam pin add coq-ssl-htt git+https://github.com/TyGuS/ssl-htt\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-htt coq-hammer coq-ssl-htt
```

### Running Synthesis with Certification

Add the following flags to run synthesis with certification.

- `--certTarget <value>`: Currently supports value `htt`.
- `--certDest <value>` (optional): Specifies the directory in which to generate a certificate file. Logs output to console if not provided.

For example, the following command produces a HTT certificate of the specification `listfree.syn`, and logs its contents to the console.

```bash
./suslik examples/listfree.syn --assert false --certTarget htt
```

By providing the `--certDest` flag, SuSLik writes out this certificate as a file to the specified directory. The following example command writes a HTT certificate named `listfree.v` to the project root directory.

```bash
./suslik examples/listfree.syn --assert false --certTarget htt --certDest .
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
