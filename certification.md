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
