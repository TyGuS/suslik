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
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm
```

For HTT, clone the repo and run `opam install .` at the root to install using OPAM.

Each synthesized Coq certificate imports `SSL`, a module consisting of predefined tactics. The module source may be compiled by running `make clean && make` in the directory `certification/coq`.

### Running Synthesis with Certification

Add the following flags to run synthesis with certification.

- `--certTarget <value>`: Currently supports value `coq`.
- `--certDest <value>` (optional): Specifies the directory in which to generate a certificate file. Logs output to console if not provided.



