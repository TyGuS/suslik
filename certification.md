# Certified Synthesis

Generation of correctness certificates for synthesized programs.
Currently, we support three target verification frameworks in Coq: HTT, VST, and Iris.

## Requirements

Follow the instructions in the README of each repository below to install the necessary
Coq libraries. Each repository also has a `benchmarks/` directory where examples of generated
certificates are viewable.

- HTT ([`TyGuS/ssl-htt`](https://github.com/TyGuS/ssl-htt))
- VST ([`TyGuS/ssl-vst`](https://github.com/TyGuS/ssl-vst))
- Iris ([`TyGuS/ssl-iris`](https://github.com/TyGuS/ssl-iris))

## Synthesis with Certification

Add the following flags to run synthesis with certification.

- `--certTarget <value>`: Currently supports values `htt`, `vst`, `iris`.
- `--certDest <value>` (optional): Specifies the directory in which to generate a certificate file. Logs output to console if not provided.

For example, the following command produces a HTT certificate of the specification `listfree.syn`, and logs its contents to the console.

```bash
./suslik examples/listfree.syn --assert false --certTarget htt
```

By providing the `--certDest` flag, SuSLik writes out this certificate as a file to the specified directory. The following example command writes a HTT certificate named `listfree.v` to the project root directory.

```bash
./suslik examples/listfree.syn --assert false --certTarget htt --certDest .
```

### Optional Flags

If HTT is chosen as the certification target, you can control additional certification parameters.
Note that this has no effect if Iris or VST are chosen.

- `--certHammerPure <value>` (boolean; default is `false`):
Controls whether to use CoqHammer to solve pure lemmas.
If `false`, the generated certificate will have all pure lemmas `Admitted` instead.
- `--certSetRepr <value>` (boolean; default is `false`):
Controls whether to use SSReflect's `perm_eq` to express multi-set equality.
If `false`, the generated certificate will use regular equality (`=`) instead.
