# Certifying Synthesis Results

This page contains instructions for running and evaluating the certification component of SuSLik, corresponding to the
following paper.

**[Certifying the Synthesis of Heap-Manipulating Programs](https://doi.org/10.1145/3473589)**  
  Yasunari Watanabe, Kiran Gopinathan, George Pîrlea, Nadia Polikarpova, and Ilya Sergey. ICFP'21
  - [Artifact, 21 May 2021](http://doi.org/10.5281/zenodo.5005829)

Currently, we support three target verification frameworks in Coq—HTT, VST, and Iris—to generate correctness
certificates for synthesized programs.

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

## Evaluation

### Overview

The paper discusses two classes of benchmarks.

1. **Standard benchmarks** are supported by HTT, VST, and Iris. This
   corresponds to Table 1 of the paper. These are available in the folder
   `$SUSLIK_ROOT/src/test/resources/synthesis/certification-benchmarks`.
2. **Advanced benchmarks** are supported by HTT only. These include test
   cases that use an alternative representation of multi-set equality and
   requires manual editing of pure lemma proofs. This corresponds to
   Table 2 of the paper. These are available in the folder
   `$SUSLIK_ROOT/src/test/resources/synthesis/certification-benchmarks-advanced`

The tool `certify-benchmarks` synthesizes proof certificates for
  both standard and advanced benchmarks, and compiles the certificates for
  standard benchmarks only.

The [`ssl-htt`](https://github.com/TyGuS/ssl-htt) repository contains a benchmarking script to compile the HTT
certificates for advanced benchmarks.

### Generating All Certificates and Compiling Standard Benchmarks

To synthesize standard and advanced benchmark certificates, and compile
the standard benchmark certificates, execute:

```
cd $SUSLIK_ROOT
./certify-benchmarks
```

This will run SuSLik with certificate generation flags enabled, for all
specification (`.syn`) files in the standard and advanced benchmarks,
for all three target frameworks.
Then, for the standard benchmarks, it will also compile the generated
certificates.
These are the default evaluation configuration, and the exact actions that will
be performed under this configuration are written to timestamped `.log` files in
the `certify` directory before each run. This configuration can be modified
by setting the `--configure` flag. See section "Customizing Benchmark Options"
for details.

As this script produces verbose output, you may consider teeing the script's
output to a log file for viewing/debugging later, instead of running the script
directly.

```
./certify-benchmarks> >(tee certify.log)
cat certify.log
```

When running the tool, please keep in mind the following.

- **It should take _2-3 hours_ to run this evaluation on all benchmark
  groups and all target frameworks.** If you need to interrupt the evaluation,
  or if the benchmarking encounters a timeout error on a slow machine, please
  refer to section "Customizing Benchmark Options" on how to resume the task
  with selected benchmark groups/target frameworks only.
- **Files in the `certify` directory will be overwritten on each subsequent
  run.**
- Unsupported test cases for certain targets (such as `sll_max` for Iris,
  as indicated in Table 1) are ignored.
- Warnings displayed during the proofs do not affect the functionality of the
  certificates.

After the script terminates, it will create five output files in
`$SUSLIK_ROOT/certify`.

- `standard-syn.csv` contains synthesis times reported in Table 1.
- `standard-{HTT,VST,Iris}.csv` contain proof/spec size and compilation
  times for each of the three target frameworks in Table 1.
- `advanced-syn.csv` contains synthesis times reported in Table 2.

#### Customizing Benchmark Options

You may wish to run the benchmarks with alternative settings.

To produce certificates and stats CSV files in a directory other than
`$SUSLIK_ROOT/certify`, run the tool with the `--outputDir` flag.

```
cd $SUSLIK_ROOT
./certify-benchmarks --outputDir <ALTERNATIVE_DIR_PATH>
```

As the benchmark tool takes several hours to run, you may need to interrupt
its execution, and then resume later on a subset of the benchmarks/frameworks.
If so, you can run the tool with the `--configure` flag.

```
cd $SUSLIK_ROOT
./certify-benchmarks --configure
```

When this flag is set, a configuration wizard is run before the benchmarks,
where you can selectively enable/disable three benchmarking parameters.

- **Compilation:** Choose whether to measure compilation times of the
  generated certificates or not.
- **Benchmark groups:** Select which benchmark groups to evaluate.
- **Target frameworks:** Select which target framework to generate/compile
  certificates for.

At each prompt, press ENTER to select the default option; alternatively, choose
the desired option (`y` or `n`). The default settings are:

- _For standard benchmarks_: Synthesize programs in all benchmark groups. Then
  generate and compile certificates for all three targets (HTT/VST/Iris).
- _For advanced benchmarks_: Synthesize programs in all benchmark groups. Then
  generate (but _don't_ compile) certificates for HTT only.

Each execution of the script generates a timestamped `.log` file listing
exactly what actions will be performed given the user-specified configuration,
which may be useful for debugging.

### Compiling Advanced Benchmarks (Manually Edited Proofs)

The steps from the above section do not produce target-specific statistics for
advanced benchmarks. This is because the test cases in Table 2 require manual
editing of the pure lemma proofs (as discussed in Section 8.2 of the paper),
whereas that tool only checks SuSLik-generated certificates.

To compile the advanced benchmark certificates with manually edited pure lemma
proofs and execute the following (`$SSL_HTT_ROOT` refers to the local `ssl-htt` repository).

```
cd $SSL_HTT_ROOT/benchmarks/advanced
python3 benchmark.py --diffSource $SUSLIK_ROOT/certify/HTT/certification-benchmarks-advanced
```

**It should take roughly _10 minutes_ to run this evaluation**.

After the script terminates, it will create two output files in
`$SSL_HTT_ROOT/benchmarks/advanced`.

- `advanced-HTT.csv` contains proof/spec size and compilation times for HTT
  in Table 2.
- `advanced-HTT.diff` compares the original SuSLik-generated certificates
  (stored in
  `$SUSLIK_ROOT/certify/HTT/certification-benchmarks-advanced`) with the
  manually edited ones (stored in `$SSL_HTT_ROOT/benchmarks/advanced`),
  showing which lines have been modified. The diff file will only be created if
  the original SuSLik-generated certificates exist.

The number of pure lemmas and those with manual proofs can be verified by
inspecting the files at `$SSL_HTT_ROOT/benchmarks/advanced`.
You can also view the diff file to verify which parts of the proofs have been
edited.

```
less advanced-HTT.diff
```

You can expect to see the following differences between the two proof versions.

- _Proofs for the pure lemmas:_ In the generated scripts, pure lemmas have
  their `hammer` proofs replaced with `Admitted` statements. In the manually
  edited scripts, these are replaced with either a call to `hammer` when that is
  sufficient, or with a proof manually constructed by the authors. Note that in
  the diff file, pure lemmas may be ordered differently between the two
  versions, due to non-determinism in the way Scala accumulates hints during
  execution.
- _Administrative renaming statements in the main proof:_ These are
  identifiable by the `try rename ...` statements; they may occur when
  two variable rename statements resulting from the same proof step
  are applied in different orders between the compared proofs, again
  dependent on Scala's execution.

You should _not_ see edits that modify the main proof structure (aside from
renaming variables).

To use this tool with custom settings, execute the script with the `--help` flag to see all
available options.
