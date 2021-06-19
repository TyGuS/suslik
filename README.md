# ICFP 2021 Artifact

Name:    Certifying the Synthesis of Heap-Manipulating Programs

## Getting Started

This artifact is distributed as a `.qcow` VM image, which should be used with
[QEMU](https://www.qemu.org/).

### Installation

#### OSX

``brew install qemu``

#### Debian and Ubuntu Linux

``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See the last section "Troubleshooting" for
details.

#### Arch Linux

``pacman -Sy qemu``

See https://wiki.archlinux.org/index.php/QEMU for more info.

See the last section "Troubleshooting" if you have problems logging into the
artifact via SSH.


#### Windows 10
Download and install QEmu via the links on https://www.qemu.org/download/#windows.
Ensure that qemu-system-x86_64.exe is in your path.
Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".
Restart your computer.

#### Windows 8

See the last section "Troubleshooting" for Windows 8 install instructions.



### Startup

If you intend to run the artifact in a VM image, download it as an archive and
unzip it. In the folder, besides the .qcow image you will find the script
`start.sh` (Unix systems) / `start.bat` (Windows) to start the VM.

Running this script will open a graphical console on the host machine, and
create a virtualized network interface.
On Linux you may need to run with 'sudo' to start the VM. If the VM does not
start then check the last section "Troubleshooting".

Once the VM has started, in a separate shell you can login to the guest system
from the host using:

```
$ ssh -p 5555 artifact@localhost             (password is 'password')
```

You can also copy files to and from the host using scp, eg:

```
$ scp -P 5555 artifact@localhost:somefile .  (password is 'password')
```

The root account password is ``password``.

The default user is username:```artifact``` password:```password```.

Here is a quick test if the artifact is working. Once you've logged in via
SSH, execute:

```
cd $SUSLIK_HOME
./certify-benchmarks --help
./certify-benchmarks2 --help
```

This should print each benchmarking tool's help dialogue.

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use:

```
$ sudo shutdown now
```


### VM Settings

You can adjust the following variables in the `start.sh` script.

- `QEMU_CPU` - Set the CPU configuration of the VM. (default: `max`)
- `QEMU_MEM_MB` - Set the amount of memory allocated to the VM.
  (default: `16384` i.e., 16GB)


## Artifact Instructions

This section contains the following information.

1. **Overview**: A summary of the two benchmark categories from the paper
   and the tools used to evaluate them.
2. **Step by Step Instructions**: How to reproduce the statistics from
   Table 1 and Table 2 of the paper; and how to run SuSLik on individual
   synthesis/verification problems.
3. **Artifact Structure**: Detailed information about how the artifact is
   structured.
4. **Other Ways To Explore**: How to run SuSLik on individual
   synthesis/verification problems, and how to interactively step through a
   proof certificate using Emacs/Proof General.
5. **Customizing Benchmark Options**: How to configure the benchmark tool to
   only evaluate selected targets/benchmark groups.
6. **Compiling Sources**: How to re-compile each of the four projects.
7. **Troubleshooting**: Solutions to common problems with VM and benchmarking.

### Overview

The paper discusses two classes of benchmarks.

1. **Standard benchmarks** are supported by HTT, VST, and Iris. This
   corresponds to Table 1 of the paper.
2. **Advanced benchmarks** are supported by HTT only. These include test
   cases that use an alternative representation of multi-set equality and
   requires manual editing of pure lemma proofs. This corresponds to
   Table 2 of the paper.

Correspondingly, the artifact provides two benchmarking tools, inside the
directory `~/projects/suslik`, to which the VM sets the environment
variable `SUSLIK_HOME`.

- `certify-benchmarks` synthesizes proof certificates for
  both standard and advanced benchmarks, and compiles the certificates for
  standard benchmarks only.
- `certify-benchmarks2` compiles the HTT certificates for advanced benchmarks.

### Step by Step Instructions

#### Generating All Certificates and Compiling Standard Benchmarks

To synthesize standard and advanced benchmark certificates, and compile
the standard benchmark certificates, SSH into the VM image and execute:

```
cd $SUSLIK_HOME
./certify-benchmarks
```

This will run SuSLik with certificate generation flags enabled, for all
specification (`.syn`) files in the standard and advanced benchmarks,
for all three target frameworks.
(Section "Artifact Structure" below shows the location of these files.)
Then, for the standard benchmarks, it will also compile the generated
certificates.

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
`$SUSLIK_HOME/certify`.

- `standard-syn.csv` contains synthesis times reported in Table 1.
- `standard-{HTT,VST,Iris}.csv` contain proof/spec size and compilation
  times for each of the three target frameworks in Table 1.
- `advanced-syn.csv` contains synthesis times reported in Table 2.

To inspect the results in table form, you can execute:

```
pretty_csv <CSV_FILE>
```

We noticed a roughly 3x overhead of running SuSLik and Coq inside the VM,
so please expect synthesis and certificate compilation times to be about three
times as long as the statistics reported in the paper.

#### Compiling Advanced Benchmarks (Manually Edited Proofs)

_**Note:** The first benchmarking tool consumes significant resources. As a
result, on some machines, we experienced significant slowdowns if
the second benchmarking tool is run immediately after completion of the first
tool, at times leading to ATP timeout errors with CoqHammer. If so, please
consider restarting the VM before proceeding, for reliable benchmarking._

The steps from the above section do not produce target-specific statistics for
advanced benchmarks. This is because the test cases in Table 2 require manual
editing of the pure lemma proofs (as discussed in Section 8.2 of the paper),
whereas that tool only checks SuSLik-generated certificates.

To compile the advanced benchmark certificates with manually edited pure lemma
proofs, execute the following.

```
cd $SUSLIK_HOME
./certify-benchmarks2
```

**It should take roughly _10 minutes_ to run this evaluation**.

After the script terminates, it will create two output files in
`$SUSLIK_HOME/certify`.

- `advanced-HTT.csv` contains proof/spec size and compilation times for HTT
  in Table 2.
- `advanced-HTT.diff` compares the original SuSLik-generated certificates
  (stored in
  `$SUSLIK_HOME/certify/HTT/certification-benchmarks-advanced`) with the
  manually edited ones (stored in `$SUSLIK_HOME/ssl-htt/benchmarks/advanced`),
  showing which lines have been modified. The diff file will only be created if
  the original SuSLik-generated certificates exist.

To inspect the results in table form, you can execute:

```
pretty_csv advanced-HTT.csv
```

The number of pure lemmas and those with manual proofs can be verified by
inspecting the files at `$SUSLIK_HOME/ssl-htt/benchmarks/advanced`.
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

To use this tool with custom settings, execute the following to see all
available options:

```
./certify-benchmarks2 --help
```

### Artifact Structure

In the VM, all main artifact files are contained inside the root directory
`~/projects/suslik`. An environment variable `$SUSLIK_HOME` is set to this
directory.

The directory contains four projects; all four projects and their dependencies
have been compiled and installed ahead of time.

The root directory contains the **SuSLik program synthesizer**, used to
generate programs and certificates from user specifications.

- `certify-benchmarks` and `certify-benchmarks2` are the two benchmarking
  tools.
- `suslik` is the executable used to run individual benchmarks.
- `src/test/resources/synthesis/certification-benchmarks` contains the
  standard benchmark test cases targetable by all three frameworks
  (Table 1).
- `src/test/resources/synthesis/certification-benchmarks-advanced`
  contains the advanced benchmark test cases supported by HTT only
  (Table 2).
- `src/main/scala/org/tygus/suslik` contains the source code for
  SuSLik. In particular, `certification` contains the code relevant to
  certified synthesis.

The benchmark test cases are stored in `.syn` files. The first line
contains flags to pass to the backend SMT solvers used by SuSLik (e.g.,
`#. -c 2`). The second line gives a description of the test case.
The lines between the two `###` separators contain the main item---the
declarative specification of the desired program, with pre- and
postconditions expressed in SSL. After the second `###` separator, some
test cases also include a SuSLang implementation of the specification. This is
the expected program that the actual synthesized result can be compared
against to test the functionality of the synthesizer itself. It is thus
optional and has no bearing on the actual synthesis/certification task.

The table below summarizes the source code's structure in relation
to key concepts from the paper. The right column displays files and folders
located in `$SUSLIK_HOME/src/main/scala`, using Scala/Java's package notation;
for brevity we omit the common prefix `org.tygus.suslik` in all listings.

|  Concept  |  Location in source  |
| ---- | ---- |
|  Synthesis  |  `synthesis.Synthesis`  |
|  Proof trees (sec 3.2, 4.1)  |  `report.ProofTrace` (collection); `certification.CertTree`, `certification.source.SuslikProofStep`, `certification.traversal.ProofTree` (construction)  |
|  Proof evaluator - interface (fig 6, sec 3.3-3.5)  |  `certification.traversal.Evaluator`  |
|  Proof step interpreter - interface (Fig 6, sec 3.3-3.5)  |  `certification.traversal.Interpreter`  |
|  Proof evaluator - implementation (e.g., HTT proofs, sec 5)  |  `certification.targets.htt.translation.ProofEvaluator`  |
|  Proof step interpreter - implementation (e.g., HTT proofs, sec 5)  |  `certification.targets.htt.translation.ProofInterpreter`  |
|  Context (sec 3.4) - implementation (e.g., HTT proofs, sec 5)  |  `certification.targets.htt.translation.ProofContext`  |
|  Iris implementation (sec 6)  |  `certification.targets.iris.*`  |
|  VST implementation (sec 7)  |  `certification.targets.vst.*`  |
|  Collection of pure lemmas (Coq hints) for HTT (sec 4.2.3)  |  `certification.targets.htt.logic.Hint`  |
|  Predicate interface and conversion to fixpoint (sec 6.1)  |  `certification.translation.GenericPredicate`, `certification.translation.PredicateTranslation`  |

The following subdirectories each contain SuSLik's Coq bindings for the
respective target verification frameworks.

- `ssl-htt`: Hoare Type Theory (HTT)
- `ssl-vst`: Verified Software Toolchain (VST)
- `ssl-iris`: Iris

In each, the `benchmarks` directory contains benchmark certificates generated
by SuSLik ahead of time.


### Other Ways To Expore

Aside from the benchmarks, here are some other ways to explore the artifact.

#### Running Standalone SuSLik

Aside from the benchmarking, you may want to use SuSlik with certification
options on a standalone user specification. 

Inside the SuSLik project directory (`$SUSLIK_HOME`), this can be accessed
via the `./suslik` executable. Run with the `--help` flag to view all options,
and refer to `README.md` and `certification.md` within the project directory
for further instructions. The four flags relevant to certification are
as the following:

1. `--certTarget` specifies the certification target. This is none by default;
   acceptable values are `htt`, `vst`, and `iris`.
2. `--certDest` specifies the directory path to store the produced certificate.
   If not provided, the certificate is printed to the console instead.
3. `--certHammerPure` is a boolean flag to choose whether to produce
   certificates with pure lemmas admitted (`false`) or with a one-line proof
   invoking CoqHammer's `hammer` tactic (`true`). This is `false` by default.
   (_Supported for HTT certification only!_)
4. `--certSetRepr` is a boolean flag to choose whether to represent multi-set
   equality via regular list equality (`false`) or with SSReflect's `perm_eq`
   (`true`). This is `false` by default.
   (_Supported for HTT certification only!_)

For example, the following would synthesize an HTT certificate for
the `listmorph.syn` specification and store it in the current directory.
The generated certificate would admit the pure lemmas, and use the `perm_eq`
representation.

```
./suslik src/test/resources/synthesis/certification/list/listmorph.syn \
    --certTarget htt \
    --certDest . \
    --certHammerPure false \
    --certSetRepr true
```

#### Interactive Proof Inspection With Emacs/Proof General

The artifact comes with an installation of
[Emacs](https://www.gnu.org/software/emacs/) and its proof assistant
interface [Proof General](https://proofgeneral.github.io/). To step through a
proof certificate called `proof.v`, execute:

```
emacs -nw proof.v
```

This will load an Emacs session in your terminal window. Some useful commands:

- `C-x C-f <filename> RET` to load a file in current buffer
- `C-c C-n` to move forward in the current buffer's Coq proof
- `C-c C-u` to move backward in the current buffer's Coq proof
- `C-x C-c` (type "yes" if prompted) to exit Emacs.

### Customizing the Benchmark Options

You may wish to run the benchmarks with alternative settings.

To produce certificates and stats CSV files in a directory other than
`$SUSLIK_HOME/certify`, run the tool with the `--outputDir` flag.

```
cd $SUSLIK_HOME
./certify-benchmarks --outputDir <ALTERNATIVE_DIR_PATH>
```

As the benchmark tool takes several hours to run, you may need to interrupt
its execution, and then resume later on a subset of the benchmarks/frameworks.
If so, you can run the tool with the `--configure` flag.

```
cd $SUSLIK_HOME
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

### Downloading and Compiling Sources

All four projects have been compiled/installed ahead of time and are ready to
use. However, if there is a need to recompile, follow these steps. For
troubleshooting, refer to their respective project READMEs.

Warnings generated during compilation are expected, and do not affect the
functionality of the tools.

#### Requirements

The projects have the following dependencies.

* [Java SE Development Kit 8](http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html)
* [Scala Build Tool](https://www.scala-sbt.org/), `sbt` (version >=1.1.6)
* [Z3 SMT solver](https://github.com/Z3Prover/z3)
* [CVC4 SMT solver](https://cvc4.github.io/), version 1.7
* [Cyclist Theorem Prover](http://www.cyclist-prover.org/installation)
* [Scala](https://www.scala-lang.org/download/) (version >= 2.12.6) - to run the standalone artifact
* [OPAM package manager](https://opam.ocaml.org/doc/Install.html), version 2.0
* [OCaml compiler](https://opam.ocaml.org/doc/Usage.html#opam-switch), version 4.10.0

#### Download

This clones the main SuSLik repository to the directory stored in the
environment variable `SUSLIK_HOME`, initializing all nested submodules.

```
git clone --recurse-submodules -b icfp21-artifact https://github.com/TyGuS/suslik.git $SUSLIK_HOME
```

If you have already cloned the root repository and navigated to it,
you can initialize all nested submodules with:

```
git submodule update --init --recursive
```

#### Compile/Install

```bash
cd $SUSLIK_HOME # or wherever you cloned the repository

# compile SuSLik
sbt assembly

# initialize OPAM and add repos
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes

# install dependencies
opam install coq.8.11.2 coq-mathcomp-algebra coq-mathcomp-ssreflect coq-hammer

# install HTT dependencies
opam install coq-htt coq-fcsl-pcm

# install VST dependencies
opam install coq-flocq.3.4.0 coq-compcert.3.7~coq-platform coq-vst

# compile + install SSL bindings for HTT
(cd ssl-htt; opam install .)

# compile + install SSL bindings for VST
(cd ssl-vst; opam install .)

# compile + install SSL bindings for Iris
(cd ssl-iris; opam pin add iris; opam pin add string-ident; opam install .)
```

### Troubleshooting

Below are solutions to some potential issue with the VM or with running the
benchmarks.

#### SuSLik

**Problem: Synthesis fails on timeout**

In a typical setup, all included benchmark programs should be synthesizable
in reasonable time.

However, you may get the following message on slow machines or if the VM has
been running for a long time. If so, please restart the VM and try again
(resume with selected groups only with the `--configure` flag as
described above).

```
The derivation took too long: more than 120000 seconds.

org.tygus.suslik.synthesis.SynthesisException: Failed to synthesise:
```

#### CoqHammer

**Problem: Out of memory**

The benchmarks have been tested to work with 16GB of memory allocated to
the VM. If, CoqHammer fails with an out of memory exception while compiling
the proofs, please try increasing the value of the `QEMU_MEM_MB` variable in
the `start.sh` script.

**Problem: ATP fails on timeout**

In a typical setup, all included benchmark programs should be certifiable
in reasonable time, and the certificates are generated with a generous
ATP time limit of 60s, more than the default.

However, you may get the following message on slow machines or if the VM has
been running for a long time. If so, please restart the VM and try again.

```
Error:
Hammer failed: ATPs failed to find a proof.
You may try increasing the ATP time limit with 'Set Hammer ATPLimit N' (default: 20s).
```

#### OSX

**Problem: Black screen on startup**

If you are running OSX Catalina and have an old version of QEMU already installed
then you may see a black screen when the VM starts. One AEC member had this problem
and resolved it by upgrading to the current version of QEMU.

**Problem: Artifact crashes frequently**

Your artifact may crash with the following error message.

```
vmx_write_mem: mmu_gva_to_gpa ffff9ac27b23fcdc failed

Abort trap: 6
```

Consider specifying the exact CPU model of the host machine in the `QEMU_CPU`
variable of the start script (`start.sh`), as described in
[this StackOverflow answer](https://stackoverflow.com/a/63746318).

#### Linux

**Problem: The 'kvm' kernel module will not load because it is disabled in the BIOS.**

Symptom:

```
$ sh start.sh
Linux host detected.
Could not access KVM kernel module: No such file or directory
qemu-system-x86_64: failed to initialize KVM: No such file or directory
```

Check whether the `kvm-intel` or `kvm-amd` module is loading correctly.
You might get:

```
$ sudo modprobe kvm-intel
modprobe: ERROR: could not insert 'kvm_intel': Operation not supported
```

Check the dmesg log to see if virtualization has been disabled in the BIOS:

```
$ dmesg | tail
...
[  848.697757] kvm: disabled by bios
```

Check your BIOS configuation for a setting like "Intel Virtualization Technology"
and ensure that it is enabled.


**Problem: My Linux server does not have a monitor.**

You can start the VM without the console display like so:

```
$ sudo sh start.sh -display none
```

Then connect to it via SSH.

```
$ ssh -p 5555 artifact@localhost
```


**Problem: Virtualization still isn't working**

If the 'KVM' virtualization system still doesn't work then you can use plain emulation
via the Tiny Code Generator. This will be slower, but otherwise have the same functionality.

```
$ sudo sh start.sh -accel tcg
```

#### Windows

On (old) Windows 8, following the instructions from the first section is known
to fail with the following:

```
c:\...\qemu-system-x86_64: Could not load library WinHvPlatform.dll.
c:\...\qemu-system-x86_64: failed to initialize WHPX: Function not implemented
```

An AEC member with a Windows 8 machine was able to get it the image working by
changing the .bat file to use the HAXM virtualization system instead of WHPX.

1. install the latest haxm
2. make sure the hyper-v feature is off
3. change the -accel flag in the .bat file to hax

