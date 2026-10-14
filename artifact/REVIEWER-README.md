# ALIEN artifact: reproduce the tables and inspect the checker

ALIEN checks finite UFO models and constructs Lean certificates or confirmed
counterexamples. This package contains its source, prebuilt Linux images,
and the completed measurements used in *ALIEN: an Automatic Lean Verification
Framework for UFO Ontological Models*. Docker is the only required
host software for the batch workflow. Desktop VS Code and Dev Containers are
optional, for inspecting the editor interface.

**Docker images:** [Zenodo](https://doi.org/10.5281/zenodo.23337283).
**Source releases:** [GitHub](https://github.com/smnicoletti/lean-ufo/releases).

## Quick start

To reproduce the paper's tables, [load the image for your machine](#load-the-image-for-your-machine),
then run the two commands below. Open
`alien-reference-results/reference-tables/tables.pdf` to inspect the results.
This checks and renders the supplied measurements without rerunning the
experiments: only Docker is required. Instructions for collecting new timings
and inspecting models in VS Code follow below.

```text
docker run --name alien-reference --network none alien-artifact:local reference
docker cp alien-reference:/results/. ./alien-reference-results
```

## Load the image for your machine

Use ARM64 on Apple Silicon and other ARM64 hosts. Use AMD64 on Intel/AMD PCs
and Intel Macs. Docker must be configured for Linux containers. Docker itself
must support the host operating system and virtualization hardware.

Download the image for your architecture from
[Zenodo](https://doi.org/10.5281/zenodo.23337283). `PACKAGE-INFO.json` records
archive sizes, image identifiers, and validation resources. `SHA256SUMS`
records the downloadable file checksums. Allow approximately **30 GB of free
disk space for one architecture**: about 5 GB for the download and 25 GB
available to Docker for the loaded image and working space. If Docker uses a
VM, check its disk allocation as well as free space on the host. These are
planning estimates; `PACKAGE-INFO.json` gives the measured archive sizes.

For ARM64:

```text
docker load --input alien-linux-arm64.tar.gz
docker tag alien-artifact:linux-arm64 alien-artifact:local
```

For AMD64:

```text
docker load --input alien-linux-amd64.tar.gz
docker tag alien-artifact:linux-amd64 alien-artifact:local
```

## What the reference command checks

The quick-start command checks
the saved observations and statistics before generating the PDF and seven
LaTeX table fragments. It does not collect new timings. Expected final output:

```text
Validated tables and PDF: /results/reference-tables/tables.pdf
```

## Check the installation and run new experiments

The fast check reports success without timing experiments:

```text
docker run --name alien-check --network none alien-artifact:local check
```

On success, the output ends with `LeanUfo DSL tests passed (fast profile; ...)`.

The complete smoke command runs the full regression suite, one preliminary
round excluded from summaries, one measured round, and table/PDF generation:

```text
docker run --name alien-smoke --network none alien-artifact:local smoke
docker cp alien-smoke:/results/. ./alien-smoke-results
```

For ten measured rounds:

```text
docker run --name alien-experiments --network none alien-artifact:local experiments 10
docker cp alien-experiments:/results/. ./alien-experiment-results
```

Both experiment commands generate the tables and PDF automatically.
Open `alien-experiment-results/experiments/RUN_ID/tables/tables.pdf`, replacing
`RUN_ID` with the directory name printed by the run. For `smoke`, use
`alien-smoke-results` instead of `alien-experiment-results`.

### How long does it take?

On Apple Silicon running the ARM64 image in a Linux VM with four CPUs and
8 GiB RAM, the fast `check` took 14 seconds and `smoke` took 13 minutes
32 seconds. Allow **15–20 minutes for smoke** on a comparable machine.
Its full regression gate and experiment startup took about 2½ minutes.
To run only the full regression suite, without timing experiments:

```text
docker run --name alien-full-check --network none --env LEANUFO_FULL_TESTS=1 alien-artifact:local check
```

For `experiments 10`, allow **about an hour** on that configuration. This is
an estimate from the completed smoke run: one warm-up plus ten measured rounds,
at about 5½ minutes per round, with the regression gate run once.
Under AMD64 emulation with QEMU 7.0.0, the full regression suite alone took
20 minutes 14 seconds with the workaround below. Native AMD64 runtimes have
not been measured. Slower machines may need substantially longer.

### Results and timeouts

Results appear under `experiments/RUN_ID/` in the copied directory. A successful
run has `valid: true` in `result.json`, and its generated report has
`valid: true` in `tables/report-result.json`. One measured
round cannot estimate a sample standard deviation.

Keep the machine awake. If sleep or another interruption stops measurement,
start a new run. Each example or synthetic invocation has a 3600-second default
timeout. Add `--env LEANUFO_EXPERIMENT_TIMEOUT_SECONDS=SECONDS` before the image
name to change it to a positive number of seconds. The runner records the
selected limit. The paper's original measurements used 600 seconds.

Containers retain their outputs after completion. Use a new container name for
each run, or copy the results before removing a previous container. The package
ships prebuilt images and completed reference data.

## Source and paper-to-code map

The repository contains the source, build recipes, and documentation.
The release asset `alien-source.tar.gz` also includes pinned dependency sources
and reference evidence, unpack it to obtain `alien-source/`.
The following paths are relative to the repository root, DSL paths
begin with `LeanUfo/UFO/DSL/`.

| Paper topic | Files to inspect |
| --- | --- |
| Checker soundness and qualified completeness | `Checker/Soundness.lean` and `Checker/Axioms.lean` |
| Compilation and relation tables | `Compiler.lean` and `Frontend/` |
| Certificates and reuse | `Certificate/Checking.lean`, `Certificate/Reuse.lean` |
| Counterexample search and presentation | `Diagnostic/AxiomAnalysis.lean`, `Diagnostic/Widget.lean` |
| Operational bounds | `Complexity/Theorems.lean`, `Complexity/Certification.lean` |
| Source-inspired and extension examples | `ConcreteExamples/` |
| Regression tests | `LeanUfo/Test/` and `LeanUfoTest.lean` |
| Timings and generated tables | `LeanUfo/PerformanceExperiments.lean`, `LeanUfo/ExperimentTables.lean` |

The paper describes the formal guarantees and trust boundaries. In particular,
the checker verifies the encoded finite interpretation. Some completeness results have extra
premises, including witness-table completeness for (a99). Native proof evaluation
has the trust requirements stated in the paper. Elapsed-time measurements are
separate from the proved operation counts.

## Optional VS Code walkthrough

This route also requires desktop VS Code and its Dev Containers extension.
Open the repository folder (or unpacked `alien-source/`) in VS Code and select
**Dev Containers: Reopen in Container**.
The image must first be loaded and tagged as `alien-artifact:local` above.
VS Code can download its server and Lean extension on first use.

Open these files under `LeanUfo/UFO/DSL/ConcreteExamples/` and inspect Lean's
Infoview after elaboration:

1. `Minimal.lean`: successful certification.
2. `FailedStudentEnrollment.lean`: a confirmed (a10) counterexample with names
   from the model and the missing classification alternatives.
3. `ReuseRoleExtension.lean`: fresh and reused proofs for a model extension.

The workspace uses a persistent Docker volume.
Edits made there remain in that volume, copy them out before removing it.
The detailed workflow is in `docs/artifact.md` inside the source folder.

## Troubleshooting

Prefer the image matching the host CPU. Cross-architecture emulation can be
much slower. With QEMU 7.0.0, a subprocess can also hang in the emulator's GLib
allocator. If this occurs, retry in a fresh container with
`--env G_SLICE=always-malloc` before the image name. The full regression suite
passed with that workaround in the tested emulated environment.

No output does not itself mean a hang: the full regression suite prints its
summary at completion. Inspect `docker logs CONTAINER`, `docker stats
--no-stream CONTAINER`, and `docker top CONTAINER`. For disk errors, check
free space inside Docker's VM as well as on the host. Do not remove a container
until its needed outputs have been copied. More detail is in `docs/artifact.md`.

## Availability, licences, and generative AI disclosure

**Artifact DOI:** [10.5281/zenodo.23337283](https://doi.org/10.5281/zenodo.23337283).
Docker images and reference evidence are distributed through Zenodo. Tagged
sources are grouped by version in
[GitHub Releases](https://github.com/smnicoletti/lean-ufo/releases).
Citation metadata is in `CITATION.cff`. ALIEN is licensed under
AGPL-3.0-or-later, dependency notices are retained in the images and source archive
and located by `artifact/THIRD-PARTY.md`. OpenAI's Codex, using GPT-5 and later
models, assisted with manuscript revision, software implementation and code review,
and Lean proof development. The author has checked the content and remains
responsible for the manuscript and artifact.
