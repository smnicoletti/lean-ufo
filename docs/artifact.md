# Run the artifact with Docker

Docker is the only required host dependency for the command-line workflow.
The image contains Lean, pinned library sources, compiled dependencies, the
experiment runner, and TeX. Results stay inside the named container until you
copy them to a visible host directory. No host Lean, Python, Make, or TeX
installation is required.

Prebuilt images and the completed reference dataset are distributed through
[Zenodo](https://doi.org/10.5281/zenodo.23337283). Source releases are available on
[GitHub](https://github.com/smnicoletti/lean-ufo/releases).
Each `docker run` creates a fresh container.

| Task | Container command | Output |
| --- | --- | --- |
| Recreate tables from the supplied ten-run dataset | `reference` | `/results/reference-tables/tables.pdf` and the shared LaTeX fragments |
| Full regression gate, warm-up, one measured run, and tables | `smoke` | A new run under `/results/experiments/` |
| Full gate, warm-up, ten measured runs, and tables | `experiments 10` | A new run under `/results/experiments/` |
| Fast regression suite | `check` | Pass/fail output, no new timings |

## Build locally

From the unpacked repository root, run:

```text
docker build -t alien-artifact:local .
```

Building needs internet access to fetch Ubuntu packages, the pinned Lean
toolchain, and library caches. The source archive includes pinned dependency
sources. To use the prebuilt image, run `docker load --input IMAGE_ARCHIVE`.

The Dockerfile pins the base-image digest. `lean-toolchain` and
`lake-manifest.json` pin Lean and library revisions. Ubuntu package versions are
recorded in `/opt/alien/system-packages.txt`; rebuilding from the Dockerfile can
fetch newer Ubuntu updates. An archived image and its checksum fix the actual
environment used for a release.

## Recreate the reference tables

```text
docker run --name alien-tables --network none alien-artifact:local reference
docker cp alien-tables:/results/. ./alien-results
```

Open `alien-results/reference-tables/tables.pdf`. The command validates and
renders saved evidence; it does not rerun experiments. The reference dataset is
separate from new outputs and remains unchanged. It contains the original
measurement metadata, raw observations, logs, and a snapshot of measured sources.
The reported timings were measured natively on macOS, not inside Docker.

## Run new experiments

For the one-run smoke test:

```text
docker run --name alien-smoke --network none alien-artifact:local smoke
docker cp alien-smoke:/results/. ./alien-smoke-results
```

For ten measured repetitions:

```text
docker run --name alien-experiments --network none alien-artifact:local experiments 10
docker cp alien-experiments:/results/. ./alien-experiment-results
```

These commands retain the container after completion, including after an error.
The smoke test includes a warm-up and the full semantic regression suite; it is
not a quick startup check. Keep the machine awake throughout timing experiments.
If sleep interrupts measurement, start a new run instead of pooling observations.
The experiment allows 3600 seconds per example or synthetic invocation by
default. A timeout invalidates the run. To change the limit, add
`--env LEANUFO_EXPERIMENT_TIMEOUT_SECONDS=SECONDS` to `docker run`, replacing
`SECONDS` with a positive integer. The selected limit is recorded in the
experiment metadata. The paper's reported measurements used 600 seconds.
Increasing it does not change the checks or turn a previous timeout into a
successful sample.

After checking the copied results, `docker rm alien-smoke` removes that named
container and its internal files. The host copy remains. Use a different
container name for another run, or remove the previous container only after
copying the results. No command needs privileged mode or a Docker socket mount.

## Compatibility and timing interpretation

Local validation on 2026-10-13 used Linux ARM64 in Colima on an Apple Silicon
Mac, with four virtual CPUs and 8 GB of VM memory. Lean uses two threads per
process. This is a tested configuration, not a minimum requirement.

| Check | Local evidence |
| --- | --- |
| Container build and full semantic suite | Passed |
| Offline reference-table generation | Passed; all seven fragments match the paper |
| Offline fast regression suite | Passed |
| One-run container experiment and PDF | Passed; 25 certifications, six expected rejections, and all 30 generated workloads |
| Persistent editor workspace | Writable named volume; `Minimal.lean` checked offline |
| AMD64 under QEMU 7.0.0 on ARM64 (2026-10-14) | Compilation, full offline regression suite, selected examples, all 30 generated workloads, and reference PDF passed with `G_SLICE=always-malloc` |
| Native AMD64, Windows, and Intel Mac execution | Not tested |

The recipe targets Linux ARM64 and AMD64. Apple Silicon needs ARM64; Intel Macs
and most Windows/Linux PCs need AMD64. Use Linux containers on Windows. Docker
does not make an unsupported host OS, missing virtualization, or insufficient
memory compatible. An older Mac still needs a Docker version supported on its
macOS release. `PACKAGE-INFO.json` records image sizes and validation resources.

Use the host's native architecture for measurements. Docker can emulate another
architecture, but its overhead makes those times unsuitable for direct comparison
with native results. Linux metadata records OS information and cgroup CPU and
memory limits where available. The CPU and memory visible inside a Docker VM
can differ from the physical host. New runs need not reproduce the reference
timings; they must reproduce expected outcomes and consistent table generation.

## Troubleshooting

### A test remains running without output

Use an image matching the host CPU whenever possible. Cross-architecture
execution adds an emulator between the program and the operating system.
During AMD64 validation on ARM64 with QEMU 7.0.0, a newly created subprocess
blocked inside QEMU's GLib memory allocator before starting its command. This
matches the fork-related allocator deadlock described in
[QEMU issue 285](https://gitlab.com/qemu-project/qemu/-/issues/285).

Silence alone does not establish a hang: the full test suite prints its summary
at completion, and some proofs take several minutes under emulation. For the
`alien-smoke` container used above, inspect its output and activity:

```text
docker logs --tail 30 alien-smoke
docker stats --no-stream alien-smoke
docker top alien-smoke
```

If the same subprocess remains idle across repeated checks, preserve its logs
and any results before stopping it. A hung run is incomplete, even if it has
not printed a test failure. Do not bypass the regression gate or combine its
partial timings with a later run.

If a matching-architecture image is unavailable, the upstream allocator
workaround can be supplied to a new container. With the image loaded as
`alien-artifact:local`, this command retries the full regression suite without
collecting timings:

```text
docker run --name alien-tests-workaround --network none --env G_SLICE=always-malloc --env LEANUFO_FULL_TESTS=1 alien-artifact:local check
```

The setting tells QEMU's GLib allocator to use `malloc`; it does not change the
Lean proofs or disable any tests. On 2026-10-14, the full offline AMD64 regression
suite passed with this setting under QEMU 7.0.0 on ARM64, using four VM CPUs,
8 GB of memory, and one Lean thread per process. It completed in 20 minutes
14 seconds. Use the host's native architecture for measurements; emulated
elapsed times must remain separate from native measurements.

### Docker reports `no space left on device`

Check free space in Docker's VM as well as on the host. Loading an image needs
space to unpack its layers, in addition to the downloaded archive. Multiple
architectures and build caches consume extra space. Preserve results before
removing any container or cache. `PACKAGE-INFO.json` accompanying the release
assets records archive sizes and resource information.

## Optional VS Code walkthrough

This walkthrough additionally requires desktop VS Code and its Dev Containers
extension. It is optional: neither is needed for batch experiments or tables.

1. Build or load `alien-artifact:local`.
2. Open the unpacked source folder in VS Code.
3. Run **Dev Containers: Reopen in Container**.
4. Open `LeanUfo/UFO/DSL/ConcreteExamples/Minimal.lean`.
5. Wait for Lean to finish, then place the cursor on the model declaration and
   open Lean's Infoview. Inspect the successful UFO diagnostics.
6. Open `FailedStudentEnrollment.lean` and inspect the confirmed (a10)
   counterexample, its named assignment, alternatives, and supporting evidence.
7. Open `ReuseRoleExtension.lean` and inspect fresh and reused per-axiom rows in
   the extension. A reused proof is still checked by Lean.

The Dev Container installs `leanprover.lean4`. VS Code may download its server
and extension on first use, so the interactive walkthrough is not claimed to
be offline. The `.devcontainer` configuration opens a persistent Docker volume
initialized from the image, including Linux caches. It does not mount or reuse
host macOS/Windows Lean binaries. The container keeps the image's user ID so
the volume remains writable even when the host user has a different ID.
Edits in that volume are separate from the host
source folder; copy them out before removing the volume. Reusing the volume also
reuses its source snapshot, so changing images does not automatically refresh it.

[Experiment protocol](experiments.md)
