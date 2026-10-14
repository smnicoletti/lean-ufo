# Reproduce the performance experiments

The experiment profile measures real DSL certification and diagnostic runs,
then exercises synthetic algorithmic workloads. One command runs both groups
after the full regression gate. It uses Lean and the existing Lake toolchain;
no Python installation or statistics package is required.

The [Docker walkthrough](artifact.md) packages Lean, its dependencies, and TeX.
Docker is the only required host dependency for that workflow. Desktop VS Code
and Dev Containers are optional, for inspecting the editor interaction.

## Generate tables without rerunning experiments

From the repository root, run:

```bash
UFO_GENERATE_TABLES=1 lake test
```

This mode validates the newest directory under `experiments/` and writes its
LaTeX table fragments and standalone `tables/tables.pdf`. It does not rerun the
regression suite or collect new timings. An incomplete newest run causes an
error; the command never silently substitutes an older successful run.
Outside Docker, PDF generation also requires `pdflatex` and the packages
`geometry`, `amsmath`, `booktabs`, `array`, `tabularx`, `longtable`, and `hyperref`.

To select a saved run explicitly, set `UFO_EXPERIMENT_RESULTS`:

```bash
UFO_GENERATE_TABLES=1 UFO_EXPERIMENT_RESULTS=experiments/RUN_ID lake test
```

Here `RUN_ID` is the directory name printed by the experiment command.
`UFO_TABLE_OUTPUT` optionally selects a different report directory. The original
observations, summary CSV, logs, and measurement metadata remain unchanged.
`report-result.json` is true only after validation and both LaTeX passes finish.

To collect new measurements and generate their tables in one invocation:

```bash
LEANUFO_PERFORMANCE_TESTS=10 UFO_GENERATE_TABLES=1 lake test
```

Do not set `UFO_EXPERIMENT_RESULTS` in this combined mode: it must report the new
run, not a separately selected dataset. The runner passes that completed run's
path directly to the renderer. Set `LEANUFO_EXPERIMENT_DIR` to change the
experiment root; standalone report mode also searches that root.

The renderer recomputes every summary from raw observations and checks it
against `summary.csv`. It also checks case coverage, each repetition's expected
outcomes, agreement with saved process logs, and stable model sizes and operation
counts. These checks detect incomplete or inconsistent records; they are not a
cryptographic guarantee against fabricated data. Historical source hashes are
retained, rather than compared with a newer rendering checkout.

The templates in `docs/experiment-tables/` use `@@name@@` placeholders for values.
Generated fragments are shared by the standalone report and manuscript, so no
numbers need to be transcribed. The overview's formula-comparison count describes
the separate regression suite, not a timing observation. Reproduction means
the same numerical content from the same dataset, not byte-identical PDFs or
identical timings on another machine.

## Reviewer smoke run

From the repository root, run:

```bash
LEANUFO_PERFORMANCE_TESTS=1 lake test
```

This command checks the full semantic suite, builds the example aggregate and
the relator witness, and runs every experiment once after one warm-up. It is a
complete experiment smoke run, not the fast default test profile. Dependency
builds and regression checks can take substantially longer than individual
timed operations. A first run also needs the normal Lake dependency setup.

For repeated measurements, set the same flag to the number of measured runs:

```bash
LEANUFO_PERFORMANCE_TESTS=10 lake test
```

The value must be a nonnegative integer. Zero disables experiments. The older
values `true` and `yes` mean one measured run. Invalid values fail rather than
silently selecting the default profile. Leave `LEANUFO_AXIOMS` unset when
reproducing the full gate; that separate flag filters semantic witness tests.

## Read the results

The command prints a unique output directory under the visible top-level
`experiments/` folder.
Each run preserves these files:

| File | Meaning |
| --- | --- |
| `result.json` | Whether every requested outcome and source-stability check passed. Use timings as a complete experiment only when `valid` is true. |
| `metadata.json` | Machine information, Lean version, Git revision and dirty status, source-content hashes, repetition count, and measurement boundaries. |
| `raw.jsonl` | Every model, file, and synthetic observation, including warm-up replicate 0. |
| `summary.csv` | Mean, sample standard deviation, median, minimum, maximum, and sample count in nanoseconds. |
| `build.log` and per-run `.log` files | Dependency-build output and the complete Lean output for each measured source or synthetic run. |

One measured run has no standard-deviation estimate: the CSV field is empty.
For repeated runs, the standard deviation describes variation between those
runs, not uncertainty due to different machines or larger models. Nanosecond
timestamps preserve sub-millisecond observations; they do not imply that the
clock or experiment is accurate to one nanosecond.

Keep the complete output directory with your measurements. `metadata.json`
records source hashes and any uncommitted changes. The runner rejects a measurement session if source files change
during it. An unpacked source archive needs Git's `hash-object` command for
content hashing, but does not need a `.git` directory.

## What is measured

### Existing DSL models

Every file in `LeanUfo/UFO/DSL/ConcreteExamples/` is registered explicitly.
Adding a file without classifying its expected outcome fails the experiment
coverage check. Files can contain more than one model, so model results and
whole-file results are separate.

| Measurement | Included work | Excluded work |
| --- | --- | --- |
| Model `compile_to_result` | Compilation of the structured declaration, generated model declarations, assertion checks, native computation, proof construction and checking, and certificate or diagnostic data generation. | Process startup, imports, surface parsing, parent-source merging, subsequent `export_certificate` commands, and interactive React rendering. |
| File `process` | The whole `lake env lean <file>` invocation, including startup, imports, parsing, and all declarations in the source file. | Dependency builds and interactive editor rendering. |

The runner prebuilds dependencies, then explicitly elaborates each source in a
fresh process. It does not time an incremental `lake build` that can reuse a
previously compiled example. One full warm-up round precedes the measured
rounds. File order rotates across rounds to spread order-related drift; source
declarations retain their original order. The OS file cache is not flushed.

Keep the machine awake and avoid other CPU-heavy work during measurement.
On macOS, the optional wrapper `caffeinate -i env LEANUFO_PERFORMANCE_TESTS=10 lake test`
prevents idle sleep for the command's lifetime. It does not prevent sleep when
the laptop lid closes. If sleep interrupts measurements, start a new run;
do not combine the interrupted samples with an uninterrupted run.

Successful models must produce the final certificate packaging declaration
without new Lean errors. Expected failures must stop with the registered,
Lean-confirmed axiom violation. Their measurements are times to diagnosis,
not successful certification times. A process timeout is recorded as a
failure and invalidates the experiment; it is not assigned a successful runtime.
The default limit is 3600 seconds per example or synthetic invocation. To use a
different limit, set `LEANUFO_EXPERIMENT_TIMEOUT_SECONDS` to a positive integer
before starting a new run. The paper's reported measurements used 600 seconds.
The runner records the selected limit in
`metadata.json`; it does not change the work performed by an experiment.
The runner's dependency-build limit is the greater of 1800 seconds and the
selected experiment limit. Zero and malformed values are rejected.

`ConceptEvolution.lean` records a higher-order pattern that the current DSL
does not support faithfully. It is included as `unsupported`, with no timing:
checking a file containing only explanatory text would not measure certification.

Extension examples retain their parent, reuse-enabled child, and fresh child.
The model timer excludes earlier parent declarations; whole-file time includes
them. These timings describe the existing examples in source order. They do
not by themselves establish a controlled speedup from certificate reuse.

### Synthetic workloads

`LeanUfo/ComplexityBenchmarks.lean` generates sparse unary facts, dense parthood,
cyclic inherence, product-family searches, and coordinate projections. The
experiment profile uses one world and 2, 3, 5, 9, 17, and 33 entities for each
family. Every case records input sizes, operation counts, and separate elapsed
times for compilation, finite-model construction, aggregate checking, and a
targeted operation.

These are timings of the **cost-instrumented algorithms**, not Lean certificate
construction. Instrumentation contributes to elapsed time. Targeted operations
run even when the aggregate checker rejects the interpretation, so early
rejection cannot hide the operation being studied. Probe timing also includes
fixture validation, which is not always included in the probe's operation count.
For example, the cyclic probe times closure construction and the subsequent
reachability sanity check, but counts only closure construction.

Each stage passes its result through a non-inlined IO function before reading
the next timestamp. This prevents pure computations from moving across timing
boundaries during compilation. The function allocates and reads a reference;
that small measurement overhead is included, so very short stage timings need
particular care when comparing runs.

All generated interpretations are expected to fail aggregate checking, while
their targeted fixture checks must pass. Operation counts and fixture metadata
must agree across repetitions. Controlled-family monotonicity checks remain
enabled; they do not claim that arbitrary added facts always increase runtime.

The standalone command retains the original four input sizes:

```bash
lake exe complexity-benchmarks
lake exe complexity-benchmarks --extended
```

Its timing columns use `_ns`, not milliseconds. The original operation-count
columns retain their meaning. The unified experiment command adds repetitions,
raw evidence, statistics, and the real example measurements.

## Implementation

`LeanUfo/PerformanceExperiments.lean` owns registration, process isolation,
timeouts, validation, metadata, and statistics. `Syntax.lean` emits a compact
JSON model summary only when the runner sets `LEANUFO_EXPERIMENT_TIMING=1`.
The existing `LEANUFO_CERT_PROFILE=1` profiler remains available for debugging
individual proof steps. The experiment runner disables that verbose profiler
to avoid its per-step logging overhead.

`LeanUfo/RunPerformanceExperiments.lean` is the executable entry point.
`LeanUfo/ExperimentTables.lean` owns report validation and rendering. Its
`--test-data RUN` option checks a completed run and exercises invalid, incomplete,
duplicate, stale-summary, mismatched-log, and single-run cases on temporary
copies. The input run is never changed.

The runner targets macOS and Linux, the platforms used for local measurements
and CI. It uses standard system commands for machine metadata and Git for
source hashing. Missing optional hardware details are recorded as unavailable.

[Docker walkthrough](artifact.md)
