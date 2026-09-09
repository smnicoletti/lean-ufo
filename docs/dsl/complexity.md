# Concrete complexity and the verified-DSL boundary

This guide maps the DSL's counted computations to their bounds and intended
execution model. The [behavior contract](behavior-contract.md) tracks open
repairs to operational accounting and source-to-model composition. Until those
repairs pass verification, the counter bounds below do not establish a complete
end-to-end bound for executed compilation, checking, and diagnostics.

## Claims

The primary target is **data complexity**: it measures growth when the UFO
checker registry is fixed (currently 116 checks) and only the finite model grows.
The secondary target is **combined complexity**: it measures growth when both
the model and the registry or formula can grow. These are different results;
the fixed-registry theorem must not be generalized silently to user-extensible
registries.

Extensibility has two distinct contracts. An additional executable check must
supply its own proved cost bound; the registry theorem then bounds their
sequential execution. For the existing diagnostic formula interpreter, the
bound must instead be derived from formula structure, including size and
quantifier nesting, domain sizes, and atomic-operation costs. These are
separate guarantees. Neither promises polynomial time in both an unrestricted
formula and its model, and neither requires a new public formula-checking API.

“Explicitly encoded” means every primitive relation cell, projection cell, and
product-family slot is represented and included in the size metric. Opaque
functions are not treated as constant-size relation inputs. The production
compiler and checker must be **erasures** of their counted executable
definitions—discarding the recorded cost while keeping the same value—or be
connected to them by a theorem that proves both implementations return the same
value.

## Unit-cost machine model

`Costed α` stores a computed `value` and a `Nat` cost. The model charges the
operations named at their executable definitions: Boolean operations,
comparisons, loop iterations, array accesses and writes, initialized cells,
queue operations, and emitted diagnostic items. A **short-circuit** operation
stops when its result is already known. For example, `false && q` does not
evaluate `q`, and a universal scan stops at its first false item. The counted
combinators follow Lean's left-to-right order and do not charge such unevaluated
branches.

The monotonicity requirement applies to proved upper bounds: increasing an
input-size parameter must not lower the bound. Exact execution counts may
decrease when added facts let a computation skip work. Tests must preserve
those skipped-operation savings rather than force exact counts to increase.
`sourceCompilerPolynomial_mono` proves this property for every size parameter
that occurs in the multivariate compiler formula. Its assumptions compare the
world, thing, fact, expanded-fact, taxonomy, specialization, family, slot, and
relation/projection cell counts component by component.

Finite world, thing, and witness-index quantifiers generate coordinates as
they visit them. They do not construct `List.finRange` before checking the
first coordinate. `allFinCosted_eq_list` and `anyFinCosted_eq_list` prove that
these loops preserve both the result and the visited-prefix cost of the list
specification. A first-item failure therefore takes the same recorded work
for one candidate and one million candidates. Array quantifiers also use
direct indices and charge each visited cell read. Other compiler traversals
and their accounting repairs remain listed in the behavior contract.

One array bounds check or access is a unit-cost primitive. Dense initialization
is charged per cell. Source name indexing includes hash-map insertions and
lookups as abstract primitives in the cost sum. It does not count their
character-level work. No constant-time theorem is claimed for
hash maps or strings unless a separate verified interface is introduced.
Character-level string work, allocation, garbage collection, elaboration,
kernel checking, native instructions, Lake overhead, and operating-system
scheduling are outside this theorem. Benchmarks measure those effects
separately.

### Name-index construction

`buildNameIndexCosted` reads the name array in source order and assigns
consecutive numeric indices. Each new name costs six units: an iteration, an
array read, a map membership query, a Boolean test, a map insertion, and an
index increment. The first duplicate costs four units and ends the scan.
Converting the scan result into an index or an error costs one further test.
The proved bound for `N` names is `6N + 1` under the stated map interface.
Each world/thing indexing stage adds one test to classify a duplicate error.

The executable traverses the array directly. It does not allocate a name list
before checking for duplicates. Its erasure agrees with an ordinary
left-to-right fold that implements the same index assignment and duplicate
policy. Tests cover source-order lookup, absent names, competing duplicates,
100,000 distinct names, and a million-entry input whose second name is already
a duplicate. That last indexing call records eleven operations; construction of
the supplied input array is outside the call.

The standalone `nameIndexCosted?` helper also scans its array directly. It
returns the first matching index, as proved against Lean's `Array.findIdx?`.
Each mismatch costs five operations: iteration, read, comparison, Boolean
test, and index increment. A match costs four because no increment follows.
Converting the completed scan to an optional index costs one more operation.
The bound is `5N + 1` for `N` names, including the empty input's final test.
Named source compilation uses the reusable index above, not this linear helper.

### Dense table queries

Unary, binary, and ternary queries record 8, 11, and 14 operations. These
counts include width products, coordinate arithmetic, fixed field selection,
flat indexing, a checked array read, and the optional-result test. They are
constant in the model size under the stated array and numeric interfaces.

Projection queries stop at different points. An invalid slot costs two
operations. An absent array cell costs eight, a cell without a stored result
costs nine, and a stored result costs eleven, including its range check.
Missing or out-of-range results preserve the tuple-as-default behavior.
A closure query costs two operations when the world matrix is absent and
six when it is present, including a cell that is itself absent.

Each native query uses the counted core's erasure through an unconditional
function equality. The proofs cover raw tables as well as well-formed compiled
tables. They establish value correspondence, not equal runtime costs for
sparse kernel reduction and dense native execution. Connecting these query
costs to the checker's abstract atomic-call counters remains a pipeline proof
obligation in the [behavior contract](behavior-contract.md).

The small `Costed` record operations and query definitions inline during
native compilation. Inlining exposes the selected `value` to Lean's optimizer,
which can remove unused cost fields. Inspection of the generated C confirms
that all five query erasures contain no cost-helper calls or record/closure
allocations. This is a generated-code check, not a wall-clock performance bound.

### Table initialization and traversal

For `C` unary, binary, ternary, and projection cells in total,
`initializeDenseCosted` records exactly `2C + 11` operations. The eleven
operations compute the four array sizes. Each cell then contributes one loop
iteration and one write. Native execution uses the initializer's counted
erasure through a proved function equality. Dense-table construction also
counts its projection-arity scan, bounded by `5F` for `F` facts.

`writeDenseFactCosted` includes row-major index arithmetic and a checked array
write. Unary, binary, ternary, and projection insertions cost 8, 11, 14, and 6
operations, respectively. A derived fact costs one tag test and leaves dense
tables unchanged. Ternary width uses three explicit multiplications. A proved
function equality makes native insertion use this counted core while retaining
the compact kernel definition. The equality covers all raw tables and indices.
Each `set!` invocation is one checked-write primitive under the array interface.

Dense insertion traverses its input array directly, adding an iteration and a
read per fact. Its bound is therefore `16F`; together with the arity scan, this
contributes `21F` before initialization and closure costs. Duplicate facts still
incur insertion work, although writing the same cell again is idempotent.

Array initialization, vector construction, and array folds accumulate costs
during traversal. They do not retain a pending addition for every visited
entry. Their correspondence proofs preserve values and counts. The fast suite
includes million-entry regressions for initialization, vector construction,
successful folds, and an early-error fold. These tests check stack behavior
and exact counts; they do not measure allocator or garbage-collector costs.

`mapArrayExceptCosted` also works directly on arrays. If each callback costs
at most `p`, mapping `N` inputs costs at most `N·(p + 4)`. A visited input
charges an iteration, a read, and an error-tag test. Success adds an output
write. The first error ends the map, so neither an output write for that input
nor any later callback is charged. The value-equivalence theorem uses Lean's
standard array map as its specification and preserves output order.

Name resolution charges one map query and one test for presence or absence.
Before continuing, `exceptBindCosted` charges one test of whether its input
is a success or an error. It charges that test even when an error skips the
continuation. Fact resolution also counts the fact-kind and scope tests.
The most expensive fact has four thing references and a named world, for
20 operations. Including array traversal gives the batch bound `24F`.

A product-family record with `S` witness slots costs at most `6S + 10`.
The ten fixed operations cover the length comparison and its Boolean test,
two name lookups, and four success/error tests. Mapping `R` records with `S`
total slots is bounded by `R·(6S + 14)`.
Here `F` counts source facts, and witness slots count both dimension and type
references. The batch bound uses the total slot count to bound each record,
so it is conservative. Only visited work contributes to the executable count.

The source compiler adds four tests between its name and reference stages.
The resolved tail adds two tests around materialization and projection
validation. Even empty compilation therefore costs 21 operations: four in
the two index stages, six stage-result tests, and eleven size computations
for table initialization. `Test/Complexity/Resolution.lean` checks this count
and the first-error order when several parts of the source are invalid.

### Explicit fact and family construction

`compileExplicitFactCosted` constructs the inspectable sparse store before
dense materialization. A unary, binary, or ternary fact costs five operations:
a tag test, fixed field-name lookup, map read, array write, and map insertion.
A projection or derived fact costs two operations: the tag test and array
write. Map operations use the stated abstract interface. Constructed lookup
closures are not queried during insertion; their later query costs belong to
the checker or diagnostics, and closure allocation is outside the cost model.

The explicit-AST compiler uses direct counted array folds for facts and
product-family registration. Sparse construction costs at most `7F` for `F`
facts, including iteration and read costs. Registering `R` existing family
records costs `3R`; conversion of their witness arrays is a separate stage.
A proved function equality makes native explicit-AST compilation use the
counted core while preserving the compact kernel definition for certificates.

### Scope expansion

Scope expansion appends facts directly into one output array. Each fact's
`everywhere` scope visits worlds in ascending order; an explicit `at` scope
visits only its stated world. The executable constructs neither a world-range
array nor a temporary expansion array for each input fact. Value-equivalence
proofs relate these writes to an append-based specification, preserving fact
order, world order, output size, projection arity, and taxonomy weights.

For `F` input facts and `E` emitted facts, the exact count is `3E + 4F`.
Each output charges a numeric-loop iteration, a world-indexed fact
instantiation, and a write. Each input charges two scope-dispatch operations
and the outer array iteration and read. An `everywhere` fact with zero worlds
therefore costs four units and emits nothing. This expansion pass does not
validate raw world coordinates: an explicit `at` scope still emits its stated
world. Source-name resolution performs the corresponding validation upstream.

Fact instantiation is a stated unit-cost interface. The raw resolved-fact type
can contain a function from a world index to a derived-fact string. Applying
that function is counted as one instantiation; this does not bound arbitrary
function bodies or string-character work. The source-to-model repair must
connect that interface to the functions produced by named source resolution.

### Fixed taxonomy expansion

`Complexity/Taxonomy.lean` defines the ordered parent graph for all 49 unary
fields. Its traversal returns the starting field and every reachable ancestor,
with no duplicates. It visits parents in declaration order and finishes each
parent's ancestry before proceeding to the next parent (depth-first order).
The output array doubles as the visited set: a repeated field ends that visit.

A rank decreases on every parent edge, and the largest rank is four. A
five-level recursion therefore covers every path. Kernel-checked theorems
establish termination, agreement with reflexive parent reachability, and
duplicate-free output. An exhaustive regression preserves the previously
observed order for every field. The two extra raw string names remain supported
outside the typed registry.

The counter records visited-set scans, parent reads, tests, iterations, and
output writes. Exhaustive kernel evaluation proves that one ancestor search
costs at most 202 operations and emits at most eight fields. These are bounds
for the fixed graph, not for a user-supplied taxonomy. No native evaluation
axiom is used in these taxonomy proofs.

Batch expansion appends consequences directly into one fact array. For `F`
input facts, `addTaxonomyFactsCosted_cost_le` proves a bound of `229F`:
two operations to visit and read each input, one tag test, at most 202 search
operations, and three operations for each of at most eight emitted ancestors.
A non-unary fact costs only four operations. Repeated input facts remain
repeated in this output; dense insertion later treats identical facts as
idempotent. The compiler uses the counted function's value, and the source
bound applies `229F` to the number of facts emitted by scope expansion.

### Reflexive specialization

An instantiation fact identifies a type that must specialize itself in every
world. Expansion preserves all original facts as an output prefix, then emits
those reflexive witnesses in input order and ascending world order. Repeated
targets produce repeated witnesses; later table insertion is idempotent.

The counted implementation first copies the prefix into an output array, at
three operations per fact: iteration, read, and write. It then scans the input
again. Each binary fact costs five inspection operations, including the field
comparison and its Boolean test; other facts cost three. Each emitted witness
costs a numeric iteration, construction, and write. No world-range or temporary
witness array is constructed.

For `F` input facts and `W` worlds, the proved bound is `F·(3W + 8)`.
Value equivalence preserves the output sequence specified above. Size and
projection-arity proofs feed the source compiler bound, where `F` is the
number of facts produced by taxonomy expansion. Two instantiations and two
worlds emit six total facts and record 28 operations. Tests also cover zero
worlds, non-instantiation facts, repeated targets, and a million witnesses.

### Projection validation

`validateTupleProjections` erases the counted validator. For `F` compiled facts
and `P = things · maximumProjectionArity · worlds` projection cells, its proved
bound is `2P + 18F`. The arity scan inspects every fact and costs at most `5F`.
Initialization charges `2P` for iterations and cell writes. Validation visits
facts in order, using at most 13 operations per visited fact, and stops at the
first conflict. Identical duplicate projections remain valid.

The bound includes the full arity scan and initialization even when validation
fails early. One projection in a two-cell table records 22 operations. Two
identical projections, or a conflict at the second projection, record 40.
Adding a non-projection fact after that conflict raises the count to 44: the
arity scan reads it, but validation does not. Regression tests check these
exact counts. A separate equivalence theorem preserves the uninstrumented
validator's result and error payload for every input.

### Counted closure

For `T` things, the evidence-carrying Warshall core has the proved bound
`23T³ + 15T² + 5T`. Its loops build reachability and first-hop matrices while
accumulating costs. A matrix access reads a row and then a cell, so it costs
two units. Each vector constructor charges a loop iteration and a write per
entry. Edge queries use the stated one-operation interface, which must be
justified by the caller's explicit relation representation.

| Phase | Worst-case cost |
| --- | --- |
| Initial reachability matrix | `5T² + 2T` |
| Initial first-hop matrix | `6T² + 2T` |
| Reachability update for one pivot | `10T² + 2T` |
| First-hop update for one pivot | `13T² + 2T` |
| Conversion of both matrices to row-major arrays | `13T²` |

The `T` pivots run in descending order. This preserves the deterministic
first-hop choices of the compact recurrence, without allocating a pivot list.
Adding one iteration charge per pivot gives the core bound. Conversion and
three charges per world—one iteration and two array writes—give the compiler
closure bound `W·(23T³ + 28T² + 5T + 3)` for `W` worlds. The matrix-only
executable omits first-hop construction and is bounded by `10T³ + 7T² + 3T`.

These are upper bounds, not exact costs assigned to each model. For two things,
the evidence-carrying core records 188 operations with no edges and 160 with
every edge present. Established reachability skips later tests. The size bound
is monotone; exact short-circuit work need not increase when facts are added.
Native regression tests check these counts, while inductive proofs establish
the general bounds and result correspondence.

Proved `csimp` function equalities select the counted closure's erasure in
native execution. Kernel reduction retains compact definitions. The compiler's
per-world builder has the same proved rewrite, including array conversion.

### Which representation receives the bound?

The operational bounds apply to the dense representation used by native
execution. They include dense-table construction, table writes, closure
precomputation, table reads, and checker control flow.

Lean's kernel uses compact sparse definitions when it checks generated
certificates. The sparse and dense implementations perform different
operations. The correspondence theorems prove that they return the same value.
They do not claim that both implementations take the same number of steps.

`toFiniteModel4Verified` requires a table-equality proof alongside the compiled
tables. Lean checks the function equality used by compiler simplification
(`csimp`) to select dense lookup. Raw `FactTables` lookup has no native override,
so absent or stale dense storage cannot change its meaning. The public raw
constructor `toFiniteModel4` keeps sparse lookup; generated DSL models use the
proof-carrying constructor. See [the repair contract](behavior-contract.md) for
the remaining operational-accounting obligations.

`ExplicitTableCorrespondence` packages the unary, binary, ternary, and tuple
projection results. `explicitCompilationGuarantee` combines that package with
`compileExplicitModelASTCosted_value`, which proves that counted compilation
erases to production compilation. These results require a well-bounded AST:
every resolved thing and world index must lie inside the encoded finite model.

The source-to-result theorem composes compiler and checker costs. Diagnostics
have a separate **output-sensitive** bound, which includes the amount of
evidence emitted as a parameter, because they run only after failure and
construct evidence. No theorem in this development bounds certificate
elaboration or kernel reduction.

## Input metrics

`SourceMetrics` includes worlds, things, source facts, name references, facts
after scope expansion, facts after deterministic taxonomy expansion, and an
explicit upper-size component for reflexive specialization. It also includes
projection declarations, product families, witness slots, and maximum
projection arity. `ModelMetrics` includes compiled primitive facts and
independently sized witness arrays. Dense table footprints include every
initialized unary, binary, ternary, projection, closure, and next-hop cell. The
last two are derived storage rather than source input and remain separate fields
so construction and space bounds cannot hide them.

The final scalar polynomial corollary is derived only after proving a
multivariate bound over all independently sized components.

## Verified-DSL theorem map

Here, “verified DSL” refers to the complete chain below. Its proof organization
draws on RadixExperiment: relate the executable interpreter to its semantics,
then prove preservation for each transformation. RadixExperiment supplies the
organizational precedent, not a complexity result for Lean UFO.

| Stage | Required theorem | Status |
| --- | --- | --- |
| Parser/emitter | documented trust boundary and generated-source validation | existing boundary; not kernel-verified parsing |
| Name resolution | success corresponds to the declared name environment | the production batch compiler builds world/thing indices once and reuses them for facts and product families. Direct array index construction has the proved bound `cost ≤ 6·names + 1`, including traversal, abstract map primitives, and final result conversion. The source stage adds one duplicate-error classification test. Each name resolution charges a map query and a presence test. Successful resolution preserves scope, taxonomy, and projection-arity metrics. |
| Scope/taxonomy/specialization passes | each pass preserves its stated source semantics | scope expansion costs exactly `3E + 4F` for `F` inputs and `E` outputs; fixed-taxonomy traversal costs at most `229F`; specialization costs at most `F·(3W + 8)` for `W` worlds. Each pass uses its own input fact count. Their value, size, cost, and projection-arity proofs connect to `SourceMetrics`. |
| Flat tables | compact and dense lookups return equal values; projection conflicts are rejected | Compact definitions support kernel reduction. `toFiniteModel4Verified` requires the equality proof used by the `csimp` native replacement. Raw lookup has no override. Theorems cover each fact write and the complete fact fold. `ExplicitTableCorrespondence` packages unary, binary, ternary, and projection lookup equality. Projection uses deterministic last-write semantics. Validation rejects different results for one projection coordinate and accepts identical duplicates. The cost theorem covers only the dense path. |
| Inherence closure | Warshall matrix corresponds to `MomentOf` | Compiler storage and axiom 68 use the proved sized-matrix recurrence. The compiler also stores deterministic first-hop evidence. Counted constructors, pivot steps, and row-major conversion give `W·(23T³+28T²+5T+3)` as an upper bound under the edge-query interface. See [Counted closure](#counted-closure) for the derivation and native correspondence. |
| Finite-model interpretation | compiled Boolean fields denote the corresponding `UFOSignature4` relations | core bridge theorems exist |
| Compiler | counted value equals compact production compilation | proved: source compilation uses a counted core, and `compileExplicitModelASTCosted_value` connects explicit-AST cost accounting to the compact proof-facing compiler. `compilerOperationalCost_le` covers every success and early-error branch with the explicit multivariate `sourceCompilerPolynomial`. Only afterwards, `source_compiler_scalar_polynomial_bound` derives the one-variable bound `463·inputSize⁴`, where `inputSize` contains every independently sized source component. |
| Checker | counted erasure equals production checker | Proved for the ordered 116-entry registry. The scalar counter bound is `3072·n⁸` under the atomic-query interface. Concrete query-cost composition remains open; see the details below. |
| Certification | successful Boolean checks imply `UFOAxioms4` | existing soundness theorem |
| Diagnostics | evidence is sound and its production cost is output-sensitive | The counted producer has a 128-item budget, deterministic truncation, and proved counter/output bounds. The sparse lookup and formula-size accounting repairs remain open, so these results do not yet establish the full production-cost claim. |

### Registry and diagnostic bounds

The checker registry contains all 116 registered checks, including the
qua-individual/endurance condition and the identity, symmetry, and seven-thing
triangle distance extensions. Its delayed computations run in order and stop
at the first failure. The returned Boolean equals `checkAxioms4Checks M` tested
with `Array.all`. Finite quantifiers have proved `true`/`∀` and `true`/`∃`
correspondences.

Each entry supplies its own cost proof. `fixed_registry_data_complexity_bound`
sums those bounds and the visited registry's traversal charges. Axiom 99's
witness, family-search, and nested checker bounds have degrees two, three, and
six. The other 115 entries contribute monomial coefficients totaling 3030;
axiom 99 contributes 42. The resulting bound is `3072·n⁸`, where `n` includes
dense relation cells, family records, and both witness arrays. The generic
registry theorem composes supplied per-check bounds; it does not derive one
from arbitrary formula size.

The compiler/checker counter sum is bounded by
`3535·(sourceSize+modelSize)⁸`. Its source and model are independent inputs.
Connecting them, and composing concrete query costs, remain open obligations.
Semantic soundness is a separate theorem.

Diagnostic assignments stream in lexicographic order and stop when the budget
is full. The final limiter costs `2·emitted+1`. The current
`diagnosticWitnessesInnerCostBound` accounts for formula traversal, evaluation,
minimization, rendering, and the specialized axiom 68, 71, 73, 78, 79, and 99
analyzers under their existing query interface.
`diagnosticWitnessesBudgetedCosted_cost_le_inner_add_emitted` adds emitted-output
work to that counter bound. Sparse query costs and the formula-size bound still
need repair. Diagnostics remain outside the headline certification bound:
they run on failure and construct user-facing output.

## Module layout

```text
LeanUfo/UFO/DSL/Complexity/
  CostModel.lean
  Metrics.lean
  Tables.lean
  Closure.lean
  Taxonomy.lean
  Compiler.lean
  Checker.lean
  Diagnostics.lean
  Theorems.lean
```

`LeanUfo/UFO/DSL/Complexity.lean` is the aggregate import. Production entry
points use the counted core directly.

## Acceptance evidence

Verification includes exact hand-checked counts on tiny examples;
monotonicity tests; sparse, dense, cyclic, projection-heavy, and product-family
generators; semantic regression fixtures; closure correctness and cubic
scaling; compiler and checker erasure; fixed-registry and parameterized
theorems; separate output-sensitive diagnostic bounds; and generated scaling
measurements. The final gate, `LEANUFO_PERFORMANCE_TESTS=1 lake test`, includes
the full semantic suite and every user-facing example. Certificate export,
validation, and the generated complexity benchmark were also checked.

The benchmark checks monotonicity on controlled prefix-growing families. It
checks compiler cost independently as worlds, things, facts, and witness slots
are added, and it checks compiler and checker costs across each reported model
family. This is not a universal monotonicity theorem for arbitrary checker
inputs: changing a fact can make a short-circuiting checker stop earlier.

### Generated scaling benchmark

`lake exe complexity-benchmarks` emits CSV for five deterministic model
families at 2, 3, 5, and 9 things. The executable records source facts,
product-family slots, explicit relation/projection cells, compiler cost,
checker cost, elapsed milliseconds, and the Boolean result. Sparse and cyclic
families have linear fact streams; dense and projection-heavy families have
quadratic streams; product families independently scale their witness slots.

The first native run on 2026-09-01 produced the following representative exact
unit-cost rows (wall-clock resolution was too coarse at these small sizes):

| family | things | facts | witness slots | relation cells | projection cells | compiler cost | checker cost |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sparse | 9 | 9 | 0 | 3438 | 0 | 13681 | 35259 |
| dense | 9 | 81 | 0 | 3438 | 0 | 13969 | 35259 |
| cyclic | 9 | 9 | 0 | 3438 | 0 | 13681 | 35259 |
| product | 9 | 9 | 162 | 3438 | 0 | 13690 | 35259 |
| projection | 9 | 81 | 0 | 3438 | 81 | 14050 | 35259 |

These rows are measurements, not theorems. In particular, every generated
model currently fails early in the ordered registry, so its observed checker
cost exercises short-circuiting rather than the worst-case registry bound.
The exact operational theorems above remain the proof evidence.

### Certification performance regression baseline

Performance acceptance uses individual targets and suite totals. Previously
passing examples must retain their existing resource limits. A repeatable
slowdown exceeding both 10% and two seconds requires user approval. Suspicious
timings are repeated under matching toolchain, dependency, machine, and cache
conditions, without overlapping test suites. Compiler, checker, diagnostic,
and certificate-elaboration timings are separated where measurable.

The review repairs are compared against their starting revision `ee87137`.
The older comparison below remains visible so that changing the repair
baseline does not erase earlier regressions.

The proof-facing/executable representation split is also checked against the
last revision before this refactor (`6a21fd5`). These are wall-clock engineering
measurements, not complexity theorems. Both revisions used separate build
directories with the same dependency checkout.

| target | base | complexity refactor | result |
| --- | ---: | ---: | --- |
| `Company` | 6.1 s | 8.3 s | certifies |
| `WoodenTable` | 7.9 s | 10 s | certifies |
| `FlowerPropertyChange` | 8.4 s | 12 s | certifies |
| `RedirectedWalk` | 8.4 s | 12 s | certifies |
| smaller example set, excluding Relator | 79.56 s | 108.06 s | certifies |
| positive Relator probe | 3649.25 s | 205.06 s | certifies; 17.8 times faster |
| full semantic test profile | 173.36 s | 170.54 s | passes; effectively unchanged |

The four small examples are 27–43% slower and the smaller set is 36% slower,
so proof elaboration has a measurable constant-factor regression. They
remain well below the former heartbeat failure. The Relator probe, which is the
dominant certification stress case, is substantially faster. Release checks
must retain both views. The complete suite detects semantic regressions. The
Examples aggregate includes Relator and detects proof-performance
regressions through the optional performance profile.

## References

- Moshe Y. Vardi, [Finite Model Theory and Its Applications](https://www.cs.rice.edu/~vardi/papers/ircsmv7.pdf), for data versus combined complexity in finite-model checking.
- Florent Madelaine and Barnaby Martin, [On the Complexity of the Model Checking Problem](https://epubs.siam.org/doi/10.1137/140965715), for parameterized finite-model-checking classifications.
- Yue Niu et al., [A Cost-Aware Logical Framework](https://doi.org/10.1145/3498670), POPL 2022, for compositional cost-aware semantics.
- Max Haslbeck, [Hoare Logics for Time Bounds](https://link.springer.com/chapter/10.1007/978-3-319-89960-2_9), for verified operational time bounds.
- Yannick Forster et al., [A Verified Time Hierarchy Theorem for Turing Machines](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20), for explicit machine/implementation correspondence in mechanized complexity.
- Tobias Nipkow et al., [Verified Textbook Algorithms](https://www.proof.cit.tum.de/~nipkow/pubs/atva20.pdf), for proving algorithm correctness and complexity together.
- Tobias Roßkopf and Tobias Nipkow, [For a practical perspective on verified checker representations](https://link.springer.com/chapter/10.1007/978-3-030-79876-5_6).
- Leonardo de Moura, [RadixExperiment](https://github.com/leodemoura/RadixExperiment), for verified-DSL proof organization: interpreter correspondence and pass-by-pass preservation.

## Current limitations

The theorem uses the unit-cost model defined above. It does not bound string
characters, allocation, garbage collection, elaboration, kernel checking,
native instructions, Lake overhead, or wall-clock time. Indexed source-name
operations remain explicit abstract map primitives; they are not claimed to be
constant-time hash-map operations.

Native relation and projection lookup uses typed dense arrays. Kernel reduction
uses compact sparse definitions so generated certificate proofs do not expand
dense initialization. Sparse maps and lookup closures also remain where
diagnostics and certificate reuse need them. The headline checker bound counts
the named dense executable lookups and does not assign a constant-time cost to
the sparse definitions.
The recursive inherence definition remains as a specification; production
closure and axiom 68 use the proved cubic matrix implementation.

The concrete parser and declaration emitter are inside the documented trusted
boundary. Lean validates the generated declarations and certificates, but this
work does not prove the parser itself correct. The benchmark reports runtime
measurements for comparison with the operational theorem; those measurements
are not proof evidence.
