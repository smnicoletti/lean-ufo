# Concrete complexity and the verified-DSL boundary

## Overview

The main result bounds the algorithmic work of certifying an explicitly stored
finite UFO model. The compiler builds indexed tables and a reachability matrix.
The checker stops when an answer is known. Diagnostics count their searches
and the evidence they produce. Proofs connect these computations to the
production workflow and show that adding counters cannot change their answers.

For the fixed 116-check registry, the bound is polynomial in source size.
Arbitrary formulas have a separate bound that depends on their nesting depth.
Neither result bounds Lean proof processing or elapsed time.

The [research sources](#references) have distinct roles: Vardi and
Madelaine–Martin ground the fixed-formula versus variable-formula distinction.
Niu and Haslbeck inform compositional operation counts. Verified-algorithm
work by Nipkow and colleagues informs correctness with cost proofs.
RadixExperiment informs the organization of implementation proofs.
These are methodological foundations, not imported proofs of Lean UFO.

## Claims

The primary result concerns **data complexity**: it measures growth when the UFO
checker registry is fixed (currently 116 checks) and only the finite model grows.
The secondary results concern **combined complexity**: growth when both
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
compiler and checker use **cost erasure**, which discards the recorded cost
and retains the computed value. Production uses that erasure directly or
through a proved native substitution. The substitution authorizes Lean's
compiler to execute the counted erasure while kernel proofs retain a compact
definition. Mere equality to an unrelated counted implementation would not
establish this execution connection.

## Source-result consistency and coordinate bounds

`compileModelSource_ok_constructionInvariant` connects a successful source
compiler call to the record it actually returns. Its
`CompiledModelSource.ConstructionInvariant` states that the AST dimensions match
the source name arrays, the AST stores the returned facts and families, the
tables are the compilation of that AST, and the expanded facts come from the
returned resolved facts. The proof follows successful branches of the existing
counted compiler without introducing another compiler implementation.

`compileModelSource_ok_wellBounded` proves that every primitive fact in the
returned AST uses valid world and thing coordinates. The name-index builder
assigns consecutive coordinates. Successful resolvers preserve their bounds,
and scope, taxonomy, and reflexive-specialization expansion preserve those
bounds in the emitted facts. A hand-built `NameIndex` needs an explicit
`NameIndex.InBounds` premise because its map can contain arbitrary numbers.

`compileModelSource_ok_lookups_agree` supplies sparse/dense lookup agreement
for the returned tables and source dimensions from compiler success alone.
Tuple slots have an independent size and need not be smaller than the thing
count. The coordinate theorem does not interpret stored derived-proposition
strings. Successful family resolution supplies the coordinate and length
conditions needed by the readback proof below. Empty source domains compile
successfully, so finite-model positivity remains a separate premise.

These results connect the source to its compiled tables. The counted finite-model
constructor covers the next operation, and `Complexity/Queries.lean` supplies
primitive-query value/cost correspondence. The workflow theorem below uses
both results on the actual compiler output. By contrast,
`combined_source_to_certification_scalar_bound` bounds a sum on two independent
inputs. That component theorem is not the source-to-workflow result.

## Unit-cost machine model

`Costed α` stores a computed `value` and a `Nat` cost. The model charges the
operations named at their executable definitions: Boolean operations,
comparisons, loop iterations, array accesses and writes, initialized cells,
string-format calls and concatenations, and emitted diagnostic
items. A **short-circuit** operation
stops when its result is already known. For example, `false && q` does not
evaluate `q`, and a universal scan stops at its first false item. The counted
combinators follow Lean's left-to-right order and do not charge such unevaluated
branches.

The arithmetic that accumulates the cost is instrumentation and is not itself
charged. A value-erasure theorem proves that instrumentation cannot change the
result; it does not prove that native execution removes all bookkeeping. The
generated name-conversion code, for example, still runs the counted fold before
projecting its value. Runtime overhead remains a performance-testing obligation.

These are selected source-level operations, not native function-call counts.
Definition checks 1, 53–55, 58–59, 63–64, 69–70, and 74 bind their shared
predicate once per visited assignment. Both equivalence operands reuse its
Boolean answer, and its search cost contributes once. Lean's native
compiler can make further optimizations. Full counted correspondence does not
imply equality with native call counts.

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
direct indices and charge each visited cell read. The compiler sections below
give the costs of name resolution, fact expansion, and table construction.

One array bounds check or access is a unit-cost primitive. Dense initialization
is charged per cell. Source name indexing includes hash-map insertions and
lookups as abstract primitives in the cost sum. It does not count their
character-level work. No constant-time theorem is claimed for
hash maps or strings unless a separate verified interface is introduced.
Character-level string work, allocation, garbage collection, elaboration,
kernel checking, native instructions, Lake overhead, and operating-system
scheduling are outside this theorem. Benchmarks measure those effects
separately.

Proof construction also affects build time. The larger diagnostic value proofs
use `dsimp only` to reduce `Costed` record projections before rewriting lookup
correspondence. Rewriting each monadic bind separately can create large proof
terms that repeat unused cost fields. Definitional reduction keeps those
intermediate terms small. The kernel still checks the same value equalities,
and neither the executable code nor its operational counts change.

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
sparse kernel reduction and dense native execution. `Complexity/Queries.lean`
connects concrete table-query costs to the registered checker computations.

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

### Product-family conversion

`Compiler/ProductFamilies.lean` converts each resolved family into one finite
witness per world. The production finite-model constructor uses
`productFamilyWitnesses`, the value of `productFamilyWitnessesCosted`.
`productFamilyWitnessesCosted_value` proves agreement with a cost-free
specification of the nested loops. Valid outputs retain family order, ascending
world order, and duplicates. Invalid coordinates or unequal array lengths cause
that family/world pair to emit no witness.

`ProductFamilySpec.WellFormed` requires valid thing coordinates and equal array
lengths. Successful source compilation proves those conditions for every
returned family. Table construction preserves the complete family array.
`productFamilyWitnessesCosted_readback` then recovers exactly the input families
paired with worlds in ascending order. Readback removes the `Fin` proofs and
recovers the original numeric arrays, including their order and duplicates.
The specification uses lists; the executable converter retains its numeric
and array loops.

`compileModelSource_ok_modelFamilies_readback` composes these results for the
production finite-model field. It requires compiler success and positive domain
sizes, with no independent family-validity or table-agreement premise. These
conditions preserve witness data. They do not establish axiom 99, whose relation
conditions still require the checker.

Validation checks the domain, quality type, world, dimension array, type array,
and array lengths in that order. A failed field skips later fields. Inside an
array, a failed coordinate leaves the accumulator in its failure state for the remaining
traversal. Those later visits perform no coordinate checks or writes.
`natArrayToFinArrayCosted` charges an initial array construction, a traversal/read
pair per element, an accumulator test, and the executed validation and writes.
Its bound for `L` elements is `7L + 1`. These are unit-cost source operations,
not native instruction counts or allocator timings.

For `W` worlds, `F` family records, and `S` total slots in both arrays across all
families, `productFamilyWitnessesCosted_cost_le_slots` proves:

```text
conversion cost ≤ 1 + W · (7S + 20F) + 2F
```

The initial output costs one. Each family costs two outer traversal operations.
Each world costs one loop operation plus at most `7(D + U) + 19` for conversion,
where `D` and `U` are that family's dimension and type array lengths. Conversion
repeats for every world, so the bound includes `W · S`. Zero worlds skip all
validation but retain the outer traversal cost. Thing count affects whether
coordinates are valid, but does not increase the unit-cost upper bound.

These results cover witness conversion. The product-family diagnostic theorem
below connects the two registry searches across that conversion. The source-linked
component bound includes conversion before one aggregate checker call.

### Finite-model construction

Generated models use `toFiniteModel4Cached`, the value of
`toFiniteModel4CachedCosted`. For W worlds, F source family records, and S total
slots across both witness arrays, the construction bound is:

```text
model construction cost ≤ 4 + W · (7S + 20F) + 2F
```

`finiteModelConstructionCost_le_sourceMetrics` proves this bound from successful
source compilation. Name resolution preserves family and slot counts, and the
compiler stores that exact registry in its returned tables. The constructor
requires primitive lookup agreement, cache correctness, matching dimensions,
and positive world and thing counts. Source compilation alone does not prove
positivity because it also accepts empty domains.

The constructor performs the counted witness conversion, constructs a lookup
bundle, assembles the finite-model record, and installs the existing cache.
Installation adds one fixed-record operation without copying any cache cells.
`finiteModelConstruction_bound_mono` proves that the upper bound does not
decrease when W, F, or S grows. Exact costs still reflect validation order and
can decrease when a failure stops conversion early.

The uncached `toFiniteModel4` and `toFiniteModel4Verified` constructors add two
operations to witness conversion, giving the corresponding bound with leading
constant three. Their counted definitions have equal values and costs, as
proved by `toFiniteModel4VerifiedCosted_eq`. The verified constructor carries
the equality proof needed for dense native lookups. A caller that supplies its
own lookup bundle uses `toFiniteModel4WithLookupsCosted`, which charges only
witness conversion and the model-record operation.

Fixed-record construction costs one unit in this operational model.
`assembleFiniteModel4` installs relation functions without evaluating them.
Function closure allocation, administrative record projections, allocator
timings, and proof checking are outside the model. Query costs belong to the
consumer; constructing a record does not bound arbitrary functions stored in it.

Cache installation preserves the interpreted UFO signature
(`toFiniteModel4Cached_signature`) and the exact witness registry
(`toFiniteModel4Cached_productFamilies`). The latter guarantee is separate
because product-family witnesses are not fields of the UFO signature.
`finiteModelFamilyMetrics_eq_sourceMetrics` gives W · F witnesses and W · S
slots for the cached model. It preserves family order, duplicate registrations,
and repeated slots.

`finiteModelCacheSize_eq_sourceMetrics` gives W world slots and W · T² cells
for T things, independently of which edges are present. If R is the source
relation-cell count, the cached model's checker-size metric is therefore:

```text
W + T + R + W · F + W · S + (W + W · T²) + 1
```

`finiteModelInputSize_le_sourceInputSize_sq` bounds this metric by 3N², where
N is `SourceMetrics.inputSize`. Family replication contributes
W(F + S) ≤ N². The base-model sum is at most N. Cache storage is also at most
N: one dense binary relation already has W · T² cells, and R includes every
binary field. Since N ≥ 1, the two linear contributions are each at most N².
Hand-built caches can contain unused extra storage, which `checkerCacheSize`
also counts; the source theorem uses the compiler's exact sized matrices.

These results connect the source to the cached constructor's cost and output
size. The registry's separate query-cost equalities cover the compiled model.

### Source-linked compiler/checker composition

`source_linked_component_bound` charges successful source compilation, cached
model construction, and one aggregate checker call on the constructed model.
The model is determined by the compiler's returned tables. It is not an
independent parameter. Successful compilation supplies lookup agreement,
cache correctness, and matching table dimensions. Positive world and thing
counts are separate premises because the source compiler accepts empty domains.

For source metrics m and N = m.inputSize, the bound is:

```text
sourceCompilerPolynomial(m)
  + 4 + W(7S + 20F) + 2F
  + 8367(3N²)⁸
```

Here W counts source worlds, F counts family records, and S counts both
witness arrays' slots. The model-size theorem supplies 3N². Construction costs
at most 26N²: world-replicated family conversion contributes at most 20N²,
and fixed setup and outer traversal contribute at most 6N².

`source_linked_component_scalar_bound` gives `54,896,424·N¹⁶` for the same
component sum. Its coefficient is `511 + 26 + 8367·3⁸`. The degree-sixteen
corollary follows from the degree-eight checker bound and quadratic model-size
bound. It is a derived upper bound, not an exact execution count or a claim
that this exponent is tight.

This result does not bound the complete `ufo_model` command. The frontend runs
per-field preflight checks: it elaborates a trial proof before submitting the
generated theorem declaration. These steps can evaluate the checker more than
once, with extra calls on reuse or failure paths. The frontend also validates
derived assertions, performs the axiom-68
precheck, and can produce failure reports. A full frontend bound must account
for those calls where they execute. Parser, elaborator, kernel, allocator, and
string-character costs remain outside the operational model.

Before these attempts, `certificateReuseSource?` erases the counted reuse
planner. Fresh mode costs one operation and skips both comparisons. Otherwise,
the planner compares child and parent source records in order. Equal sources
skip footprint lookup. Unequal sources trigger a search for the field's
footprint: the list of relation tables on which its checker depends. The
planner then compares those ordered table rows and any required projection or
product-family data. It selects a candidate parent; the generated proof must
still establish equal checker results.

`Complexity/Reuse.lean` proves that these comparisons and the candidate choice
preserve the previous policy. Arrays retain order and duplicates. A length
mismatch or first unequal item stops the scan. An array comparison costs at
most `2 + Σᵢ(cᵢ + 4)`, where cᵢ bounds the item comparison. The two units test
lengths; each visited item adds two reads, a loop step, and a Boolean test.

Source comparison costs at most `13 + 5W + 5T + 18F + 13P + 5S`: W and T
count declared worlds and things, F counts source facts, P counts families,
and S counts all dimension and type slots. These are the child source's
sizes. The scalar corollary is `18N` for its complete explicit input size N.
`reuseFootprintCostBound` sums named parent-table rows, projection rows, and
family slots, with coordinate comparison costs of 3, 5, and 7 for pairs,
triples, and quadruples. `certificateReuseSource_cost_le` composes the source
bound, registry search, and a conservative sum of footprint bounds. That sum
is not executed work: only one footprint can be selected.

The bounds have nonnegative size coefficients; actual counts can decrease
when execution stops earlier. String comparisons and map reads retain the
compiler's abstract primitive interface, not a native hash-table or character
cost guarantee.

`compileExplicitModelAST_rowSizes` bounds each stored row array by the expanded
fact count. Every fact appends at most one row; family registration, dense
writes, and closure construction preserve these arrays. Duplicates remain
stored entries. Successful source compilation bounds the expanded fact count
and preserves family records and slots. `certificateReuseSource_source_bound`
uses these facts to prove `18C + 11023P` for the executed planner, where C and P
are the complete child and parent source sizes. Parent tables must be the
returned compiler output. No independent table-size assumption is needed.
`certificateReuseSource_bound_mono` proves that this bound cannot decrease
when either size grows. The coefficient uses the fixed 116-field registry.
The checked-attempt driver includes this planner cost. The source-workflow
theorem connects its proof callbacks to the concrete scheduled checker calls.

`Certificate/Checking.run` owns reuse planning and the initial and fresh
checked-field attempts. It runs the planner once and supplies the selected
parent to both initial callbacks. Fresh fallback does not repeat planning.
The production frontend supplies planner and elaboration callbacks and erases
the driver's branch charges. `runCosted` uses the same control flow with counted
callbacks. `checkedField_erasure` proves equal results after cost erasure.

A failed preflight skips its declaration. Only failed reuse permits a fresh
attempt. The driver adds at most five operations for Boolean tests and the
reuse-option match. `checkedField_cost_le` bounds its cost by those five
operations plus the planner cost and four proof-callback costs. An exact count
includes only callbacks that run. This local bound takes callback costs as
inputs; the source-linked preparation theorems supply them from actual checker
computations. Semantic proof attempts and diagnostic production are composed
separately in the workflow theorem.

`source_planned_checked_bound` supplies the actual source-linked planner to
this driver. Its bound includes `18C + 11023P`, five driver operations, and
the four proof-callback costs. The initial callbacks use the planner's actual
selected parent. Their costs remain explicit; this theorem does not assume
arbitrary proof callbacks have polynomial bounds.

`Certificate/Checking.runField` surrounds the checked attempts with the
axiom-68 precheck and semantic proof attempts. A failed precheck skips reuse
planning and all proofs. A failed checked attempt skips semantic proofs.
After a checked success, the command-only policy runs once. Other fields get
a semantic term trial before declaration. Its failure skips the declaration.

`fieldDriver_erasure` preserves the result and reuse source.
`fieldDriver_cost_le` adds at most five driver decisions to the precheck,
checked-attempt, policy, and semantic-trial costs, plus the larger of the two
declaration-mode costs. Only one declaration mode can run. The policy costs at
most 15 operations. The guarded precheck costs two on other fields and adds
those two operations to the axiom-68 closure search when selected.
`source_field_precheck_scalar_bound` bounds this precheck by 124N⁴ for the
complete source size N. It substitutes the declared world and thing counts;
no independently sized finite model, compiler-success premise, or positive
domain assumption is needed. This common bound allows the full search, while
the exact count on other fields remains two.

`Certificate/Checking.runFields` owns the outer registry loop in production.
It records a field as completed only after its callback succeeds. After the
first failure, later visits invoke no callback and cost three operations each.
The returned completed names and reuse rows feed the widget and manifest.

`registryDriver_erasure` proves equal results after erasure.
`registryDriver_cost_le` gives `2 + Σᵢ (Cᵢ + 7)`, where Cᵢ is the counted
callback cost for field i. Two operations initialize the progress arrays.
Seven cover a successful visit, result selection, a stored-name read, and both
array writes. A failed visit needs five. This bound charges each permitted
callback once, including calls after an early failure only in the upper bound.
Production uses `CertField.field` as the stored-name accessor. The theorem
does not bound an arbitrary computation substituted for that accessor.
The source-workflow theorem supplies these callback costs from concrete model
construction, checked attempts, semantic proofs' algorithm calls, and selected
diagnostics.

`certificationRegistry_control_bound` composes both drivers with the production
precheck and command-only policy. For each registered field, it reserves
`2W(T(T(11T + 26) + 19) + 3) + 33` operations plus its checked and semantic
callback costs. W and T count worlds and things. The bound reserves the
closure search for every field, although execution selects it only for axiom
68. The constant 33 combines six precheck operations, fifteen policy
operations, five field-driver decisions, and seven outer-driver operations.
This is a control-flow composition bound, not a polynomial claim about
arbitrary proof callbacks or Lean elaboration.

Generated reuse proofs call `resultsAgree` on the ordinary child and parent
checker results. This Boolean function erases `resultsAgreeCosted`.
`compareChecksCosted` composes both counted checker calls with that same
comparison primitive. `compareChecks_erasure` proves equal values, and
`reuseComparison_cost` gives the exact cost C+P+1, where C and P are the child
and parent checker costs. Model construction remains separate. Keeping cost
records out of the generated proof goals preserves compact proof elaboration.
Trials and declarations can each run this comparison. Agreement still requires
the parent's checked theorem before the child can be certified.

`CertificateChecking.ProofScript` supplies both the emitted proof and its
registered native-call requests. A request either checks an expected Boolean
answer or compares the child and parent results for one field. Its generated
proof term includes an explicit type naming those inputs. Ordinary proof text
appears between requests. Axioms 73 and 78 keep their future prerequisite
before the failed-field check in counterexample probes.

`checkedScript_checkerCalls` proves one requested checker evaluation for fresh
proofs and two for reuse. `semanticScript_checkerCalls` proves at most one;
`counterexampleScript_checkerCalls` proves at most two. Trials and declarations
render the same script but remain separate attempts. These numbers count
requested checker invocations, not unit-cost operations or observed execution.
`script_prefix_checkerCalls_le` permits stopping before later requests. Axiom
99's general counterexample tactic is excluded proof work, not a registered
request. The source-linked preparation and workflow theorems below connect
reached requests to their operation costs and the shared driver.
The Lean parser, emitter, and proof engine
remain outside the verified boundary.

Here a prefix means the first zero or more requests, in order.
`registeredCounterexample_names_agree` checks every direct backend in the fixed
registry: its completeness proof and typed native request name the same checker.

`registered_check_scalar_bound` bounds each call in the fixed UFO registry by
8367n⁸, where n is that model's `checkerInputSize`. It uses the sum of proved
entry budgets, not the aggregate checker's actual early-exit count. For example,
a registry can stop after four operations while a later entry costs 100 when
called separately.

`source_registered_check_scalar_bound` connects the selected entry to the
successful compiler's returned model. With positive world and thing counts,
the per-call source bound is 54895887N¹⁶ for `N = (sourceMetrics source).inputSize`.
`registered_reuse_comparison_bound` includes both model sizes and the Boolean
comparison.

Generated model definitions can rebuild tables from the returned AST before
constructing the finite model. `explicitCompilation_cost_le_source` proves that
this table-building stage costs no more than the successful source compilation
that first ran it. `explicitCompilation_source_scalar_bound` therefore gives
511N⁴ per reconstruction. This is an upper bound, not a charge for rerunning
name resolution: the reconstruction's exact count comes from
`compileExplicitModelASTCosted compiled.ast`.

`source_registered_reconstruction_scalar_bound` adds that table reconstruction,
finite-model construction, and one selected registered check. Its bound is
54,896,424N¹⁶, using 511N⁴, 26N², and 54,895,887N¹⁶ for the three terms.
It requires successful source compilation and positive domain sizes, and the
selected check must belong to the constructed model's registry. These results
leave runtime dispatch unchanged. The source-workflow theorem composes these
calls with the remaining frontend work, including separate child and parent
reconstruction allowances on reuse.

`compileVerifiedModelCosted` composes the table builder with the cached model
constructor, using the tables that the builder returns. Its erasure equals
`compileVerifiedModel`, and its exact cost is the sum of those two stages.
Successful compilation bounds this construction by 537N⁴ and the returned
model's `checkerInputSize` by 3N². `reconstructedCheckCosted` then executes its
checker on that returned model. `reconstructedCheck_source_bound` proves the
54,896,424N¹⁶ bound for this composition. Its membership premise identifies the
full counted registry result, including cost, rather than only the Boolean answer.

`nativeRequestCosted` includes the generated decision's Boolean comparison.
An expected-answer request evaluates only the child and costs its operand cost
plus one. An agreement request evaluates the child, then the parent, and adds
one comparison. Both generated terms use the erasure of this comparison.
For C and P, the child and parent `sourceMetrics.inputSize` values, the bounds
are 54,896,424C¹⁶ + 1 and
54,896,424C¹⁶ + 54,896,424P¹⁶ + 1, respectively. Each operand allows one model
reconstruction. These bounds do not assert that native execution always rebuilds
a shared model. The emitter resolves field names before generating checker calls.
The theorems assume those resolved computations and do not verify name resolution
inside the emitter. The shared preparation and workflow drivers establish how
many requests each frontend attempt reaches, as described in
[Source-to-workflow composition](#source-to-workflow-composition).

`nativeScript_prefix_source_bound` sums these concrete request costs for any
supplied prefix. With K requested checker invocations and R decisions in the
whole script, its bound is `K · 54,896,424 · max(C,P)¹⁶ + R`. An agreement
contributes two to K and one to R. The theorem requires successful compilation,
positive domains, and counted registry membership for the resolved operands.
Expected-answer requests require no parent membership proof.
`nativeScript_source_bound_mono` proves that increasing C or P cannot reduce
this bound. The prefix theorem does not prove which calls the frontend reaches
or include list traversal in the production count.

The executor in `Certificate/Execution.lean` runs each script's
requests before elaborating the remaining proof text. It uses Lean's existing
native-decision API and inserts the returned proofs into that text.
`proofScriptPrepare_erasure` preserves the prepared text or first error.
`proofScriptPrepare_cost_le` bounds the shared loop by the sum of native
callback costs plus `3R + 1`, where R is the script's request count. Parsing,
proof rendering, and elaboration are excluded. `Syntax.lean` calls this
executor inside the existing proof-attempt error capture. Preparation uses
the resource options attached to that proof source. The remaining proof text
receives the native proofs, so it has no registered checker tactic to repeat.
Axiom 99's general counterexample tactic remains excluded proof work.
Source-size composition of the native callback costs and the complete workflow
bound require separate proofs; the loop theorem alone does not establish them.

`nativeScript_prepare_source_bound` now composes that loop with concrete
source reconstruction, checker execution, and Boolean comparison. Its bound
is `K · 54,896,424 · max(C,P)¹⁶ + 4R + 1`, with C, P, K, and R as above.
One comparison and at most three loop operations contribute four per request.
Successful compilation, positive domains, and counted registry membership
remain premises. `nativeScript_prepare_source_bound_mono` proves monotonicity
in both source sizes.

Proof production is represented by its returned proof or error, outside the
algorithmic cost model. A preparation error skips later requests.
`preparedProofAttemptCosted` also takes the observed result of subsequent Lean
elaboration as a Boolean input. It does not assign zero cost to an arbitrary
executable callback. Its erasure preserves the failure status, and its
algorithmic cost is exactly the preparation cost. The results below first
bound checked retries, semantic attempts, and counterexample probes separately,
then compose them through the production drivers.

`preparedCheckedAttemptsCosted` composes preparation with the production retry
driver. It includes the initial trial and declaration, followed by fresh
fallback only after failed reuse. Its erasure preserves that sequence and the
returned reuse choice. If one reconstructed checker costs at most B, the
checked phase costs at most the planner cost plus `6B + 25`. Initial reuse
allows two decisions with two operands each; fresh fallback allows two with
one operand each. Four preparation/comparison costs contribute at most twenty,
and the retry driver contributes at most five.

`source_prepared_checked_bound` supplies the concrete operands and planner,
giving `18C + 11023P + 6 · 54,896,424 · max(C,P)¹⁶ + 25`. Both sources must
compile successfully with positive domains, and the selected counted checker
must belong to the fixed registry on both returned models. The proof supplies
native costs from those facts rather than assuming callback-cost bounds.

For one source of size N, `source_prepared_proof_bound` gives the preparation
bound `K · 54,896,424 · N¹⁶ + 4R + 1`, where K counts checker operands and R
counts native requests. It requires successful compilation, positive domains,
and full counted registry membership on the returned model. It permits any
observed proof-production or elaboration failure.

`source_prepared_semantic_bound` applies that result to both semantic proof
forms. Each has at most one checker operand, so each attempt costs at most
`54,896,424 · N¹⁶ + 5`. `source_prepared_counterexample_bound` applies it to
the failed field's counterexample probe. At most two operands give the bound
`2 · 54,896,424 · N¹⁶ + 9`. These are bounds on registered native algorithm
work and preparation control, not on proof search or elaboration. They do not
by themselves establish a bound for the whole certification workflow. The
following result adds registry traversal and the selected final report.

### Source-to-workflow composition

`Complexity/Certification.lean` supplies the composition. Its `CompiledInput`
contains a source, its successful compiler result, and positive-domain proofs.
No independent table or model is admitted. A parent is optional: root models
use the actual constant `none` planner, whose cost is zero. Extension models
use the counted source/table reuse planner.

Let C and P be the child and parent source sizes, N = max(C,P), and
B = 54,896,424 · N¹⁶. For a root model, P = C. The per-field bound is
`124C⁴ + 18C + 11023P + 8B + 55`. It includes the closure precheck, reuse
planning, checked-proof trials and declarations, fresh fallback, semantic
attempts, and policy/control operations. The registry adds seven operations
per field and two array initializations. With R registered fields, its bound is
`2 + R · (124C⁴ + 18C + 11023P + 8B + 62)`.

Two more shared drivers connect the branches that surround this registry:

- `runAfterAssertions` saves the derived-fact precheck once. A known false
  assertion skips its Lean proof. Either kind of assertion failure skips the
  registry and selects the report from the saved precheck result.
- `reportAfterRegistry` runs a counterexample probe and failure analysis only
  for the recorded failed field. It runs neither after registry success and
  preserves the completed prefix and reuse rows.

Both drivers are used by `Syntax.lean` and have cost-erasure theorems.
`postCompileCosted` also counts construction of the two name arrays, which
subsequent stages reuse. `sourceWorkflow_bound` adds the actual source compiler
cost and gives the multivariate workflow bound. Its native checker premises
require full counted registry membership on the reconstructed models, not
merely Boolean agreement or a supplied callback-cost inequality.

`sourceWorkflow_scalar_bound` gives
`(439,182,619 · R + 109,798,953) · N¹⁶ + D`. The fixed-registry corollary,
`sourceWorkflow_fixed_data_bound`, substitutes R = 116 and gives
`51,054,982,757 · N¹⁶ + D`. These deliberately loose coefficients come from
the component inequalities; they are not assigned operation counts or timing
predictions. `sourceWorkflowScalarBound_mono` proves monotonicity in N, R, and D.

D is the selected `failureReportBound`, described below; it is zero if the
registry succeeds. If derived assertions fail first, the registry and final
report do not run. The upper bound may still reserve their allowance, while
the counted execution records the early exit. Diagnostic formula search and
emitted output keep their own parameters. A variable R here means a sequence
of registered, bounded checker computations, not unrestricted input formulas.

The theorem assumes successful source compilation and nonempty finite-model
domains. Rejected sources remain covered by the compiler's independent bound.
The parent certificate is existing input; its previous certification is not
repeated. Source-name map operations retain the stated abstract primitive
contract. Parsing, name resolution inside Lean's generated proof expressions,
native compilation, proof search/elaboration, kernel checking, final declaration
and manifest emission, and widgets are outside this result. In particular,
axiom 99's general proof-search fallback is not a registered native request.
These exclusions do not remove the registered checker computations executed
by proof preparation: those are counted, including reconstruction allowances.

After the counterexample probe, `certificationFailureReportCosted` selects the
report used by the frontend. `certificationFailureReport_value` proves its
classification, text, and row order. Timeout classification runs once and stops
at the first matching error. Only the selected analyzer runs.

`certificationFailureReport_cost_le` bounds this selection by
`18 + 17E + I + 7R + C + 3K`. Here E counts probe errors, I is the existing
witness-analyzer bound, R counts its retained rows, C is the closure-analyzer
bound, and K counts its rows. The bound allows both analyzers, although a run
selects at most one. The 17E term includes classification, error-row production,
and copying. String operations have unit cost. Character scanning and the
proof probe are excluded. The witness limit remains 128 rows and does not cap
the surrounding probe messages.

The semantic proofs for axioms 73, 78, and 79 reuse available checked
theorems. Their potential additional checker calls are:

| Generated proof body | Axiom 73 | Axiom 78 | Axiom 79 |
| --- | --- | --- | --- |
| Successful semantic proof | check 75 | check 79 | none |
| Counterexample probe | checks 75 and 73 | checks 79 and 78 | check 79 |

The success path already has the current field's checked theorem. A failure
probe cannot assume that theorem exists, so it evaluates the failed field as
false. Checks 75 and 79 are later prerequisites of axioms 73 and 78 and must
still execute. Trial and declaration elaboration each run the listed success
body. A probe stops if a prerequisite proof fails, before testing the current
field. The table therefore lists possible calls, not an exact execution count.
These calls use the existing counted checkers and their per-axiom bounds.
The source-workflow theorem bounds these calls through the shared preparation
and attempt drivers. The inventory alone would not establish that bound.

### Scope expansion

Scope expansion appends facts directly into one output array. Each fact's
`everywhere` scope visits worlds in ascending order; an explicit `at` scope
visits only its stated world. The executable constructs neither a world-range
array nor a temporary expansion array for each input fact. Value-equivalence
proofs relate these writes to an append-based specification, preserving fact
order, world order, output size, projection arity, and taxonomy weights.

For F input facts, let e(f) be the number of outputs for fact f and let E be
their sum. The exact count is
`Σ_f (instantiationCost(f)+2)·e(f) + 4F`, bounded by `31E+4F`.
The two operations per output are a numeric-loop iteration and an array write.
Each input adds two scope-dispatch operations, an outer iteration, and a read.
An `everywhere` fact with zero worlds therefore costs four units and emits
nothing. An explicit `at` scope still emits its stated world, even outside the
raw domain. Source-name resolution validates world references upstream.

Primitive instantiation costs one dispatch operation, so primitive-only input
has exact cost `3E+4F`. A derived assertion stores a field name and one to four
resolved thing coordinates in `ResolvedDerivedFact`. Instantiation adds the
cost of `renderDerivedFactCosted`, which builds the Lean proposition for that
world. The resolved AST contains no arbitrary rendering function.

`Compiler/DerivedFacts.lean` proves that rendering preserves the certificate
text and costs at most 28 unit operations. Unary and binary fields select the
required UFO signature through at most seven or four comparisons, respectively.
Each visited comparison and branch costs two operations. Each coordinate costs
three operations to format, followed by two concatenations to append it.
The largest branch is the seventh unary definition: 14 selection operations,
three for its head, ten for its coordinates and separators, and one arity
dispatch. Fact instantiation thus costs at most 29.

Coordinates change the text but not these operation counts. String-character
processing, including numeric formatting length, remains outside the unit-cost
model. The frontend's separate summary rendering call is also outside this
compiler bound. Source metrics already include every expanded fact and argument
reference. With the rendering charge, the resolved compiler tail has scalar
bound `447N⁴` and the complete source compiler has bound `511N⁴`, where N is
`SourceMetrics.inputSize`.

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

For T things and edge queries costing at most E operations,
`warshallStateEvalCosted_cost_le` bounds the evidence-carrying Warshall core by
`23T³ + (2E + 13)T² + 5T`. The callback returns both its Boolean value and its
executed cost. A diagonal cell skips the callback because reflexivity already
determines reachability. Initial reachability and first-hop construction each
query the off-diagonal pairs once. Pivot steps use the resulting matrices and
make no further input-edge queries.

A matrix access reads a row and then a cell, so it costs two operations. Each
vector constructor charges a loop iteration and a write per entry.
`warshallStateCosted` supplies the special one-operation callback interface,
giving `23T³ + 15T² + 5T`. The compiler instead uses the counted dense binary
read, with E = 11 and core bound `23T³ + 35T² + 5T`.

| Phase | Worst-case cost |
| --- | --- |
| Initial reachability matrix | `(E + 4)T² + 2T` |
| Initial first-hop matrix | `(E + 5)T² + 2T` |
| Reachability update for one pivot | `10T² + 2T` |
| First-hop update for one pivot | `13T² + 2T` |
| Conversion of both matrices to row-major arrays | `13T²` |

The `T` pivots run in descending order. This preserves the deterministic
first-hop choices of the compact recurrence, without allocating a pivot list.
Adding one iteration charge per pivot gives the core bound. Conversion and
three charges per world (one iteration and two array writes) give the compiler
closure bound `W·(23T³ + 48T² + 5T + 3)` for W worlds. Its edge callback and
typed binary queries share `FactTables.binaryCellCosted`, which counts width
and coordinate arithmetic, field selection, flat indexing, the checked read,
and the option test. The eleven-operation total is proved for every input.
The matrix-only Boolean-callback API omits first-hop construction and is bounded
by `10T³ + 7T² + 3T` under its one-operation query premise.

These are upper bounds, not exact costs assigned to each model. For two things,
the one-operation core records 188 operations with no edges and 160 with every
edge present. Dense queries raise these counts to 228 and 200. The four input
queries each contribute ten additional operations. Row-major conversion adds
52 operations, giving 280 and 252 for the compiler's per-world builder.
Established reachability skips later tests. The size bound is monotone, but
exact short-circuit work need not increase when facts are added.
Native regression tests check these counts, while inductive proofs establish
the general bounds and result correspondence.

For models without a cache, the checker constructs closures through `inherenceMatricesCosted`.
Its world traversal calls `warshallMatrixEvalCosted` and accumulates each returned
cost. `inherenceMatricesCosted_cost_le` gives
`W(10T³ + 17T² + 3T + 2)`, including two vector-construction operations per world.
For one world and two things, its count is 110 without edges and 94 with a
two-edge cycle. Each executed inherence query contributes eleven operations.
`compiledInherenceMatrices_eq_countedTables` connects that charge to the
verified uncached model's complete dense binary read. Arbitrary hand-written
relation functions still need their own cost contract. Generated cached models
read the compiler's proved cache without closure construction or matrix conversion.

The matrix-only core accepts counted callbacks. If each edge query costs at
most B, its bound is `10T³+(B+6)T²+3T`. Initialization skips diagonal queries
and calls each off-diagonal query once. Pivot updates read only stored cells,
so the concrete edge cost changes the quadratic term, not the cubic term.
The one-operation Boolean interface specializes this same executable core.
The bound is proved monotone in both T and B. Exact counts can decrease when
added edges let a pivot update skip later reads.

`reachableInheresInWarshallCosted` charges three reads for each checker closure
query: the world matrix, the source row, and the target cell. Finite indices
already carry bounds proofs, so these reads need no optional-result tests.
`ultimateBearerOfCosted_cost` gives the exact branch costs: ten operations
when the candidate is a moment, otherwise ten plus the reachability query's
returned cost. The ten operations are an eight-operation unary table read,
a negation, and a branch test. A moment
cannot be an ultimate bearer, so the first branch skips that query. Axiom 68
uses the same counted bearer search for both storage representations. With a
query bound E, uniqueness costs at most `T(T(E + 15) + E + 13)`.

`compiledBearerSearch_eq_countedTables` proves equality of the complete
counted search to loops over the compiler's unary evaluator. It includes both
candidate discovery and the repeated scan that rejects a second qualifying
bearer. `compiledAx68WithReachability_eq_countedTables` also connects the
outer moment premise, with bound `T(W(T(T(E+15)+E+13)+12)+2)`.
The added twelve operations per world are the unary read, implication tests,
and world-loop overhead.

`FiniteModel4.inherenceCache` stores arrays with a proof that their lookups equal
the model's inherence reachability. `checkAx68Costed` charges one operation to
select a cache or the uncached path. Cached queries call the same
`closureLookupCosted` as compiler diagnostics, at a cost of at most six.
`checkAx68Costed_cost_le_of_cached` therefore excludes closure construction:
its bound is `T(W(T(T · 21 + 19) + 12) + 2) + 1`.
`compiledAx68_eq_countedTables` proves full counted equality for this cached
production call, including cache selection and the actual flat arrays.
`checkAx68_eq_warshall` proves both execution paths equal the compact matrix
specification. The generic registry bound permits fallback construction and
uses E = 6 to cover both query representations.

Proved `csimp` function equalities select the counted closure's erasure in
native execution. Kernel reduction retains compact definitions. The compiler's
per-world builder has the same proved rewrite, including array conversion.
The checker likewise keeps a compact `inherenceMatrices` definition for kernel
reduction. `inherenceMatrices_eq_erased` proves equality to its counted native
implementation for every finite model.

### Stored closure correspondence

`FactTables.InherenceCacheValid` states that both stored caches are the exact
per-world outputs of Warshall over the table's dense inherence relation.
The invariant fixes world order, array sizes, reachability cells, and first-hop
entries. `withDenseFacts_inherenceCacheValid` proves it after materialization,
even if the incoming tables contain a stale or malformed cache. The compiler
overwrites that cache after it populates the dense relation cells.

`compileModelSource_ok_inherenceCacheValid` derives the invariant from source
success. `compileModelSource_ok_modelClosure_lookup` then proves that stored
closure lookup answers the reachability recurrence for the actual constructed
model. Source success supplies cache validity, dimensions, and primitive-table
agreement. No independent graph or cache is assumed. The existing counted
lookup has the same value and costs at most six operations.

Primitive-table agreement alone cannot justify reuse: replacing cached rows
does not change primitive lookups. Regression tests retain that agreement
while rejecting swapped world rows and forged next-hop entries. The exact
next-hop readback identifies which entries Warshall produced.
`compileModelSource_ok_modelPath_sound` proves that every returned path follows
inherence edges in the source-produced model and ends at the requested target.
`compileModelSource_ok_modelPath_exists_iff` proves that reconstruction succeeds
exactly for reachable pairs within the existing fuel limit. The checker reads
the reachability matrix; diagnostic path reconstruction reads the next-hop
entries.

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
constructor `toFiniteModel4` keeps sparse lookup; generated DSL models use
`toFiniteModel4Cached`, which adds proved closure reuse to the verified primitive
constructor. The [workflow theorem](#source-to-workflow-composition) composes
source compilation, model construction, checks, and selected reports.

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
| Scope/taxonomy/specialization passes | each pass preserves its stated source semantics | scope expansion costs at most `31E + 4F` for `F` inputs and `E` outputs, including derived proposition rendering; fixed-taxonomy traversal costs at most `229F`; specialization costs at most `F·(3W + 8)` for `W` worlds. Each pass uses its own input fact count. Their value, size, cost, and projection-arity proofs connect to `SourceMetrics`. |
| Flat tables | compact and dense lookups return equal values; projection conflicts are rejected | Compact definitions support kernel reduction. `toFiniteModel4Verified` requires the equality proof used by the `csimp` native replacement. Raw lookup has no override. Theorems cover each fact write and the complete fact fold. `ExplicitTableCorrespondence` packages unary, binary, ternary, and projection lookup equality. Projection uses deterministic last-write semantics. Validation rejects different results for one projection coordinate and accepts identical duplicates. The cost theorem covers only the dense path. |
| Inherence closure | Warshall matrix corresponds to `MomentOf` | Compiler storage and axiom 68 use the proved sized-matrix recurrence. The compiler also stores deterministic first-hop evidence. Its counted constructors, eleven-operation dense edge reads, pivot steps, and row-major conversion give `W·(23T³+48T²+5T+3)` as an upper bound. Uncached checker construction also has a proved dense-edge cost connection, with bound `W(10T³+17T²+3T+2)`. The complete cached axiom-68 call has proved table-cost correspondence. See [Counted closure](#counted-closure) for the derivation and native correspondence. |
| Finite-model interpretation | compiled Boolean fields denote the corresponding `UFOSignature4` relations | core bridge theorems exist |
| Compiler | counted value equals compact production compilation | proved: source compilation uses a counted core, and `compileExplicitModelASTCosted_value` connects explicit-AST cost accounting to the compact proof-facing compiler. `compilerOperationalCost_le` covers every success and early-error branch with the explicit multivariate `sourceCompilerPolynomial`. Only afterwards, `source_compiler_scalar_polynomial_bound` derives the one-variable bound `511·inputSize⁴`, where `inputSize` contains every independently sized source component. |
| Checker | counted erasure equals production checker | Proved for the ordered 116-entry registry. Concrete table-cost equalities cover 112 entries; the four definition checks return `⟨true, 0⟩`. The model-size bound is `8367·n⁸`. Eleven identified checks explicitly share their predicate result. `Complexity/Certification.lean` composes the scheduled calls. |
| Certification | successful Boolean checks imply `UFOAxioms4` | existing soundness theorem |
| Diagnostics | evidence is sound and its production cost is output-sensitive | Both axiom reports and pre-certification derived-assertion reports have compositional production-cost and output bounds. Their default caps are 128 and nine rows respectively. Formula evaluation has a separate node-count and quantifier-depth bound. Path reconstruction is sound and complete for compiled caches. The workflow theorem includes the selected diagnostic allowance separately from its certification polynomial. |

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
six. Expanding the registry bound, including traversal and axiom 99's outer
loops, gives ordinary monomial coefficients totaling 8269. The remaining
product-family search term contributes 98 after its cubic bound is applied.
The resulting bound is `8367·n⁸`, where `n` includes
dense relation cells, family records, and both witness arrays. The generic
registry theorem composes supplied per-check bounds; it does not derive one
from arbitrary formula size.

The compiler/checker counter sum is bounded by
`8878·(sourceSize+modelSize)⁸`. Its source and model are independent inputs.
The source-linked component theorem above connects successful compilation to
model construction and one checker call. `Complexity/Certification.lean`
supplies the source-to-workflow composition through the shared drivers.
Semantic soundness is a separate theorem.

#### Instantiation scans and axioms 1–17

All checks from 1 through 17 have full counted-computation equalities to the
compiler's table evaluators in `Complexity/Queries.lean`. These equalities
retain the original loop order, repeated scans, and skipped queries.

`typeBCosted` searches for an instance of its candidate across all W worlds and
T things, visiting worlds first. Here “type” is a UFO classification of a model
thing, not Lean's `Type` universe. The current-world argument does not restrict
the search. An instance ends both loops. Each visited binary read costs 11,
with two more operations per thing and two per world. Write `Q = W(13T+2)`
for its upper bound. `individualBCosted` negates the answer at cost at most
`Q+1`. Checking that every world has no instance negates each visited world's
answer and costs at most `R = W(13T+3)`.

Instance subsumption tests that every instance of x also instantiates y.
It skips the second read after a false first read and stops at the first
counterexample. Its bound is `S = W(26T+2)`, including both loop levels.
`subDefBCosted` first checks that both arguments are types, then tests
subsumption, with bound `2Q+S+2`. The second type scan and subsumption run
only when the preceding test succeeds.

| Check | Cost bound |
| --- | --- |
| Axiom 1 | T(W(2Q+4)+2) |
| Axiom 2 | T(W(Q+R+5)+2) |
| Axiom 3 | T(T(W(2Q+17)+2)+2) |
| Axiom 4 | W(T(T(T(Q+27)+2)+2)+2) |
| Axiom 5 | T(T(W(2Q+S+17)+2)+2) |
| Axiom 6 | T(T(T(W(74T+54)+2)+2)+2) |
| Axioms 7 and 8 | T(W(Q+13)+2) |
| Axiom 10 | T(W(Q+22)+2) |
| Axioms 15 and 16 | T(W(Q+12)+2) |

Axiom 1 binds one type scan at each thing/world pair. On a two-thing,
two-world model with no instantiation facts, it returns true at cost 244.
A first-position instance lowers the cost to 160 without changing the answer.
The theorem does not replace this tautology with a constant-time result.
The existing upper bound retains slack for a second scan.

Axiom 6's premise has four binary reads, three conjunction tests, and two
negations, giving at most 49 operations. Each upper/lower witness candidate
has three binary reads and two conjunction tests, plus two loop operations:
at most 37. The upper search runs first. The lower search runs only if the
upper search finds no witness. Together they cost at most `74T+1`.
The implication and world-loop overhead give the per-world bound `74T+54`.

The larger type-scan bound also propagates to axioms 44 and 66.
`Complexity/Queries.lean` supplies full value/cost correspondence for their
concrete table queries. The source-to-workflow theorem composes registered
checks with actual compilation and selected failure reports.

#### Modal classification and taxonomy bridges

Axioms 18–23 and the three two-thing taxonomy bridges have full value/cost
equalities to the compiler's table evaluators. W counts worlds and T counts
things. The equalities require the actual compiled tables, dimensions, and
sparse/dense agreement, as for the other concrete query results.

A possible-instance scan and a necessary-instance scan each cost at most 13W:
eleven operations per binary read and two per visited world. Searching for
absence adds a negation per read, giving 14W. Rigidity first searches for a
possible instance, then checks all worlds only when it finds one. Its bound
is T(26W+4). Anti-rigidity uses an absence search as its second scan, giving
T(27W+4). Both scans restart at world zero for each thing.

| Check | Cost bound |
| --- | --- |
| Axiom 18 | T(W(T(26W+4)+21)+2) |
| Axiom 19 | T(W(T(27W+4)+21)+2) |
| Axiom 20 | T(40W+2) |
| Axiom 21 | T(W(T(13W+11)+12)+2) |
| Axiom 22 | T(T(W(W(24T+2)+25)+2)+2) |
| Axiom 23 | T(W(T(W(26T+2)+11)+21)+2) |
| Instantiation-to-endurant, subkind-to-sortal, non-sortal propagation | T(T(32W+2)+2) |

Axiom 20's consequent has three unary reads, two negations, and two
conjunction tests, totaling at most 28. Its outer unary read, equivalence,
and world loop add at most twelve.

Axiom 21 checks each candidate's kind field before scanning worlds for
necessary instantiation. This costs at most T(13W+11) per endurant/world pair.
Axiom 22 searches for a different kind in world-then-thing order. Each
alternative costs at most 22: unary read, binary read, two conjunction tests,
and one finite-index comparison. Including both loops gives W(24T+2).
The antecedent, its implication, and negating the search add 23, followed
by the world-loop cost two.

Axiom 23 reuses axiom 5's instance-subsumption scan, whose bound is W(26T+2).
Testing a candidate kind adds a unary read, conjunction, and thing-loop cost,
giving T(W(26T+2)+11). The endurant-type test, sortal equivalence, and outer
world loop add at most 21.

The bridge helper accepts counted predicates. Its bound adds the three
predicate bounds, three Boolean operations, and two world-loop operations.
Each taxonomy bridge uses two unary reads and one binary read, totaling 27.
The same helper serves axiom 48. Its part queries use a finite-index equality
test followed, when needed, by a counted binary-table lookup.
`compiledAx48_eq_countedTables` proves this correspondence for both values and
costs on the compiled cached model.

#### Unary checker calls with concrete table costs

`Complexity/Queries.lean` connects 31 registry checks to loops over
`unaryTypedTableCosted` on the compiler's cached model: axioms 9, 11–14, 17, 20,
24–41, 45, 83–85, 89, and the kind-stability bridge.
These are equalities of the complete `Costed Bool`, including the cost field.
The compiler's sparse/dense agreement proof is required for the actual tables
and dimensions. The cache does not change these unary fields.

Each unary lookup has eight operations: one width product, two coordinate
operations, field selection, two flat-index operations, a checked read, and an
option test. `unaryTableBlock_eq_counted` expands the checker's eight-operation
call charge into this counted computation. It is a block-correspondence proof,
not an upper bound attached to an unrelated function. No equality of sparse
kernel-reduction steps and dense native steps is claimed.

For T things and W worlds, implication costs at most T(20W+2) and disjointness
at most T(21W+2). Both skip the right lookup when the left result is false.
Disjointness adds one negation only when it executes the right lookup. A
one-thing, one-world implication therefore costs 14 with a false premise and
22 with a true premise. These counts include both finite loops.

Classification equivalences compare both sides once. Within each side,
conjunction skips its second operand after false, and disjunction skips it
after true. The proofs preserve these branches and the original loop order.
Their bounds include loop overhead:

| Check shape | Cost bound |
| --- | --- |
| `a ↔ (b ∧ c)` | T(29W+2) |
| `a ↔ (b ∧ ¬c)` | T(30W+2) |
| `(a ∨ b) ↔ (c ∧ d)` | T(38W+2) |
| World-first `¬(a ∧ b)` | W(20T+2) |
| `(a ∨ b) ↔ c`, or `a ↔ (b ∨ c)` | T(29W+2) |
| `(a ∨ (b ∨ c)) ↔ d` | T(38W+2) |
| Thing/world/world implication | T(W(20W+2)+2) |

Here a, b, c, and d are unary table answers at the current coordinates.
The last row compares answers in two worlds. Axiom 45 evaluates six
kind-refinement equivalences in order, with bound `6·(T(29W+2)+3)`.
Its registry adds three operations per visited entry and stops at the first
failure. On a one-thing, one-world model, all six false/false equivalences
cost 156 operations. A mismatch in the first entry costs 25; the same mismatch
in the last entry, after five false/false successes, costs 155.

The shared helpers accept Boolean relation functions. Their concrete
eight-operation implementation guarantee applies to the proved compiler
instances, not arbitrary hand-written functions. All registry query consumers
have concrete correspondence proofs. The scalar registry theorem bounds source
operations and supplies a component of the source-to-workflow bound.

#### Quality and classification by instances

The quality predicate and axioms 42–44 have full result-and-cost equalities to
the compiler's table evaluators. These equalities preserve repeated searches
and each check's loop order. They require the verified compiled model and its
actual table agreement.

Quality means that exactly one quality kind classifies a thing in the current
world. The checker scans candidate kinds in index order. For each match, it
restarts at index zero and checks that every matching kind has the same index.
A distinct match stops that competitor scan. The outer search then continues.
The implementation therefore retains a quadratic worst case in T, the number
of things.

A candidate test costs at most 20: a unary quality-kind read costs eight,
a binary instantiation read costs eleven, and conjunction adds one. The
instantiation read is skipped when the kind read is false. A competitor adds
an implication, finite-index equality, and loop overhead, for at most 25.
Thus the competitor scan costs at most 25T. Testing a candidate and its
uniqueness costs at most 25T+21. The outer loop gives the quality bound
K = T(25T+23).

Axiom 42 evaluates things before worlds. A true mode read skips quality.
Axiom 43 evaluates worlds before things, and a false mode read skips quality.
For W worlds, their bounds are T(W(K+21)+2) and W(T(K+12)+2), respectively.
The separate semantic theorems identify the checks with their UFO axioms.

Axiom 44 evaluates ten families in registry order. Each family first compares
its unary type classification with a possible-instance scan and, if an
instance exists, checks the family condition on every instance. Let
I = W(13T+2) bound the possible-instance scan. If the leaf condition costs at
most P, checking all instances costs at most C(P) = W(T(P+15)+2).
The fifteen comprises a binary read, implication, and inner-loop overhead.
The outer family bound is F(P) = T(W(I+C(P)+13)+2).

Nine families use a direct unary leaf, so their bound is F(8). The quality
family uses its full counted search, giving F(K). Registry traversal adds
three operations per visited family. The complete bound is
9(F(8)+3)+F(K)+3. A failed family skips later entries.

Exact two-thing tests give quality costs 24 with no candidate kinds, 61 for a
unique first kind, 73 for a unique last kind, and 121 for two matching kinds.
A one-thing fixture satisfying all axiom-44 families costs 610. A first-family
failure costs 58; a last-family failure costs 611. The latter adds one negation
because the left side of its equivalence is false. These fixtures isolate
axiom 44 and do not claim to satisfy the complete UFO registry.

The quality bound also propagates through axioms 92, 93, and 95–98. Their
concrete query correspondences are described under quality values and simple
and complex qualities. They contribute to the source-to-workflow bound above.

#### Specific kinds and part relations: axioms 46–52

These seven checks have full value-and-cost equalities to their compiled table
computations. Axiom 46 searches for one of six specific endurant kinds and
then checks instantiation. Each of the first five kind positions adds eight
for its unary read and one for the following Boolean branch. The final
position has no following branch, so the complete kind scan costs at most 53.
A witness adds an instantiation read, a conjunction, and loop overhead, giving
67T for T candidate things. The world and endurant loops give
T(W(W(67T+2)+12)+2) for W worlds.

Compiled part and overlap queries first compare their two thing coordinates.
Equal coordinates return true without reading the table. This is short-circuit
execution: an answer already determined by the first test skips the remaining
work. Equality and its branch cost two operations. Unequal coordinates also
read the binary table, giving thirteen operations in total. Proper-part
queries read their table directly and cost eleven.

The shared query annotation preserves the supplied relation's answer, including
for hand-written models that are not reflexive. Its implementation-cost claim
requires a compiled model. Under that premise, `reflexiveBinaryBlock_eq_counted`
proves equality of the whole counted result with the equality test followed,
when needed, by the actual table evaluator. It therefore justifies the
data-dependent charge without changing arbitrary-model semantics. The extra
arithmetic that maintains the cost counter remains outside the source-operation
model, as for the other counted combinators.

For T things and W worlds, the remaining bounds are:

| Check | Cost bound |
| --- | --- |
| Axiom 47, reflexivity | T(4W+2) |
| Axiom 48, antisymmetry | T(T(32W+2)+2) |
| Axiom 49, transitivity | T(T(T(44W+2)+2)+2) |
| Axiom 50, common-part overlap | T(T(W(29T+17)+2)+2) |
| Axiom 51, supplementation | T(T(W(30T+18)+2)+2) |
| Axiom 52, proper part | T(T(43W+2)+2) |

Reflexivity always uses the two-operation equal-coordinate path.
Antisymmetry uses at most two thirteen-operation part queries and one equality.
Transitivity uses at most three part queries. Their bounds include conjunction,
implication, and loop charges. Common-part search costs at most 29T:
two part queries, their conjunction, and two loop operations per candidate.
Supplementation adds one negation per candidate, giving 30T.
Axiom 52 includes its direct proper-part read and both guarded part queries.
All loops retain their original order and stop at the first decisive result.

On the two-thing empty-part fixture, axioms 47–52 cost 12, 68, 162, 154, 116,
and 112 respectively. A three-thing chain without its transitive edge fails
axiom 49 after 190 operations. These exact counts describe the visited work,
not a monotonicity claim about adding facts. The size-based bounds remain
monotone.

#### Functional dependence: axioms 53–55

The functional predicates have full value-and-cost correspondence with their
table-based source computations. For T things, the generic predicate first
tests instantiation and functions-as for each source candidate. A qualifying
source then needs a distinct functioning instance of the target type.

Each witness candidate costs at most 27: one inequality, two eleven-operation
binary reads, two conjunction branches, and two loop operations. The generic
predicate's premise costs at most 23. Implication and its outer loop add four,
giving the generic bound G = T(27T+27).

Individual functional dependence evaluates G first, then two instance reads
and a functions-as implication. Four binary reads and five Boolean operations
give I = G+49. A functional component first tests proper part. That read and
its conjunction add twelve, giving F = I+12.

For W worlds, the source-counter bounds are:

| Check | Cost bound |
| --- | --- |
| Axiom 53 | T(T(W(2G+4)+2)+2) |
| Axiom 54 | T(T(T(T(W(2I+4)+2)+2)+2)+2) |
| Axiom 55 | T(T(T(T(W(2F+4)+2)+2)+2)+2) |

Each definition check binds its predicate once and reuses the Boolean result.
The existing upper bounds remain valid but retain slack for a second search.
These formulas bound source operations, not native calls.

For one thing and one world, axiom 53 costs 23 with no instance, 39 with a
functioning instance but no distinct witness, and 34 with a non-functioning
instance. The searches cost 16, 31, and 27 respectively. Three quantifier
iterations add six operations, and equivalence adds one or two according to
the shared Boolean result. Value and full table-cost correspondence hold for
the shared computation.

In the three-thing fixture, generic dependence costs 48 when every source
instance test fails. A functioning source with no witness fails at 63. A
first target witness gives success at 90; a last target witness costs 106.
Individual dependence can stop after the generic failure at 64. If every
condition succeeds, it costs 139. A missing proper-part fact skips both
dependence searches at cost twelve.

#### Constitution: axioms 56–62

Constitutional dependence uses direct eleven-operation instantiation and
constituted-by reads. Its witness search costs at most 25T: two reads, one
conjunction, and two loop operations per candidate. The generic predicate
first tests each source instance, then searches for its constituting witness.
Its bound is C = T(25T+15), including the source read, implication, and loop.

The individual constitution predicate tests both instance fields before C.
After C succeeds, it checks the selected constituted-by field. Its bound is
D = C+36: three direct reads and three conjunction branches beyond C.
This order differs from individual functional dependence, which evaluates its
generic condition first. The counted correspondences preserve both orders.

Axiom 56 checks agreement of the endurant and perdurant classifications.
Each classification equivalence costs at most eighteen for two unary reads
and its Boolean operations. Their conjunction costs at most 37.
Axiom 57's premise has three binary and two unary reads joined by four
conjunctions, costing at most 53. Axiom 60's persistence scan tests existence
in each world before reading constituted-by, costing at most 23W.
For T things and W worlds:

| Check | Cost bound |
| --- | --- |
| Axiom 56 | T(T(52W+2)+2) |
| Axiom 57 | T(T(T(T(58W+2)+2)+2)+2) |
| Axiom 58 | T(T(W(2C+4)+2)+2) |
| Axiom 59 | T(T(T(T(W(2D+4)+2)+2)+2)+2) |
| Axiom 60 | T(T(W(23W+24)+2)+2) |
| Axiom 61 | T(T(27W+2)+2) |
| Axiom 62 | T(2W+2) |

Axioms 58 and 59 bind their shared predicate once per assignment. Their bounds
retain slack for a second search. Axiom 60 repeats its persistence scan for
each qualifying outer world in the source definition. Axiom 61 reads the reverse relation only
after the forward read succeeds. Axiom 62 makes no relation queries but still
visits its thing and world loops.

Exact tests distinguish a first and a last constitutional witness (39 and 53
operations), a missing individual instance that skips the generic search (24),
and a complete successful individual constitution (120). A two-world persistence
fixture costs 173 for success with no later existence, 113 for a later-world
failure, and 184 when the later-world constitution also holds. Added facts can
therefore shorten an actual visited path by exposing a failure. The size-based
upper bounds remain monotone.

#### Existential dependence and inherence

Axioms 63–67 have full counted equality to the compiled table evaluators.
Existential dependence scans every world in ascending order: each world where
x exists must also contain y. The supplied current-world coordinate does not
restrict this scan. A false x-existence read skips y's read. A counterexample
stops the scan. Each visited world costs twelve operations after a false
premise, or twenty when both existence reads execute. Write D = 20W for the
bound, where W counts worlds.

Existential independence requires counterexamples in both directions. If x
depends on y, it returns false without the reverse scan. Otherwise it tests
whether y depends on x. Its bound is I = 2D+3, including two negations and the
branch. Axioms 63 and 64 each bind their shared predicate once per assignment.
Their bounds retain slack for a second search. Independence still needs its
two directional searches when the first direction does not establish dependence.

Inherence is a binary table read costing eleven operations. Axiom 65 tests
existential dependence only for an inherence edge. Axiom 66 also requires its
source to be a moment. It then searches for an instance of the bearer across
the model and reads concrete-individual classification only if that search
fails. With Q = W(13T+2), where T counts things, the consequent costs at most
Q+18. Axiom 67 rejects the first pair of distinct bearers of one moment.

| Check | Bound |
| --- | --- |
| Axiom 63 | T(T(W(2D+4)+2)+2) |
| Axiom 64 | T(T(W(2I+4)+2)+2) |
| Axiom 65 | T(T(W(D+15)+2)+2) |
| Axiom 66 | T(T(W(Q+33)+2)+2) |
| Axiom 67 | T(T(T(28W+2)+2)+2) |

The shared dependence scan also contributes to external dependence and
axiom 79's boxed existence implication. Both bounds include D = 20W.
Axiom 79's full query correspondence also covers its other primitive calls.

#### External dependence

Axioms 69–70 have full value/cost equalities to dense table computations.
External dependence on y first requires existential dependence on y. It then
checks every bearer z of x in the supplied world. For each bearer, y and z must
each exist without the other in some world. The two witnesses need not be the
same world. Failed dependence skips the bearer scan. A failed first separation
scan skips the reverse scan.

A difference scan tests `ex y v && !ex z v` across worlds in ascending order.
Each visited world costs eleven operations if y is absent, or twenty if both
existence reads execute. With W worlds and T things, write D = 20W. A bearer
check costs at most S = 2D+14: two difference scans, an eleven-operation
inherence read, and three connective operations. Its false premise costs
thirteen operations and skips both scans.

External dependence therefore costs at most X = D+1+T(S+2). Mode classification
first reads the unary mode table, then searches for an external object only
if that read succeeds. Its bound is U = 9+T(X+2).

| Check | Bound |
| --- | --- |
| Axiom 69 | T(T(W(2X+4)+2)+2) |
| Axiom 70 | T(W(2U+4)+2) |

Both checks bind the shared predicate once. The bounds retain second-search slack.
The shared U bound also contributes to axioms 71–73 and 75.

#### Foundations and qua-individuals

Axioms 71–78 have full value/cost equalities to counted table computations.
All foundation and qua-individual reads cost eleven operations. Classification
reads cost eight. Part queries cost two operations for equal coordinates and
thirteen otherwise. The equality case returns true without a table read.

The unique-foundation query searches for a foundation candidate. When an edge
exists, an inner scan checks that every foundation equals that candidate.
A missing edge skips the inner scan. With T things, the inner scan costs at
most 16T, a candidate costs at most 16T+12, and the full query has bound
F = T(16T+14). A shared-foundation query searches for an object related to both
inputs. It reads the second relation only after a successful first read, giving
S = 25T. The qua-individual query searches for one `quaIndividualOf` edge, with
bound Q = 13T.

Let W count worlds and let U be the external-mode bound defined above.
Axiom 71 first checks the foundation edge. Its consequent requires an external
mode or a relator, and then a perdurant foundation. A successful mode test skips
the relator read. Axiom 73 compares each part with its classification as an
external mode that inheres in the proposed bearer and shares a foundation.
Its classification bound is C = U+S+13, and its part scan has bound P = T(C+17).
The two conjunctions still cost two operations when a false mode test skips
both subsequent queries.

| Check | Bound |
| --- | --- |
| Axiom 71 | T(T(W(U+33)+2)+2) |
| Axiom 72 | T(W(U+F+4)+2) |
| Axiom 73 | T(T(W(P+15)+2)+2) |
| Axiom 74 | T(W(2Q+4)+2) |
| Axiom 75 | T(W(Q+U+4)+2) |
| Axiom 76 | T(T(T(28W+2)+2)+2) |
| Axiom 77 | T(W(F+12)+2) |
| Axiom 78 | T(T(W(S+26)+2)+2) |

Axiom 74 binds its shared search once. Its bound retains second-search slack.
The shared Q and S bounds also contribute to axiom 79.

#### Relators, mediation, and type characterization

Axioms 79–82 and the qua-individual/endurant typing check have full value/cost
equalities to counted table computations. Proper-part, qua-individual,
foundation, instantiation, inherence, mediation, and characterization reads
cost eleven operations. Unary classification reads cost eight. Mediation uses
the reflexive part query, which costs two for equal coordinates and thirteen
otherwise. The following bounds use T things and W worlds.

Axiom 79 first searches for a proper part. If one exists, it checks every pair
of proper parts for compatible qua-individual status, a shared foundation, and
dependence in both directions. It then checks that every candidate compatible
with a proper part is itself a proper part. This last condition is called
closure in the code. It does not compute inherence paths. A failed proper-part
search skips both later scans; a failed pairwise check skips the closure check.

Write Q = 13T for qua-individual search, S = 25T for shared-foundation search,
and D = 20W for dependence. Pair compatibility has bound K = 2Q+S+2D+4.
Testing its two proper-part premises adds at most 25 operations. The closure
premise has bound J = Q+S+2D+15, and testing the consequent adds at most thirteen.
Thus the pairwise and closure bounds are A = T(T(K+27)+2) and
B = T(T(J+15)+2), respectively. The full characterization has bound
C = 13T+A+B+2. Axiom 79 has bound T(W(C+12)+2).

Mediation searches for a qua-individual of the target that is also part of the
relator. A failed qua-individual read skips the part query, giving search bound
R = 27T. Axiom 80 tests relator and endurant classification before that search.
Its bound is T(T(W(R+33)+2)+2). The separate qua-individual/endurant typing check
has bound T(T(23W+2)+2).

Type characterization checks witnesses in both directions. Every instance of
the endurant type needs an instance of the moment type that inheres in it.
Every moment instance needs a unique bearer that instantiates the endurant
type. The unique-bearer query checks instantiation and inherence before its
inner uniqueness scan. A missing candidate skips that scan. Its bound is
U = T(28T+26), including both binary reads in each uniqueness test.

The forward witness search has bound H = 25T, and the complete forward
direction has bound F = T(H+15). The reverse direction has bound G = T(U+15).
Axiom 81 first tests the two type classifications, then checks the forward
direction before the reverse direction. Its consequent has bound V = F+G+19.
Axiom 82 requires the reverse direction for a characterized quality type.

| Check | Bound |
| --- | --- |
| Axiom 81 | T(T(W(V+15)+2)+2) |
| Axiom 82 | T(T(W(G+24)+2)+2) |

These equations count the selected branches even when a supplied model fails
other UFO axioms. Their table correspondence requires the compiled model's
proved representation agreement, not successful certification of that model.

#### Quality structures and proper subset

Checks 86–88, 90, and 91 have full value/cost equalities to counted table
computations. A quality structure is associated with exactly one quality type.
The candidate test reads quality-type classification before the association
edge. It costs nine operations when classification fails and twenty otherwise.
With T things, the complete uniqueness search has bound Q = T(25T+23).

Checking whether a quale belongs to exactly one quality structure nests that
search inside another uniqueness search. Each structure test costs at most Q,
followed by one branch and an eleven-operation membership read. The outer
uniqueness scan has bound H = T(Q+17), and its candidate search has bound
E = T(Q+H+15). The type-to-structure query has the same bound: it substitutes
an association read for the membership read. Both queries repeat the structure
test for each candidate. Their bounds do not assume a cache.

Nonempty-set search has bound N = 13T. With W worlds, the registry bounds are:

| Check | Bound |
| --- | --- |
| Axiom 86 | T(W(Q+N+13)+2) |
| Axiom 87 | T(W(E+12)+2) |
| Axiom 88 | T(W(Q+21)+2) |
| Axiom 91 | T(W(E+21)+2) |

Axiom 86 checks set classification before searching for a member. Axiom 88
reads dimension classification only when domain classification is false.
Axiom 91 skips the structure search when intrinsic-moment-type classification
is false. These choices affect exact counts, while the bounds cover every branch.

Axiom 90 compares structures associated with a strict subtype pair. Its
antecedent checks two associations and both subtype directions, with bound 48.
The consequent first checks containment, then searches for an element present
only in the larger set. Each scan costs at most 26T, so proper-subset evaluation
has bound 52T+1. Failed containment skips the difference scan. The full bound is
T(T(T(T(W(52T+53)+2)+2)+2)+2).

The subtype relation here is a compiled binary table read. No recursive
subtype search is hidden in the antecedent. The source compiler charges
taxonomy expansion separately.

#### Quality values

Checks 92–94 have full counted-table equalities. Axiom 92 requires each
`hasValue x y` fact to connect a quality to a quale. It reads `hasValue`
first, searches for the unique quality kind of x, then reads y's quale
classification. A false premise skips the consequent. A failed quality search
skips the quale read.

Axiom 93 requires exactly one value for each quality. Each proposed value
costs eleven operations to read. Only a present value triggers the uniqueness
scan. Each competitor costs at most sixteen, including the implication,
equality test, and loop. With T things, the full value search has bound
U = T(16T+14). The scan includes the proposed value itself and compares its
coordinate again. Duplicate source facts occupy the same Boolean table cell,
so they do not create additional values.

Axiom 94 searches for a type instantiated by x and a quality space associated
with that type which contains y. It visits types first, then spaces, in
coordinate order. Its candidate contains three binary reads and two Boolean
branches, with bound 35. Failed instantiation costs thirteen: the inner and
outer conjunctions each inspect a Boolean even though both later reads are
skipped. Failed association costs 24. The complete witness bound is
R = T(37T+2), including both loops.

With W worlds and quality-search bound K = T(25T+23), the registry bounds are:

| Check | Bound |
| --- | --- |
| Axiom 92 | T(T(W(K+24)+2)+2) |
| Axiom 93 | T(W(K+U+4)+2) |
| Axiom 94 | T(T(W(R+15)+2)+2) |

The proofs use the compiled model's table agreement. They count source
operations and do not claim that native compilation preserves repeated calls.

#### Simple and complex qualities

Checks 95–98 have full value/cost equalities to counted table computations.
A simple quality has no inhering things: no candidate y has an `inheresIn y x`
edge to that quality x. A complex quality passes quality classification and
fails the simple-quality test. The source definition repeats classification
inside that test. These counts retain both occurrences, subject to the
source-level cost model: native optimization can share more work than these
definitions explicitly share. No cache is assumed.

With T things, each visited inherence test costs fourteen, including negation
and loop overhead. The search stops at the first edge. Let K = T(25T+23)
bound quality classification. The simple-quality bound is S = K+14T+1,
and the complex-quality bound is C = K+S+2. A false initial classification
skips the inherence search and, for the complex predicate, the repeated test.

Simple-quality and complex-quality type checks read type classification first.
They then check every instance, skipping non-instances. The respective bounds
are ST = T(S+15)+9 and CT = T(C+15)+9. Nine operations cover the unary type
read and branch. Each instance test adds eleven for its binary read, two for
implication, and two for the loop. A classified type without instances satisfies
either universal condition.

For W worlds, the registry bounds are:

| Check | Bound |
| --- | --- |
| Axiom 95 | T(T(W(ST+25)+2)+2) |
| Axiom 96 | T(T(W(CT+25)+2)+2) |
| Axiom 97 | Apply `z ↦ T(z+2)` five times to `W(C+55)` |
| Axiom 98 | T(W(C+T(S+15)+4)+2) |

Axioms 95 and 96 skip the type check when the association is absent. Otherwise
they evaluate both sides of Boolean equivalence, even when dimension or domain
classification is false. Axiom 97 checks that two inhering instances of the
same type are identical. Its antecedent adds four binary reads, five conjunction
branches, and one type-equality test to C, giving C+50. A failed inner conjunction
still passes through the remaining conjunction branches, but skips later reads.
Axiom 98 checks each inhering thing for simple quality only after the containing
quality passes the complex-quality test.

#### Product-family witnesses: axiom 99

The product-family check has full counted-table correspondence, including its
actual family array. A family supplies dimension and type arrays of equal
length D. D is independent of the number T of model things. The checker tests
the family's domain, type, and world before its projection, association, and
coverage conditions, stopping when a condition fails.

Projection has different costs even when the result is the input tuple. A slot
outside the projection table costs two operations. A missing array cell costs
eight, an initialized empty cell nine, and a stored result eleven, including
its finite-coordinate check. The internal model carries `tupleProjectionCosted`
and its bound of eleven. Ordinary `tupleProjection` returns the value field.
The verified lookup bundle carries the counted projection. Its proof-facing
definition keeps the compact value and the dense evaluator's cost. The proved
native replacement runs that dense evaluator once and returns both fields.
Model assembly installs the callback directly, without another lookup for the
cost. `compiledProjection_eq_countedTable` proves full counted equality under
table agreement. An arbitrary callback's counter bound alone does not establish
its execution cost. Missing raw cells retain their documented tuple fallback.

For each domain member, the checker visits the D slots. A slot first projects
the tuple, reads its dimension, then reads membership in that dimension. These
operations cost at most 23, plus two for the loop. The projection-row bound is
T(25D+15). Fifteen operations cover the outer membership read, implication, and loop.

Association rows read the dimension and type slots before the association
query. If it succeeds, characterization reads the type slot again. The source
cost is at most 28D. Coverage visits all T possible characterization targets.
Each matching target searches for an equal type in the family, giving bound
T(4D+15). The complete witness bound is:

```text
B(T,D) = 8 + T(25D+15) + 28D + T(4D+15)
```

Eight operations cover header comparisons and conjunction branches. Each visited
family adds one array read and two loop operations, so the full search bound
is P = Σ_family(B(T,D_family)+3). Invalid entries do not hide a later valid
entry, and the first successful entry stops the search. With W worlds, axiom
99 has bound T(T(W(P+24)+2)+2).

For the explicit checker size n, each witness bound is at most 95n², the search
bound at most 98n³, and the whole axiom bound at most 126n⁶. These bounds include
independently sized family arrays and all slot reads. They do not assume that
the Lean compiler preserves repeated source calls or array reads.

#### Distance witnesses and life-of equivalence: axioms 100, 101, and 103

Axiom 100 checks that each distance tuple relates two qualia with a common
quality structure. This witness search tests membership, without a separate
quality-structure classification of the witness. It reads membership twice per
candidate, but skips the second read if the first is false. Each candidate
costs at most 25 operations, including its branch and loop. The search bound
is 25T for T things. The two quale reads and their branches add at most 18.
The distance read, implication, and world loop add 18 more.

Axiom 101 searches for exactly one distance result. A candidate starts its
uniqueness scan only after its distance read succeeds. Each uniqueness row
costs at most 19 operations: a distance read, implication, equality, and loop.
The complete search bound is U = T(19T+17). This includes rejected candidates
and repeated reads during uniqueness checks.

Axiom 103 characterizes the life of an endurant through overlapping events.
Its equivalences evaluate both sides. Each overlap row costs at most 37,
including a reflexive overlap query, event classification, a possible manifests
read, up to two Boolean connective operations, and the loop. Self-overlap skips the table
read and costs two operations. Other overlap queries cost thirteen.

For W worlds, the complete bounds are:

| Check | Cost bound |
| --- | --- |
| Axiom 100 | T(T(T(W(25T+36)+2)+2)+2) |
| Axiom 101 | T(T(W(U+21)+2)+2), where U = T(19T+17) |
| Axiom 103 | T(T(W(37T+33)+2)+2) |

The full counted equalities in `Complexity/Queries.lean` connect these loops
to the actual compiled table operations. They retain source evaluation order
and skipped work. As with the other checks, native sharing can change the
number of calls without changing the source counter.

#### Definition checks: axioms 105–108

The finite signature defines disjointness, complete coverage, partitioning,
and categorization by these axioms' right-hand sides. Each axiom therefore
holds for every interpreted finite model, as proved by its soundness theorem.
Its executable check returns `⟨true, 0⟩` without reading a table. The registry
still charges traversal of each visited entry. User-written derived assertions
are checked separately and retain their own cost bounds.

#### Binary and ternary checker calls

The same full counted-computation equality covers axioms 102 and 104 and the
distance identity, symmetry, and triangle extensions. Together with the unary
instantiation, modal, bridge, quality, part, functional, constitution, dependence,
inherence, bearer, distance-witness, and life-of checks, 112 registry checks
have a proved table-cost connection. The four definition checks complete the
116-entry query-cost inventory.
Binary reads cost 11 operations:
two width multiplications, four coordinate operations, field selection, two
flat-index operations, a checked read, and an option test. Ternary reads cost
14, with one more width multiplication and two more coordinate operations.
The ternary value proof connects the proof-facing width expression using a
power to the counted expression using explicit multiplications. Native execution
uses the counted function's value projection through the compiler's proved
`ternaryTypedTableDense_eq_erased` replacement. Thus the cost model counts
those multiplications, not an opaque exponentiation call.

For T things and W worlds, the bounds are:

| Check | Cost bound |
| --- | --- |
| Axioms 102 and 104 | T(T(32W+2)+2) |
| Distance identity | T(T(T(28W+2)+2)+2) |
| Distance symmetry | T(T(T(32W+2)+2)+2) |
| Distance triangle | Apply `z ↦ T(z+2)` seven times to `74W` |

Identity tests coordinate equality before reading distance. Symmetry reads the
reverse distance only when the forward distance is present. The triangle
antecedent has four ternary reads joined by three left-associated conjunctions.
An early false read skips later reads but still visits the three enclosing
branch tests. Its cost is at most `4·14+3=59`. The implication, binary comparison
read, and world loop add at most `2+11+2`, giving 74 per world before the seven
thing loops. These bounds describe the compiled table implementation under the
unit-cost model and contribute to the source-to-workflow bound above.

The axiom 99 diagnostic checks product-family registration with a direct array
scan. Each visited entry costs five operations when its domain differs, or six
when the domain matches and the quality type must also be compared. The first
matching key stops the scan. The proved upper bound is `6R` for `R` registered
records, regardless of their witness-array lengths. This bound covers key
presence only. Missing registration produces a report before witness validation.

`Complexity/Diagnostics/ProductFamily.lean` validates the supplied records.
It rejects unequal array lengths and out-of-domain coordinates, then checks
projection membership, dimension/type associations, and coverage of every
characterization target. A record can fail without ending the registry search:
a later valid record for the same key still supplies a witness. Projection
reads use the compiler's flat table, including its tuple-as-default rule.

For `T` things, `D` dimension slots, and `Z` type slots in one record, the proved
bound is

```text
T·(31D + 15) + 39D + T·(4Z + 15) + 4D + 4Z + 16.
```

The first three terms bound projection, association, and coverage scans.
The remaining terms cover coordinate validation, key comparisons, and branches.
The bound is monotone in `T`, `D`, and `Z`. The registry bound sums each record's
bound plus three operations for its visited array read, loop step, and Boolean
test. Record lengths are independent input sizes, not bounded by `T`.

For `R` records, total dimension slots `DΣ`, and total type slots `ZΣ`,
`productFamiliesDiagnosticBound_eq_sizes` gives the same bound as
`(31T+43)·DΣ + (4T+4)·ZΣ + (30T+19)·R`. Thus record order and slot distribution
do not affect the bound. Its monotonicity theorem permits any registry whose
record and slot totals are larger, including added records.

`productFamilyDiagnosticCosted_valid_iff` states the three witness conditions
over dense tables. `productFamilyDiagnosticCosted_checker_iff` connects them to
the checker's `productFamilyWitnessProp` for finite arrays when the two use the
same relation and projection interpretations.

`productFamiliesDiagnosticCosted_eq_checker_of_compile` proves equal Boolean
results for the two registry searches after successful source compilation.
Its model is the cached model constructed by generated declarations. Source
success supplies table agreement and the exact family/world readback. Every
resolved family has a finite witness in each world, and every stored witness
reads back to a resolved family. The proof transports the per-family conditions
through this correspondence, including repeated records and a valid record
after an invalid one. Positive domain sizes and finite query coordinates are
explicit premises.

The theorem compares results, not execution costs. The diagnostic validates
natural-number coordinates and lengths; the checker receives bounded
coordinates and equal-length proofs. Their separately counted work still
requires source-to-result cost composition.

The axiom 99 diagnostic visits worlds, domain candidates, and quality types in
ascending coordinate order. It stops at the first failed association. A false
quality-domain query skips the type loop. A false association query skips both
registry scans and report construction. Numeric loops avoid temporary lists
of coordinates. Value theorems identify the result with the first report in
this order.

The report collector visits all `T` characterization candidates and appends
matching coordinates to one array. Its bound is `22T+1`, including array
initialization. A value theorem identifies this array with the filtered
coordinate range. Under table agreement, its entries are exactly the sparse
characterization facts. A second theorem limits its length to `T`.

The renderer reads each selected name directly. It counts string concatenations
as unit operations, not their character-level work. Report construction costs
at most `31T+48` and produces at most five rows. This bound includes the collector,
name reads, separators, array initialization, and emitted rows. Missing
registration and invalid registered witnesses retain distinct reports.

Let `P` be the registry-validation bound defined above, and let `R` count records.
The association bound is `A = 6R + P + 31T + 68`.
The domain-candidate bound is `Q = 13 + T·(A+3)`.
For `W` worlds, the complete axiom 99 analyzer satisfies

```text
cost ≤ W·(T·(Q+3)+3)+6.
```

Each loop visit contributes three control operations. The final six cover
result selection and the two fallback rows when no association fails. These
are bounds for the counted executable, before shared dispatch and output-budget
handling. The whole-analyzer monotonicity theorem covers `W`, `T`, `R`, `DΣ`,
and `ZΣ`. Exact counts can decrease when an earlier answer skips later work.

Generic diagnostic assignments stream in lexicographic order and stop when the budget
is full. Variable lookup scans the environment array directly and retains the
last matching binding, so inner quantifiers hide bindings with the same name.
For `E` environment entries, its exact cost is `4E+1`: each entry requires an
iteration, a read, a name comparison, and a conditional selection. The final
default selection costs one. An absent variable returns zero. The list-fold
correspondence theorem and the appended-binding theorem establish this behavior
for every environment, not only the regression examples.

Formula quantifiers and derived-predicate quantifiers visit numeric coordinates
directly. They do not construct a range list before the first test. The shared
finite loops accumulate costs before continuing, so a full scan needs no stack
of deferred additions. Their list-specification equalities preserve both the
Boolean answer and exact visited-prefix cost: each visited coordinate adds two
operations to its predicate cost. Formula quantifiers also charge one operation
to append each variable binding and one outer constructor test.

Asserted derived propositions use an indexed array search with four operations
per visited entry: read, string comparison, iteration, and early-exit test. The
search stops at the first matching proposition and costs at most `4D`, where
`D` is the number of stored assertions. String-character costs are excluded.
Primitive unary, binary, and ternary atoms use guarded dense reads. Coordinate
checks cost two operations each, followed by the existing 8-, 11-, or 14-operation
table core. The resulting bounds are 12, 17, and 22. Invalid coordinates return
false at the first failed guard. Sparse/dense agreement proves equal values for
in-domain queries, and bounded explicit compilation supplies that agreement.
This is value correspondence, not an equality between sparse and dense costs.
Field-index bounds and injectivity use kernel-checked finite proofs. The three
compiled-query correspondence theorems depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms, not native evaluation.

Possible-instance search uses the guarded binary read and costs at most
`W(19T+2)` for `W` worlds and `T` things. Primitive atom bounds also include
variable lookup and constructor selection. Each atom costs one outer
constructor test. Binary atoms also inspect the field constructor. Reflexive
`part` and `overlap` atoms stop before resolving the world or reading a table.

For environment size `e`, let `A(e)` bound an atomic evaluation and `E_f(e)`
bound evaluation of formula `f`. The recursive evaluator bound is:

| Formula | Bound |
| --- | --- |
| Atom | `A(e)+1` |
| Thing or world equality | `8e+4` |
| Negation of `p` | `E_p(e)+2` |
| Conjunction or disjunction of `p` and `q` | `E_p(e)+E_q(e)+2` |
| Implication or equivalence of `p` and `q` | `E_p(e)+E_q(e)+3` |
| Quantifier or modality over `N` coordinates, with body `p` | `N(E_p(e+1)+3)+1` |

The quantifier domain size `N` is `T` for things and `W` for worlds. Every
clause includes the formula-constructor test. Exact costs include only visited
operands and coordinates. The upper bound includes both branches where needed
to cover either outcome. The environment-monotonicity theorem assumes that
`A` is monotone. The concrete atomic bound satisfies this condition. Formula
structure remains a parameter; this recurrence does not claim a uniform
polynomial for unrestricted formulas.

`Complexity/Diagnostics/Formula.lean` derives a closed bound from this
recurrence. Let `s` count formula nodes and `q` be the maximum number of nested
quantifiers on a path through the formula. Modal operators count as world
quantifiers. For an initial environment of size `e`, put `E = e + q`.
Every environment reached by the evaluator has at most `E` entries. If
`A` bounds atomic evaluation at every environment size up to `E`, then:

```text
evaluation cost ≤ s · (A + 8E + 4) · (W + T + 1)^q
```

`diagnosticFormula_recurrence_le_size` proves the structural inequality.
`diagnosticFormula_cost_le_size` applies it to the production interpreter with
`A = diagAtomCostBound W T tables E`. Thus the bound includes the existing
charges for environment lookup, guarded dense reads, and derived-predicate
searches. The proof does not add a runtime traversal or replace measured costs.

A connective sums child bounds. A quantifier repeats its body at most once per
domain member, so each nesting level contributes a factor of at most
`W + T + 1`. The extra one keeps the bound valid for empty domains, where
constructor selection still costs work. For example, two nested universal
loops over two worlds and three things evaluate a reflexive equality in 147
operations. A false left operand in a conjunction can skip both loops.

`diagnosticFormula_sizeBound_mono` proves that the upper bound is monotone in
all six parameters `s`, `A`, `E`, `W`, `T`, and `q`. Exact counts retain early
exits and need not be monotone. A fixed formula fixes `s` and `q`. An arbitrary
input formula can increase the exponent. This is a formula-dependent bound,
not a uniform polynomial for combined formula/model input. Report construction
and the fixed certification registry have separate theorems.

Modal dependence, functional dependence, constitution, and qua-individual
predicates also use the guarded query core. Their sparse-formula equalities
require table agreement and in-domain arguments. The proofs compose query
correspondence through each Boolean operation and finite search, preserving
the computed result without assuming equal sparse and dense costs.

For `W` worlds and `T` things, the counted bounds are:

| Predicate | Upper bound |
| --- | --- |
| Modal existence implication; existence without the other thing | `28W` each |
| Existential independence | `56W+3` |
| External dependence | `28W+T(56W+22)+1` |
| Externally dependent mode | `T(28W+T(56W+22)+3)+13` |
| Generic functional dependence | `F = T(39T+39)` |
| Individual functional dependence; component of | `F+73`; `F+91` |
| Generic constitutional dependence | `C = T(37T+21)` |
| Constitution | `C+54` |
| Qua-individual | `19T` |

For example, generic functional dependence first checks whether each source
instance functions as the source type. Its two guarded reads and conjunction
cost at most 35. Implication and outer-loop control add four. Each target
candidate adds at most 39 for distinctness, two guarded reads, conjunctions,
and loop control. Summing gives `T(39T+39)`. Actual counts exclude skipped
reads and later candidates after an answer is known.

Derived-name dispatch tests names in order and charges two operations for each
visited comparison and branch. Unary dispatch adds at most four operations;
binary dispatch adds at most ten. Value proofs preserve each recognized
predicate and case-sensitive fallback to asserted proposition lookup. These
dispatch costs are included in `derivedLookupCostBound`, separately from the
predicate bounds above.

Assertion keys use counted decimal-format calls and string concatenations.
Each finite coordinate costs three operations: one decimal-format call and
two concatenations around the numeral. Appending a space-separated coordinate
adds two further concatenations. The `sig.<field>` prefix costs one, giving
11 operations for unary keys, 16 for binary keys, and 26 for quaternary keys.
The assertion scan follows key construction and retains its `4D` bound.
General value proofs preserve the exact key text. Known computed predicates
skip both key construction and the assertion scan.

These are counts of string-operation calls. Character traversal, decimal digit
work, and allocation remain outside the unit-cost theorem, so a call is not
claimed to take constant wall-clock time.

Assignment-domain traversal also uses numeric coordinates and accumulates costs
before its tail call. It returns when the stop predicate becomes true. Under
the one-operation stop-call interface, visiting a coordinate costs the visitor's
work plus three operations: iteration, stop call, and branch test. The production
stop predicate compares output size with the evidence budget. For a domain of
size `N` and a visitor bound `P`, the traversal costs at most `N(P+3)`.
A proved ordered-fold specification fixes the final state and witness order.

Assignment-variable traversal reads the variable array directly at the requested
index. It neither copies the array to a list nor traverses a skipped prefix.
A full budget returns after two operations. An exhausted variable array adds
four operations to the visitor cost: stop and index comparisons and their
branches. A remaining variable adds those four operations, one array read,
and a kind selection. Each child then adds an environment push and an index
increment, alongside the domain loop's three operations.

For visitor bound `P` and remaining variables `v :: rest`, the recurrence is
`B([]) = P+4` and `B(v :: rest) = 6+domainSize(v)·(B(rest)+5)`.
The environment-sensitive version increases the environment size at each
level before applying `P`. The implementation is proved equal, including its
cost, to the ordered list recurrence used only as a specification. The visitor
bound includes evidence construction when this traversal produces a report;
see [Suggestion and report composition](#suggestion-and-report-composition).

The computed external-dependence witness collector also uses the numeric loop.
It returns the filtered ascending thing coordinates, with proved no-duplicate
and output-size properties. It emits at most `T` witnesses and costs at most
`T(28W+T(56W+22)+6)+1`: each candidate incurs its dependence check, a result
branch, at most one array push, and three loop operations. The initial empty
array costs one, including for an empty domain. The candidate list
in its filter theorem is a specification, not a runtime allocation.

Declared external-dependence candidates use the same numeric loop. For `D`
stored assertions, each candidate costs at most `16+4D` for key construction
and assertion lookup, plus a branch, an optional push, and three loop
operations. The collector therefore costs at most `T(4D+21)+1`, including
empty-array initialization, and returns at
most `T` distinct coordinates in ascending order. Both diagnostic callers use
this collector. Explicit compilation is proved to return false for the
unsupported primitive name `externallyDependent`, so candidate collection
needs only the stored derived assertions.

Failure explanation chooses the first declared candidate, if present. Otherwise
it searches inherence facts in ascending coordinate order and stops at the
first match. If no match exists, it selects zero for a nonempty thing domain
or returns no candidate for an empty domain. Each visited coordinate costs at
most 17 for the guarded binary query, one result branch, and three loop
operations. The complete selection costs at most `21T+5`. Its value theorem
requires bounded thing/world coordinates and sparse/dense table agreement.

Existence-witness search uses the same first-witness loop. It finds the first
world where `Ex(x)` holds and `Ex(y)` does not, skipping the second lookup
when `Ex(x)` is false. Two guarded unary queries cost at most 24 operations.
Conjunction and negation add two, and the search adds one result branch and
three loop operations. The bound is therefore `30W`, including early-stop
control. An empty world domain costs zero. The sparse-relation value theorem
requires bounded thing coordinates and table agreement.

The external-dependence failure explanation counts its searches and text
construction. Indexed-name rendering costs four operations: comparison and
branch, then either array read and name rendering, or numeric rendering and
concatenation for the `#n` fallback. Formatting and concatenation are primitive
calls here; their character-level work remains outside the model.

Both directional existence searches run to distinguish which independence
witness is missing. Their explanation costs at most `60W+18`, including two
name renders, at most eight concatenations, and two result tests. Bearer search
visits thing coordinates directly and checks inherence before those searches.
It retains the first failing bearer and its reason. The bound is
`T(60W+40)`: each candidate adds a guarded binary query (at most 17), its
branch, optional-result selection, and three loop operations to the
independence explanation. Rendering the retained result adds at most 27
operations for four names, ten concatenations, and one result test.

The complete failure-reason bound is `30W+T(60W+40)+28`. A world that violates
the modal implication takes precedence over bearer inspection, and its
coordinate is reused in the message. General value theorems fix the first
bearer and preserve the explanation text.

The mode-status renderer counts the guarded mode query, witness/candidate
searches, name joining, text construction, and emitted rows. Joining `I` indexed
names costs at most `9I+1`: each array entry adds two traversal/read operations,
four name-rendering operations, an accumulator test, and at most two
concatenations. Final optional-result selection adds one. Its value theorem
preserves comma placement, input order, repeated indices, and name fallbacks.

For `W` worlds, `T` things, and `D` stored assertions, let
`C = T(28W+T(56W+22)+6)` be the computed-witness loop bound. The collector
costs at most `C+1`, including its initial array. The complete
mode-status bound is
`C + T(4D+51) + (30W+T(60W+40)+28) + 45`.
The terms cover computed witnesses; declared candidates, candidate selection,
and name joining; the selected failure reason; and fixed control/rendering
work, including initialization of both candidate arrays. A row charges one
array push and one emitted item, with one array
initialization per output. The renderer emits at most three rows. Its general
value theorem requires table agreement and bounded thing/world coordinates.

Axiom 71 searches worlds, left things, and right things in increasing coordinate
order. It retains the first failing founded pair and the classification and
foundation results used in its explanation. No Cartesian-product list is
allocated. The search value theorem fixes this order under sparse/dense table
agreement, and a separate theorem proves that retained coordinates are in range.

Let `M = T(28W+T(56W+22)+3)+13` be the computed-mode bound and `A = M+46`.
One assignment costs at most `A`: a guarded `FoundedBy` query costs 17,
its branch costs one, mode-or-relator classification costs at most `M+13`,
the `Perdurant` query costs 12, and the final Boolean tests cost three.
Classification skips the relator query when computed mode is already true.
For each right-thing candidate, retaining its result adds one operation and
loop control adds three. The left-thing and world loops each add their own
three operations per visit. Thus the search bound is
`S = W·(T·(T·(A+4)+3)+3)`.

Failure formatting costs at most `3I+49` for `I` mode-status rows. The fixed
49 covers three name renders, 20 string concatenations, four Boolean tests,
one array initialization, and six push/emission pairs. Each existing status
row adds a read, iteration, and push; its emission was charged by its producer.
The formatting theorem preserves every literal row and both suggestions.
With mode-status bound `R` above, the complete axiom 71 bound is `S+R+71`:
the final match costs one, the displayed relator query costs at most 12, and
formatting costs at most 58 because `I ≤ 3`. The analyzer emits at most nine
rows. The complete bound is proved monotone in `W`, `T`, and the stored-assertion
count. If no assignment fails, its one-row result adds four operations to the
search cost.

Axiom 73 distinguishes sharing a foundation from having equal unique
foundations. Its right-hand predicate requires some common `FoundedBy` target,
even when either thing has other targets. The shared-foundation theorem states
this existential condition explicitly. The evidence formatter separately
compares unique foundations and reports ambiguity when uniqueness fails.

Foundation candidates are the ascending finite targets whose `FoundedBy`
query is true. The collector visits each coordinate once, so duplicate facts
cannot produce duplicate candidates. Under sparse/dense table agreement and
bounded coordinates, its value theorem gives exactly the filtered relation.
With `T` things, initialization costs one operation. Each target costs at most
17 for the guarded query, one for its branch, one for a successful push, and
three for numeric traversal. The resulting bound is `22T+1`.

Unique-foundation lookup returns a target only when the candidate array has
size one. The size test and safe array read give a bound of `22T+4`. Comparing
two foundations runs both searches and charges each visited option branch and
the final equality, for at most `44T+11` operations. A missing or ambiguous
foundation returns `none`; two distinct unique foundations return `some false`.

Status formatting produces the same missing, unique, or ambiguous-foundation
text as its specification. The ambiguity loop renders names directly into a
string accumulator, in candidate order, without an intermediate name list.
For `I` candidates, it costs at most `11I+2`, including indexed-name lookup,
quoting, separators, array traversal, and the message prefix. Candidate
collection and the selected formatting branch together cost at most `33T+12`.
These bounds grow with `T`. String-character copying and allocation costs
remain outside the unit-cost model.

The counted part query tests reflexivity first. An equal pair costs two
operations and skips the table query, including its coordinate guards. A
non-reflexive pair costs at most 19. Shared-foundation search visits targets
directly and stops at the first common target. Each target costs 20 operations
when the first `FoundedBy` query is false, or 37 when both queries run. Its
bound is `37T`, with no allocated target list.

The right-hand predicate checks computed mode, inherence, then a common
foundation. Each later condition runs only if the preceding ones are true.
Its bound is `P = M+37T+19`, where `M` is the computed-mode bound above. The
19 covers the guarded inherence query and two conjunction branches. This
bound is proved monotone in world and thing counts. Calling the fixed mode
predicate directly avoids string-name dispatch and assertion lookup.

The complete characterization scan compares the part predicate with the
right-hand predicate at each thing. It returns false at the first mismatch.
Its general value theorem preserves the universal characterization under table
agreement and bounded queried coordinates. Its bound is `T(P+22)`: each thing
adds a part query of at most 19, one Boolean equality, and two loop operations.
This bound is also proved monotone in world and thing counts. The scan uses
numeric traversal without a thing list.

For an asserted `QuaIndividualOf` fact, the constituent search retains the
first failure in coordinate order. Its classifier reports a missing computed
mode before missing inherence, and missing inherence before a missing common
foundation. A non-part is a failure only when it satisfies all three conditions
on the right-hand side. Later predicates run only when the preceding results
leave them relevant. The classifier's value theorem preserves this priority.
It returns no failure exactly when the part predicate agrees with the
characterization. A second theorem lifts that equivalence to the complete
finite search, including empty domains.

The classifier bound is `C = P+21`. Numeric search costs at most `T(C+4)`,
including the option-map branch that retains the failing coordinate and the
loop operations. The selected coordinate and failure reason pass to the
formatter, which renders names and the assignment line once. Missing-mode,
missing-inherence, and missing-part evidence cost 36, 42, and 36 operations.
Foundation evidence also compares unique foundations and renders both status
messages. Its bound is `110T+85`: the lookup/status bounds contribute
`110T+35`, reason selection contributes at most two, and the remaining name,
text, branch, initialization, push, and emission operations contribute 48.
The formatter returns three rows, or five for foundation evidence.

The primary scan costs at most `T(C+4)+110T+87`, including its entry and result
branches. If its supplied `QuaIndividualOf` Boolean is false, it returns
`none` in one operation without a constituent query or text construction.
The classifier and scan bounds are monotone in world and thing counts.
The assignment evaluator obtains that Boolean through a guarded dense query,
at cost at most 17. When the fact is absent, only the reverse direction needs
checking: does the complete characterization hold despite the missing fact?
Its three-row report costs exactly 29 operations: three indexed names cost
12, assignment and explanation concatenations cost 10, array initialization
costs one, and three pushes with emissions cost six. This is a unit-cost text
bound, not a bound on copied characters.

Write `H = T(C+4)+110T+87` for the primary-scan bound. One assignment costs at
most `A = H+T(P+22)+49`. The 49 includes the table query, three branch tests,
and reverse-direction formatting. The evaluator produces no report exactly
when its `QuaIndividualOf` Boolean equals the complete characterization.
This equation concerns the diagnostic predicates. It does not prove their
equivalence to the production checker. Confirmed semantic failure still
requires the generated negation proof.

Three nested numeric loops visit world, qua-individual, and bearer coordinates
in increasing order. They stop at the first report without allocating the
Cartesian product of assignments. Their bound is
`S = W·(T·(T·(A+3)+3)+3)`, including each loop's control operations.
The ordered-list specification proves which assignment is selected. No
assignment is selected exactly when every bounded assignment satisfies the
diagnostic biconditional. The complete analyzer costs at most `S+4` and returns
at most five rows. The extra four operations cover the final branch and the
one-row message when no mismatch is found. This bound is monotone in `W` and
`T`; exact counts still depend on where the search stops.

For axiom 78, three nested numeric loops compare relators with their parts in
world/relator/part order. A guarded relator query runs first. Non-relators skip
the part query, and non-parts skip the foundation comparison. Equal unique
foundations produce no rows. Distinct unique foundations produce a mismatch;
missing or ambiguous foundations produce witness requirements.

Each selected pair appends five evidence rows to the shared array. The
formatter renders three names once, computes both foundation-status strings,
and reuses those values across the rows. Its bound is `66T+67`: the status
strings contribute `66T+24`, names contribute 12, and concatenations, wording
selection, pushes, and emissions contribute 31. The complete pair bound is
`110T+113`, including guarded relator/part queries and the foundation comparison.
The analyzer's bound is `W·(T·(T·(110T+116)+3)+3)+12`, monotone in `W` and `T`.
The final 12 covers array initialization and the longest finishing branch.

The loops stop between evidence groups once the budget is full. The last group
can exceed the budget by at most four rows, as proved by the scan invariant.
The public producer takes the budget-sized prefix. If no pair produces
evidence, the analyzer constructs only the allowed prefix of its two fallback
rows. A suggestion is appended only when evidence exists and space remains.
The value theorems specify row text and ordered traversal. Under table
agreement and bounded coordinates, the pair theorem uses the sparse relator
and part relations. These results do not establish the separate correspondence
between this diagnostic and the production checker.

Axiom 79 collects proper parts with guarded queries of
`ProperPart(candidate, whole, world)`. It visits candidate coordinates in
increasing order and appends each matching coordinate once. The collector's
value theorem equates the array with the filtered finite domain. Membership
also implies that the coordinate is below `T`, and the array has no duplicates.
Under table agreement and bounded whole/world coordinates, the filter uses
the sparse proper-part relation. An ordinary `Part` fact does not suffice.

The collection bound is `22T+1`. Initialization costs one. Each candidate costs
at most 17 for the guarded query, one for its branch, one for a successful
push, and three for numeric traversal. With valid coordinates, an absent
proper part costs 21 operations and a present one costs 22. The bound grows
with `T`; duplicated source facts do not add candidate slots.

For each pair, the analyzer checks qua-individual status, unique equal
foundations, and existential dependence in both directions, in that order.
It stops at the first failed requirement. The fixed predicate calls agree in
value with the derived-name dispatcher, but omit its string comparisons.
The classifier costs at most `82T+56W+17`, where `W` is the world count.
Its renderer constructs only the selected report, with at most six rows and
cost `66T+76`. Their composition costs at most `148T+56W+94` per pair.
This bound is monotone in `W` and `T`; actual counts follow the queries visited.

The suggestions refer to inputs used by the computed predicates:
`QuaIndividualOf` for qua status, `FoundedBy` for foundations, and `Ex` for
existential dependence. Adding derived assertions for `QuaIndividual` or
`ExistentialDependence` does not override these computations.

The pair search traverses the part array twice in nested loops. It visits
self-pairs and preserves array order, stopping both loops at the first report.
The loops use `Except`: `ok` continues, and `error` carries a report and stops.
Its value theorem agrees with search of the Cartesian product, but execution
does not construct that product. For a supplied array of `P` parts, the bound is
`P·(P·(148T+56W+98)+4)+2`. Each visited pair adds four operations for the inner
iteration, array read, optional-report test, and loop-result test. Each visited
outer entry adds four for its iteration, read, inner-result selection, and
loop-result test. Two final selections complete the call, even for an empty
array. Input-array allocation is outside this call.

The bound is monotone in `W`, `T`, and `P`. The production collector supplies
`P ≤ T`, proved independently of source order and duplicate facts.

The outer analyzer visits worlds first, then things, in ascending order. A
guarded relator query costs at most 12, followed by one Boolean branch. For a
relator, the analyzer collects its proper parts and charges two operations to
test whether that array is empty. An empty array produces a three-row report
at an exact formatting cost of 21. Otherwise, the pair search runs on that
array. Writing `B(W,T,P)` for the pair bound above, one assignment costs at most
`R(W,T) = 22T+37+B(W,T,T)`.

The whole axiom 79 analyzer costs at most `W·(T·(R(W,T)+3)+3)+6`. The extra
three operations at each loop level cover traversal and stopping. The final
six cover result selection and, if no report was found, the two fallback rows.
The result contains at most six rows, and the bound is monotone in both domain
sizes. Ordered-search and row-text theorems specify its output. Under table
agreement and finite coordinates, an assignment uses the sparse relator and
proper-part relations. These diagnostic results do not establish the separate
correspondence to the production axiom checker.

The axiom 68 diagnostic follows stored next-hop cells. A cell gives the next
coordinate toward a target. Fuel `F` limits the number of cells that the helper
can follow, so cyclic raw tables still terminate. Its path and cost accumulators
advance before each tail call. Generated C uses a loop jump for that call.
The value recurrence specifies target recognition, missing cells, and exhausted
fuel independently of the accumulated cost.

A continued hop costs eleven operations: equality and its branch, the fuel
test, two index operations, a bounds comparison and branch, a read, an option
test, a path append, and a loop step. Target recognition and its append cost
three. Exhausted fuel costs three, an out-of-range cell costs seven, and an
empty in-range cell costs nine. The proved bound is `11F+3`. A successful result
adds at most `F+1` coordinates to the input accumulator. World selection and
accumulator initialization give `momentOfPathCosted` a bound of `11T+7`, where
`T` is the thing count and also the supplied fuel.

Bearer collection checks the guarded moment flag first. It reconstructs a path
only for non-moments, then appends each successful candidate once. A candidate
costs at most `11T+21`. The numeric collector costs at most
`C(T) = T·(11T+26)+1`, including initialization and loop control. It returns at
most `T` candidates, each with at most `T+1` path coordinates. Value theorems
specify the ordered filtered candidates. Table agreement connects each finite
moment query to the sparse relation.

The assignment search visits worlds before things and stops at the first
accepted candidate array. Its category predicate must supply a cost bound of
one. Production uses emptiness and comparison with one for missing and multiple
bearers. The search bound is
`S(W,T) = W·(T·(T·(11T+26)+19)+3)`, monotone in both domain sizes.
The missing-bearer search adds one operation to project its result. It runs
before the multiple-bearer search, so a missing bearer has priority even after
an earlier multiple-bearer case.

The elaborator's Boolean precheck, `hasAx68ClosureFailure`, erases
`hasAx68ClosureFailureCosted`. It uses these same two searches and costs at most
`2S(W,T)+4`. The four fixed operations cover the missing-result projection,
two option tests, and the disjunction's branch. A missing bearer skips the
second search. Exact regressions give 76 operations for the two-thing missing
case, 265 for the three-thing multiple-bearer case, and four with no worlds.
If the elaborator subsequently requests a report, that separate call repeats
the searches. The precheck bound does not cover that later work, and the
source-to-result theorem must include both calls when both execute.

Report construction reuses the selected paths. Joining `L` path coordinates
costs at most `9L+1` primitive calls. Adding the bearer name and surrounding
text costs eight more. The candidate loop adds at most five operations per
bearer for traversal, result selection, and separators, then one final default
operation. Since each of at most `T` paths has length at most `T+1`, all bearer
text costs at most `T·(9T+23)+1`.

The two report names cost eight operations. Missing-bearer rows cost twelve,
and multiple-bearer rows cost fourteen, including category selection, array
initialization, concatenations, writes, and emissions. The complete analyzer
therefore costs at most `2S(W,T)+T·(9T+23)+26` and emits at most three rows.
Both claims are proved, as is monotonicity of the bound in `W` and `T`. Value
theorems preserve category priority, candidate order, separators, and report
text. These are primitive-call counts. String-character work remains outside
the unit-cost model.

`Complexity/Diagnostics/Paths.lean` connects returned paths to actual inherence
edges. At every Warshall stage, a stored hop away from the target is an
original graph edge. Existing routes retain their hop. A newly discovered
route inherits the hop toward the current pivot. The pivot cannot be the
source in this branch, because then the route would already exist.

`warshall_nextHopPath_sound` applies this invariant to the production
pointer-following loop. `FinitePath` states that the returned coordinates are
in range, start at the requested source, follow adjacent graph edges, and end
at the target. It permits repeated vertices and does not require a shortest
route. The list in this predicate specifies the returned array. Execution does
not construct a second representation for the proof.

`compileModelSource_ok_modelPath_sound` derives the edge relation from the
actual source-produced model. It requires successful compilation and positive
world/thing counts, which the finite-model constructor needs. Source success
supplies cache validity, matching dimensions, and dense/sparse agreement.
The existing `11T+7` cost and `T+1` vertex bounds apply to the same call.

Completeness follows from a separate decreasing-rank invariant. For each target,
Warshall's stored pointers decrease a natural-number rank. At each pivot stage,
old routes keep their ranks. New routes rank above all old routes and follow
the preceding stage's decreasing ranks toward the pivot. Once a new route
enters an old route to the target, its rank also decreases. These ranks are
proof data only. The compiler does not compute or store them.

Strict decrease excludes repeated vertices. A route in the `T`-vertex domain
therefore contains at most `T` vertices and uses fewer than `T` hops. The
production loop follows this route within its existing `T`-hop limit.
`warshall_nextHopPath_exists_iff_reachable` proves success exactly for the
reachable matrix entries. `compileModelSource_ok_modelPath_exists_iff` connects
that result to the source-produced model's inherence closure. For valid compiled
endpoints, a missing path means unreachability, not exhausted fuel.

Regressions cover all 512 directed graphs on three vertices and a nine-vertex
chain that needs eight hops. The general proof applies to every finite graph,
including cyclic graphs. The diagnostic fallback reports the result without
attributing every unexplained certification failure to the Lean proof bridge.

The public producer applies one cap through `boundedEvidenceCosted`, which also
limits widget messages. For budget `B` and input length `N`, this helper copies
exactly `E = min(B,N)` items through indexed reads. Each retained item costs
four operations: iteration, read, write, and emission. The fixed cost is four:
two for prefix selection, one for array initialization, and one for the
truncation comparison. Its exact cost is `4E+4`. It does not visit discarded
items. `boundedEvidence_eq_prefix` proves the output and truncation flag equal
the prefix specification. A second theorem proves that applying the same cap
again cannot change the items.

The dispatcher performs no prefix copies. The widget retains its own cap
because it also accepts messages from outside the witness producer. It uses
the same helper. The public witness theorem counts its own copy, not the later
widget call. `diagnosticWitnessesBudgetedCosted_cost_le_inner_add_emitted`
composes the inner counter bound with `4E+4`.

Specialized field selection visits ax68, ax71, ax73, ax78, ax79, and ax99 in
that order. Each comparison and branch costs two operations. A match skips the
remaining tests, so selection adds two through twelve operations. The public
axiom 99 missing-family example therefore costs `155+12+8=175` at budget one.
Its budget-zero count is `155+12+4=171`, because this budget removes output
without skipping the specialized search.

Generic formulas use one counted pass to collect leading universal variables
and select the remaining body. For `K` leading variables, extraction costs
exactly `3K+2`: one selection, append, and loop step per variable, plus array
initialization and the final selection. The cost accumulator advances before
each tail call. Value proofs preserve variable order, duplicate names, and the
first non-universal body. Existential and modal nodes stop extraction.

Generic lookup scans a fixed array of 107 field/formula pairs. Every visited
entry costs eight operations: three loop controls, three for the checked array
read, a string comparison, and its branch. A match stops before another read.
The next stop test costs three when entries remain. The bound is `8R` for
registry size `R`, or 856 for this registry. The dispatcher includes the
returned lookup cost. The first entry, ax1, costs 11 to select. An unknown
field costs 856 to reject. The registry is static program data. Module-startup
initialization of program constants is outside the per-call cost model.

Generic fallback rows count their concatenations, initialization, writes, and
emissions. The public theorem composes the evaluation, minimization, and report
bounds. Before assignment traversal, the generic producer charges two operations
to initialize its environment and output arrays. These charges remain even
with a zero budget or an empty domain. The empty-domain ax1 dispatcher fixture
therefore costs 47 operations, or 43 at budget zero.

The evaluator and failure minimizer have explicit formula-size bounds. Evidence
construction and enumeration of outer assignments still require their own
size bounds and composition into the complete report result.
Report construction has a separate bound from certification. The derived-fact
and axiom-68 prechecks can also run on successful models, so source-to-result
composition must include them rather than treat all diagnostic work as confined
to failure.

### Derived-assertion prechecks

`Diagnostic/DerivedAssertions.lean` checks explicitly written derived claims
before axiom certification. It returns the first failure in source-fact and
scope-world order. The elaborator then either displays that report or attempts
the generated Lean proofs. This path is separate from the axiom-report
dispatcher and is not covered by its cost theorem.

The precheck resolves a textual reference with `thingIndexByStringCosted`.
Its value theorem proves equality with the array's first matching rendered
name, including duplicate and missing names. Each visited entry costs three
operations for a guarded read, one name-rendering call, one string comparison,
and four search controls. The bound is `9T` for `T` declared names.
An early match adds three operations for the next stop test when entries
remain, but performs no further read or rendering. Name-character and allocator
work remain outside the primitive-call model.

The six quality predicates also erase counted computations. Their bounds use
`T` for the number of things:

| Predicates | Operation bound |
| --- | --- |
| `Quality`, `QualityStructure` | `34T + 2` |
| `SimpleQuality`, `ComplexQuality` | `55T + 4` |
| `SimpleQualityType`, `ComplexQualityType` | `T(55T + 27) + 14` |

`Complexity/Diagnostics/Unique.lean` supplies the search for exactly one
matching index. It retains the first match and stops at the second. Each
candidate first incurs a classification query (at most 12 operations).
Only a classified candidate incurs the relation query (at most 17).
The intervening branch costs one, and search control costs at most four per
candidate. The terminal and result-option tests give the final two operations.
The value theorem characterizes the result by the sole element of a filtered
domain. Execution does not construct that list.

A simple quality has no inhering thing. A complex quality has at least one.
Their shared first-match search costs at most `21T`: 17 for each relation query
and four for search control. It runs only after `Quality` succeeds. Its result
test and the preceding branch yield the bound `55T + 4`.

The quality-type checks search for an instance that fails the corresponding
quality condition. Non-instances skip that condition. With condition bound
`P`, this search and the outer quality-type test cost at most `T(P + 23) + 14`.
Substituting `P = 55T + 4` gives the quadratic bound in the table.

These value theorems require valid finite coordinates and agreement between
the sparse and dense tables. Query bounds include coordinate guards and dense
array access. They do not assign a constant cost to an opaque sparse lookup.
The size bounds are monotone in `T`, although added facts can reduce actual
cost by causing an earlier exit.

Set, specialization, and classification predicates use the same guarded query
model. Let `W` be the number of worlds and `T` the number of things. The
possible-instance search has bound `P = W(19T + 2)`. A thing has typehood here
when something instantiates it in at least one world. The search visits worlds
in order and then things within each world, stopping at its first instance.

| Predicate | Operation bound |
| --- | --- |
| `NonEmptySet` | `21T + 1` |
| `SubsetOf` | `40T + 1` |
| `ProperSubsetOf` | `80T + 3` |
| `ProperSub` | `36` |
| `Categorizes` | `P + 40T + 2` |
| `IsDisjointWith` | `2P + 39T + 3` |
| `IsCompletelyCoveredBy` | `58T + 1` |
| `IsPartitionedInto` | `2P + 97T + 5` |
| `UltimateBearerOf` | `20` |

`firstRelatedThingCosted` supplies both membership and inherence witnesses.
Its `21T` bound includes a binary query (17) and search control (four) per
candidate. Testing whether a member exists adds one operation.

`firstRelationDifferenceCosted` finds the first thing related to the left
target but not the right target. Subset checks use membership on both sides.
Categorization uses instantiation on the left and specialization on the right.
Only a left match incurs the right query. Two queries, a branch, a negation,
and search control give `40T`. Proper subset checks first establish inclusion,
then search for a difference in the reverse direction to establish strictness.
`ProperSub` uses two specialization queries without a domain search.

Disjointness first checks typehood on both sides, then searches for a shared
instance. Each candidate incurs at most two queries, one branch, and four
search controls, giving `39T`. The two typehood tests retain the executable
left-associated conjunction: failure of the first test skips the second test
and the witness search, but still incurs two conjunction branches.

Coverage searches for an instance outside both covering types. A non-instance
skips both cover queries. A match in the first cover skips the second query.
Three queries, two branches, a negation, and search control give `58T`.
Partition checks compose coverage with disjointness and skip disjointness when
coverage fails. These bounds are monotone in both `W` and `T`.

Failure reports reuse these first-witness searches. The search value theorems
fix ascending coordinate order and require the same representation agreement
and finite-coordinate premises as the quality predicates. The complete report
bound below includes these searches and the surrounding text construction.

`UltimateBearerOf` tests that the bearer is not a moment, then reads the
stored inherence closure. The moment query costs at most 12, negation and its
branch cost two, and the closure query costs at most six. A missing world
matrix stops after two operations. A present matrix adds two index operations,
a cell read, and the cell-option test. The lookup theorem preserves the
explicit row width, including for raw tables whose stored width differs.
Typed checker queries use the same counted core with the stored width.
This lookup correspondence does not establish that the matrix represents
inherence reachability or that the compiled widths agree.

`evalNamedDerivedFactCosted` covers the complete evaluation of one named
derived assertion. Its value theorem proves equality with
`evalNamedDerivedFactSpec`, which fixes supported spellings, fallback results,
and left-to-right argument resolution. The production failure search calls this
counted evaluator. The specification is not a second executed evaluator.

For unary and binary assertions, name resolution precedes field selection.
An unknown name stops evaluation. Unknown ternary and quaternary predicates
return no result before name resolution. Every visited field test costs two:
one string comparison and one branch. Resolving one argument costs at most
`9T + 1`, including its success/failure test. There are at most four arguments,
seven field tests, and one arity test, giving the bound
`B_named(W,T,D) + 36T + 19`.

Here `D` is the number of stored derived propositions. `B_named` is
`namedDerivedPredicateCostBound`: the fixed sum of the bounds for the numeric
predicates, with one copy of each shared quality-family bound. It includes
the shared unary/binary fallback bound and all three quaternary predicate
bounds. The proof bounds each executed predicate by its component of that sum.
`namedDerivedPredicateCostBound_mono` proves monotonicity in `W`, `T`, and `D`.
This result covers the declared dispatcher, not unrestricted formula syntax.

`firstDerivedAssertionFailureCosted` searches source facts in order and returns
the first failure. Named and resolved entries pair by array index. Missing or
non-derived pairs skip evaluation. An `at` scope checks its one resolved world.
An `everywhere` scope checks worlds in ascending order without constructing a
world-index array. A successful assertion continues the search. A false result
or a reconstruction failure stops it, retaining the fact, source scope, world,
and failure kind for the report. The stored proposition builder is not called.

For `F` named source facts, the selection cost is at most
`F(10 + (W+1)(B_named(W,T,D) + 36T + 24))`. Each paired entry costs at most two
array reads and four constructor tests. Scope selection adds one. Each world
adds at most two result tests and three loop controls to the dispatch cost.
The outer loop adds three controls per visited fact. The factor `W+1` also
covers an explicit `at` scope when `W=0`. The bound is monotone in `F`, `W`,
`T`, and `D`; actual counts can decrease after an earlier failure appears.

The value theorem states first-failure selection as nested ordered searches.
`derivedAssertionFailure?` formats the selected record without evaluating the
assertion again. It erases `derivedAssertionFailureCosted`, which includes
selection, complete report construction, and the final output cap.

### Complete derived-assertion reports

For `W` worlds, `T` things, and `D` stored derived propositions, the report
construction bound is

```text
R(W,T,D) = 112WT² + 200T² + 214WT + 8TD + 866T + 184W + 519.
```

`derivedAssertionReportCostBound_eq` proves this expansion. The bound includes
both report dispatchers, every argument-name search, the selected field-specific
text and evidence, suggestions, and common rows. The required-missing dispatcher
constructs its fallback before selecting a field, even when it will not use that
fallback. Each selected field resolves all argument names before inspecting
their results. A missing first name therefore does not erase the costs of later
name searches. Unsupported fields skip name resolution.

The public `derivedAssertionFailureBudgetedCosted` producer retains the first
`budget` rows after constructing the report. Let `E` be its emitted row count.
Its proved bound is

```text
F(10 + (W+1)(B_named(W,T,D) + 36T + 24)) + R(W,T,D) + 4E + 5.
```

Here `F` counts named source facts and `B_named` is the predicate bound defined
above. The final five operations cover the failure-option test and fixed
prefix-copy work. A no-failure execution performs neither report construction
nor a prefix copy; the displayed bound covers that case too. All terms are
monotone in their size parameters. This is a bound for the fixed supported
derived predicates, not for arbitrary input formulas. String-character work,
allocator behavior, and proof elaboration remain outside the primitive-call model.

Every report has at most nine rows: four common rows and at most five evidence
rows, or two rows for reconstruction failure. The default producer uses budget
nine. Its value theorem proves that this cap preserves the full report. The
frontend keeps this precheck result during semantic proof elaboration. On
failure, `derivedAssertionFailureReportCosted` selects the saved report at cost
one, or constructs the one-row fallback at cost four. It does not scan the
facts again. Finding no false assertion does not establish that Lean accepted
the semantic proof, so that fallback remains necessary.

`derivedAssertionAnalysisCosted` composes one scan with this report selector.
`derivedAssertionAnalysisCosted_eq_bind` proves equality of the combined value
and cost, and `derivedAssertionFailureReportCosted_precheck_value` proves that
reusing the result preserves the frontend's report choice. The bound adds at
most four operations to the scan and report producer. On successful proof
elaboration, the frontend skips the report selector. Proof elaboration itself
remains outside this count. The report value proofs use independent cost-free
dispatch and formatting specifications.

`Diagnostics/Source.lean` connects these diagnostic costs to the actual
compiler output. `compileExplicitModelAST_derivedProps_size_le` proves that
each explicit fact adds at most one stored derived proposition. Family
registration, dense writes, and closure construction preserve that array.
Duplicate assertions still occupy separate entries. Successful source
compilation then gives
`compiled.tables.derivedProps.size ≤ m.specializationFactsUpper ≤ N`, where
`m = sourceMetrics source` and `N = m.inputSize`.

The named-predicate bound has degree at most three in worlds W, things T,
and stored propositions D. With each bounded by N, it is at most `1648N³`.
The report bound is at most `2103N³`. Named-fact selection adds the outer
fact and world loops, yielding `3426N⁵`. The nine-row cap contributes at most
41 more operations. Thus `source_derivedAssertionFailure_cost_bound` proves
`5570N⁵` for the precheck, and `source_derivedAssertionAnalysis_cost_bound`
proves `5574N⁵` for one precheck followed by saved-report selection.

These bounds concern the fixed named-predicate dispatcher, including its
unsupported-name fallback. They allow empty domains because diagnostics accept
them. The theorems bound calls supplied with the frontend's name arrays;
constructing those arrays and compiling the source are separate costs.
Neither theorem claims a bound for complete command execution. The bounds
increase with N even when an added fact lets the actual precheck stop sooner.

`namesFromStringsCosted` counts the frontend's name-array construction. It
preserves each string as one Lean name component, including dots, empty strings,
and duplicates. The exact cost for k entries is `4k + 1`: one initialization,
then an iteration, a read, a name construction, and a write per entry.
`namesFromStrings` erases this counted traversal and is shared by fresh-model,
extension, and imported-source paths. String characters and allocation remain
outside the unit-cost model.

For the compiler's world and thing arrays, construction costs
`4(W + T) + 2 ≤ 6N`. `source_derivedAssertion_component_bound` combines those
two calls with source compilation and the precheck/report producer:

```text
compiler cost + world-name cost + thing-name cost + derived-analysis cost
  ≤ 6091 N⁵
```

The coefficient is `511 + 6 + 5574`; the compiler's quartic bound and the
linear conversion bound are each bounded by the corresponding fifth-degree
term because N is positive. This sum uses the successful compiler's actual
tables and the names returned by the counted conversions. It does not include
generated declarations, per-axiom checks, widgets, or other failure branches.

The two-thing empty-set regression costs 76 for failure selection and 166 for
report construction. With budget zero, the total is 247. Each retained row
adds four operations, giving 271 for the complete six-row report. These tests
show that truncation does not conceal prior construction work. The whole-report
bounds compose into the source-workflow theorem through separate pipeline and
cache-correspondence proofs. Formula evaluation has its own size-dependent
theorem above.

Quality reports collect all competing quality kinds or associated quality
types with `relatedCandidatesCosted`. The shared accumulator returns the
ordered filter of the selected unary/binary relation pair. Each candidate
costs at most 30 query operations, one match test, one retained-index write,
and three loop controls. Array initialization adds one, giving `1 + 35T`.
The resulting array contains at most `T` indices. Correspondence with sparse
fact lookup requires table agreement and valid coordinates. These results
cover candidate collection, not the later name rendering and text assembly.

Quality-type checks and reports share `firstInvalidInstanceCosted`. It returns
the first instance that violates the supplied condition, in declaration order.
Non-instances skip the condition. A first violation stops the search.
For `T` things and condition cost at most `P`, the bound is `T(P + 23)`:
each candidate costs at most 17 for instantiation, two for the branch and
negation, four for search control, and `P` for the condition. Both simple and
complex quality have `P = 55T + 4`, giving `T(55T + 27)` for the search.
The bounds are monotone in their size parameters. Sparse correspondence
requires table agreement and valid coordinates. The Boolean quality-type
check adds at most 14 for classification and result handling. The reports'
surrounding text and row construction remain outside this search bound.

Dependence reports use counted first-failure searches. The functional search
returns the first source instance that functions as its type but has no
distinct, functioning target instance. Its bound is `T(39T + 41)`: at most
39 operations per target candidate, 35 for source eligibility, and six for
negation, the source branch, and outer search control. The constitutional
search returns the first source instance without a target instance related
by `ConstitutedBy(source, target)`. Its bound is `T(37T + 23)`, with at most
37 operations per target, 17 for source eligibility, and six outer operations.
Both bounds are monotone in `T`. These searches inspect one supplied world,
so `W` affects lookup validity but does not add a world loop.

The value theorems preserve the first source witness in declaration order,
under table agreement and valid coordinates. Ineligible sources skip target
search, and a matching target ends the inner search. Functional targets must
be distinct from the source. Its left-associated conjunction still tests the
second branch after distinctness fails, without performing either table read.
Constitutional targets have no distinctness condition. These report searches
are separate from Boolean dependence checks, which return no source witness.

`derivedAssertionSuggestionCosted` selects fixed advice text. Its value theorem
preserves every literal in the cost-free specification, including the generic
fallback. An arity test costs one, and each visited field comparison and branch
cost two. There are at most eleven field tests, giving a bound of 23. Argument
names are not read. This bound excludes the caller's prefix concatenation and
row emission. String-character work remains outside the primitive-call model.

`qualityStatusEvidenceCosted` covers one complete quality-status row. Candidate
collection costs at most `35T + 1` and retains `N ≤ T` indices. The renderer
uses the counted indexed-name and name-joining functions from axiom diagnostics.
Size tests, concatenations, initialization, and row emission are also counted.
Rendering costs at most `9N + 24`, giving `44T + 25` overall. The value theorem
preserves the three messages for no kind, a unique kind, or competing kinds.
The size theorem states that each case returns exactly one row.

The following report components have bounds that include their queries,
names, text construction, and array operations. Here `W` is the number of worlds
and `T` is the number of things:

| Report | Required-missing bound | Assertion and evidence bound |
| --- | --- | --- |
| `Quality` | `44T+19` | `44T+37` |
| `QualityStructure` | `44T+13` | `44T+25` |
| `SimpleQuality` | `55T+19` | `78T+41` |
| `ComplexQuality` | `34T+12` | `78T+41` |
| `SimpleQualityType` | `T(55T+27)+27` | `T(55T+27)+44T+66` |
| `ComplexQualityType` | `T(55T+27)+27` | `T(55T+27)+44T+66` |
| `NonEmptySet` | `14` (exact) | `21T+26` |
| `SubsetOf` | `40T+23` | `40T+34` |
| `ProperSubsetOf` | `40T+19` | `40T+34` |
| `ProperSub` | `35` | `67` |
| `UltimateBearerOf` | `35` | `20T+57` |
| `ExternallyDependent` | `30W+T(60W+40)+43` | `30W+T(60W+40)+48` |
| `ExistentialDependence` | `30W+25` | `30W+28` |
| `ExistentialIndependence` | `60W+33` | `60W+38` |
| `Categorizes` | `W(19T+2)+40T+25` | `W(19T+2)+40T+38` |
| `IsDisjointWith` | `39T+19` | `39T+30` |
| `IsCompletelyCoveredBy` | `58T+31` | `58T+38` |
| `IsPartitionedInto` | `97T+26` | `97T+38` |
| `GenericFunctionalDependence` | `T(39T+41)+21` | `T(39T+41)+34` |
| `IndividualFunctionalDependence` | `T(39T+39)+72` | `T(39T+39)+T(39T+41)+83` |
| `ComponentOf` | `47` | `T(39T+39)+T(39T+41)+98` |
| `GenericConstitutionalDependence` | `T(37T+23)+23` | `T(37T+23)+36` |
| `Constitution` | `T(37T+21)+68` | `T(37T+21)+T(37T+23)+79` |

The functional and constitutional report bounds include complete field-specific
text construction after name resolution. Generic reports retain the first
failing source. Individual functional dependence checks generic dependence
before either instantiation. Constitution checks both instantiations first.
Component reports check proper parthood before individual functional dependence.
These orders determine which reason is reported when several requirements fail.

A Boolean dependence check does not retain a witness. If it fails, the
individual or component evidence builder performs a separate source search.
Both executions are charged: the functional bounds use `T(39T+39)` for the
Boolean check and `T(39T+41)` for the search. The constitutional counterparts
are `T(37T+21)` and `T(37T+23)`. No shared result is assumed. All five evidence
builders emit exactly two rows. Value proofs preserve the messages, fallbacks,
relation direction, and the functional target's distinctness requirement.
The three quaternary report families require sparse/dense table agreement and
valid coordinates for their value correspondence; their cost and size bounds
hold for arbitrary tables and natural-number coordinates.

For four things, a first functional failure costs 115 to find: 35 for source
queries, one source branch, 71 for target search, one negation, four search
controls, and three for the next stop check. Required-missing text adds 21;
two-row evidence adds 34. When the first failing source is last, the individual
functional evidence costs 394: 175 for the Boolean check, 181 for the separate
search, and 38 for names, text, branch selection, and output. The tests check
these exact counts, empty domains, early and late target witnesses, duplicate
facts, field isolation, and the public report's row order. These are primitive
operation counts, not wall-clock measurements.

Each quality collector costs at most `35T+1` and returns `N ≤ T` indices. The two
required-missing builders add at most `9N+18` and `9N+12` for rendering and
control. `Quality` evidence adds nine operations for its assertion row and
three to copy the one-row status array. `QualityStructure` constructs both
rows directly, with at most `9N+24` beyond collection. Both evidence results
have exactly two rows, with the assertion first. Their value proofs preserve
the no-candidate, unique-candidate, and competing-candidate text. These four
quality/quality-structure bounds are monotone in `T` and include candidate-name joins.
All bounds in the table exclude source-name resolution, outer dispatch, the
common report preamble, and output budgeting. String-character work remains
outside the primitive-call model. The collector's sparse correspondence requires
table agreement and valid coordinates.

`SimpleQuality` and `ComplexQuality` evidence first check quality at cost at
most `34T+2`. If quality fails, a separate status report costs at most `44T+25`.
The assertion row, negation, branch, and one-row copy add 14. If quality holds,
the incoming-inherence search costs at most `21T`. Rendering and control add
at most 28 for a witness or 14 with none. Both paths fit `78T+41` and return
two rows. The value proofs preserve the quality-status text and select the
first incoming witness in declaration order. The cost includes both searches
on the failed-quality path. It assumes no shared cache.

`SimpleQuality` required-missing text adds at most 17 operations to the quality
check and the selected inherence search, giving `55T+19`. Its fallback is
already supplied by the caller. `ComplexQuality` required-missing text uses
the quality check plus ten operations for one name, four concatenations,
negation, and branching, giving `34T+12`. It does not search for an inhering
part: after an assertion fails, a successful quality check leaves that missing
part as the explanation. All four bounds are monotone in `T`.

Quality-type reports first test the primitive `QualityType` classification,
at cost at most 12. A failed classification skips the instance search.
Otherwise, the first-invalid-instance search costs at most `T(55T+27)` for
either simple or complex quality. Required-missing text adds at most 15 for
names, concatenations, and control, giving `T(55T+27)+27` including the
classification query. The caller supplies and charges any fallback text.

Evidence returns two rows for a missing classification or no failing instance,
and three for a failing instance. In that third case, the extra quality-status
report costs at most `44T+25`. Classification, names, text, branch tests,
row construction, and the one-row copy add at most 41. The complete evidence
bound is therefore `T(55T+27)+44T+66`. A missing classification costs at most
33, and no failing instance costs at most `T(55T+27)+26`. Value proofs preserve
the messages under table agreement and valid coordinates. Cost and three-row
upper bounds hold for arbitrary inputs, and the size-based bounds are monotone.
The extra row can report a valid quality whose simple/complex condition fails.

`UltimateBearerOf(x, y)` evidence displays the moment classification of bearer
`x` and reconstructs the directed path from `y` to `x`. It computes both even
when `x` is a moment, because both appear in the three-row report. Bounded
next-hop traversal costs at most `11T+7` and returns at most `T+1` vertices.
Joining `N` vertex names costs at most `9N+1`. Two concatenations surround the
path text, and other report work costs at most 38. These bounds give `20T+57`.
The no-path branch uses ten text operations instead of the join and its two
concatenations, and satisfies the same bound. Required-missing text performs
only the classification query and rendering, with bound 35.

Bearer value proofs require agreement between sparse and dense lookups and
valid coordinates. Cost and three-row size bounds hold even for malformed
next-hop tables. Path soundness uses the separate compiled-cache theorem above.
For successfully compiled sources, every returned path consists of model
inherence edges and ends at the requested bearer. Reconstruction succeeds
exactly when those endpoints are related by the model's inherence closure.

`ExternallyDependentMode` evidence prefixes the counted mode-status report
with two introductory rows. Their name, text, initialization, and emission
cost 11. Copying at most three status rows costs at most nine. With `W` worlds,
`T` things, and `D` stored derived propositions, the resulting bound is
`T(28W+T(56W+22)+6) + T(4D+51) + (30W+T(60W+40)+28) + 65`.
The value proof preserves row order and the full status report, including
declared-candidate notes. At most five rows are returned. This component
bound excludes the outer report work listed after the table.

Modal report components reuse the counted world searches and failure reasons.
External dependence first seeks a world where the source exists without the
target. Only if none exists does it inspect the source's bearers. Its reason
bound is `30W+T(60W+40)+28`. Required-missing text adds 15 for two names and
seven concatenations. Three-row evidence adds 20 for names, concatenations,
array initialization, and row writes/emissions.

Existential-dependence reports seek the first world where the implication
`Ex(x) → Ex(y)` fails, at cost at most `30W`. Required-missing text adds at
most 25, or just one match when it returns a caller-supplied fallback.
Two-row evidence adds at most 28. Existential-independence reports search
for both separation witnesses: a world with `x` but no `y`, and a world with
`y` but no `x`. Both searches run so the reason can distinguish the missing
directions. The shared reason costs at most `60W+18`. Required-missing text
adds at most 15 and two-row evidence at most 20.

These six modal component value proofs preserve the ordered reports in terms
of the shared counted searches and reasons. Their cost and size theorems hold
for arbitrary inputs. The search-to-sparse-relation correspondence retains its
separate table-agreement and coordinate premises. All six bounds are monotone
in their size parameters. Caller-supplied fallback construction and the outer
report work remain outside these component bounds.

`Categorizes(x, y)` reports first establish that `x` is a computed `Type`:
it has an instance in some world. That search costs at most `P = W(19T+2)`.
If it succeeds, the report seeks the first current instance of `x` without
the required `Sub` relation to `y`, at cost at most `40T`. A missing type skips
this second search. Required-missing text adds at most 25 operations, giving
`P+40T+25`. Two-row evidence adds at most 38. The no-instance and no-failure
branches use less work. Possible typehood ranges over all worlds, but the
specialization counterexample must occur in the report's world.

Disjointness reports seek the first shared instance at cost at most `39T`.
Required-missing text adds at most 19 for three names, six concatenations,
and one match. Evidence adds at most 30, including both rows. These reports
explain an already failed assertion. With no shared instance, the unmet
disjointness condition is typehood, so the required-missing text does not
repeat the typehood searches. The no-witness evidence instead asks the reader
to inspect typehood and instantiation facts.

Coverage reports seek the first covered-type instance that instantiates
neither covering type. The search costs at most `58T`. Non-instances skip
both cover queries, and a match in the first cover skips the second query.
Required-missing text adds at most 31. Two-row evidence adds at most 38.
Partition reports first use this coverage search, then search for a shared
instance of the part types only if coverage passes. The search bounds sum
to `97T`. Required-missing text adds at most 26, including two option matches
on the second path. Two-row evidence adds at most 38. A coverage failure
retains priority even when the parts also overlap at another instance.

All eight type-relation report bounds include names, concatenations, and array
operations and are monotone in `W` and `T`. Value proofs preserve the specified
branch order, first witnesses, messages, and caller-supplied fallbacks in terms
of the counted searches. Evidence always has two rows. The search-to-relation
correspondence has separate table-agreement and coordinate premises. These
component results still exclude outer dispatch, fallback construction, the
common preamble, and output budgeting.

`NonEmptySet` evidence selects the first incoming `MemberOf` edge in declaration
order, at cost at most `21T`. Rendering adds at most 26 operations: 12 for
names, eight concatenations, one option match, one array initialization, and
four row writes/emissions. The no-member branch adds only 20. Both cases
return exactly two rows. Required-missing text performs no query and costs
14 for two names and six concatenations.

`ProperSub` evidence queries both directions of `Sub`, even when the forward
edge is absent, because it displays both Boolean values. The two queries cost
at most 34. Eight name operations, 16 concatenations, two Boolean branches,
one array initialization, and six row writes/emissions give the bound 67.
Required-missing text queries only the forward edge to explain an already
failed assertion. Its bound is 35: 17 for the query, eight for names, two for
negation and branching, and eight concatenations. Value proofs preserve the
messages under table agreement and valid coordinates. The evidence always
contains three rows. These constant bounds cannot decrease with input size.

Each `SubsetOf` and `ProperSubsetOf` component searches once for the first
left member absent from the right set. This search costs at most `40T`.
These components explain assertions that the precheck already found false.
The Boolean subset check tests whether the same search returned no witness,
so a report can retain that witness without checking and searching again.
The proper-subset value theorems prove equality with the Boolean-first
decision structure, including its unreachable false-subset/no-witness branch.

`SubsetOf` required-missing text adds at most 23 operations: 12 for names,
ten concatenations, and one option match. With no witness, it returns the
caller's fallback at cost one. The caller must charge fallback construction.
Evidence adds at most 34: 16 for names, 12 concatenations, five array
initialization/write/emission operations, and a match. With no witness, it
returns an empty array at cost two beyond the search.

`ProperSubsetOf` required-missing text adds at most 19 operations for a witness,
or 17 when the subset condition holds and the report explains missing
strictness. Evidence adds at most 34 or 28 respectively and always returns
two rows. All four bounds are monotone in `T`. Each component counts its own
search. Sharing a search between required-missing text and evidence remains
outside these component results.

`QuaIndividual` reports use `quaIndividualTargetsCosted` to collect every
`QuaIndividualOf(source, target)` match in declaration order. The collector
does not reverse the relation or test a target classification. Its bound is
`22T+1`: at most 17 for each query, five for branch/write/loop control, and one
for the initial array. Value and size proofs specify at most `T` distinct
target indices. Sparse correspondence requires table agreement and valid
source/world coordinates. Duplicate facts therefore do not repeat a target.

`quaIndividualEvidenceCosted` constructs the two evidence rows, including the
target collector. For `N ≤ T` targets, name rendering, concatenation, size
tests, array initialization, and row emission cost at most `9N+17`. The total
bound is `31T+18`, monotone in `T`. Separate value and size proofs preserve
the empty-case text, the ordered name list, and exactly two rows. Targets with
the same displayed name still appear separately. The required-missing text
costs exactly 14 operations: two indexed names and six concatenations. These
results begin after source-name resolution and exclude dispatch, the caller's
prefixes, and output budgeting.

`requiredMissingFallbackCosted` constructs the generic false-assertion text.
Its bound is 18: at most ten for the relation summary, four for the world name,
and four concatenations. `unreconstructedDerivedReportCosted` constructs the
two rows for an assertion that the diagnostic evaluator cannot reconstruct.
It costs at most 17: ten for the summary, two concatenations, one array
initialization, and two row writes/emissions at two each. Neither result
covers first-failure selection or the model-specific required-missing branches.

`externalModeRequiredMissingCosted` constructs the complete explanation for an
`ExternallyDependentMode` assertion after its source name becomes a thing index.
It checks `Mode` first and skips
candidate work when that classification is false. Otherwise it chooses the
first declared candidate, then the first inherence target if none is declared.
If both searches fail, it reports no candidate. This path does not select
thing zero as a fallback, unlike the general mode-status renderer.

For `D` stored assertions, candidate selection costs at most `T(4D+42)+4`:
the declared collector costs `T(4D+21)+1`, an inherence scan costs at most
`21T`, and first-entry selection adds at most three. The complete explanation
costs at most `T(4D+42) + (30W+T(60W+40)+28) + 36`. The middle term bounds
the selected failure reason. Other work includes the mode query, reused source
name, optional target/world names, branches, and every text concatenation.
The bound is monotone in `W`, `T`, and `D`. Value correspondence requires
table agreement and valid coordinates. Selecting the explanation by relation
name, resolving the source name, adding the caller's prefix, and emitting the
row remain outside this explanation bound.

Evidence-line appending reads only the prefix that fits after the existing
output. For budget `B`, existing row count `O`, and evidence count `N`, it
appends `E = min(B-O,N)` rows, with natural-number subtraction. Each row gains
the prefix `  - `. A value theorem states this output as the original array
followed by the formatted prefix. Existing rows, order, and duplicates remain
unchanged, including when the original array already exceeds the budget.

The exact cost is `5E+3`. Each appended row costs a loop step, an indexed read,
a text concatenation, a write, and an emission. Capacity subtraction and
minimum selection cost three. The loop constructs no index list and does not
visit discarded evidence. Its size-based bound is `5N+3`, monotone in `N`.
Both the context-evidence and failing-atom callers use this formatter and
consume evidence arrays directly. Their bounds include counted source-fact
discovery and context traversal.

Generic formula rendering costs at most `F·(20E+39)` primitive operations for
`F` formula nodes and `E` environment bindings. The bound is monotone in both
parameters. `F` counts syntax-tree occurrences, including repeated subtrees,
not only distinct heap objects. Rendering follows formula syntax without
enumerating thing or world domains. This theorem concerns formula text. Formula evaluation has
separate, domain-dependent costs.

Each variable reference scans the environment and renders one indexed name,
at exact cost `4E+5`. Last-binding lookup and the `#n` fallback remain unchanged.
An atom needs at most five references. Constructor selection, field-label
selection, and counted concatenations give the atom bound `20E+38`. A formula
node adds its own constructor selection. Summing the node bounds gives the
whole-tree result. Value proofs preserve field labels, infix notation,
punctuation, and the text of every formula constructor.
The shared `Costed.appendString` primitive adds both operand costs and one
concatenation. Its value and cost equations keep proof reduction separate from
the implementation of the preceding text operations.

The renderer and its text specification use the decreasing node count to
prove termination. This explicit measure keeps their value equations within
the default proof-checking heartbeat limit. Production projects the counted
renderer value. There is no separate native rendering implementation. String
characters, allocation, and native stack behavior remain outside the unit-cost
theorem. The generic producer includes this renderer through its counted
condition-line function. Suggestion generation is included separately in
[Suggestion and report composition](#suggestion-and-report-composition).

Condition layout expands nested conjunctions (`and`) or disjunctions (`or`)
into rows, in left-to-right order. Other connectives remain whole entries.
One counted traversal serves both cases. It costs at most `3F+1` for `F`
formula nodes, including array initialization. Value and size proofs show that
the output retains duplicates and has at most `F` entries. The sum of their
formula-node counts is also at most `F`.

The row formatter joins text directly, without an intermediate string list.
For total row-node count `S`, row count `L`, and environment size `E`, its bound
is `S(20E+39)+6L+1`. The shared fold theorem sums the bound for each row.
Thus layout, including formula selection and expansion, costs at most
`F(20E+48)+3`.

Label selection costs at most `8F+3`. For a conjunction, it expands the rows
and searches for a negated equality. This search stops at the first match,
but the count includes the preceding full expansion. The condition-line
function adds a newline test and punctuation. Its bound is `F(20E+56)+11`,
monotone in `F` and `E`. A text-equality theorem includes embedded newlines in
source names. String search counts as one primitive call, with character work
outside the model. The generic bound includes the complete condition-line cost.

Assignment summaries use a counted forward fold. For `V` displayed variables
and `E` environment bindings, their bound is `V(4E+13)+1`, monotone in both
parameters. Each entry pays `4E+8` for kind selection, variable lookup, indexed
name text, and two concatenations. The fold adds an iteration, an array read,
an accumulator test, and at most two separator concatenations. The final
empty-result selection costs one. A value theorem preserves the original
comma-separated text, including duplicate variable names and name fallbacks.

The generic producer includes this cost and the two concatenations around the
assignment summary. Its preamble accepts counted text for the assignment,
condition, and suggestion. These arguments are already evaluated, so their
costs remain in the total even when no output space remains. Three capacity
checks cost six operations. Each retained row adds one write and one emission.
For total supplied text cost `C` and `R` newly retained rows, the exact preamble
cost is `C+6+2R`. Since `R ≤ 3`, this gives the bound `C+12`. The equation also
holds for initially oversized output, which remains unchanged.

Variable discovery has bound `2F+1+E(4E+8(V+F)+5)`, where `F` counts formula
nodes, `V` counts outer variables, and `E` counts environment entries. The bound
is monotone in all three parameters. Binder collection appends directly to the
outer candidate array and costs at most `2F`. Candidates retain declaration
order: outer variables first, then formula binders in preorder. A binder comes
before its body, and a left subformula comes before its right sibling.

The environment fold retains the first occurrence of each recognized name.
It checks duplicates against the output array, with no separate hash set.
For `K` selected variables, this scan costs at most `4K`. Candidate-kind lookup
stops at the first matching declaration and costs at most `8(V+F)`. Each fold
step adds at most one output entry, so `K ≤ E`. The fold's growth theorem gives
the stated bound, including one output-array initialization. A value theorem
proves the set-based specification and the counted scan agree. The set appears
only in that specification, not in the production path.

The generic producer includes the complete discovery cost. Discovery chooses
the first declared kind for a name, while assignment text uses its last
environment binding. These are separate rules. Duplicate names with conflicting
kinds do not change either priority. Unknown names remain absent from the
displayed assignment.

Atom suggestion text costs at most `20E+42` operations for `E` environment
entries. A suggestion uses at most five name lookups, each costing `4E+5`.
The five-name branch adds fourteen string joins, two Boolean selections, and
one atom selection. Other branches use fewer names. Typed fields also charge
their label selection, and binary fields charge selection of infix notation.
Type and individual suggestions use one name and cost `4E+11`.

`suggestionForAtomCosted_value` proves equality to the independent text
specification for every atom and requested truth value. Suggestion selection
uses this counted formatter directly. This bound excludes character traversal,
as does the shared string-join primitive.

The syntactic atom scan costs at most `2F+1` for `F` formula nodes. It visits
each node once and appends at most one atom per node. The final one counts
output initialization. Its exact count is `F+A+1`, where `A` is the number of
appended atoms. Quantifiers contribute their body once, regardless of
domain size. Negation retains the atom inside it, while equality formulas
contribute no atom. The value proof preserves order and duplicates. This scan
supplies evidence candidates. Selecting the atoms that actually fail also
requires model evaluation and has a separate cost.

### Failing-atom discovery

`failingAtomsIntoCosted` preserves the accumulator specification, including
order and duplicates. Universal quantifiers visit every assignment in ascending
coordinate order. Existential and possibility formulas first evaluate the
formula. If that evaluation succeeds, discovery returns no new atoms. A failed
implication collects the antecedent's written atoms before the consequent's
failing atoms. Necessity visits each world and descends only into a failing body.

The discovery bound depends on the formula tree. Let `A(e)` bound an atomic
evaluation with `e` environment entries, `E_f(e)` bound evaluation of formula
`f`, and `D_f(e)` bound its failing-atom scan. Let `F_p` count the nodes of
subformula `p`, and let `N` be the quantifier's world or thing count.

| Formula | Discovery bound `D_f(e)` |
|---|---|
| Atom | `A(e)+3` |
| Equality | `1` |
| Negation | `E_f(e)+4` |
| Conjunction `p ∧ q` | `D_p(e)+D_q(e)+1` |
| Disjunction or equivalence | `E_f(e)+D_p(e)+D_q(e)+2` |
| Implication `p → q` | `E_f(e)+2F_p+D_q(e)+2` |
| Universal quantifier | `N(D_body(e+1)+4)+1` |
| Existential quantifier or possibility | `E_f(e)+N(D_body(e+1)+4)+2` |
| Necessity | `W(E_body(e+1)+D_body(e+1)+6)+1` |

The complete scan adds one operation for the initial output array. Each domain
visit includes the binding write and numeric loop work. Necessity also charges
the body's evaluation, Boolean negation, and result branch. Domain lists occur
only in the value specification, not in the counted scan.

The structural theorem takes an atomic cost bound as an explicit premise.
`diagnosticFailingAtoms_cost_le_size` supplies the concrete diagnostic query
bound and derives a formula-size bound. Arbitrary quantifier nesting can
multiply domain sizes repeatedly, so no uniform polynomial for unrestricted
formula input follows.

### Suggestion and report composition

The report includes suggestion selection and the final failing-atom scan in
its accumulated cost. A conjunction first expands its rows and scans them for
a distinctness requirement. That scan stops at the first match. Otherwise,
selection counts failing-atom discovery and examines the first result. An empty
array selects the no-atom message at cost two. A singleton adds five operations
to its atom-specific formatter. Multiple atoms select the many-atom message at
cost five. The head read has an explicit bounds check.

For formula `f`, `F` nodes, and environment size `e`, suggestion selection has
bound `D_f(e)+E_f(e)+8F+20e+51`. The terms `D_f` and `E_f` are the discovery
and evaluation bounds defined above. Row expansion costs at most `3F+1`, and
the distinctness scan costs at most `5F`. The value theorem preserves every
message and its selection priority.

Minimization can rebuild a disjunction from two failed formulas and concatenate
their environments. Its cost proof therefore uses a fixed environment limit
`H = body.failureEnvSizeBound e`, not the original environment size alone.
Evaluation and discovery bounds are monotone in environment size when the
atomic bound is monotone. The diagnostic atomic bound has that property.

`failureDetailCostBound` defines `K_f(H)` from the original formula. Each node
adds `E_f(H)+D_f(H)`. A leaf adds nothing further. A one-child node adds
`2K_child(H)+4`, and a binary node adds `2K_left(H)+2K_right(H)+4`. The theorem
proves that `K` bounds evaluation plus discovery for the minimized formula,
including rebuilt disjunctions. This is a proof-only recurrence.

Suggestion text, its prefix, and the final atom scan together cost at most
`2K_body(H)+8F+20H+53`, where `F` counts nodes in the original body. The generic
report bound includes this term. These calls still execute when the output
budget is zero.

### Failure minimization

`minimizeFailureCosted` selects a failed subformula, its variable assignment,
and the successful context that explains the failed obligation. Its value
theorem proves equality with the cost-free `minimizeFailureSpec` for every
input. The specification fixes selection and ordering. It does not claim a
globally smallest counterexample.

Each visited formula costs one constructor test. Boolean branches, nested
constructor tests, and the conjunction's Boolean negations each cost one.
A terminal result initializes an empty context array at cost one. Child
evaluation, witness search, and successful-trace collection contribute their
returned costs.

Array joins use `Costed.appendArray`. Like Lean's `Array.append`, it traverses
the right operand and retains the left operand as its initial accumulator.
Each right-hand entry costs an iteration, a read, and a write. Its value theorem
proves ordinary append, and its exact cost is `3 * right.size`. Allocator and
copy-on-write costs remain outside this primitive-call model.

For a formula `f` and an environment of size `e`, write `M_f(e)` for
`failureMinimizeCostBound`. Let `E_f(e)` bound evaluation and `S_f(e)`
bound successful-trace collection before its one-operation initialization.
Let `V_f(e)` and `C_f` bound the minimized environment and context sizes.
The recurrence follows the executed branches:

| Formula | Upper bound |
| --- | --- |
| Atom or equality | `2` |
| `not p` | `E_not(p)(e) + Q_p(e) + 5` |
| `and p q` | `E_p(e) + E_q(e) + S_p(e) + M_p(e) + M_q(e) + 3C_q + 6` |
| `or p q` | `E_or(p,q)(e) + M_p(e) + M_q(e) + 3V_q(e) + 3C_q + 3` |
| `imp p q` | `E_imp(p,q)(e) + S_p(e) + M_q(e) + 3C_q + 3` |
| `iff p q` | `E_iff(p,q)(e) + E_p(e) + E_q(e) + S_p(e) + S_q(e) + M_p(e) + M_q(e) + 3C_p + 3C_q + 5` |
| Quantifier or modal formula with body `b` | `E_f(e) + R_b(e) + M_b(e+1) + 4` |

Here `R_b(e)` is `firstMatchCostBound` for the selected thing or world domain.
For `p = not q`, `Q_p(e) = M_q(e)`. For a quantified or modal `p` with
body `b`, `Q_p(e) = R_b(e) + M_b(e+1)`. In all other cases, `Q_p(e) = 0`.
The theorem `minimizeFailureCosted_cost_le` proves this bound by following
the recursive minimizer. Unselected branches contribute only to the upper
bound, never to the recorded count.

#### Explicit bounds for failure selection

For a formula with s nodes, quantifier depth q, and an initial environment of
size e, let E = e + q. Modal operators count as world quantifiers. Define:

```text
A = diagAtomCostBound W T tables E
R = s · (A + 8E + 10) · (W + T + 1)^q
L = 3R + 2s(2R + 5) + 6s² + 3sE + 10
```

`R` bounds either evaluation or one witness search for a subformula within
these limits. The constant ten covers the witness loop's control operations.
It enlarges the upper bound without changing the counted program.
`diagnosticFailureMinimize_cost_le_size` proves that the executed minimizer
costs at most sL. `diagnosticSuccessTraces_cost_le_size` bounds successful-context
collection by s(2R + 5) + 1, including its output-array initialization.

The derivation assigns each visited formula node a local budget. The largest
branch includes three evaluations, two successful-context collections, and
copies of context and environment arrays. Recursive calls consume the budgets
of their smaller subformulas. Negation can skip a constructor and recurse into
a quantifier body, so the proof uses induction on node count rather than only
immediate children. All evaluations and copies remain in the executed counter.

`diagnosticFailureMinimize_storage_le_size` bounds the returned environment by
sE entries and its context by s² traces. A trace stores a successful subformula
and its variable assignment. Failed disjunctions concatenate environments, so
the returned environment can exceed E. The proof includes that concatenation.
These are entry counts, not byte bounds or string-character costs.

The evaluation and minimization bounds are monotone in their size parameters.
The atomic bound also includes the stored derived-proposition count. Fixed s
and q give polynomial data-complexity bounds for these components. An input
formula can increase q, so no uniform polynomial in formula and model size is
claimed. The report theorem below composes these results with source evidence,
rendered rows, and outer assignment enumeration.

#### Explicit bound for the generic report

`Complexity/Diagnostics/Reports.lean` proves a size-dependent bound for the
public generic-report producer. Let W and T count worlds and things, F count
named source facts, and r count diagnostic-registry entries. Let V count the
selected formula's leading universal variables. After those variables are
removed, the residual body has s nodes and quantifier depth q. Let e count
the rows retained by the public output cap, so e is at most the budget.

For one assignment visit, define B = W + T + 1 and:

```text
E = v + q
M = sE
H = M + E + s
A(H) = diagAtomCostBound W T tables H
R = s · (A(H) + 8H + 10) · B^q
L = 3R + 2s(2R + 5) + 6s² + 3sH + 10

P(v) = R + sL + (2s + 1 + M(4M + 8(v+s) + 5))
       + M(4M + 13) + s(20M + 56) + 27
       + s²(s(A(H) + 60H + 115 + 275F) + 21)
       + sB^q(40M + 76 + 275F)
       + 2(R + (3s+3)R) + 8s + 20M + 53
```

Here v bounds both the variable array and the initial environment. M bounds
merged failure environments; H also covers retained context and later bindings.
The atomic bound A(H) includes the stored derived-proposition count. P is
`diagnosticGenericVisitBound`. Its summands charge evaluation, minimization,
variable discovery, assignment/condition text, context evidence, atom evidence,
and suggestions. Text and discovery work remain charged even if no row fits.

Failure minimization does not increase node count or quantifier depth. Thus
the actual failed formula needs at most sB^q atom records. Discovery costs at
most (3s+3)R+1, including its initial array. These facts bound evidence for
the returned formula, including disjunctions rebuilt by the minimizer.

Assignment search costs at most `(P(2V) + 11(V+1))B^V + 2`. The two operations
initialize its arrays. Each variable adds a domain loop. The proof reserves
eleven control operations per expanded node and bounds each domain by B.
The argument 2V covers the fixed variable array plus every environment length
used in the dependent loop bound. This is a conservative proof parameter, not
an extra runtime array or traversal.

`diagnosticGenericReport_cost_le_size` proves the public bound:

```text
(P(2V) + 11(V+1))B^V + 3V + 8r + 4e + 28
```

The additional terms cover variable extraction, registry lookup, dispatch,
fallback construction, and copying retained output. The theorem requires the
formula to be the registry's actual selection and excludes the six fields
with specialized analyzers. Those analyzers have their own bounds. Unknown
fields use the dispatcher's separate fallback bound.

`diagnosticGenericReportBound_mono` proves monotonicity in every size parameter,
including stored derived propositions, registry entries, and emitted rows.
Fixed V, s, and q give a polynomial data-complexity bound. Unrestricted formulas
can increase the exponents. This theorem bounds report execution, not the
whole compiler/checker pipeline or the semantic soundness of every explanation.

### Successful context construction

`successTracesIntoCosted` appends successful formulas and their assignments to
an existing trace array. Its value theorem proves equality with
`successTracesIntoSpec`, including trace order and witness choices. The
specification serves the proof and has no role in production execution.

Each call counts child evaluation, then two operations for Boolean negation
and the initial branch. A true result adds one formula-constructor test.
Each retained trace adds one array write. Disjunction and implication add a
Boolean branch, while existential formulas add a witness-result test and the
witness-search cost. Only the selected recursive path contributes its cost.
`successTracesCosted` adds one operation for the empty accumulator.

The structural recurrence `successTraceCostBound` bounds this counter for any
formula and environment. The wrapper's bound adds one to that recurrence.
These trace records are internal evidence, not emitted diagnostic strings.

Witness search traverses numeric coordinates in ascending order. Its value
theorem preserves the first match specified by list `findSome?`, but execution
constructs no list. For a domain of size `N`, the search bound is `N(E+6)+1`,
where `E` bounds body evaluation with one additional environment binding.
Each visit adds three loop operations, an environment write, a Boolean
comparison, and a branch. Domain-kind selection costs one. If a match leaves
coordinates unvisited, the next stop test costs three and performs no further
body evaluation. The selected environment is the one used for that evaluation.

### Source-fact evidence scan

`collectNamedFactEvidenceCosted` scans the source array directly. Its callback
returns an optional evidence row and the cost of matching and rendering that
fact. The scan retains each returned row in source order, including duplicates.
Its value theorem proves equality with list `filterMap`, which selects the
same rows. The executable scan constructs no intermediate list.

For `N` source facts, callback costs `c_i`, and indicators `r_i` equal to one
for retained rows and zero otherwise, the exact scan cost is
`1 + Σ_i (c_i + 3 + r_i)`. Initialization costs one. Each fact costs an
iteration, an array read, and an optional-result test. Each retained row adds
one array write. If every callback costs at most `C`, the total is at most
`1 + N·(C+4)`, which is monotone in both size and callback bound.

Two matching operations have separate counted definitions. A scope check costs
one for `everywhere` and six for a named world, including indexed-name rendering.
Taxonomy implication constructs the ordered ancestor fields and searches them
until the first match. Construction costs at most 202, and the search visits
at most eight fields at four operations each. The total bound is 234 for the
fixed taxonomy. Its value theorem connects direct field membership to expanded
compiled-fact membership, so the scan needs no temporary compiled facts.

`Frontend/ModelText.lean` owns counted fact rendering. Its value theorems
preserve the declarative formats, including infix instantiation and
specialization, projections, scopes, and derived assertions. The ordinary fact
renderers return the counted values. A derived assertion costs at most ten
operations for arity selection and concatenation. A complete scoped fact costs
at most 15, including scope and field selection. String-character work remains
outside these bounds.

`unaryEvidenceCosted` renders the requested thing name once and scans all `N`
source facts. Each callback tests the fact constructor, thing name, scope, and
taxonomy membership in that order. A false test skips the later tests and all
text construction. A match retains the source fact's surface form. If taxonomy
expansion supplies the requested field, the row also names that field in a
suffix. The value theorem preserves these rows and their order.

The bound is `5 + 270N`. Name rendering and scan initialization cost five.
Each callback costs at most 266: one fact-constructor test, 243 for the combined
matching condition, one result branch, and at most 21 for text and its suffix.
The array scan adds at most four operations per fact. This bound is monotone
in `N`; exact counts depend on which tests fail. For one Mode source fact,
name mismatch costs 12, scope mismatch costs 19, an exact match costs 99, and
taxonomy evidence for Moment costs 110.

`atomEvidenceCosted` covers every diagnostic atom. It resolves each variable
before scanning the facts, then calls the matcher for that atom's arity and
field kind. Primitive and derived assertions remain separate. Type evidence
selects instantiation targets and reuses the target's rendered name throughout
the scan. Individual-semantic atoms have no source-fact evidence and return an
empty array at cost two. All value proofs preserve row order and duplicates.

Every non-unary matcher costs at most 34 per fact. The largest case has five
comparisons, five Boolean tests, a scope check costing six, two constructor
tests, and at most sixteen operations for the output branch and rendering.
Unsuccessful tests skip later comparisons and text. Each retained row adds
the scan's array write; nested constructor tests run only for the relevant
outer constructor.

For `E` environment bindings and `N` source facts, the uniform bound is
`20E + 23 + 270N`, monotone in both parameters. At most four thing references
cost `4E+5` each, and the world reference costs `4E+1`. Atom selection and scan
initialization add two. The fact coefficient uses the larger unary bound of
270; non-unary scans need at most 38 per fact. Variable resolution and the
scan each return a value and cost, which the atom result combines directly.
The list collectors and declarative matchers serve as proof specifications.
Production uses the counted array scan.

The failing-atom report includes the source-evidence count, the atom label,
two header joins, and each retained row. It reads the atom array directly and
stops when the output budget is full. Its value theorem preserves source order,
duplicates, and the header-only result when only one slot remains.

For `K` atoms, `E` environment bindings, and `N` source facts, this report
section costs at most `K(40E + 76 + 275N)`. The bound is monotone in all three
parameters. Per atom, source lookup costs at most `20E+23+270N`, and the
label costs at most `20E+38`. The empty test, header joins, and header write
add six. Evidence insertion costs at most `5N+3`. Loop control and the checked
array read add six per visited atom. A stop before a remaining atom costs
three and skips that atom's read and all evidence work.

Source lookup precedes header insertion. A header-only result therefore pays
for the complete source scan. The generic report includes this section's bound.
The separate derived-assertion path is outside this axiom-report theorem.

### Context-formula evidence

Context traces explain why the failed obligation applies. Their atom evidence
uses source rows first. Without a source match, it evaluates the atom in the
generated model. A true result produces the generated-model row. A false result
produces no atom row. The enclosing loop guarantees room before each visit.

Let `Q` bound a diagnostic atom evaluation, `E` count environment bindings,
and `N` count source facts. One context atom costs at most
`Q+40E+68+275N`. The terms include source lookup, the possible model check,
the atom label, and retained rows. Each skipped branch contributes no child
cost. The loop adds six operations for control and a checked array read.

For `F` formula nodes, a context-formula report costs at most
`F(Q+60E+115+275N)+15`. Rendering the formula costs at most `F(20E+39)`.
The header and final fallback reuse this one label. Atom collection costs at
most `2F+1` and produces at most `F` atoms. Header insertion, the final
size test, and the optional fallback contribute at most fourteen further
operations. The bound is monotone in `F`, `Q`, `E`, and `N`.

The value theorem preserves text, source duplicates, and row order. The
renderer expects a context formula whose truth the caller established. Its
formula-level fallback does not perform another truth check. Text and atom
collection precede the budget stop, so a zero budget does not erase their cost.

The outer context report includes each formula report's cost. It reads traces
from their array and stops when the output is full. For `C` traces, each with
at most `F` formula nodes and `H` environment bindings, its bound is
`C(F(Q(H)+60H+115+275N)+21)`. Here `Q(H)` bounds atom evaluation at environment
size `H`. Each trace visit adds six operations to the formula report's bound.
The value theorem preserves trace order, row order, and output limits.

Failure minimization supplies the premises for this bound. Given an original
formula with `F` nodes and an environment with `E` bindings, every context
formula has at most `F` nodes, and every context environment has at most
`H=E+F` bindings. Witness search adds one binding at a time. Context
concatenation joins trace arrays without merging their entries' environments.
The generic bound uses this `H` and the proved context-array size bound.

The context environment and failed assignment can differ. A regression retains
six bindings from a successful antecedent and only two in the failed consequent.
The bounds therefore track both objects separately. The dispatcher bound holds
for every evidence budget. The producer still counts the executed budget checks
and the final output cap. Its bound includes trace construction, evaluator
dispatch, and failure minimization.

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
  Queries.lean
  Frontend.lean
  Reuse.lean
  Diagnostics.lean
  Diagnostics/
    Formula.lean
    Paths.lean
    ProductFamily.lean
    Reports.lean
    Source.lean
    Unique.lean
  Theorems.lean
  Certification.lean
```

`LeanUfo/UFO/DSL/Complexity.lean` is the aggregate import. Production entry
points erase counted cores directly or use proved native replacements that
preserve compact kernel reduction. `Certification.lean` composes the
source-linked workflow through the shared frontend drivers.

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
are added, and it checks compiler and targeted-probe costs across each reported
model family. It does not require exact aggregate-checker counts to grow:
changing a fact can make that checker stop earlier.

### Generated scaling benchmark

`lake exe complexity-benchmarks` emits CSV for five deterministic model
families at 2, 3, 5, and 9 things. These are numeric AST inputs, not parsed DSL
sources. The executable records input facts, product-family slots, explicit
relation/projection cells, AST-compiler cost, cached-model construction cost,
aggregate-checker cost, and a targeted operation probe. Separate elapsed times
cover those four stages. Sparse and cyclic
families have linear fact streams; dense and projection-heavy families have
quadratic streams; product families independently scale their witness slots.

The constructor uses the same verified cached representation as production.
The harness first checks generated coordinate bounds. Targeted probes then
exercise every unary or binary cell, rebuild cyclic closure, search the complete
product-family array, or validate every projection cell. Their fixture checks
must pass even if the aggregate checker stops at an earlier axiom. This keeps
an early failure from hiding the operation the family is intended to measure.

The 2026-09-11 run passed all 20 cases. Representative operation counts follow;
millisecond timing remains too coarse at these sizes for a scaling claim.

| family | things | compiler cost | model cost | checker cost | targeted probe | probe cost |
| --- | ---: | ---: | ---: | ---: | --- | ---: |
| sparse | 9 | 23081 | 4 | 119541 | unary scan | 90 |
| dense | 9 | 24836 | 4 | 119541 | binary scan | 1071 |
| cyclic | 9 | 22394 | 4 | 119541 | closure rebuild | 15288 |
| product | 9 | 23108 | 1336 | 119541 | family search | 234 |
| projection | 9 | 24431 | 4 | 119541 | projection scan | 1314 |

These rows are measurements, not theorems. In particular, every generated
model fails early in the ordered registry, so its aggregate-checker cost does
not measure the worst-case registry bound. The separate probes all pass.
The unary scan costs 10n; the dense binary scan costs n(13n + 2), including
finite-loop visits. Cyclic closure counts at 2, 3, 5, and 9 things are 252, 754,
3016, and 15288. The proved cubic closure bound, not these four measurements,
establishes the growth guarantee.

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

An isolated comparison during the workflow repair exposed a certifiability regression:
`FlowerPropertyChange` passed at `ee87137` in 7.14 seconds but failed in the
feature snapshot after 15.92 seconds. The failure occurred in the generated
derived-assertion proof, where broad simplification exhausted its step limit.

`ufo_cert_tac` first exposes the finite proposition and tries ordinary `decide`,
keeping the model definition folded. This lets proof reduction select the
required fields without first simplifying the complete model construction.
Predicates without a computable decision procedure use the semantic simplifier.
Neither path adds native proof axioms or raises resource limits. The change
concerns proof elaboration, which is outside the algorithmic cost theorem.

The repaired branch passed these isolated checks with prebuilt dependencies:

| target | repair baseline `ee87137` | repaired branch | result |
| --- | ---: | ---: | --- |
| `Company` | 5.52–6.05 s | 2.40 s | certifies |
| `WoodenTable` | 6.81 s | 2.83 s | certifies |
| `FlowerPropertyChange` | 7.14 s | 2.96 s | certifies |
| `RedirectedWalk` | 7.13 s | 3.03 s | certifies |
| `RelatorProbe` | 141.04 s | 125.88 s | certifies |

The 2026-09-11 `LEANUFO_PERFORMANCE_TESTS=1 lake test` passed in 437.39 seconds,
including 1,652 build jobs and the user-facing performance fixtures. That time
includes rebuilds and is not comparable to the isolated file timings. The user
accepted the earlier Company comparison (5.52–6.05 seconds versus 8.10–8.29
seconds), but did not accept loss of certifiability. The default regression
imports reuse the flower example and audit its derived-assertion proof for
unexpected axioms. Both revisions used Lean 4.33.1 and the same dependency
checkout. Each measurement ran `lake env lean` on the named example without
another build or suite running. These are isolated file timings, not total
clean-project build times.

The latest all-inclusive run, on 2026-09-13, passed in 362.58 seconds with a
1,656-job test dependency graph. It covered semantic fixtures, diagnostics,
certificate export/revalidation, namespace discovery, all user-facing examples,
and Relator. No suite or benchmark ran alongside it, and no resource limits
were raised. This was an incremental verification run, not a clean-build
speed comparison. Subsequent changes affected documentation and comments only.

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

In that earlier representation-split snapshot, the four small examples were
27–43% slower and the smaller set was 36% slower. Those measurements record
the regression at that stage, not the later repaired branch's performance.
The isolated repair comparison above and the latest full profile provide the
subsequent evidence. The complete suite detects semantic regressions. The
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
