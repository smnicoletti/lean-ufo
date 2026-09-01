# Concrete Complexity and Verified-DSL Boundary

This is the canonical guide to Lean UFO's operational complexity results.
Every complexity claim below refers to a counted production computation.

## Claims

The primary target is **data complexity**: it measures growth when the UFO
checker registry is fixed (currently 116 checks) and only the finite model grows.
The secondary target is **combined complexity**: it measures growth when both
the model and the registry or formula can grow. These are different results;
the fixed-registry theorem must not be generalized silently to user-extensible
registries.

“Explicitly encoded” means every primitive relation cell, projection cell, and
product-family slot is represented and included in the size metric. Opaque
functions are not treated as constant-size relation inputs. The production
compiler and checker must be **erasures** of their counted executable
definitions—discarding the recorded cost while keeping the same value—or be
connected to them by a theorem that proves both implementations return the same
value.

## Unit-Cost Machine Model

`Costed α` stores a computed `value` and a `Nat` cost. The model charges the
operations named at their executable definitions: Boolean operations,
comparisons, loop iterations, array accesses and writes, initialized cells,
queue operations, and emitted diagnostic items. A **short-circuit** operation
stops when its result is already known. For example, `false && q` does not
evaluate `q`, and a universal scan stops at its first false item. The counted
combinators follow Lean's left-to-right order and do not charge such unevaluated
branches.

One array bounds check or access is a unit-cost primitive. Dense initialization
is charged per cell. Source name indexing reports hash-map insertions and
lookups separately as abstract `mapOps`; it does not silently turn them into
constant-time character operations. No constant-time theorem is claimed for
hash maps or strings unless a separate verified interface is introduced.
Character-level string work, allocation, garbage collection, elaboration,
kernel checking, native instructions, Lake overhead, and operating-system
scheduling are outside this theorem. Benchmarks measure those effects
separately.

### Which representation receives the bound?

The operational bounds apply to the dense representation used by native
execution. They include dense-table construction, table writes, closure
precomputation, table reads, and checker control flow.

Lean's kernel uses compact sparse definitions when it checks generated
certificates. The sparse and dense implementations perform different
operations. The correspondence theorems prove that they return the same value.
They do not claim that both implementations take the same number of steps.

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

## Input Metrics

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

## Verified-DSL Theorem Map

The term “verified DSL” is reserved for the following chain, inspired in part
by RadixExperiment's executable-interpreter/relational-semantics equivalence and
per-optimization preservation proofs:

| Stage | Required theorem | Status |
| --- | --- | --- |
| Parser/emitter | documented trust boundary and generated-source validation | existing boundary; not kernel-verified parsing |
| Name resolution | success corresponds to the declared name environment | the production batch compiler builds world/thing indices once and reuses them for facts and product families; structural index construction is the counted executable and has the proved early-exit bound `mapOps ≤ 2·names`; lookup exposes one abstract `mapOp`; successful resolution preserves scope, taxonomy, and projection-arity metrics |
| Scope/taxonomy/specialization passes | each pass preserves its stated source semantics | scope expansion has exact charge `Σ(scopeMultiplicity+1)`; taxonomy uses an accumulator with exact charge `inputFacts+emittedFacts`; specialization is a single accumulator pass; their concrete sizes, costs, and projection-arity preservation are connected to `SourceMetrics` |
| Flat tables | compact and dense lookups return equal values; projection conflicts are rejected | Compact definitions support kernel reduction. `implemented_by` selects typed dense arrays for native execution, and counted lookups erase to those dense functions. Theorems cover each fact write and the complete fact fold. `ExplicitTableCorrespondence` packages unary, binary, ternary, and projection lookup equality. Projection uses deterministic last-write semantics. Validation rejects different results for one projection coordinate and accepts identical duplicates. The cost theorem covers only the dense path. |
| Inherence closure | Warshall matrix corresponds to `MomentOf` | compiler storage and production axiom 68 derive from the same verified sized-matrix recurrence; the compiler additionally carries deterministic first-hop evidence, with row-major lookup, hop-implies-reachability, exact `W·(13T³+9T²+1)` evidence-carrying construction cost, and `MomentOf` correspondence proved |
| Finite-model interpretation | compiled Boolean fields denote the corresponding `UFOSignature4` relations | core bridge theorems exist |
| Compiler | counted value equals compact production compilation | proved: source compilation uses a counted core, and `compileExplicitModelASTCosted_value` connects explicit-AST cost accounting to the compact proof-facing compiler. `compilerOperationalCost_le` covers every success and early-error branch with the explicit multivariate `sourceCompilerPolynomial`. Only afterwards, `source_compiler_scalar_polynomial_bound` derives the one-variable bound `80·inputSize⁴`, where `inputSize` contains every independently sized source component. |
| Checker | counted erasure equals production checker | proved. Production finite quantifiers are counted erasures with `true`/`∀` and `true`/`∃` correspondence. All 116 registered checks are counted computations, including the auxiliary qua-individual/endurance condition and the identity, symmetry, and seven-thing triangle distance extensions. The exact ordered registry stores delayed computations, has proved size 116, stops at first failure, and returns the same Boolean as `checkAxioms4Checks M`. Each registry entry carries its own concrete proved bound. `fixed_registry_data_complexity_bound` sums those 116 heterogeneous formulas plus actual traversal charges. The generic heterogeneous and uniform registry theorems provide the separate combined-complexity forms. The scalar metric explicitly includes dense relation cells, product-family records, and both witness arrays. Axiom 99's witness, family-search, and nested checker bounds are quadratic, cubic, and degree six. Unfolding the other 115 entries yields ordinary monomial coefficient sum 2898, while axiom 99 contributes 42, giving the proved fixed-registry bound `2940·n⁸`. Compiler and checker compose to `3020·(sourceSize+modelSize)⁸`; the independently sized explicit model is retained because compilation expands scopes and per-world witnesses. Every operational result remains separate from semantic soundness. |
| Certification | successful Boolean checks imply `UFOAxioms4` | existing soundness theorem |
| Diagnostics | evidence is sound and output-sensitive | certification-failure output passes through a counted erasure with a deterministic 128-item budget. The limiter has exact cost `2·emitted+1`, and every witness branch returns a deterministic prefix. Generic quantified assignments stream in lexicographic order and stop when the budget is full. Formula traversal, evaluation, minimization, rendering, and the specialized axiom 68, 71, 73, 78, 79, and 99 analyzers are included in `diagnosticWitnessesInnerCostBound`. The public theorem `diagnosticWitnessesBudgetedCosted_cost_le_inner_add_emitted` bounds the complete production diagnostic by that input-dependent formula plus emitted output. The companion exact-cost and size theorems state the emitted-prefix boundary. Diagnostics remain outside the headline certification bound because they run only after failure and construct user-facing output. |

RadixExperiment is engineering precedent, not a complexity source and not
evidence that the remaining Lean UFO obligations are already discharged.

## Module Layout

```text
LeanUfo/UFO/DSL/Complexity/
  CostModel.lean
  Metrics.lean
  Tables.lean
  Closure.lean
  Compiler.lean
  Checker.lean
  Diagnostics.lean
  Theorems.lean
```

`LeanUfo/UFO/DSL/Complexity.lean` is the aggregate import. Production entry
points use the counted core directly.

## Acceptance Evidence

The completed verification includes exact hand-checked counts on tiny examples;
monotonicity tests; sparse, dense, cyclic, projection-heavy, and product-family
generators; semantic regression fixtures; closure correctness and cubic
scaling; compiler and checker erasure; fixed-registry and parameterized
theorems; separate output-sensitive diagnostic bounds; and generated scaling
measurements. The final verification passed `lake build`, the fast and full
test profiles, certificate export and validation, and the
generated complexity benchmark.

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

The proof-facing/executable representation split is also checked against the
last revision before this refactor (`6a21fd5`). These are wall-clock engineering
measurements, not complexity theorems. Both revisions used separate build
directories with the same dependency checkout.

| target | base | feature branch | result |
| --- | ---: | ---: | --- |
| `Company` | 6.1 s | 8.3 s | certifies |
| `WoodenTable` | 7.9 s | 10 s | certifies |
| `FlowerPropertyChange` | 8.4 s | 12 s | certifies |
| `RedirectedWalk` | 8.4 s | 12 s | certifies |
| smaller example set, excluding Relator | 79.56 s | 108.06 s | certifies |
| positive Relator probe | 3649.25 s | 205.06 s | certifies; 17.8 times faster |
| full semantic test profile | 173.36 s | 170.54 s | passes; effectively unchanged |

The four small examples are 27–43% slower and the smaller set is 36% slower,
so proof elaboration still has a measurable constant-factor regression. They
remain well below the former heartbeat failure. The Relator probe, which is the
dominant certification stress case, is substantially faster. Release checks
must retain both views. The complete suite detects semantic regressions. The
Examples aggregate now includes Relator and detects proof-performance
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

## Current Limitations

The theorem uses the unit-cost model defined above. It does not bound string
characters, allocation, garbage collection, elaboration, kernel checking,
native instructions, Lake overhead, or wall-clock time. Indexed source-name
operations remain explicit abstract `mapOps`; they are not claimed to be
constant-time hash-map operations.

Native relation and projection lookup uses typed dense arrays. Kernel reduction
uses compact sparse definitions so generated certificate proofs do not expand
dense initialization. Sparse maps and lookup closures also remain where
diagnostics and certificate reuse need them. The headline checker bound counts
the named dense executable lookups and does not assign a constant-time cost to
the sparse definitions.
The recursive inherence definition remains as a specification; production
closure and axiom 68 use the proved cubic matrix implementation.

The concrete parser and declaration emitter remain in the documented trusted
boundary. Lean validates the generated declarations and certificates, but this
work does not prove the parser itself correct. The benchmark reports runtime
measurements for comparison with the operational theorem; those measurements
are not proof evidence.
