# Testing guide

[Docs home](README.md) · [Project README](../README.md)

The test driver is:

```text
LeanUfoTest.lean
```

The test tree is:

```text
LeanUfo/Test/
  Certificates/
  Complexity/
  Syntax/
  Certification/
    Positive/
    Negative/
  Diagnostics/
  Coverage/
```

## Default tests

```bash
lake test
```

The default profile checks syntax smoke fixtures, diagnostic rendering checks,
registry/manifest consistency, and counted traversal regressions.
`Certificates/Generation.lean` checks prerequisite order and the generated
checker calls for axioms 73, 78, and 79. It covers both trial proofs and
declarations. Failure probes must not refer to a checked theorem for the
failed field, which need not exist. These source-level tests complement the
full profile's certification and counterexample fixtures.
Typed-request tests check all 116 fields' fresh and reuse requests and their
explicit generated goal types. Probe tests retain the ordered pairs 75/73 and
79/78, and the single false-answer request for axiom 79. Registry-wide checks
require every registered native decision to come from a request node; only
axiom 99's excluded general fallback retains a raw native tactic. General
examples check fresh/reuse invocation counts and prefix bounds. These tests do
not claim that every requested call executes.
`Certificates/Execution.lean` checks exact preparation costs and request order
on success and early failure. It checks that Lean accepts prepared fresh and
parent-reuse proofs. A false answer must stop before a later unknown checker
is resolved. Command, ordinary-term, and strict-term capture must report that
failure without leaking errors into subsequent attempts. Integration tests
use the same proof sources and executor as the production frontend.
Prepared-attempt tests cover every pair of native and subsequent proof-failure
outcomes. With a ten-operation native callback, preparation costs twelve on
native failure and fourteen on success. Subsequent proof failure changes the
reported status without changing the algorithm work already performed.
`Complexity/SourceCorrespondence.lean` applies the source-size preparation
bound to the production axiom-75 proof source, including fresh and reused forms.
Checked-attempt composition tests include a seven-operation planner and actual
native comparison costs for ten-operation child and twenty-operation parent
checks. Fresh success costs 39; reuse success costs 79. Failed native reuse
followed by fresh success costs 75; failure in the subsequent trial proof costs
77 instead. Failure in the initial declaration's proof followed by fresh
success costs 112. A general source-bound application uses independently
supplied child and parent sources and the real axiom-75 registry entry.
Further source-bound applications cover axiom 73's semantic trial and
declaration, which request axiom 75, and its counterexample probe, which
requests axiom 75 followed by axiom 73. Each uses the real counted checker
entries and allows arbitrary observed proof failures.
`Complexity/Certification.lean` tests the joined workflow. Root and extension
applications use actual registered checkers on source-produced models. An
empty registry plus report selection costs three operations and invokes no
analyzer. Selecting a 100-operation failure analyzer costs 101; success costs
one and skips it. State traces verify that only the recorded failed field is
analyzed, once, with its completed/reuse prefix retained. Derived-assertion
tests cover skipped proof work, proof-only failure, and successful continuation;
the synthetic ten-operation precheck gives exact totals of 13, 16, and 112.
The whole source-to-workflow bound is applied to an axiom-75 request, including
source compilation and the selected diagnostic allowance.
The same test module imports the public DSL guarantees. Its automated axiom
audit covers the multivariate, scalar, fixed-registry, and monotonicity workflow
theorems, plus the changed scope-expansion and fresh-reuse guarantees. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted.
Exact request tests cover all Boolean operand values. A child costing ten
operations gives an expected-answer request cost of eleven, even with a parent
costing one million. Agreement with a twenty-operation parent costs 31.
A general equality proves that expected-answer requests ignore the parent
computation in both result and cost.
Prefix tests use all 116 fields' fresh and reused scripts. An empty prefix
costs zero; one decision costs eleven or 31 with the operand costs above.
Axiom-73 and axiom-78 probe prefixes cost zero, eleven, and 22. A limit beyond
the two requests does not add work.
The same module checks the production checked-field driver's result and callback
order for all 32 combinations of reuse and attempt outcomes. Seven exact-cost
cases cover successful reuse, fresh success, skipped declarations, and failed
fallback. Callback charges of 10, 20, 100, and 200 distinguish the selected
attempts from the driver's two, three, or five branch operations.
Planner tests check all 32 paths again with an explicit planning event and
record the parent supplied to each initial callback. A separate 32-case exact
cost test gives planning seven operations and requires that charge exactly
once, including after failed reuse. A precheck-failure test proves the planner
and all proof callbacks are skipped.
Outer-loop tests cover all 64 success/reuse combinations for three fields.
They compare the completed prefix, parent records, failed field, and callback
trace with an independent first-failure specification. Exact cases charge
153 operations for all three successes and 23, 47, or 151 for failure at each
position. An empty registry costs two. Running the counted fresh-attempt
driver for all 116 fields costs 4,526 in the synthetic callback fixture.
The per-field driver has a 128-case result/trace test. Exact counts distinguish
early precheck and checked-proof failures, command-only proofs, skipped
declarations, and preserved parent reuse. The real policy costs 2, 14, and 15
operations at selected positions. A non-68 field skips closure search even
with million-sized supplied domains. A combined 116-field test uses both
drivers, the real policy and precheck, and synthetic proof callbacks.
Reuse-source tests cover all 116 fields, require the counted comparison's
erasure and the parent theorem, and reject cost records in generated goals.
Boolean comparison tests cover all four answer pairs, including two false
answers. The extension fixture requires every unchanged-alias field to report
reuse, so a malformed reuse proof cannot pass unnoticed through fresh fallback.
`Certificates/Reuse.lean` tests the counted planner. It compares all 784 pairs
of 28 source records, covering each fact form, world scopes, family fields and
slots, and source options. Exact-count cases cover empty and unequal-length
arrays, first and later mismatches, duplicate and reordered entries, table
field isolation, skipped optional components, fresh mode, and source-equality
bypass. These tests complement the planner's general equivalence and bounds.
An explicit-AST fixture checks that duplicate metadata rows survive dense
materialization. A source-linked bound test compiles a parent with repeated
facts and family slots, then checks all 3,248 combinations of 116 fields and
28 child sources. General examples exercise the compiler row invariant, the
source-linked planner theorem, and monotonicity of its size bound.
`Complexity/Traversal.lean` checks million-entry initialization, folds, and
compiler array mapping and scope expansion. Name-index tests also cover
100,000 distinct names. The standalone linear name scan has million-entry
early-success and full-failure cases. Small cases check empty input, exact error-prefix
costs, first-error order, and fact/world ordering. These tests guard against
cost accumulation causing stack-depth failures; they are not wall-clock benchmarks.
`Complexity/Resolution.lean` checks exact source-resolution costs and which
error wins when several references are invalid. It covers scope selection,
product-family lengths and witness slots, duplicate world/thing names, and
empty source compilation.
`Complexity/DerivedFactRendering.lean` checks exact certificate text and
operation counts for all eleven signature selections, direct-field fallbacks,
and all four arities. It also covers large coordinates, empty-world expansion,
explicit out-of-domain scopes, and a fixture that attains the scope bound.
`Complexity/SourceCorrespondence.lean` checks the successful compiler record's
construction invariant, coordinate bounds, and lookup-agreement bridge. The
general lookup proof requires only compiler success. Other proofs reject a
substituted world count and an invalid hand-built name index. Concrete cases
cover all five fact constructors, both scopes, first/last source coordinates,
tuple slots larger than the thing count, empty domains, taxonomy, reflexive
specialization, family storage, and duplicate-world rejection. These checks do
not establish a complete source-to-checker cost bound. Family readback tests
connect successful source resolution to the production model's exact registry.
They cover name order, repeated family records and witness slots, zero worlds,
unequal array lengths, and unknown witness names.
The source-level product-family theorem compares diagnostic and checker search
results without an independent relation-agreement premise. Native regressions
exercise both worlds, a later valid family after an invalid one, invalid-only
and empty registries, mismatched domain/type keys, and repeated valid records.
Source-metric tests derive family counts, slot counts, construction costs, and
the checker-size bound from compiler success. A two-world source with two
six-slot families produces four witnesses, 24 slots, 20 cache slots/cells, and
256 construction operations. An empty registry produces no witnesses, retains
the same cache size, and costs four operations. The generic tests use the
cached constructor and its source-only cost, cache-size, and 3N² model-size
bounds. They also check construction-bound monotonicity and preservation of
the exact witness registry during cache installation.
Reconstruction tests charge the returned AST's table builder, model constructor,
and each selected registered checker. Both concrete source fixtures satisfy
the per-call bound; empty domains and rejected sources are excluded. General
examples prove that reconstruction costs no more than successful source
compilation and satisfies its 511N⁴ bound. These component tests are separate
from the invocation-count and whole-workflow tests described above.
The counted reconstruction tests also check its exact two-stage cost and
537N⁴ bound. General examples prove constructor erasure and use the concrete
axiom-75 checker to instantiate the registered reconstruction bound and the
expected-answer erasure theorem.
Two agreement tests use distinct child and parent ASTs. They prove the erased
comparison and its exact cost, including both constructions and checker calls.
A general axiom-75 example instantiates the source-size prefix bound for the
generated fresh and reused checked scripts. It proves the required registry
membership and covers every prefix limit.
A general precheck test supplies source domain sizes to the guarded axiom-68
precheck and proves its 124N⁴ bound without requiring compiler success.
Individual-call tests use the full registry budget even when an aggregate run
stops early. Synthetic callbacks distinguish a four-operation early exit from
a later 100-operation call. Concrete sources check every registered entry
against the source-size bound.
Checker-closure tests count matrix construction at one and two worlds. Two
things cost 110 operations without edges and 94 with a cycle at one world.
The corresponding uncached axiom-68 checks cost 139 and 123, including cache
selection. Raw-model fixtures check the source counter's eleven-unit edge
interface. `Complexity/Queries.lean` separately checks compiled dense models:
a single directed edge costs 102, in either direction. The general block
equality connects the uncached constructor to complete counted table reads.
Matrix-only tests check zero size, skipped expensive diagonal queries, exact
reachability arrays, and the callback-size-dependent bound.
Checker closure queries also have exact three-read tests for world isolation
and edge direction. Ultimate-bearer tests check both the thirteen-operation lookup
branch and the ten-operation branch that skips closure reads. A two-world
case with one moment and one bearer costs 61 operations for witness selection,
212 for closure construction, and 113 for axiom evaluation. Cache selection adds
one, totaling 326. The same model with a proved cache costs 120: direct flat
queries add six operations to evaluation, but closure construction is skipped.
Three-thing compiled fixtures check missing, first, last, and multiple bearers.
Their cached axiom-68 counts are 66, 130, 149, and 157, respectively.
A false outer moment premise skips the search at cost 43 for the whole model.
An expensive reachability callback verifies that a moment candidate skips it.
Existence-scan tests exhaust all sixteen two-world existence patterns.
Exact counts distinguish a first-world counterexample (20) from a second-world
counterexample after a false premise (32). Opposite-direction counterexamples
cost 55 for independence. Definition checks 63 and 64 retain both source
occurrences in their counts, subject to AMB-004.
Inherence tests cover skipped implications, failed dependence, missing moment
classification, successful instance search, concrete-individual fallback, and
two distinct bearers. Shared-caller tests check the external-dependence early
exit and axiom 79's boxed existence implication.
External-dependence tests distinguish first- and last-world difference witnesses
and exhaust the sixteen two-world existence patterns. A three-world fixture
separates the two difference witnesses. Its bearer test costs 13 when no edge
exists, 56 when the first difference scan fails, 96 when the reverse scan
fails, and 105 when both succeed. Mode tests cost 9 when classification fails,
101 for the first external witness, 328 for a later witness, and 423 when no
witness exists. Whole-check tests retain both definition occurrences in axioms
69–70. A second truth-table test varies the edge and both witness worlds.
Foundation tests cover absent, first, last, and conflicting foundations.
On three things, unique-foundation searches cost 42, 60, 88, and 105 operations,
respectively. Shared-foundation tests distinguish a skipped second read from
a failed second read. Checks 71, 72, and 77 cover missing classifications,
skipped searches, invalid foundations, and successful axiom checks.
Qua-individual tests cover first and last targets, skipped mode checks, and
two conflicting targets. Axiom 73's classification tests isolate a failed mode
test, a failed inherence test, a missing shared foundation, and a complete
match. Its part scan covers both the reflexive shortcut and distinct-coordinate
table reads. Axiom 78 tests the same shortcut with first and last foundations.
Relator fixtures isolate proper-part search, pair compatibility, and inclusion
of compatible candidates. The successful one-part characterization costs 596
operations, and its whole axiom check costs 717. Removing the first qualifying
candidate skips the inclusion check; adding a compatible object outside the
part relation makes that inclusion check fail. Mediation witnesses distinguish
the reflexive part shortcut (16), a later distinct part (41 or 55), and a
searched domain without a witness (42 or 55).
Type-characterization fixtures distinguish missing type classification,
missing forward witnesses, missing reverse witnesses, and duplicate bearers.
On three things, unique-bearer searches cost 42 without candidates, 86 with
the first candidate, 114 with the last candidate, and 166 with two bearers.
An exhaustive test varies both instance and inherence facts. The whole-axiom
tests also cover vacuous quality characterization when no moment instance
exists and verify the separate qua-individual/endurant typing check.
Quality-structure tests cover no associated type, the first type, the last type,
and two associated types, with counts 36, 74, 98, and 146 on three things.
Outer membership and type-association searches cost 153 without a structure,
284 with the first structure, 386 with the last, and 554 with two structures.
Independent fixtures test missing set classification, empty membership, domain
versus dimension classification, and the intrinsic-moment-type guard.
Proper-subset tests cover failed containment, equal sets, and first or last
strict-difference witnesses. An exhaustive sixteen-pattern test checks the
Boolean result. Axiom 90 tests each association/subtype stopping point, including
both subtype directions, which make its strict-subtype premise false.
Quality-value tests cover absent, first, last, and conflicting values. Their
three-thing searches cost 42, 60, 88, and 105 operations. Repeating a source
fact preserves the first-value result and count. Whole checks exercise skipped
quality/quale tests and failed uniqueness. Axiom 94 tests failed instantiation
(13), failed association (24), and visited membership (35). First and last
type/space witnesses cost 39 and 185. Exhaustive Boolean fixtures check the
three axiom results independently of their counted implementations.
Simple/complex-quality fixtures separate first and last inhering children,
unclassified children, and reverse edges that make the children complex.
Exact parent tests distinguish the repeated source-level quality computation
from the inherence scan. Axiom 97 fixtures retain the five conjunction branches
after an early failure and reject distinct inhering instances of the same type.
Type fixtures cover skipped classification, types without instances, and failed
simple/complex instances. Exhaustive Boolean tests check all four axiom results.

Kernel and native table tests compare the full projection value/cost pair.
Generated-code review checks that model assembly calls the counted projection
once, without a second lookup to recover its cost.

Product-family tests distinguish absent slots, initialized empty cells, and
stored self-projections that return the same tuple with different costs.
They cover projection membership failure, missing association, missing
characterization, uncovered targets, and wrong family headers. Ordered searches
test missing registrations, repeated valid entries, and a valid second entry.
A five-slot family over three things checks that arity remains independent of
model size. Additional tests cover zero slots, world isolation, and counted
projection correspondence for every successful source compilation.

Distance tests separate classification failures, common-membership search,
missing results, and non-unique results. Exact counts distinguish first and
last witnesses and reject a reversed distance pair. Life-of tests check
self-overlap, directed overlap, event classification, and manifests reads.
False-left equivalences still evaluate the right side. Exhaustive Boolean
fixtures verify these outcomes independently of the counted correspondence.
The four definition checks have kernel/native zero-cost tests and general
semantic proofs for every finite model.

Source-composition tests apply the multivariate and scalar bounds to the
successful compiler's returned tables. A test driver evaluates compilation,
model construction, and the aggregate checker in that order. Fixtures cover
scoped facts, replicated families, empty domains, and duplicate-name rejection.
These tests do not represent the frontend's per-field proof driver.

Cache installation costs one operation beyond the ordinary model constructor.
The cache-size regression includes its two world slots and eight cells.
Cache-correspondence tests connect stored lookup to the actual source-produced
model. Cases cover world-specific edges, swapped world rows, forged first hops,
replacement of malformed incoming caches, and empty domains. Swapping cached
rows preserves primitive-table agreement but fails cache validity.

`Complexity/Formula.lean` imports the public complexity aggregate and checks
the formula-size theorem against the existing diagnostic interpreter. Tests
cover quantifier nesting across branches and modalities, exact counts for
nested loops and empty domains, and skipped million-element domains. The
general monotonicity test covers the size bound, not exact execution counts.
Failure-selection tests apply the production cost and storage bounds. A failed
disjunction costs 36 operations with an empty environment and 71 with one
binding, including the copied binding. A conjunction retains one successful
context trace at cost 34. Nested negation costs 23. Successful-context tests
check array initialization and skipped million-element domains. Monotonicity
tests include domain, formula, environment, and derived-proposition counts.

`Complexity/Queries.lean` checks the unary checker/table connection. On a
verified compiled model, implication costs 14 with a false premise and 22
when it reads both tables. Disjointness costs 23 when it reads and negates the
right answer. Two-world/two-thing cases check world-first traversal within each
thing and stopping at the first failure, with costs 34 and 48. A general source
test derives all table/cache premises from successful compilation and compares
the full counted computation, not only its Boolean value.

Seven classification truth tables cover 64 Boolean combinations. Each case
compares both the answer and exact cost, including skipped reads and the
negation after a false left-hand side of equivalence. A two-world, three-thing
conflict costs 46 and distinguishes world-first traversal from thing-first
traversal. Axiom 45's six-entry registry costs 156 when all entries succeed,
25 when the first entry fails, and 155 when only the last entry fails.

Binary and ternary tests cover their complete block equalities and malformed
empty arrays, which cost 11 and 14. Truth tables cover axioms 102/104, distance
identity/symmetry, and all branches of the triangle antecedent. The triangle
tests use independent coordinates for its four reads. Asymmetric two-thing
distance fixtures fail symmetry at 80 or 124 operations, depending on edge
direction. Identity skips those unequal pairs and succeeds at 132.

Instantiation tests distinguish the current world from the searched worlds.
On two-thing, two-world fixtures, the type scan costs 15 for a first-position
witness and 56 for a last-position witness or an absent witness. Its complement
adds one. Axiom 1 retains both identical scans and costs 468 with no facts,
302 with a first-position instance, and 466 with a last-position instance.
Axiom 2's corresponding costs are 476, 312, and 478.

Subsumption tests distinguish direction and first failure (28, 64, and 75).
Specialization tests verify skipped scans and separate upper/lower searches.
Upper success costs 66 in the three-thing fixture; lower success costs 108
because it follows the failed upper search. Eight Boolean combinations test
each upper-witness read. Another truth table compares answers and exact costs
for axioms 7, 8, 10, 15, and 16 together. Modal tests compare possible, necessary, and absent instantiation in both
worlds. Exact cases cover rigidity, anti-rigidity, and semi-rigidity, including
skipped scans and failure before the second world. Kind tests distinguish
first/last candidates and the same-kind comparison from a conflicting kind.
A cross-world conflict costs 74 to find and 103 in the complete axiom-22 check.
Bridge truth tables exercise all premise branches with unary/binary read order.
A non-sortal violation in the second pair stops the checker at cost 62.

Quality tests cover all sixteen combinations of two kind fields and two
instantiation fields. They compare the exact counts for no match, a unique
first or last match, and two matches. Mode tests check both skipped and executed
quality searches. A two-world fixture distinguishes axiom 42's thing-first
order (78 operations) from axiom 43's world-first order (99).
Axiom 44's ten-entry registry costs 610 when all families pass, 58 on a
first-family failure, and 611 on a last-family failure. With no instances,
each family skips its leaf search and the registry costs 330. These fixtures
test individual checks, not certificates for the whole UFO registry.
Kind-witness tests cover all six specific-kind positions and a failed generic
kind. A two-world fixture checks skipped and executed instantiation reads.
Part-query tests distinguish equal coordinates (two operations) from unequal
coordinates (thirteen), and verify that part facts do not affect overlap reads.
They also preserve the answer of an arbitrary non-reflexive relation.

Exact axiom 47–52 tests cover empty relations, directed and mutual edges,
first failures, and first/last witnesses. A three-thing chain without its
transitive edge fails axiom 49 at cost 190. Sixteen combinations of directed
part and proper-part facts check axiom 52's Boolean condition.
Functional-dependence tests distinguish the distinctness check, first/last
target witnesses, absent source instances, failed functions-as reads, and
world isolation. A 32-case truth table checks the generic predicate.
Constitution tests exercise classification agreement, kind restrictions,
witness order, and persistence across two worlds. Sixteen classification
combinations check axiom 56. Exact tests for axioms 53–55 and 58–59 describe
the source counter, which charges both predicate occurrences. Native
compilation currently shares those identical calls; AMB-004 remains open.
The query module has 220 examples.

`Complexity/Reports.lean` checks the composed generic-report bounds through the
public aggregate. Exact cases cover a full three-assignment search (74
operations), zero budget (four), and an empty domain (eight). First and later
failures preserve their assignment text. A direct failed visit costs 145 with
no room and 147 when it retains one row: text construction precedes retention.
Tests also cover atom discovery, the public ax1 dispatcher, minimized formula
depth, and monotonicity in all report-bound size parameters.
Frontend-selector cases cover confirmed and unconfirmed probes, axiom 99's
witness limitation, axiom 68's closure report, and all three timeout markers.
An unconfirmed unknown field costs 15 operations without errors and 32 with
one nonmatching error. A timeout stops classification and suppresses raw errors.

`Complexity/Paths.lean` connects path soundness to the production source model
and the existing path cost/size bounds. A diamond with a cycle checks route
selection, while an isolated vertex and a second world check missing routes.
Exact counts cover direct, two-hop, reflexive, missing-world, and exhausted-fuel
calls. A forged raw table returns a false path, demonstrating why soundness
requires cache validity. An exhaustive regression checks path existence within
three hops for all 512 directed graphs on three vertices, including self-loops.
General theorem tests cover path existence for arbitrary finite graphs and
the actual source-produced model. A nine-vertex chain checks success after
eight hops (91 operations) and failure with insufficient fuel (80 operations).
`Complexity/ProductFamilyConversion.lean` checks the production finite-model
field against the counted witness converter. Exact counts cover empty inputs,
zero worlds, valid records, every failing field, mismatched lengths, and array
elements after failure. Output cases preserve family/world order and duplicates,
and keep a valid record after an invalid record with the same key.

`Complexity/Tables.lean` also checks the closure builder's counted edge callback
against the shared binary read. Empty and singleton closures skip all edge
queries. Two-thing cases assign a large cost to skipped diagonal queries and
eleven operations to each visited pair. The per-world builder costs 280 with
no edges and 252 with a two-edge cycle, including array conversion. Both tests
check reachability and first-hop arrays as well as costs.
Constructor tests charge the lookup bundle and model record separately from
witness conversion. They check the raw/verified cost equality, installed
relation fields, reflexive part behavior, and retained witnesses.
`Complexity/Taxonomy.lean` records ancestor membership and order across the
entire unary-field registry, including shared ancestors. It checks exact search
and batch counts, raw string names, repeated facts, and 10,000 inputs that each
exercise the largest taxonomy expansion.
`Complexity/Specialization.lean` checks original-prefix and witness ordering,
repeated targets, zero worlds, all fact constructors, exact counts, and a
million emitted specialization witnesses.
`Complexity/Tables.lean` checks exact dense-insertion counts, row-major
coordinates, field isolation, and duplicate writes. It also checks sparse-store
records and queries, raw projection-conflict behavior, family registration,
and exact empty and derived-only explicit-AST compilation counts.
Dense-query regressions check arithmetic counts, field isolation, invalid
projection slots/results, and missing world matrices or cells. These cases
also protect the raw-table fallbacks used by the value-correspondence proofs.
`Complexity/Diagnostics.lean` checks variable-lookup counts, absent variables,
last-binding shadowing, equality, and conjunction's early exit. A million-entry
environment checks direct accumulation during a full scan. Million-element
thing/world domains check immediate termination for all six formula quantifiers.
Separate full scans exercise both finite loops and an absent derived assertion.
Small assertion arrays check duplicates, first-match order, and exact read costs.
Assignment-domain tests cover empty input, a pre-filled budget, stopping after
one or two visits, nonzero starting coordinates, and a million-visit full scan.
A two-world, three-thing fixture checks lexicographic order under truncation.
Variable-array tests cover indices at and beyond the end, skipped prefixes,
repeated variable names, and exact descent costs. Million-entry arrays test
immediate budget stops and an empty first domain without a list copy.
Guarded query tests check all three arities, field isolation, missing cells,
each coordinate guard, and duplicate compiled facts. Exact atom counts cover
variable resolution, possible-instance search, and reflexive `part`/`overlap`
early exits. General proof tests instantiate bounded-compilation correspondence.
Modal tests use three worlds to separate dependence witnesses and check both
directions of existential independence. Functional and constitutional tests
check nested-search counts, distinct-target rejection, successful witnesses,
empty domains, and early exits before a nested search.
Dispatch regressions cover all seven recognized unary/binary names, unknown
names, case-sensitive fallback, and the precedence of computed predicates over
matching asserted text. Their exact counts include each visited name test.
Assertion-key tests compare literal expected strings for unary, binary, and
quaternary lookups, including empty field names, Unicode names, and multi-digit
coordinates. They separately check coordinate formatting, concatenation,
environment lookup, and assertion-scan costs.
Saved-result report tests cover retained rows, duplicates, an empty retained
report, and the proof-failure fallback. General theorem applications check that
reuse preserves the report choice and that one scan plus selection equals the
composed analyzer in both value and cost. Selection costs one operation for a
retained report and four for the fallback, independently of source size.
`SourceCorrespondence.lean` also checks the diagnostic bound on actual compiler
results. Cases include repeated derived assertions expanded over two worlds,
family registration, mixed primitive/derived facts, empty domains, and rejected
duplicate world names. General tests require compiler success, without an
independent assumption about the stored-proposition count.
Name-conversion tests preserve empty strings, dotted single-component names,
Unicode, order, and duplicates. They check exact counts of 1, 5, and 13 for
zero, one, and three entries, plus a 100,000-entry conversion at cost 400,001.
The source/diagnostic regressions charge compilation and both name arrays
before the precheck and saved-report selection.
Computed external-dependence witness tests check an empty domain, a single
successful candidate among failures, and a full ordered result. Exact costs
include array initialization, the dependence predicate, loop control, branches,
and witness pushes. An empty collector costs one. The three-candidate modal
fixture costs 645, and the four-witness fixture costs 425.
Declared-candidate tests check coordinate order independently of assertion
order, duplicate assertions, world-sensitive matching, empty domains, and exact
key/scan costs. These counts also include initialization: one for an empty
domain, 61 for three candidates with no assertions, and 91 for the duplicate
assertion fixture. A general theorem test checks that explicit compilation cannot
populate the unsupported primitive `externallyDependent` field.
Failure-candidate tests cover declared-candidate precedence, first inherence
match, no-match fallback, and an empty domain. Exact counts distinguish a
complete scan from an early stop. The general value test requires table
agreement and bounded coordinates explicitly.
Existence-witness tests check both directions of the search, absent witnesses,
empty worlds, and invalid-coordinate guards. Their exact counts check that a
false first existence query skips the second query. The shared first-witness
loop has million-coordinate full-scan and immediate-match regressions.
Failure-message tests cover all four combinations of directional independence
witnesses, literal explanation text, hierarchical names, and the `#n` fallback.
Bearer tests cover empty/no-edge domains, a bearer with no independence
failure, and multiple failing bearers. An edge written later at coordinate zero
must take precedence over an earlier edge at coordinate two. Exact counts
check that the selected reason is retained and that a modal witness avoids the
bearer search.
Mode-status tests check non-mode early return, the successful witness row,
two failure rows, and the optional declared-candidate note. Exact counts
include table guards, string operations, array initialization, pushes, and
emitted rows. Name-joining tests check empty/singleton arrays, repeated and
out-of-range indices, and agreement with comma-separated list intercalation.
Axiom 71 tests cover empty domains, absent founded pairs, valid relators,
computed-mode classification, and competing failures in different worlds.
Exact counts check that computed mode skips the relator query and that the
search stops after the first failing coordinate, independently of fact order.
Literal row tests preserve the assignment, trigger, classifications, status-row
order, both suggestions, and missing-name fallbacks. Complete-analyzer counts
include the retained search result, mode-status explanation, and final row
construction.

Axiom 73 predicate tests check reflexive part queries before coordinate guards,
non-reflexive part reads, common-target order, duplicate facts, and empty
domains. Cases with multiple common foundations distinguish shared targets
from unique-foundation equality. A general theorem test states the common-target
condition explicitly. Exact counts cover both query orders and the branches
that skip inherence or foundation search. A million-target full scan checks
tail accumulation. The universal characterization tests cover an empty domain,
success across all things, and the first mismatch, including an immediate
mismatch in a million-thing domain without a list allocation.

Foundation-status tests cover missing, unique, ambiguous, and distinct unique
foundations. Candidate arrays follow coordinate order despite reordered or
duplicate facts. Exact counts include initialization, guarded reads, both
searches in a comparison, and only the option branches actually visited.
The text checks include quoting, separators, repeated supplied indices, and
missing-name fallbacks. A million-target collector checks full traversal.
General proofs connect lookup to the filtered relation and formatting to its
specified text. An arithmetic regression proves that all four component
upper bounds grow with the thing count.

Axiom 73's first-failure tests distinguish all four constituent reasons and
check report priority when later predicates also fail. General theorem tests
connect the absence of a selected failure to the Boolean characterization.
Exact counts cover empty and complete scans, an immediate failure in a
million-thing domain, and an unasserted `QuaIndividualOf` input that skips the
scan. Text regressions cover assignment order, all failure rows, foundation
status, suggestions, and missing-name fallbacks.

The outer axiom 73 search tests both directions of the characterization and
world-before-thing ordering, including facts stored in a different order.
An empty one-world, one-thing table costs 40 operations per assignment and
49 for the nested search. Two things cost 253 for the search and 257 with
the no-mismatch report. Reverse-direction formatting costs 29, including
missing-name fallbacks. Million-entry empty-domain cases check that traversal
does not allocate assignment lists. General theorems characterize the absence
of a report and bound the complete analyzer's output by five rows.

Axiom 78 tests cover matching, distinct, missing, and ambiguous foundations,
reflexive parts, non-relators, invalid coordinates, and missing names. Exact
rows and counts check formatter reuse, multiple evidence groups, world order,
duplicate facts, and suggestion placement. Budgets zero, one, five, and six
exercise stopping between groups and public prefix truncation. A two-world,
two-thing mismatch costs 423 operations at budget one and 527 at budget six.
Million-entry domains test immediate budget exhaustion and a full empty-thing
scan. A general theorem bounds internal output by the budget plus four rows.
The ambiguous-foundation case retains a missing-witness report even when the
relator and part have a common target, because `FoundationOf` requires uniqueness.

Axiom 79's proper-part collector tests query direction, world isolation,
ascending order, duplicate facts, and the distinction between `Part` and
`ProperPart`. Exact counts cover empty domains, invalid whole/world
coordinates, and a million-candidate full scan. General theorem tests state
duplicate freedom, membership with its coordinate bound, and sparse-table
correspondence. The collection bound is monotone in the thing count.

Pair tests cover each failure reason, forward and reverse dependence failures,
successful self-pairs, missing display names, and early termination at the
first failing pair. Exact text tests check suggestions against the source
facts used by the computed predicates. Simple reports cost 34 operations.
A two-thing distinct-foundation report costs 162, including both foundation
status searches. A general theorem limits a pair report to six rows.

The nested pair traversal tests ascending and reversed input order, duplicate
array entries, empty arrays, successful self-pairs, and complete successful
search. A million-entry array fails at its first pair in 84 counted operations,
excluding allocation of the supplied array. This regression detects eager
construction of its trillion-pair Cartesian product. General theorems connect
the array traversal to ordered product search and bound its cost in worlds,
things, and supplied part slots.

Outer axiom 79 tests cover non-relators, invalid coordinates, absent proper
parts, successful pair searches, and competing reports across worlds and
things. The missing-part formatter costs 21 operations, including fallback
names. A one-world, one-thing missing-part report costs 65 in the full analyzer.
Empty-world and empty-thing cases exercise domain traversal separately, including
million-entry domains. General theorems bound output by six rows and establish
monotonicity of the whole-analyzer bound.

Axiom 99 registration tests cover empty arrays, domain and type mismatches,
duplicate keys, and large witness arrays. A million-entry registry stops at its
first match in six operations. A full domain-mismatch scan costs five million.
These counts exclude construction of the input arrays. A one-world, two-thing
regression checks that an unregistered quality-domain association is rejected
by ax99 and reported as missing registration, even without characterization
targets. It does not establish that the other 115 axioms hold.

Declared-family tests compare the diagnostic with ax99 on valid witnesses,
missing associations, missing characterization facts, projection failures,
uncovered characterization targets, empty families, repeated types, and invalid
coordinates. A later valid record must remain usable after an invalid record
for the same key. A missing projection uses the tuple itself, which can either
satisfy or fail dimension membership. The complete successful one-record
example costs 188 operations. Million-entry tests cover an immediate successful
registry search and immediate rejection of an invalid dimension coordinate.

The axiom 99 collector tests empty, absent, and present characterization targets.
A three-thing absent-target scan costs 64 operations. One target adds one array
append. Full report tests cover both registration categories and nonempty target
names. Search tests check world, thing, and type priority independently of fact
order. The complete analyzer costs 155 for missing registration, 272 for the
invalid registered example, and 319 for the valid example. These counts include
loop control and final result selection. An absent association costs 18 even
with a million thing names. A full million-candidate collector scan with an
invalid world costs 10,000,001 operations. Input-array construction is outside
these calls.

Output-limit tests cover empty input, budget zero, exact-size budgets,
truncation, duplicate items, and prefix order. Keeping one item from a
million-item array costs eight operations, excluding input construction.
General proofs connect the copy to `Array.extract` and show that repeated
caps preserve the items. The axiom 99 public-producer tests count one copy:
175 operations at budget one and 171 at budget zero for the missing-family
example. Budget zero removes output but does not skip this specialized search.
The general axiom 99 bound test permits simultaneous growth of world count,
thing count, record count, and total dimension/type slots.

Axiom 68 path tests cover target recognition without fuel, exhausted fuel,
missing worlds, out-of-range cells, empty cells, and a two-hop path. The path
costs 25 operations, or 29 with world selection and accumulator initialization.
A malformed cycle runs for one million hops and costs 11,000,003 without a
stack overflow. Compiled cyclic and diamond graphs check path choice, including
duplicate edges and competing routes.

Bearer tests check that moments skip path reconstruction and that candidates
retain coordinate order. The chain, missing-bearer, and multiple-bearer
collectors cost 83, 49, and 92 operations. Search tests cover missing-bearer
priority and world order. An empty world domain skips a million-thing search.
A full million-thing scan with no moments costs 16,000,004 operations, including
result projection. These counts do not include report construction. The
fallback test rejects the unsupported conclusion that an unexplained failure
must come from the proof bridge.

Report tests cover path separators, out-of-range name rendering, empty bearer
lists, and complete report text. A two-name path costs seventeen operations.
Two one-hop bearer descriptions cost 59. Complete missing-bearer and
multiple-bearer examples cost 95 and 345, respectively. The empty-domain
fallback costs eight. General theorem applications check the analyzer bound,
its monotonicity, and the three-row output limit.

Dispatcher tests prove that each of the six specialized names selects its
analyzer for arbitrary inputs. The selection adds two operations per visited
comparison and branch. Axiom 68's missing-bearer report costs 105 through the
public producer at budget one, or 101 at budget zero. Unsupported names retain
case-sensitive fallback text. Their counts include the generic registry scan.

Formula-prefix tests retain mixed thing/world variables and repeated names in
order. Extraction stops at existential and modal nodes. The exact count is
`3K+2` for `K` leading universal variables. A 100,000-variable prefix costs
300,002 operations and returns all variables without a stack overflow. Formula
construction is outside that extraction call.

Evidence-line tests cover empty input, zero/full budgets, oversized existing
output, empty strings, duplicates, and order. Keeping one formatted row from
a million-item array costs eight operations, excluding input construction.
General proofs specify the formatted prefix and the exact `5E+3` count for
`E` appended rows. The conditional size theorem assumes that existing output
already fits the budget.

Rendering tests cover every atom family, instantiation/subtyping notation,
custom labels, duplicate variable bindings, and out-of-range names. With three
environment bindings, a name reference costs seventeen, an instantiation atom
costs 58, and a four-argument atom costs 98. Formula examples check equality,
negation, conjunction, quantifier text, and modal text. A thousand nested
negations cost 3,037 operations and produce 6,005 characters. Input construction
and character work are outside that count. General proofs check text equality,
the formula-size bound, and its monotonicity.

Assignment-summary tests cover mixed world/thing variables, supplied order,
duplicate names, shadowing, and missing names. With three bindings, one
assignment costs twenty operations. A one-entry summary costs 24. Four entries
cost 99. General proofs specify the text and the bound `V(4E+13)+1` for `V`
displayed variables and `E` bindings.

Preamble tests supply text with total cost 41. Budgets zero through three give
counts 47, 49, 51, and 53. Thus a full budget skips row writes but retains the
cost of text already produced and all capacity checks. Tests also retain
existing and oversized output, duplicate text, and the conditional size bound.
The exact equation is `C+6+2R` for supplied text cost `C` and `R` retained rows.
A generic equality-failure test checks that the caller includes variable
discovery, assignment text, and condition text at budget zero. Its current
counter is 159, or 161 with room for one row. These counts include the suggestion
line and final atom scan.

Failure-minimization tests cover the value-specification and cost theorems,
constructor selection, nested negation, empty domains, witness search, and
successful context. At two bindings, a leaf costs two operations. A conjunction
that fails on the left costs 25. A true left side followed by a false right
side costs 72, including successful-trace collection.

Array-join tests distinguish the two operands. The shared append operation
costs three times the right array's size, including when the left array has
100,000 entries. Two disjunction tests swap a leaf failure and an implication
failure with one context trace. Their costs are 150 and 147: only the first
copies the right-hand context trace. A nested implication costs 168 and retains
the successful antecedents in order.

Condition-layout tests preserve row order, duplicates, nested connectives, and
all label categories. With three bindings, a two-equality conjunction costs 95
operations to lay out and 118 to produce the labeled condition. A negated
equality in the first row stops label selection sooner than one in the second
row: sixteen operations instead of twenty. An embedded newline in a binder
name selects multiline punctuation even without row expansion. A thousand
nested conjunctions expand into 1,001 rows at cost 5,004. Their complete
condition line costs 33,037 with an empty environment. Input construction is
outside these counts. General proofs check text equality and the monotone
bound `F(20E+56)+11` for `F` formula nodes and `E` bindings.

Variable-discovery tests preserve outer-variable priority, preorder of binders,
first recognized environment occurrence, and unknown-name omission. They include
repeated names with different kinds and modal witness variables. A two-candidate
lookup costs eleven for a first-position match and sixteen for a last-position
match or a missing name. A two-variable discovery costs 43. Scanning 100,000
unknown entries costs 400,002. Scanning 100,000 copies of one recognized name
costs 700,008 and skips repeated kind lookups. Input construction is outside
these counts. General proofs cover specification equality, output size, the
three-parameter bound, and its monotonicity.

Atom-suggestion tests cover each atom form and both requested truth values.
With three environment entries, a five-name suggestion costs 102 operations.
Instantiation and specialization each cost 63. Type and individual suggestions
each cost 23. Text tests retain infix notation, missing-name fallbacks, and the
last binding for repeated names. General theorem applications cover text
equality and the bound `20E+42`, where `E` counts environment entries.

Syntactic atom-scan tests retain order and duplicates through negation and
quantifiers. An eleven-node formula with three atoms costs fifteen operations,
including output initialization. An equality formula produces no atom and
costs two. A nonempty accumulator keeps its entries and adds the new atoms.
General theorem applications check specification equality and the `2F+1`
bound for `F` formula nodes. The exact-count theorem separates node visits
from output writes, including for a nonempty initial accumulator.

Source-fact scan tests cover empty input, all-discarded input, retained
duplicates, and mixed facts in source order. The 100,000-fact no-match scan
costs 400,001 with a one-operation callback. Scope tests include `everywhere`,
matching and different world names, and the out-of-range `#n` fallback.
Taxonomy tests distinguish eager ancestor construction from the short-circuit
membership scan: Mode implies itself in 72 operations, while a final match or
an absent target costs 88. General tests apply the value and cost theorems to
arbitrary source and target fields and arbitrary evidence callbacks.

Fact-rendering tests cover primitive and derived arities, both infix forms,
named and universal scopes, and projection-index text. Value theorems preserve
the declarative formats for all facts. The largest fixed format costs 15.
Unary-evidence tests cover each early exit, exact and taxonomy matches,
duplicate rows, and empty input. One exact Mode match costs 99; evidence that
Mode implies Moment costs 110. A 100,000-fact name-mismatch scan costs 700,005.
The general bound is `5 + 270N` for `N` source facts.

Atom-evidence tests cover all eight atom constructors. With five environment
bindings, the fixtures cost 99 for instantiation, 74 for a derived unary fact,
103 for a derived binary fact, 131 for a primitive ternary fact, and 161 for a
derived quaternary fact. Type evidence costs 74 and accepts only instantiation
targets. A Mode fact costs 142 including variable lookup. Individual-semantic
atoms return no source evidence at cost two. Wrong-field, wrong-arity, and
primitive-versus-derived tests check that selection does not cross those
boundaries. A mixed scan preserves two duplicate instantiations and costs 132.
General theorem tests cover value equality, the bound `20E + 23 + 270N`, and
its monotonicity in environment size `E` and source-fact count `N`.

Failing-atom report tests include the source scan, header, and retained rows.
One instantiation header and its evidence row cost 201 operations. A header-only
budget costs 196. A second atom after a full report adds only the three-operation
stop test. Duplicate source rows remain in order. With 100,000 atoms, an already
full report costs three, while a complete scan of individual-semantic atoms
costs 1,000,000 and emits nothing. General proofs check output limits and the
bound `K(40E+76+275N)`, where `K` is the atom count.

Context-atom tests distinguish source priority from the generated-model fallback.
One source row costs 109. Without source rows, a true model check and its
fallback text cost 244, while a false check costs 158 and emits nothing.
Context-formula tests include header and atom collection: a source-backed
report costs 209, and a generated-model report costs 344. A negated absent
atom produces the formula fallback at cost 268. An equality with no atoms costs
69. These fallbacks reuse the header label. A zero budget still costs 99 for
the binary-atom formula, and a header-only budget costs 101. General proofs
check specification equality, output size, and the monotone bound
`F(Q+60E+115+275N)+15`, where `F` counts formula nodes and `Q` bounds atom
evaluation.

Context-trace tests check the bounds on each stored formula and environment.
Nested successful witnesses retain environments of sizes one and two in order.
A failed implication retains a six-binding successful context beside its
two-binding failed assignment. Report tests include the formula cost and the
indexed trace visit: one equality report costs 35, a header-only report costs
33, and a second trace after a full report adds three. An already full report
with 100,000 traces costs three and retains the existing output. General proofs
check output size and the context bound under explicit per-trace size premises.

Successful-trace tests check specification equality for arbitrary initial
arrays and the structural cost bound. An empty-environment equality costs
nine, including the trace-array initialization. A false equality with two
bindings costs 23 and emits no trace.
Conjunction, both disjunction branches, implication, and empty and nonempty
witness domains have exact-count tests. Evaluator and atom-constructor tests
contribute only on visited paths. The minimizer tests also cover its constructor,
branch, initialization, and array-copy costs.

`LeanUfo/Test/Complexity/DerivedAssertions.lean` covers the separate
pre-certification path. Name-search tests prove first-match correspondence and
the `9T` bound. Exact cases include missing and duplicate names, case
sensitivity, qualified names, and an immediate match in 100,000 entries.
Behavior tests cover primitive-only inputs, unknown references and predicates,
source-fact priority, world-scope priority, and an empty world domain.

`LeanUfo/Test/Complexity/DerivedReportComposition.lean` covers the complete
report boundary. Exact counts check eager argument resolution, all 25 fields
in both report dispatchers, unsupported fields, fallback construction, and
the common preamble. Budget tests retain zero through six rows and verify that
larger caps do not change a complete report. They charge construction even at
budget zero. The file is imported by the regular test driver.

The same file tests the six counted quality predicates. Unique-search cases
cover zero, one, and multiple matches, including immediate termination in a
100,000-entry domain. Relation tests cover duplicate facts and isolation of
the quality-kind/instance fields from the quality-type/association fields.
Simple and complex quality tests exercise first and last inherence witnesses
and skip inherence when the quality check fails. Quality-type tests skip the
condition on non-instances and stop at the first failing instance. General
tests retain the correspondence assumptions and all three monotone bounds:
`34T + 2`, `55T + 4`, and `T(55T + 27) + 14`.

Set and classification tests cover empty sets, strict inclusion, failed
inclusion, specialization in both directions, and field isolation. Exact
categorization counts include typehood established in a different world.
Disjointness tests retain both conjunction branches when first-type typehood
fails. Coverage tests verify that a first-cover match skips the second query,
and partition tests verify that failed coverage skips disjointness. General
tests retain the finite-coordinate and representation-agreement premises.

Bearer tests cover missing matrices and cells, explicit row width, paths,
cycles, and skipped closure reads for a moment bearer. Named-dispatch tests
check all arities, unknown names, unsupported predicates, field selection,
and exact costs for selected predicates. General proofs test correspondence
with the cost-free decision specification, the composed dispatch bound, and
its monotonicity in worlds, things, and stored derived propositions.

Derived-precheck traversal tests cover empty source/world arrays, missing
resolved entries, non-derived pairs, both failure kinds, and successful
assignments. Exact counts cover first and last failing worlds and a successful
scan. A first failure in 100,000 source entries costs 19 operations: only the
first entry and the next stop test execute. General proofs check ordered
selection, the composed bound, and monotonicity in all four size parameters.

Quality-report collector tests retain zero, one, or multiple matches in
declaration order. Duplicate facts produce one index, and classification/relation
fields remain isolated. The exact costs are 1 for an empty domain, 35 for two
failed classifications, 53 for one match, and 71 for two matches. General
proofs check sparse correspondence, the `1 + 35T` bound, and output size at most `T`.

Quality-type failure-search tests cover empty domains, non-instances, first
and last failures, passing instances, and duplicate facts. A two-operation
condition gives exact counts of 28 for an immediate violation, 47 for a last
violation after a non-instance, and 50 for two visited instances. Two
non-instances cost 44 and skip even a condition with cost 100,000. General
proofs check sparse correspondence and the monotone bounds `T(P + 23)` and
`T(55T + 27)`. Public report tests check that both the required-missing row
and the evidence row name the first invalid instance for both quality forms.
Existing Boolean quality-type tests retain their exact counts.

Dependence-report tests cover empty domains, ineligible sources, first and
last failures, first and last target witnesses, and relation direction.
A self-witness fails the functional search but can satisfy the constitutional
search. Public report tests retain the first source when both sources fail.
General proofs test sparse correspondence with explicit premises and the
monotone bounds `T(39T + 41)` and `T(37T + 23)`.

Suggestion tests cover all 25 supported literals and unknown fields in each
arity. Exact counts follow the number of visited field tests. General proofs
check agreement with the text specification and the constant bound of 23.

Complete quality-row tests check the no-kind, unique-kind, and competing-kind
messages, duplicate-fact behavior, and out-of-range name spelling. Exact costs
are 13 for the empty domain and 47, 77, and 105 for the two-thing fixtures.
General proofs check message equality, exactly one output row, and the monotone
`44T + 25` bound. Generic required-missing text tests cost 12 for a unary fact
and 18 for a quaternary fact. Reconstruction-failure reports cost 11, 13, 15,
and 17 across the four arities and always emit two rows. A public precheck
fixture retains the full reconstruction-failure report.

External-mode required-missing tests cover false classification, absent
candidates, directed inherence, declared-candidate priority, and missing names.
Candidate selection costs 3 for an empty domain and 85 for a two-thing scan
with no match. An immediate inherence match costs 67; a declared candidate
costs 53 in the one-assertion fixture. Complete explanation counts are 32 for
missing `Mode`, 110 for no candidate, and 166 or 134 for a failing inherence
or declared candidate. A missing classification skips 1,000 stored assertions
without increasing its count. A public precheck fixture preserves the complete
required-missing row. General proofs cover candidate correspondence, the
explanation bound, and monotonicity in worlds, things, and stored assertions.

`QuaIndividual` report tests cover no targets, one target, multiple targets,
duplicate facts, reversed edges, unrelated fields, and repeated displayed names.
Collector counts are 1 for an empty domain and 43, 44, or 45 for two things
with zero, one, or two targets. Complete evidence counts are 15 for the empty
domain and 57, 68, or 78 for the two-thing cases. The required-missing text
costs 14, including with `#n` name fallbacks. General proofs check sparse
correspondence, distinct ordered indices, size, and the monotone `31T+18` bound.
Public precheck tests preserve the required-missing and evidence rows.

Complete `Quality` and `QualityStructure` report tests cover absent, unique,
and competing candidates, empty domains, missing names, and repeated names.
For two things, `Quality` evidence costs 59, 89, and 117 across its three cases.
`QualityStructure` evidence costs 57, 77, and 107. Required-missing text costs
52 or 105 for `Quality`, and 46 or 99 for `QualityStructure`, with absent or
competing candidates. General proofs preserve the evidence text and two-row
size and check all four monotone bounds. Public precheck tests retain the
required-missing and evidence rows for competing candidates.

`NonEmptySet` report tests cover absent, first, and last members, duplicate
facts, reversed edges, unrelated fields, and missing names. Two-thing evidence
costs 62 with no member, 50 with the first member, and 68 with the last member.
An empty-domain report costs 20. Required-missing text always costs 14.
`ProperSub` evidence tests cover all four forward/reverse Boolean combinations
at cost 67, including the reverse-only case that requires both queries.
Self-edges, duplicates, and out-of-range names have separate regressions.
General proofs check component bounds and row counts. Public precheck tests
retain the missing-condition text and the displayed relation values.

Subset report tests cover first/last counterexamples, declaration order,
duplicates, equal sets, reverse-only membership, unrelated fields, and empty
domains. With two things, the difference search costs 43 for the first
counterexample and 62 for the last. Both evidence components then cost 77 or
96. With no left member, `SubsetOf` returns empty evidence at cost 46 and
`ProperSubsetOf` returns its missing-strictness explanation at cost 72.
Value proofs preserve the Boolean-first proper-subset decision structure while
the executable components search only once. General bounds and public-report
regressions cover required-missing text as well as evidence.

Simple- and complex-quality report tests cover absent and competing quality
kinds, a valid quality with no inhering part, first/last parts, duplicates,
reversed edges, empty domains, and name fallbacks. Two-thing evidence costs
95 without quality and 187 with competing kinds, including the separate status
report. With a valid quality, evidence costs 108 without a part, 104 with the
first part, and 122 with the last. Extra inherence facts do not change the
failed-quality count. Required-missing tests check both explanations and the
simple-quality fallback. General proofs cover bounds and two-row size. Public
precheck regressions preserve the displayed witnesses and messages.

Quality-type report tests cover missing classification, no instances, first/last
invalid instances, duplicates, declaration order, valid instances, and empty
domains. In two-thing fixtures, missing classification costs 22 for required-missing
text and 33 for evidence. With a type but no instances, evidence costs 70.
When instances fail the quality condition, first/last evidence costs 149 and
168, including the third quality-status row. Separate cases fail the simple
or complex part condition while that extra row reports valid quality. Public
precheck regressions preserve all three rows. General proofs check quadratic
bounds, their monotonicity, and the three-row limit.

Ultimate-bearer report tests cover missing paths, direct paths, a two-hop path
in a cyclic graph, duplicate facts, reversed edges, field isolation, and empty
name arrays. Two-thing evidence costs 61 without a path and 75 with a direct
path. A moment bearer still costs 75 and retains the path row. A malformed
next-hop loop stops at its traversal limit. Required-missing text costs 35
for a non-moment and 29 for a moment. General proofs check the linear bound
and three-row size.

External-mode evidence tests cover missing classification, computed witnesses,
and declared candidates that fail the computed condition. The latter report
has five rows and costs 284 in the two-thing fixture. A missing classification
costs 43, even with 1,000 stored candidate strings that are not visited. A
three-world computed witness costs 688. Public precheck tests preserve the path
row and the declared-candidate note. General tests check the mode bound,
monotonicity in worlds, things, and stored assertions, and the five-row limit.

Modal report tests check required-missing text and evidence for external
dependence, existential dependence, and existential independence. A one-world
failed existence implication costs 64/69 for the two external-dependence
components and 55/58 for existential dependence. External-dependence reports
skip bearer searches on that path, even with extra inherence facts. Two-world
tests retain the first failing world regardless of fact order or duplicates.
A separate failed-bearer fixture checks the full three-row report at cost 199.

Independence evidence distinguishes neither, one, or both missing separation
witnesses. It costs 72 with no existence facts, 81 with one direction present,
and 98 when both things exist together in the one-world fixture. Two worlds
with both separation witnesses return the caller's fallback at cost 83, or the
no-reason evidence rows at cost 100. Empty domains and public precheck rows
have separate regressions. General tests check all six bounds and row sizes.

Type-relation report tests cover categorization, disjointness, coverage, and
partition. Required-missing text and evidence have separate exact counts and
literal-output tests. Three-thing disjointness evidence costs 84 with no shared
instance, 72 with the first, and 113 with the last. Coverage evidence costs
90 with no covered instances, 99 with the first failure, and 140 with the last.
A first-cover match saves seventeen operations against a second-cover match.

Partition regressions preserve coverage-first priority even when another
instance belongs to both parts. Categorization tests separate possible
typehood across worlds from specialization in the report's world. Duplicate
facts, declaration order, relation direction, field isolation, empty domains,
fallbacks, and public report rows have regressions. General theorem tests
check all eight bounds, their monotonicity, and the four two-row size results.

Witness-search tests cover empty domains at cost one and a one-coordinate
equality match at cost 19. A million-coordinate immediate match costs 22,
including the stop test before the unvisited suffix. Later-match and no-match
fixtures check ascending order. A repeated variable name preserves the
extended environment and uses its newest binding. General theorems prove
first-match correspondence, environment size, and the `N(E+6)+1` bound.

Formula-registry tests cover empty arrays, first and last matches, unknown
names, case sensitivity, and duplicate-name priority. An immediate match in
100,000 entries costs 11. The fixed registry has 107 entries. Its first lookup
costs 11, while its last lookup and unknown-name scan cost 856. Dispatcher tests
include these costs: an unsupported field costs 874 before the public output
cap, and 882 with one retained row. Axiom 1 over empty domains costs 45, or 41
with a zero evidence budget. Specialized dispatch tests verify that those
analyzers skip the generic registry entirely.

Failing-atom tests distinguish evaluation from evidence collection. They cover
successful atoms, failed atoms, skipped disjunction branches, failed
implications, negation, equivalence, and repeated evidence. Quantifier tests
cover empty domains and bindings that shadow an existing name. A full scan of
100,000 assignments to an equality body costs 500,002 operations and emits no
atoms. General theorem applications preserve the accumulator specification and
check the structural bound under an explicit atomic-cost premise.

Suggestion-selection tests cover no atoms, one atom, multiple atoms, and the
distinctness search's first-match behavior. The two-row distinctness fixtures
cost sixteen or twenty operations, depending on the matching row's position.
Model-dependent tests include negated atoms, conjunctions, implications, and
quantifiers. General proofs preserve all messages and connect suggestion and
discovery costs to the generic report bound. The environment monotonicity
proofs and rebuilt-disjunction bound are separate from exact execution counts.

## CI

GitHub Actions runs the default `lake test` profile on pull requests and pushes
to `dev` or `main`.

The full semantic witness profile runs when the workflow is started manually.
The nightly scheduled workflow checks `dev` and runs the full profile only when
`dev` has received a commit in the previous 24 hours.

## Full semantic witness tests

```bash
LEANUFO_FULL_TESTS=1 lake test
```

This runs the slower positive and negative certification fixtures.

Use this profile when only semantic fixtures changed. For a final gate after
compiler, checker, certificate, or performance-sensitive work, use the
performance profile below instead of running both profiles: the performance
profile already includes the full semantic suite.

## Incremental certificate tests

The incremental certificate fixtures live under:

```text
LeanUfo/Test/Certification/Positive/
  ModelExtension.lean       -- same-module extends, reuse, certify_fresh
  ModelExtensionBase.lean   -- exported parent for cross-module extension
  ModelExtensionChild.lean  -- imported-parent extension and reuse checks
```

They check that:

- `checked_axN` declarations are generated and usable as Lean proofs;
- exact-source aliases can reuse parent checker proofs;
- `certify_fresh` marks fields as fresh rather than reused;
- an extension that adds car-window mereology facts still certifies;
- affected mereology fields are checked freshly;
- unaffected fields can be reused through Lean-checked equality;
- cross-module parent lookup works after importing the parent module;
- certificate manifests render to JSON;
- the full test profile can export concrete manifests and validate one of them
  with a Lean proof recheck.
- inherited `given everywhere:` facts remain expanded over the parent's world
  set in extensions;
- extension syntax rejects attempts to add new worlds, preserving that
  `everywhere` scoping policy.
- a certifying base model can still have a failing extension when the child
  additions violate an axiom; `ExtensionInvalidAddition.lean` checks this with
  an inherited object that the child also classifies as a perdurant.
- `ExtensionInvalidConstitutionAddition.lean` checks the later-failure shape:
  a certifying base model, reused/fresh checks completed for the child, and a
  subsequent failure at constitution axiom `ax61`.

Run just this positive seed with:

```bash
lake build LeanUfo.Test.Certification.Positive.Seed
```

The user-facing concrete reuse workflows live in:

```text
LeanUfo/UFO/DSL/ConcreteExamples/ReuseModelExtension.lean -- car/window/body mereology
LeanUfo/UFO/DSL/ConcreteExamples/ReuseRoleExtension.lean  -- person plus employment role
LeanUfo/UFO/DSL/ConcreteExamples/ReuseModeExtension.lean  -- person plus inhering enrollment mode
```

The car/window workflow is also used by the export/recheck examples:

```bash
lake build LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
lake exe export-certificates --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension --out certificates/
lake exe validate-certificate certificates/CarWithWindow.certificate.json --module LeanUfo.UFO.DSL.ConcreteExamples.ReuseModelExtension
```

`LeanUfo/Test/Certificates/ManifestValidation.lean` checks complete manifests
and rejects missing, malformed, duplicate, and altered certificate rows.
It alters both theorem-name columns in every row, checks status/reuse-source
consistency, rejects non-hexadecimal digests, and requires unique rows in the
rebuilt manifest as well as the exported JSON.
`LeanUfo/Test/Certificates/InputSafety.lean` tests identifier parsing in the fast
profile. The full profile also injects commands into final and per-field
theorem names and checks that validation rejects them without creating a marker
file. Direct digest-helper tests cover callers that bypass the CLI wrapper.
The ordinary export and proof-recheck cases remain the successful controls.
`ExportDiscoveryMarked.lean` checks namespaced marked selection, comments, and
import ownership. `ExportDiscoveryFallback.lean` checks the no-marker rule: all
and only manifests owned by that module are exported.
`NamespacedParent.lean` certifies an extension whose nearer parent is imported.
A different cached root parent must not change that namespace resolution.

Release automation uses the same commands after setting the manifest artifact
version in the runner workspace with:

```bash
scripts/set-artifact-version.sh vX.Y.Z
```

## Selected axiom tests

```bash
LEANUFO_AXIOMS=ax13 lake test
LEANUFO_AXIOMS=ax10,ax18,ax61 lake test
LEANUFO_AXIOMS=ax66 lake test
LEANUFO_AXIOMS=ax1,ax2,ax3,ax4,ax5,ax6,ax7,ax8,ax9,ax10,ax11,ax12,ax13,ax14,ax15,ax16,ax17,ax61,ax71,ax77 lake test
LEANUFO_AXIOMS=ax18,ax19,ax20,ax21,ax22,ax23,ax24,ax25,ax26,ax27,ax28,ax29,ax30,ax31,ax32,ax33,ax_instEndurant,ax_sub_kind_sortal,ax_nonSortal_up,ax_kindStable lake test
LEANUFO_AXIOMS=ax34,ax35,ax36,ax37,ax38,ax39,ax40,ax41,ax42,ax43 lake test
LEANUFO_AXIOMS=ax44,ax45,ax46 lake test
LEANUFO_AXIOMS=ax47,ax48,ax49,ax50,ax51,ax52 lake test
LEANUFO_AXIOMS=ax53,ax54,ax55 lake test
LEANUFO_AXIOMS=ax56,ax57,ax58,ax59,ax60,ax61 lake test
LEANUFO_AXIOMS=ax62,ax63,ax64 lake test
LEANUFO_AXIOMS=ax65,ax66,ax67,ax68 lake test
LEANUFO_AXIOMS=ax69,ax70,ax71,ax72,ax73,ax74,ax75,ax76,ax77,ax78,ax79,ax80,axQuaIndividualOfEndurant lake test
LEANUFO_AXIOMS=ax81,ax82 lake test
LEANUFO_AXIOMS=ax83,ax84,ax85,ax86,ax87,ax88,ax89,ax91,ax92,ax93,ax94,ax100,ax101,axDistanceIdentity,axDistanceSymmetry,axDistanceTriangle lake test
LEANUFO_AXIOMS=ax102,ax103,ax104,ax105,ax106,ax107,ax108 lake test
```

The default imports also include `Certificates/DerivedReduction.lean`. It
reuses `FlowerPropertyChange` to check finite derived-assertion reduction at
the example's existing limits. Its axiom audit rejects native proof axioms in
`assertedDerivedFacts`; the separate registered-axiom certificates retain their
documented native trust boundary.

Use the performance profile after compiler, checker, table-representation, or
certificate-tactic changes:

```bash
LEANUFO_PERFORMANCE_TESTS=1 lake test
```

This profile runs the full suite and builds every user-facing example through
`LeanUfo.UFO.DSL.Examples`. That aggregate includes the `Company`,
`WoodenTable`, `FlowerPropertyChange`, and `RedirectedWalk` examples that guard
against certificate-elaboration regressions. It also includes `RelatorProbe`,
the main certificate-performance stress example. The profile builds
`LeanUfo.Test.Certification.Positive.Relator` to check the model's semantic
properties directly. Use clean, otherwise equivalent build directories for
wall-clock comparisons. Incremental runs verify wiring but are not comparable
benchmarks.

For such changes, this is the most complete final command. Do not
precede it with separate default and full-profile runs unless diagnosing a
failure; those checks are already included and would only repeat work.

Selecting axioms runs the relevant semantic witness profile for those fields.
Use this when changing one axiom extractor, one fixture, or one diagnostic path.
The long selections above exercise grouped regions of the reflective checker.

The selected `ax73` profile builds
`LeanUfo.Test.Certification.Positive.Relator`. This fixture certifies a
three-world model with a relator, two qua-individual proper parts, distinct
bearers, a shared foundation, and two mediation facts. It also proves that the
compiled signature satisfies active part-based (a73) and refutes historical
`ax_a73_printed`.

`ax68` is included in the §3.9 checker-backed selection. It uses the bounded
finite closure checker for `MomentOf` and `UltimateBearerOf`.

After checker changes, the `ax68` positive test exercises the Warshall-style
finite closure bridge from executable
reachability to the core inductive `MomentOf` relation. The direct negative
fixture uses the same checker-aware counterexample pattern as the other
direct-complete checker fields: prove `¬ axN` from `checkAxN_complete` and a
computed `checkAxN = false`.

## Direct negative witness audit

```bash
LEANUFO_REQUIRE_DIRECT_WITNESSES=1 lake test
```

This is a strict backfill audit: it fails if any registered axiom lacks a direct
negative witness, including axioms that are currently classified as
compiler-enforced or blocked in the manifest. The ordinary `lake test` profile
checks that every registered axiom is classified exactly once.

## Coverage manifest

The manifest lives in:

```text
LeanUfo/Test/Coverage/AxiomManifest.lean
```

Each registered axiom is classified for negative coverage as one of:

- `directNegativeWitnessAxioms`: a small fixture exists and Lean confirms the
  first semantic failure is this axiom;
- `compilerEnforcedNegativeAxioms`: direct falsification is not expected because
  compiler semantics enforces the condition;
- `blockedNegativeWitnessAxioms`: the axiom needs missing surface syntax,
  extractor support, or a better negation-proof path.

## Negative fixture rule

A negative fixture only counts as direct coverage if:

- the first stopped certificate field is the intended axiom;
- Lean confirms a finite semantic counterexample;
- the fixture is small and section-local where feasible.

The test runner enforces the first-failure rule by scanning generated
certificate/checker failure messages.  A fixture fails the audit if its output
mentions another generated field, even when the expected `certified_axN` text is
also present.  This catches over-specified fixtures that happen to expose an
earlier axiom after the checker or proof backend becomes more precise.

Timeout-style counterexample-probe limits and unclassified probe failures do
not count as direct negative coverage.

[Docs home](README.md) · [Project README](../README.md)
