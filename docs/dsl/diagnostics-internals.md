# Diagnostics internals

[Docs home](../README.md) · [Project README](../../README.md)

## Overview

> [!IMPORTANT]
> **Bottom line.** Diagnostics reuse the compiled model, search in a fixed
> order, and cap their output. Their formulas select explanations. Generated
> Lean negation theorems establish semantic counterexamples.

A Lean proof of the failed axiom's negation confirms a semantic counterexample.
A failed proof attempt alone does not. Operation counts cover the selected
searches and report construction, following the compositional cost method
described in the [complexity guide](complexity.md#references), including Niu
and colleagues' cost-aware semantics. The bounds and output limits are
separate from the correctness of a generated counterexample theorem.

Diagnostics explain rejected derived claims and failed generated certificates.
They reconstruct source-level evidence from compiled finite tables. Their
explanations do not replace Lean's checks of generated theorem declarations.

The only diagnostic branch that establishes a semantic model failure is the
confirmed-counterexample branch, where Lean checks a generated negation theorem
for the failed field. A failed negative probe is classified as a
timeout-style counterexample-probe limit only when Lean reports
heartbeat/timeout wording; otherwise it remains an unclassified probe failure.

| Component | Job | Guarantee |
| --- | --- | --- |
| Formula mirror | Find a failed assignment | Deterministic value correspondence |
| Specialized analyzer | Recover axiom-specific evidence | Sound evidence for its supported relation |
| Minimizer | Retain the failed part and useful context | Deterministic selection with no global-minimum claim |
| Renderer | Produce bounded rows and text | Counted, output-sensitive construction |
| Negation probe | Ask Lean to prove the failed axiom false | Semantic confirmation when Lean accepts it |

## Flow

```text
failed certificate field
  -> optional specialized analyzer
  -> diagnosticFormula? mirror
  -> finite-table evaluation
  -> minimizeFailure
  -> evidence and suggestion rendering
  -> Diagnostic/Widget JSON props
```

The generic formula mirror cannot retain every axiom-specific relation. Separate
analyzers therefore handle ultimate-bearer closure, foundation equality,
relator foundation, and quality-domain product witnesses.

## Formula mirrors

`Diagnostic/AxiomAnalysis.lean` defines a small first-order formula language over
finite things and worlds. These formulas mirror selected axiom shapes closely
enough to find a concrete counterexample assignment and render it in DSL
vocabulary.

The core axioms determine certification. An incorrect formula mirror can damage
the explanation, but it cannot change the certificate result.

## Failure minimization

The remaining sections describe `Diagnostic/AxiomAnalysis.lean`.
`Diagnostic/Analysis.lean` integrates the analyzers and selects the report after
a proof probe. Its production selector erases `certificationFailureReportCosted`.
The selector preserves the confirmed/unconfirmed distinction, scans timeout
messages once, and charges the selected analyzer and surrounding rows.
`Complexity/Frontend.lean` proves output equivalence and the composed bound.

`minimizeFailure` returns the value of `minimizeFailureCosted`. It selects a
failed subformula and keeps successful context that explains why the obligation
applied. An implication retains its successful antecedent. A disjunction
retains both failures and joins their assignments in left-to-right order.
The value theorem proves equality with `minimizeFailureSpec`. This guarantees
deterministic selection. Global minimality is outside its guarantee.

The count includes formula and branch tests, empty context initialization,
child computations, and array joins. A join traverses its right operand, so
prepending successful traces charges the existing failure context. The
[complexity guide](complexity.md#failure-minimization) states the bound and
the primitive-call model's exclusions.

`successTracesCosted` collects those successful context formulas and their
assignments in evaluation order. The widget uses them to show the evidence
that made a missing condition relevant. Its value theorem preserves the
separate `successTracesSpec` specification. Its cost includes child evaluation,
witness search, branch tests, and trace-array writes. The
[complexity guide](complexity.md) states the remaining cost-model gaps.

## Evidence

Evidence is reconstructed from user-written facts and deterministic compiler
closures. Each explanation should answer:

- which DSL facts made this obligation apply;
- which expected DSL fact is missing;
- whether the issue is a forbidden asserted fact or a missing witness;
- whether a broader `everywhere` assertion is involved.

When adding a diagnostic, prefer a clear source-level explanation over a
verbatim restatement of the Lean axiom.

## Derived-assertion prechecks

`Diagnostic/DerivedAssertions.lean` handles explicit derived claims before
axiom certification. For example, a `Quality` claim requires exactly one
instantiated `QualityKind`. The precheck searches facts in source order and
each fact's resolved worlds in scope order. It returns the first failure
report, or no report when it finds no failure.

After a precheck succeeds, Lean must still accept the generated
derived-assertion theorem and the axiom certificates. A failed
precheck supplies explanatory rows to the widget and stops certificate
generation for that model.

Name lookup uses a counted first-match search with a proved linear bound.
The six quality predicates also use counted execution. The unique-witness
search stops at the second match. Simple and complex quality checks then
search for an inhering thing, and their type checks examine each instance.
Their value proofs require valid coordinates and agreement between the sparse
and dense tables. The [complexity guide](complexity.md#derived-assertion-prechecks)
gives the bounds and derivations.

Set inclusion, strict inclusion, specialization, categorization, disjointness,
coverage, and partition checks also use counted definitions. Their report
builders reuse the same first-member, first-difference, shared-instance, and
uncovered-instance searches. The searches visit things in declaration order
and stop at the first witness. Typehood additionally searches all worlds.

The named-predicate dispatcher and `UltimateBearerOf` also use counted
execution. The dispatcher proves its result against a cost-free specification
and includes name searches, field tests, and the selected predicate's work in
its bound. The closure lookup uses the explicit diagnostic matrix width.

The counted traversal retains the first failed assignment for report
construction. Named and resolved entries pair by source index. Missing or
non-derived pairs skip evaluation. The value theorem preserves source order,
ascending world order for `everywhere`, and the single world of an `at` scope.
Its bound grows with source facts, worlds, things, and stored derived
propositions. Its report has a separate composed bound, described below;
the axiom-report theorem is not used as a bound for this path.

Quality reports use one counted collector for quality-kind instantiations and
quality-type associations. It retains every matching target in declaration
order, unlike the uniqueness check that stops after its second match. Its
linear cost and storage bounds cover collecting indices. Shared counted name
renderers preserve index order and the `#n` fallback. The complete required-missing
text and two-row evidence for `Quality` and `QualityStructure` include these
costs. Both evidence arrays put the assertion before the computed status.
The component bounds exclude outer dispatch, source-name resolution, the
common preamble, and output budgeting.

`NonEmptySet` reports use the first incoming membership edge in declaration
order. Their component bounds include both evidence rows and required-missing
text. `ProperSub` evidence reads both directed relations because it displays
both values, even when the first is false. Its Boolean checker can stop after
a false forward query. The report therefore has its own bound. These component
results exclude the shared report work covered by the complete producer bound.

Each subset report component retains the first left-only membership witness
from one counted search. The proper-subset components use that witness
directly, since their Boolean subset check would run the same search. Value
proofs preserve both the witness explanation and the missing-strictness case.
`SubsetOf` evidence stays empty when no counterexample exists. Component
bounds include names and output construction, but exclude caller-supplied
fallback text and the common report work.

Simple- and complex-quality report components count the initial quality
check, the selected inherence search, and all names and rows. When quality
fails, the evidence also counts the separate quality-status collector and
copies its one-row explanation. A valid quality instead uses the first
incoming inherence witness. The component theorems preserve both paths and
their two-row output. The complete producer adds the shared report work.

Simple- and complex-quality-type reports use the same first-invalid-instance
search as their Boolean checks. A missing type classification skips the search,
and non-instances skip the condition. The search stops at the first violation
in declaration order. Required-missing text and evidence count the surrounding
names and row construction. A failing instance adds its quality-status row,
including that row's computation and copy. The result has at most three rows.
Value proofs require table agreement and valid coordinates. Cost and size
bounds hold for arbitrary inputs. The complete producer includes their costs.

Ultimate-bearer evidence counts both the bearer classification and path
reconstruction from moment to bearer. A moment classification does not skip
the path because the report displays both. The three-row size and linear
cost bounds also hold for malformed next-hop tables. Path validity for the
compiled model is proved separately in `Complexity/Diagnostics/Paths.lean`,
including soundness and reconstruction completeness. External-mode evidence
counts its two introductory rows, the complete mode-status report, and the
copy of up to three status rows. Their component bounds exclude shared report
work, which is included in the complete producer bound.

External-dependence reports count the complete reason and its surrounding
text and rows. A world where the source exists without the target takes
precedence over bearer failures. Existential-dependence reports retain the
first failing world. Existential-independence reports run both directional
searches to distinguish which separation witness is missing. Their counted
required-missing and evidence builders preserve the messages and fallbacks.
These component bounds exclude outer dispatch, fallback construction, and
the common preamble.

The four type-relation report families also have counted required-missing
text and two-row evidence. `Categorizes` first searches all worlds for an
instance of the category, then checks current instances for failed `ProperSub`:
forward specialization must hold and reverse specialization must fail.
Disjointness selects the first shared instance. Coverage selects the
first instance outside both covering types. Partition selects a coverage
failure before searching for overlapping parts. Value proofs preserve these
orders and the messages, including fallbacks when no witness is isolated.
Their bounds include names and row construction but exclude outer dispatch,
caller-supplied fallback construction, and the common report work.

Functional- and constitutional-dependence reports use counted searches that
retain the first failing source instance. An ineligible source skips the
target search. A target witness ends the inner search. The functional search
requires a distinct target, whereas the constitutional search checks the
directed `ConstitutedBy(source, target)` relation without a distinctness test.
The searches and all five field-specific report families have quadratic bounds
in the number of things. Individual functional dependence checks generic
dependence before instantiation; constitution checks instantiation first.
Component reports check proper parthood first. If a Boolean dependence check
fails, evidence runs a separate witness search and charges both executions.
The required-missing text and two-row evidence include name rendering and
output construction. Value proofs preserve the original messages and check
order. See the [report bounds](complexity.md) for the explicit formulas.

Suggestion selection also has counted execution. Its value proof preserves
the fixed advice text, and its bound includes the arity test and visited field
comparisons. It does not render names or construct the report's surrounding text.

The complete quality-status row has a counted renderer. It collects candidate
kinds, renders names, constructs text, and emits exactly one row. The generic
required-missing fallback and the two-row reconstruction-failure report also
have counted construction. Their value proofs preserve the existing messages,
including `#n` for an out-of-range world coordinate. The outer report counts
name resolution, dispatch, common text, and the final output cap. Its bound
composes these operations with the field-specific builders. All requested name
lookups run before the report tests their results; a missing first argument
does not skip the later lookups. The required-missing fallback is also charged
before field selection.

The default precheck cap is nine rows, enough for every current report by a
size theorem. Smaller budgets retain a deterministic prefix after construction.
Budget zero therefore still pays for finding and explaining the failure.
`derivedAssertionFailure?` erases its counted producer. The editor retains
that result during semantic proof elaboration. If the proof fails, it uses
`derivedAssertionFailureReportCosted` to select the report without scanning
the facts again. Selection costs one operation for a retained report or four
for the one-row fallback when no false assertion was found. The
[complexity guide](complexity.md) gives the
complete bounds and their representation assumptions.

The external-mode required-missing explanation also has complete counting
after source-name resolution. It checks the mode classification before any
candidate search. The first declared candidate takes priority over inherence
targets. With neither kind of candidate, this explanation reports absence
instead of selecting thing zero. Its value proof preserves that distinction
and the existing text. Its bound includes the selected failure reason, names,
and concatenations, but excludes dispatch and the caller's row construction.

`QuaIndividual` has counted required-missing text and a complete two-row evidence
renderer. Its target collector visits each thing once and keeps every matching
`QuaIndividualOf(source, target)` fact in declaration order. Duplicate facts do
not duplicate targets. The renderer preserves repeated displayed names for
distinct targets. Its bounds include names, concatenations, array initialization,
and row emission. Dispatch, source-name resolution, and output budgeting remain
separate obligations.

[Docs home](../README.md) · [Project README](../../README.md)
