# Diagnostics Internals

[Docs home](../README.md) · [Project README](../../README.md)

Diagnostics explain failed generated certificates. They are not the trusted
proof path: Lean checks generated theorem declarations first, and diagnostics
then reconstruct source-level evidence from the compiled finite tables.

The only diagnostic branch that establishes a semantic model failure is the
confirmed-counterexample branch, where Lean checks a generated proof of the
failed field's negation. A failed negative probe is classified as a timeout-style
proof-search limit only when Lean reports heartbeat/timeout wording; otherwise
it remains an unclassified generated-proof/search failure.

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

Specialized analyzers are used when the generic formula mirror loses important
structure, for example ultimate-bearer closure, foundation equality, relator
foundation, and quality-domain product witnesses.

## Formula Mirrors

`Diagnostic/Analysis.lean` defines a small first-order formula language over
finite things and worlds. These formulas mirror selected axiom shapes closely
enough to find a concrete counterexample assignment and render it in DSL
vocabulary.

Do not treat these formulas as replacements for the core axioms. If a diagnostic
mirror is wrong, the certificate result is still authoritative; only the
explanation is affected.

## Failure Minimization

`minimizeFailure` walks a failed formula to find the smallest useful failed
subformula. It keeps successful context when that context explains why a failed
obligation applied, such as the antecedent of an implication or the left side of
a biconditional.

`successTraces` collects those successful context formulas so the widget can
show both the missing condition and the evidence that made it relevant.

## Evidence

Evidence is reconstructed from user-written facts and deterministic compiler
closures. It should answer practical modeling questions:

- which DSL facts made this obligation apply;
- which expected DSL fact is missing;
- whether the issue is a forbidden asserted fact or a missing witness;
- whether a broader `everywhere` assertion is involved.

When adding a diagnostic, prefer a clear source-level explanation over a
verbatim restatement of the Lean axiom.

[Docs home](../README.md) · [Project README](../../README.md)
