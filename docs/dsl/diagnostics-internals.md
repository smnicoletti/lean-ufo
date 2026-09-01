# Diagnostics internals

[Docs home](../README.md) · [Project README](../../README.md)

Diagnostics explain failed generated certificates. They are not the trusted
proof path: Lean checks generated theorem declarations first, and diagnostics
then reconstruct source-level evidence from the compiled finite tables.

The only diagnostic branch that establishes a semantic model failure is the
confirmed-counterexample branch, where Lean checks a generated negation theorem
for the failed field. A failed negative probe is classified as a
timeout-style counterexample-probe limit only when Lean reports
heartbeat/timeout wording; otherwise it remains an unclassified probe failure.

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

`Diagnostic/Analysis.lean` defines a small first-order formula language over
finite things and worlds. These formulas mirror selected axiom shapes closely
enough to find a concrete counterexample assignment and render it in DSL
vocabulary.

These formulas do not replace the core axioms. An incorrect mirror can damage
the explanation, but it cannot change the certificate result.

## Failure minimization

`minimizeFailure` walks a failed formula to find the smallest useful failed
subformula. It keeps successful context when that context explains why a failed
obligation applied, such as the antecedent of an implication or the left side of
a biconditional.

`successTraces` collects those successful context formulas so the widget can
show both the missing condition and the evidence that made it relevant.

## Evidence

Evidence is reconstructed from user-written facts and deterministic compiler
closures. Each explanation should answer:

- which DSL facts made this obligation apply;
- which expected DSL fact is missing;
- whether the issue is a forbidden asserted fact or a missing witness;
- whether a broader `everywhere` assertion is involved.

When adding a diagnostic, prefer a clear source-level explanation over a
verbatim restatement of the Lean axiom.

[Docs home](../README.md) · [Project README](../../README.md)
