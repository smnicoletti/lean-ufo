# Diagnostics Guide

[Docs home](../README.md) · [Project README](../../README.md)

The DSL frontend saves a VS Code diagnostics widget for each
`ufo_model ... certify` command. It also emits terminal errors for failed
commands.

## What The Widget Shows

- model name;
- declared worlds and things with generated finite indices;
- user-written input facts;
- expanded finite facts after taxonomy and scope expansion;
- certificate status for each registered axiom;
- failure analysis for derived assertion failures and certificate failures.

Certificate fields are reported as:

- `success`: this generated theorem checked;
- `failed`: this is the first field that did not certify;
- `unchecked`: certification stopped before this field.

## Counterexample Confirmation

When a generated certificate fails, the frontend runs a separate negative probe.

If Lean proves the negation of the axiom for the generated finite model, the
diagnostic says:

```text
A finite counterexample was confirmed for axN.
```

If the negation probe also fails, the diagnostic says that no counterexample
proof was found.

## Paired Example

The following model makes `EnrollmentClassifier` a rigid sortal object type but
does not classify it as a `Kind` or `SubKind`:

```lean
ufo_model FailedEnrollmentClassifier : UFO where
  worlds actual
  things PersonKind EnrollmentClassifier Alice
  given actual:
    ObjectKind(PersonKind)
    ObjectType(EnrollmentClassifier)
    Rigid(EnrollmentClassifier)
    Sortal(EnrollmentClassifier)
    EnrollmentClassifier ⊑ PersonKind
    Object(Alice)
    Alice :: EnrollmentClassifier
    Alice :: PersonKind
  derive_relations
  certify
```

Certification stops at `ax26` and presents the counterexample as follows:

![Diagnostic card showing the ax26 counterexample for EnrollmentClassifier](../assets/diagnostic-card.svg)

## Condition Headings

Counterexample boxes use headings that describe the shape of the failed
obligation:

- `Required but missing`: one missing DSL-level fact is required.
- `Need one of`: at least one listed alternative must hold.
- `Required together`: all listed facts/conditions must hold together.
- `Missing witness requirements`: an existential/witness obligation is missing.
- `Forbidden condition`: a fact or combination holds but should be absent.

The card above shows a `Need one of` obligation: at least one listed
alternative is missing.

For a witness obligation:

```text
Counterexample 1    k = Person, x = Alice, w = actual.

FAILED CONDITION
Missing witness requirements:
  - [actual] Kind(AlternateKind)
  - [actual] Alice :: AlternateKind
  - not (AlternateKind = Person)
```

the user needs a witness satisfying all listed requirements.

## Suggestions And Evidence

Suggestions use layout-neutral wording such as "this counterexample", so the
same text works in the VS Code widget and terminal output.

Evidence lines show the finite DSL facts that made the obligation apply.

## Current Caveat: ax68

`ax68` has a custom ultimate-bearer proof shape. The diagnostics closure checker
can detect finite table situations where a moment lacks a reachable non-moment
ultimate bearer. The current negation probe does not yet always prove the full
ax68 negation. Ax68 therefore has direct positive coverage and remains blocked
for managed direct negative coverage.

[Docs home](../README.md) · [Project README](../../README.md)
