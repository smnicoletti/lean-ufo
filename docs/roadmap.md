# Roadmap And Limitations

[Docs home](README.md) · [Project README](../README.md)

This project is active research infrastructure. Current next steps:

## DSL Surface

- Add level-aware syntax for higher-order type patterns, especially for the
  concept-evolution examples where types can instantiate higher-order types.
- Add higher-level generation of §3.12 quality-domain facts around existing
  `product_family` witnesses.
- Consider custom accessibility relations beyond the current universal S5
  frame.

## Diagnostics

- Extend structured extractors for the remaining blocked axioms.
- Apply the ax68 checker-aware counterexample pattern to other hard axioms where
  direct simplification is not enough to confirm semantic failure.
- Keep suggestions tied to axiom shape: alternatives, missing witnesses,
  forbidden facts, and required conjunctions should remain visually distinct.

## Testing

- Continue replacing shared positive coverage with small direct positive
  fixtures where that improves clarity.
- Continue backfilling direct negative fixtures for each axiom where the DSL can
  express a genuine first-failure counterexample.
- Add lightweight documentation checks for stale syntax examples and broken
  local links.

## Formal Guarantees

- Strengthen the current pipeline theorems into more extensional statements
  where useful, for example exactness properties of taxonomy closure and
  reflexive specialization insertion.
- Consider replaying more of the frontend-produced `ModelAST` construction
  inside Lean declarations to tighten the audit trail.

[Docs home](README.md) · [Project README](../README.md)
