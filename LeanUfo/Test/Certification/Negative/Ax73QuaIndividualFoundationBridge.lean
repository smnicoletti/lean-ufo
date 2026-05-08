import LeanUfo.UFO.DSL.Syntax

/-!
Expected-failure ax73 fixture.

`Q` is explicitly a qua individual of `B`.  The first failure is the
foundation-based `QuaIndividualOf` definition; the diagnostic extractor records
that no simpler finite-table foundation mismatch was found.
-/

open LeanUfo.UFO.DSL

ufo_model FailedAx73QuaIndividualFoundationBridge : UFO where
  worlds actual
  things K Q B
  given actual:
    ObjectKind(K)
    Object(Q)
    Object(B)
    Q :: K
    B :: K
    QuaIndividualOf(Q, B)
  derive_relations
  certify
