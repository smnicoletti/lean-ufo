import LeanUfo.UFO.DSL.Syntax

/-
Negative diagnostic example: an anti-rigid phase is also asserted as rigid.

This is a small variation of `FlowerPropertyChange.lean`.  The passing example
uses `RedFlower` and `BrownFlower` only as phases.  Here `RedFlower` is also
declared as an `ObjectKind`, which makes it both phase-like and kind-like.

The model is intentionally not certifiable.  Open this file in VS Code to see
the UFO diagnostics widget stop at `certified_ax18`.
-/

open LeanUfo.UFO.DSL

ufo_model FailedFlowerTaxonomyExample : UFO where
  worlds summer autumn
  things Flower RedFlower BrownFlower Rose1

  given everywhere:
    ObjectKind(Flower)
    ObjectKind(RedFlower)
    ObjectType(RedFlower)
    RedFlower ⊑ Flower

    Phase(BrownFlower)
    ObjectType(BrownFlower)
    BrownFlower ⊑ Flower

    Object(Rose1)
    Rose1 :: Flower

  given summer:
    Rose1 :: RedFlower

  given autumn:
    Rose1 :: BrownFlower

  derive_relations
  certify
