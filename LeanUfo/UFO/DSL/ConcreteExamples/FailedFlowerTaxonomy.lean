import LeanUfo.UFO.DSL.Syntax

/-!
Negative diagnostic example: a rigid kind loses an instance.

RedFlower is declared as an ObjectKind, but Rose1 instantiates it only in
summer. This violates the rigidity required by axiom (a18). BrownFlower is a
phase, so its contingent instantiation is permitted.

The model must fail certification. Open this file in VS Code to see
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
