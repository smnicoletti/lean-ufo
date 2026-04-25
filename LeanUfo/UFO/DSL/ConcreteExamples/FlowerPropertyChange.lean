import LeanUfo.UFO.DSL.Syntax

/-
Paper example: minimal flower property-change witness

Section 4.3 first discusses a flower whose color changes from red to brown.
The paper treats color as a quality with values in a quality structure.  The
current Phase 1 DSL does not yet expose set-extension syntax for quality
structures, so this example records the same change pattern with two phases of
Flower: RedFlower and BrownFlower.

The important certified point is modal: the same rose remains a Flower while
contingently instantiating different anti-rigid phases in different worlds.
-/

open LeanUfo.UFO.DSL

ufo_model FlowerPropertyChangeExample : UFO where
  worlds summer autumn
  things Flower RedFlower BrownFlower Rose1

  given everywhere:
    Flower : ObjectKind

    RedFlower : Phase
    RedFlower : ObjectType
    RedFlower ⊑ Flower

    BrownFlower : Phase
    BrownFlower : ObjectType
    BrownFlower ⊑ Flower

    Rose1 : Object
    Rose1 :: Flower

    IsPartitionedInto(Flower, RedFlower, BrownFlower)

  given summer:
    Rose1 :: RedFlower

  given autumn:
    Rose1 :: BrownFlower

  derive_relations
  certify
