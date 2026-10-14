import LeanUfo.UFO.DSL.Syntax

/-!
Paper example: a flower quality changes value

Following Section 4.3 of Guizzardi et al. (2022), the same color quality inheres
in the same flower across two worlds, taking a different value in each world.
The quality dimension contains two quales, Red and Brown. A discrete distance
relation supplies the finite witnesses required by the quality-space axioms.

This example retains the paper's quality/value mechanism. It uses one flower
kind and one quality kind, without the paper's full type and color hierarchy.
-/

open LeanUfo.UFO.DSL

ufo_model FlowerPropertyChangeExample : UFO where
  worlds summer autumn
  things Flower FlowerColor Rose1 Color1 ColorValues Red Brown Zero One Two

  given everywhere:
    ObjectKind(Flower)
    QualityKind(FlowerColor)
    Object(Rose1)
    IntrinsicMoment(Color1)
    Rose1 :: Flower
    Color1 :: FlowerColor
    InheresIn(Color1, Rose1)
    Characterization(Flower, FlowerColor)
    QualityDimension(ColorValues)
    Set(ColorValues)
    AssociatedWith(ColorValues, FlowerColor)
    Quale(Red)
    Quale(Brown)
    MemberOf(Red, ColorValues)
    MemberOf(Brown, ColorValues)
    AbstractIndividual(Zero)
    AbstractIndividual(One)
    AbstractIndividual(Two)
    Distance(Red, Red, Zero)
    Distance(Brown, Brown, Zero)
    Distance(Red, Brown, One)
    Distance(Brown, Red, One)
    DistanceZero(Zero)
    DistanceSum(Zero, Zero, Zero)
    DistanceSum(Zero, One, One)
    DistanceSum(One, Zero, One)
    DistanceSum(One, One, Two)
    DistanceGreaterEq(Zero, Zero)
    DistanceGreaterEq(One, Zero)
    DistanceGreaterEq(One, One)
    DistanceGreaterEq(Two, Zero)
    DistanceGreaterEq(Two, One)
    Ex(Rose1)
    Ex(Color1)

  given summer:
    HasValue(Color1, Red)

  given autumn:
    HasValue(Color1, Brown)

  derive_relations
  certify
