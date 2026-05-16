import LeanUfo.UFO.DSL.Syntax

/-!
# Product-family witness syntax

This small certified model demonstrates the `product_family` declaration used
by the reflective checker for axiom (a99).  The declaration records the finite
family that can witness the existential product decomposition of a quality
domain.

The first model keeps the color-space names inert, so it is a compact syntax
example.  The second model adds the finite tuple facts that such a witness uses:
a color-space member, a hue-space member, and a tuple projection from the color
value to its hue coordinate.  It deliberately avoids `QualityDomain`,
`QualityDimension`, and `Characterization`; those facts activate the full §3.12
quality-type obligations and belong in a dedicated semantic stress test.
-/

open LeanUfo.UFO.DSL

ufo_model ColorSpaceProductFamily : UFO where
  worlds actual
  things
    K I
    ColorSpace ColorQuality
    HueSpace SaturationSpace BrightnessSpace
    Hue Saturation Brightness

  given actual:
    I :: K
    Object(I)
    ObjectKind(K)
    AbstractIndividual(ColorSpace)
    AbstractIndividual(ColorQuality)
    AbstractIndividual(HueSpace)
    AbstractIndividual(SaturationSpace)
    AbstractIndividual(BrightnessSpace)
    AbstractIndividual(Hue)
    AbstractIndividual(Saturation)
    AbstractIndividual(Brightness)

  product_family ColorSpace for ColorQuality:
    dimensions HueSpace SaturationSpace BrightnessSpace
    types Hue Saturation Brightness

  derive_relations
  certify

ufo_model ColorSpaceProductFamilyFacts : UFO where
  worlds actual
  things
    K I
    ColorSpace HueSpace
    ColorQuality Hue
    ColorValue HueValue

  given actual:
    I :: K
    Object(I)
    ObjectKind(K)

    AbstractIndividual(ColorQuality)
    AbstractIndividual(Hue)

    AbstractIndividual(ColorSpace)
    AbstractIndividual(HueSpace)
    Set(ColorSpace)
    Set(HueSpace)

    AssociatedWith(ColorSpace, ColorQuality)
    AssociatedWith(HueSpace, Hue)

    MemberOf(ColorValue, ColorSpace)
    MemberOf(HueValue, HueSpace)
    AbstractIndividual(ColorValue)
    AbstractIndividual(HueValue)

    TupleProjection(ColorValue, 0, HueValue)

  product_family ColorSpace for ColorQuality:
    dimensions HueSpace
    types Hue

  derive_relations
  certify
