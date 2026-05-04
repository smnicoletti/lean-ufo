import LeanUfo.UFO.Core.Signature3_3

universe u v

/--
Extension of `UFOSignature3_3` with the §3.4
taxonomy of endurant types.

This adds:
- type-level refinements such as `ObjectType`, `RelatorType`, ...
- kind-level refinements such as `ObjectKind`, `RelatorKind`, ...

`QualityKind` is already present in §3.3 because definition (d6) uses it to
define `Quality`.
-/
structure UFOSignature3_4 extends UFOSignature3_3 where

  /- Additional type-level categories from P_E and P_E' -/
  SubstantialType : Thing → F.World → Prop
  MomentType      : Thing → F.World → Prop

  ObjectType      : Thing → F.World → Prop
  CollectiveType  : Thing → F.World → Prop
  QuantityType    : Thing → F.World → Prop
  RelatorType     : Thing → F.World → Prop
  ModeType        : Thing → F.World → Prop
  QualityType     : Thing → F.World → Prop

  /- Specific endurant kinds from P_K -/
  ObjectKind      : Thing → F.World → Prop
  CollectiveKind  : Thing → F.World → Prop
  QuantityKind    : Thing → F.World → Prop
  RelatorKind     : Thing → F.World → Prop
  ModeKind        : Thing → F.World → Prop
