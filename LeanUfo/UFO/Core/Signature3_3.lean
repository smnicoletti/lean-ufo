import LeanUfo.UFO.Core.Signature3_2

universe u

/--
Extension of `UFOSignature3_2` with the §3.3
taxonomy of endurant individuals.

Formalization note:
The paper gives definition (d6), `Quality(x)`, only in §3.12. However, §3.3
already uses `Quality` as one member of the `IntrinsicMoment` partition in
(a42) and (a43). To avoid making `Quality` a primitive signature predicate and
later constraining it by a definition-like axiom, we formalize (d6) in
`Section3_3`.

That requires `QualityKind` to be available in this signature earlier than it
appears in the paper's exposition. Its intended type-level behavior is still
constrained later by §3.4.
-/
structure UFOSignature3_3 extends UFOSignature3_2 where

  /- Partition of Endurant -/
  Substantial      : Thing → F.World → Prop
  Moment           : Thing → F.World → Prop

  /- Partition of Substantial -/
  Object           : Thing → F.World → Prop
  Collective       : Thing → F.World → Prop
  Quantity         : Thing → F.World → Prop

  /- Partition of Moment -/
  Relator          : Thing → F.World → Prop
  IntrinsicMoment  : Thing → F.World → Prop

  /- Partition of IntrinsicMoment -/
  Mode             : Thing → F.World → Prop

  /- Needed for definition (d6) of Quality -/
  QualityKind      : Thing → F.World → Prop
