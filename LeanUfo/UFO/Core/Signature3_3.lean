import LeanUfo.UFO.Core.Signature3_2

universe u

/--
Extension of `UFOSignature3_2` with the §3.3
taxonomy of endurant individuals.
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
  Quality          : Thing → F.World → Prop
