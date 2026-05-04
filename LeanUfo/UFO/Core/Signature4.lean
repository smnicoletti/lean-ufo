import LeanUfo.UFO.Core.Signature3_13

universe u v

/--
Extension of `UFOSignature3_13` with the §4 type-structure predicates.

These predicates are constrained by axioms (a105)–(a108):
- `IsDisjointWith` records disjointness between two types,
- `IsCompletelyCoveredBy` records binary complete coverage of one type by two
  other types,
- `IsPartitionedInto` combines complete coverage with disjointness,
- `Categorizes` relates a categorizing type to the type categorized by its
  instances.
-/
structure UFOSignature4 extends UFOSignature3_13 where

  IsDisjointWith :
    Thing → Thing → F.World → Prop

  IsCompletelyCoveredBy :
    Thing → Thing → Thing → F.World → Prop

  IsPartitionedInto :
    Thing → Thing → Thing → F.World → Prop

  Categorizes :
    Thing → Thing → F.World → Prop
