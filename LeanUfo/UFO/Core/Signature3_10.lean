import LeanUfo.UFO.Core.Signature3_9

universe u v

/--
Extension of `UFOSignature3_9` with the §3.10
relator predicates.

We use representative names for the paper's symbols:
- `ExternallyDependent` for `externallyDependent`
- `ExternallyDependentMode` for `ExternallyDependentMode`
- `FoundedBy` for `foundedBy`
- `QuaIndividualOf` for `quaIndividualOf`
- `QuaIndividual` for `QuaIndividual`
- `Mediates` for `mediates`
-/
structure UFOSignature3_10 extends UFOSignature3_9 where

  ExternallyDependent :
    Thing → Thing → F.World → Prop

  ExternallyDependentMode :
    Thing → F.World → Prop

  FoundedBy :
    Thing → Thing → F.World → Prop

  QuaIndividualOf :
    Thing → Thing → F.World → Prop

  QuaIndividual :
    Thing → F.World → Prop

  Mediates :
    Thing → Thing → F.World → Prop
