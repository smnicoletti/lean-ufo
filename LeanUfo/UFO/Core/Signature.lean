import LeanUfo.UFO.Modal.Basics

universe u v

/--
Semantic signature for UFO over S5 possible-world semantics.

- `Thing` is the domain of quantification (the top category in the taxonomy).
- `Type_` and `Individual` are world-indexed predicates.
- `Inst` is world-indexed instantiation (written `::` in the paper).
-/
structure UFOSignature where
  F          : S5Frame
  Thing      : Type v
  Type_      : Thing → F.World → Prop
  Individual : Thing → F.World → Prop
  Inst       : Thing → Thing → F.World → Prop

namespace UFOSignature

infix:50 " :: " => UFOSignature.Inst

end UFOSignature
