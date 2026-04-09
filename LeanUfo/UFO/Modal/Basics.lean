universe u

/--
A Kripke frame.

`World` is the type of possible worlds.
`R` is the accessibility relation.
-/
structure Frame where
  World : Type u
  R : World → World → Prop

namespace Frame

variable {F : Frame}

/-- Necessity (□) -/
def Box (φ : F.World → Prop) : F.World → Prop :=
  fun w => ∀ v, F.R w v → φ v

/-- Possibility (◇) -/
def Dia (φ : F.World → Prop) : F.World → Prop :=
  fun w => ∃ v, F.R w v ∧ φ v

notation "□[" F "]" φ => Frame.Box (F := F) φ
notation "◇[" F "]" φ => Frame.Dia (F := F) φ

end Frame
