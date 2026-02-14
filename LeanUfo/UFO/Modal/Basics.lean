universe u

/--
An S5 Kripke frame.

`World` is the type of possible worlds.
`R` is the accessibility relation.

S5 is characterized by `R` being an equivalence relation.
-/
structure S5Frame where
  World : Type u
  R : World → World → Prop
  refl  : ∀ w, R w w
  symm  : ∀ {w v}, R w v → R v w
  trans : ∀ {w v u}, R w v → R v u → R w u

namespace S5Frame

variable {F : S5Frame}

/-- Necessity (□) -/
def Box (φ : F.World → Prop) : F.World → Prop :=
  fun w => ∀ v, F.R w v → φ v

/-- Possibility (◇) -/
def Dia (φ : F.World → Prop) : F.World → Prop :=
  fun w => ∃ v, F.R w v ∧ φ v

notation "□[" F "]" φ => S5Frame.Box (F := F) φ
notation "◇[" F "]" φ => S5Frame.Dia (F := F) φ

end S5Frame
