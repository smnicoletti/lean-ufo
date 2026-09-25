import LeanUfo.UFO.Modal.Basics

universe u

/--
An S5 Kripke frame.

S5 is characterized by `R` being an equivalence relation.
-/
structure S5Frame extends Frame where
  refl  : ∀ w, R w w
  symm  : ∀ {w v}, R w v → R v w
  trans : ∀ {w v u}, R w v → R v u → R w u

namespace S5Frame

variable {F : S5Frame}

/--
In an S5 frame, possibility is invariant across accessible worlds.
-/
theorem dia_stable
  {φ : F.World → Prop} :
  ∀ {w v : F.World},
    F.R w v →
    (Frame.Dia (F := F.toFrame) φ w ↔ Frame.Dia (F := F.toFrame) φ v) :=
by
  intro w v hRv
  constructor
  · intro hDia
    rcases hDia with ⟨u, hWu, hφu⟩
    refine ⟨u, ?_, hφu⟩
    exact F.trans (F.symm hRv) hWu
  · intro hDia
    rcases hDia with ⟨u, hVu, hφu⟩
    refine ⟨u, ?_, hφu⟩
    exact F.trans hRv hVu

/--
In an S5 frame, necessity is invariant across accessible worlds.
-/
theorem box_stable
  {φ : F.World → Prop} :
  ∀ {w v : F.World},
    F.R w v →
    (Frame.Box (F := F.toFrame) φ w ↔ Frame.Box (F := F.toFrame) φ v) :=
by
  intro w v hRv
  constructor
  · intro hBox u hVu
    have hWu : F.R w u := F.trans hRv hVu
    exact hBox u hWu
  · intro hBox u hWu
    have hVu : F.R v u := F.trans (F.symm hRv) hWu
    exact hBox u hVu

/-- Coercion from S5 frames to general Kripke frames.
    Allows S5Frame to be used transparently wherever a Frame is expected. -/

instance : Coe S5Frame Frame where
  coe F := F.toFrame

end S5Frame
