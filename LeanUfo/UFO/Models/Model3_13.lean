import LeanUfo.UFO.Core.Section3_13
import LeanUfo.UFO.Models.Model3_12

universe u

namespace Model3_13

/-
  A concrete model for UFO §3.13 (Endurants and perdurants).

  Design choice (minimal extension of Model3_12):
  we reuse the same tiny domain and single-world S5 frame from `Model3_12.sig3_12`
  and interpret the new endurant/perdurant connection relations as empty.

  Intuition:
  - the inherited witness has an endurant individual but no perdurants,
  - therefore no manifestation, life-of, or meet facts are needed,
  - the corrected (a102), (a103), and (a104) all hold with the empty
    interpretation.

-/

/--
Signature interpretation for §3.13 extending the §3.12 concrete signature.

The witness still has the same two entities:
- `K`, the unique type/kind,
- `I`, the unique individual, with `I :: K` as the only instantiation fact.

All previous layers remain unchanged. For the new §3.13 layer we interpret
`Manifests`, `LifeOf`, and `Meet` as empty.
-/
def sig3_13 : UFOSignature3_13.{0,0} :=
{ toUFOSignature3_12 := Model3_12.sig3_12

  Manifests := fun _x _y _w => False
  LifeOf := fun _x _y _w => False
  Meet := fun _x _y _w => False
}

attribute [simp] sig3_13

/-- Proof that `sig3_13` satisfies (a102). -/
theorem ax102_sig3_13 : ax_a102 sig3_13 := by
  unfold ax_a102
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_13] at h

/-- Proof that `sig3_13` satisfies (a103). -/
theorem ax103_sig3_13 : ax_a103 sig3_13 := by
  unfold ax_a103
  intro x y w
  cases w
  cases x <;> cases y <;>
    simp [sig3_13, Model3_12.sig3_12, Model3_11.sig3_11, Model3_10.sig3_10,
      Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6,
      Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3, Model3_2.sig3_2]

/-- Proof that `sig3_13` satisfies (a104). -/
theorem ax104_sig3_13 : ax_a104 sig3_13 := by
  unfold ax_a104
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_13] at h

/-- Consistency witness: a concrete model of UFO subsection 3.13. -/
instance : UFOAxioms3_13 sig3_13 :=
by
  classical

  have h12 : UFOAxioms3_12 sig3_13.toUFOSignature3_12 := by
    simpa [sig3_13] using (inferInstance : UFOAxioms3_12 Model3_12.sig3_12)

  refine
  { toUFOAxioms3_12 := h12
    -- §3.13 axioms
    ax102 := ax102_sig3_13
    ax103 := ax103_sig3_13
    ax104 := ax104_sig3_13
  }

end Model3_13
