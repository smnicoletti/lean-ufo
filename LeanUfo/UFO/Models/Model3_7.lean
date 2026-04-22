import LeanUfo.UFO.Core.Section3_7
import LeanUfo.UFO.Models.Model3_6

universe u

namespace Model3_7

/-
  A concrete model for UFO §3.7 (Constitution).

  Design choice (minimal extension of Model3_6):
  we reuse the same tiny domain and single-world S5 frame from `Model3_6.sig3_6`
  and interpret constitution in the smallest way compatible with
  axioms (a56)–(a61).

  Intuition:
  - `Ex` is total on the tiny domain,
  - `ConstitutedBy` is empty,
  - `GenericConstitutionalDependence` is true exactly for those types with no
    instances, making (a58) hold vacuously,
  - `Constitution` is empty because it requires `ConstitutedBy`,
  - the modal clauses are therefore immediate.
-/

/--
Signature interpretation for §3.7 extending the §3.6 concrete signature.

The witness reuses the tiny domain inherited from `Model3_2`:
- `K`, the unique type/kind in the model,
- `I`, the unique individual, which instantiates `K`.

As in the previous witness models, there is only one world, `I` is an
endurant, there are no perdurants, and the new constitution predicates are
interpreted minimally.

We interpret:
- `Ex` as universally true,
- `ConstitutedBy` as empty,
- `GenericConstitutionalDependence` as holding exactly for instance-empty types,
- `Constitution` as empty.
-/
def sig3_7 : UFOSignature3_7.{0,0} :=
{ toUFOSignature3_6 := Model3_6.sig3_6

  Ex := fun _x _w => True

  ConstitutedBy := fun _x _y _w => False

  /-
    Since `ConstitutedBy` is empty, axiom (a58) forces
    `GenericConstitutionalDependence x' y'` to be false when `x'` has an
    actual instance, and true when `x'` has no instances at all.

    In this tiny witness:
    - `K` has the instance `I`, so `GCD K y'` must be false;
    - `I` has no instances, so `GCD I y'` is vacuously true.
  -/
  GenericConstitutionalDependence := fun x' _y' _w =>
    match x' with
    | Model3_2.Thing3_2.K => False
    | Model3_2.Thing3_2.I => True

  Constitution := fun _x _x' _y _y' _w => False
}

attribute [simp] sig3_7

/-- Proof that `sig3_7` satisfies (a56). -/
theorem ax56_sig3_7 : ax_a56 sig3_7 := by
  unfold ax_a56
  intro x y w h
  cases h

/-- Proof that `sig3_7` satisfies (a57). -/
theorem ax57_sig3_7 : ax_a57 sig3_7 := by
  unfold ax_a57
  intro x y x' y' w h
  exact False.elim h.1

/-- Proof that `sig3_7` satisfies (a58). -/
theorem ax58_sig3_7 : ax_a58 sig3_7 := by
  unfold ax_a58
  intro x' y' w
  cases w
  cases x'
  · constructor
    · intro h
      cases h
    · intro h
      have hI := h Model3_2.Thing3_2.I (by simp [sig3_7, Model3_6.sig3_6, Model3_5.sig3_5, Model3_2.sig3_2])
      rcases hI with ⟨y, hyInst, hyConst⟩
      cases hyConst
  · constructor
    · intro _
      intro x hx
      cases x <;> simp [sig3_7, Model3_6.sig3_6, Model3_5.sig3_5, Model3_2.sig3_2] at hx
    · intro _
      trivial

/-- Proof that `sig3_7` satisfies (a59). -/
theorem ax59_sig3_7 : ax_a59 sig3_7 := by
  unfold ax_a59
  intro x x' y y' w
  cases w
  simp [sig3_7]

/-- Proof that `sig3_7` satisfies (a60). -/
theorem ax60_sig3_7 : ax_a60 sig3_7 := by
  unfold ax_a60
  intro x y w h
  intro w' hw' hxEx
  exact False.elim h.2

/-- Proof that `sig3_7` satisfies (a61). -/
theorem ax61_sig3_7 : ax_a61 sig3_7 := by
  unfold ax_a61
  intro x y w h
  cases h

/-- Consistency witness: a concrete model of UFO subsection 3.7. -/
instance : UFOAxioms3_7 sig3_7 :=
by
  classical

  have h6 : UFOAxioms3_6 sig3_7.toUFOSignature3_6 := by
    change UFOAxioms3_6 Model3_6.sig3_6
    infer_instance

  refine
  { toUFOAxioms3_6 := h6
    -- §3.7 axioms
    ax56 := ax56_sig3_7
    ax57 := ax57_sig3_7
    ax58 := ax58_sig3_7
    ax59 := ax59_sig3_7
    ax60 := ax60_sig3_7
    ax61 := ax61_sig3_7
  }

end Model3_7
