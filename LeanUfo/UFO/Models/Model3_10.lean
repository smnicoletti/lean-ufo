import LeanUfo.UFO.Core.Section3_10
import LeanUfo.UFO.Models.Model3_9

universe u

namespace Model3_10

/-
  A concrete model for UFO §3.10 (Relators).

  Design choice (minimal extension of Model3_9):
  we reuse the same tiny domain and single-world S5 frame from `Model3_9.sig3_9`
  and interpret the new relator predicates in the smallest way compatible with
  axioms (a69)–(a80).

  Intuition:
  - existential dependence is already total in the inherited witness,
  - inherence and foundedness are empty,
  - so external dependence becomes total, but externally dependent modes remain
    empty because there are no modes,
  - qua individuals, relators, and mediation are all empty.
-/

/--
Signature interpretation for §3.10 extending the §3.9 concrete signature.

The witness still has the same two entities:
- `K`, the unique type/kind,
- `I`, the unique individual, with `I :: K` as the only instantiation fact.

All earlier layers remain unchanged:
- there is only one world,
- there are no perdurants, no moments, and no inherence facts,
- mereology is still identity-based,
- constitution is empty,
- existential dependence is total and existential independence is empty.

For the new §3.10 layer we choose the minimal compatible interpretation:
- `ExternallyDependent` is total, because `ed` is total and `InheresIn` is
  empty, so the condition in (a69) is always satisfied,
- `ExternallyDependentMode` is empty, because there are no modes,
- `FoundedBy`, `QuaIndividualOf`, `QuaIndividual`, `Relator`, and `Mediates`
  are all empty in this witness.
-/
def sig3_10 : UFOSignature3_10.{0,0} :=
{ toUFOSignature3_9 := Model3_9.sig3_9

  ExternallyDependent := fun _x _y _w => True

  ExternallyDependentMode := fun _x _w => False

  FoundedBy := fun _x _y _w => False

  QuaIndividualOf := fun _x _y _w => False

  QuaIndividual := fun _x _w => False

  Mediates := fun _x _y _w => False
}

attribute [simp] sig3_10

/-- Proof that `sig3_10` satisfies (a69). -/
theorem ax69_sig3_10 : ax_a69 sig3_10 := by
  unfold ax_a69
  intro x y w
  cases w
  constructor
  · intro _
    refine ⟨?_, ?_⟩
    · intro w' hw' hx
      trivial
    · intro z hz
      cases hz
  · intro _
    trivial

/-- Proof that `sig3_10` satisfies (a70). -/
theorem ax70_sig3_10 : ax_a70 sig3_10 := by
  unfold ax_a70
  intro x w
  cases w
  cases x <;> simp [sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3, Model3_2.sig3_2]

/-- Proof that `sig3_10` satisfies (a71). -/
theorem ax71_sig3_10 : ax_a71 sig3_10 := by
  unfold ax_a71
  intro x y w h
  cases h

/-- Proof that `sig3_10` satisfies (a72). -/
theorem ax72_sig3_10 : ax_a72 sig3_10 := by
  unfold ax_a72
  intro x w h
  cases h

/-- Proof that `sig3_10` satisfies (a73). -/
theorem ax73_sig3_10 : ax_a73 sig3_10 := by
  unfold ax_a73 FoundationOf
  intro x y w
  cases w
  cases x <;> cases y <;> simp [sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5]

/-- Proof that `sig3_10` satisfies (a74). -/
theorem ax74_sig3_10 : ax_a74 sig3_10 := by
  unfold ax_a74
  intro x w
  cases w
  simp [sig3_10]

/-- Proof that `sig3_10` satisfies (a75). -/
theorem ax75_sig3_10 : ax_a75 sig3_10 := by
  unfold ax_a75
  intro x w h
  cases h

/-- Proof that `sig3_10` satisfies (a76). -/
theorem ax76_sig3_10 : ax_a76 sig3_10 := by
  unfold ax_a76
  intro x y y' w h
  exact False.elim h.1

/-- Proof that `sig3_10` satisfies (a77). -/
theorem ax77_sig3_10 : ax_a77 sig3_10 := by
  unfold ax_a77
  intro x w h
  cases h

/-- Proof that `sig3_10` satisfies (a78). -/
theorem ax78_sig3_10 : ax_a78 sig3_10 := by
  unfold ax_a78
  intro x y w h
  exact False.elim h.1

/-- Proof that `sig3_10` satisfies (a79). -/
theorem ax79_sig3_10 : ax_a79 sig3_10 := by
  unfold ax_a79 FoundationOf
  intro x w
  cases w
  cases x <;> simp [sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5]

/-- Proof that `sig3_10` satisfies (a80). -/
theorem ax80_sig3_10 : ax_a80 sig3_10 := by
  unfold ax_a80
  intro x y w
  cases w
  simp [sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3, Model3_2.sig3_2]

/-- Proof that `sig3_10` satisfies the bridge axiom used for `t33`. -/
theorem ax_quaIndividualOf_endurant_sig3_10 :
    ax_quaIndividualOf_endurant (Sig := sig3_10) := by
  unfold ax_quaIndividualOf_endurant
  intro x y w h
  cases h

/-- Consistency witness: a concrete model of UFO subsection 3.10. -/
instance : UFOAxioms3_10 sig3_10 :=
by
  classical

  have h9 : UFOAxioms3_9 sig3_10.toUFOSignature3_9 := by
    change UFOAxioms3_9 Model3_9.sig3_9
    infer_instance

  refine
  { toUFOAxioms3_9 := h9
    -- §3.10 axioms
    ax69 := ax69_sig3_10
    ax70 := ax70_sig3_10
    ax71 := ax71_sig3_10
    ax72 := ax72_sig3_10
    ax73 := ax73_sig3_10
    ax74 := ax74_sig3_10
    ax75 := ax75_sig3_10
    ax76 := ax76_sig3_10
    ax77 := ax77_sig3_10
    ax78 := ax78_sig3_10
    ax79 := ax79_sig3_10
    ax80 := ax80_sig3_10

    -- Bridge axiom used for t33
    axQuaIndividualOfEndurant := ax_quaIndividualOf_endurant_sig3_10
  }

end Model3_10
