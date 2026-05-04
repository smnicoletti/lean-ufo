import LeanUfo.UFO.Core.Signature3_3
import LeanUfo.UFO.Core.Section3_3
import LeanUfo.UFO.Models.Model3_2

universe u

namespace Model3_3

/-
  A concrete model for UFO §3.3 (Endurant individuals taxonomy).

  Design choice (minimal extension of Model3_2):
  We reuse the same `Thing` and S5 frame from `Model3_2.sig3_2`,
  and we interpret the new §3.3 predicates as a *pure refinement*
  over existing Endurant individuals.

  Intuition:
  - Every Endurant individual is taken to be a Substantial (hence an Object).
  - There are no Moments in this tiny model (Relators, Modes, Qualities are empty).
  - This satisfies the required “disjoint + complete” partition axioms (a34–a43)
    in the simplest possible way.
-/

/--
Signature interpretation for §3.3 extending the §3.2 concrete signature.

We classify all endurants as Substantials (and Objects),
and leave the other leaf categories empty.
-/
def sig3_3 : UFOSignature3_3.{0,0} :=
{ toUFOSignature3_2 := Model3_2.sig3_2

  /- Partition of Endurant individuals -/
  Substantial := fun x w => Model3_2.sig3_2.Endurant x w
  Moment      := fun _x _w => False

  /- Partition of Substantial -/
  Object      := fun x w => Model3_2.sig3_2.Endurant x w
  Collective  := fun _x _w => False
  Quantity    := fun _x _w => False

  /- Partition of Moment -/
  Relator         := fun _x _w => False
  IntrinsicMoment := fun _x _w => False

  /- Partition of IntrinsicMoment -/
  Mode := fun _x _w => False

  /- Needed for the derived definition of Quality -/
  QualityKind := fun _x _w => False
}

attribute [simp] sig3_3

/-
  §3.3 axioms (a34–a43) hold in this model by construction.

  The proofs are all “by simp” because each axiom reduces to a propositional tautology
  once you unfold the chosen interpretations:
  - `Substantial x w` is definitionally `Endurant x w`
  - everything on the Moment side is `False`
  - `Object x w` is definitionally `Endurant x w`
-/

/-- (a34) Substantial(x) ∨ Moment(x) ↔ Endurant(x) -/
theorem ax34_sig3_3 : ax_a34 sig3_3 := by
  intro x w
  simp [sig3_3]

/-- (a35) ¬∃x (Substantial(x) ∧ Moment(x)) -/
theorem ax35_sig3_3 : ax_a35 sig3_3 := by
  intro w
  simp [sig3_3]

/-- (a36) Object(x) ∨ Collective(x) ∨ Quantity(x) ↔ Substantial(x) -/
theorem ax36_sig3_3 : ax_a36 sig3_3 := by
  intro x w
  simp [sig3_3]

/-- (a37) ¬∃x (Object(x) ∧ Collective(x)) -/
theorem ax37_sig3_3 : ax_a37 sig3_3 := by
  intro w
  simp [sig3_3]

/-- (a38) ¬∃x (Object(x) ∧ Quantity(x)) -/
theorem ax38_sig3_3 : ax_a38 sig3_3 := by
  intro w
  simp [sig3_3]

/-- (a39) ¬∃x (Collective(x) ∧ Quantity(x)) -/
theorem ax39_sig3_3 : ax_a39 sig3_3 := by
  intro w
  simp [sig3_3]

/-- (a40) Relator(x) ∨ IntrinsicMoment(x) ↔ Moment(x) -/
theorem ax40_sig3_3 : ax_a40 sig3_3 := by
  intro x w
  simp [sig3_3]

/-- (a41) ¬∃x (Relator(x) ∧ IntrinsicMoment(x)) -/
theorem ax41_sig3_3 : ax_a41 sig3_3 := by
  intro w
  simp [sig3_3]

/-- (a42) Mode(x) ∨ Quality(x) ↔ IntrinsicMoment(x) -/
theorem ax42_sig3_3 : ax_a42 sig3_3 := by
  intro x w
  simp [sig3_3, Quality]

/-- (a43) ¬∃x (Mode(x) ∧ Quality(x)) -/
theorem ax43_sig3_3 : ax_a43 sig3_3 := by
  intro w
  simp [sig3_3, Quality]

/-- Consistency witness: a concrete model of UFO subsection 3.3. -/
instance : UFOAxioms3_3 sig3_3 :=
by
  classical

  -- get inherited §3.2 axioms from Model3_2
  have h2 : UFOAxioms3_2 Model3_2.sig3_2 := inferInstance

  -- build full structure explicitly
  refine
  { -- inherited §3.1 + §3.2 fields
    ax1  := h2.ax1
    ax2  := h2.ax2
    ax3  := h2.ax3
    ax4  := h2.ax4
    ax5  := h2.ax5
    ax6  := h2.ax6
    ax7  := h2.ax7
    ax8  := h2.ax8
    ax9  := h2.ax9
    ax10 := h2.ax10
    ax11 := h2.ax11
    ax12 := h2.ax12
    ax13 := h2.ax13
    ax14 := h2.ax14
    ax15 := h2.ax15
    ax16 := h2.ax16
    ax17 := h2.ax17

    ax18 := h2.ax18
    ax19 := h2.ax19
    ax20 := h2.ax20
    ax21 := h2.ax21
    ax22 := h2.ax22
    ax23 := h2.ax23
    ax24 := h2.ax24
    ax25 := h2.ax25
    ax26 := h2.ax26
    ax27 := h2.ax27
    ax28 := h2.ax28
    ax29 := h2.ax29
    ax30 := h2.ax30
    ax31 := h2.ax31
    ax32 := h2.ax32
    ax33 := h2.ax33

    ax_instEndurant   := h2.ax_instEndurant
    ax_sub_kind_sortal := h2.ax_sub_kind_sortal
    ax_nonSortal_up    := h2.ax_nonSortal_up
    ax_kindStable      := h2.ax_kindStable

    -- §3.3 axioms
    ax34 := ax34_sig3_3
    ax35 := ax35_sig3_3
    ax36 := ax36_sig3_3
    ax37 := ax37_sig3_3
    ax38 := ax38_sig3_3
    ax39 := ax39_sig3_3
    ax40 := ax40_sig3_3
    ax41 := ax41_sig3_3
    ax42 := ax42_sig3_3
    ax43 := ax43_sig3_3
  }

end Model3_3
