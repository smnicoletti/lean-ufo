import LeanUfo.UFO.Core.Section3_5
import LeanUfo.UFO.Models.Model3_4

universe u

namespace Model3_5

/-
  A concrete model for UFO §3.5 (Mereology).

  Design choice (minimal extension of Model3_4):
  we reuse the same tiny domain and single-world S5 frame from `Model3_4.sig3_4`
  and interpret mereological parthood as identity.

  Consequences:
  - `Part` is reflexive, antisymmetric, and transitive,
  - `Overlap` also collapses to identity via shared parts,
  - `ProperPart` is empty, because nothing is a strict part of itself and
    identity admits no non-trivial strict parts in this model.
-/

/--
Signature interpretation for §3.5 extending the §3.4 concrete signature.

We interpret:
- `Part x y` as `x = y`,
- `Overlap x y` as `x = y`,
- `ProperPart x y` as `False`.
-/
def sig3_5 : UFOSignature3_5.{0,0} :=
{ toUFOSignature3_4 := Model3_4.sig3_4

  Part := fun x y _w => x = y
  Overlap := fun x y _w => x = y
  ProperPart := fun _x _y _w => False
}

attribute [simp] sig3_5

/-- Proof that `sig3_5` satisfies (a47). -/
theorem ax47_sig3_5 : ax_a47 sig3_5 := by
  unfold ax_a47
  simp
--  intro x w
--  cases w
--  simp [sig3_5]

/-- Proof that `sig3_5` satisfies (a48). -/
theorem ax48_sig3_5 : ax_a48 sig3_5 := by
  unfold ax_a48
  simp

/-- Proof that `sig3_5` satisfies (a49). -/
theorem ax49_sig3_5 : ax_a49 sig3_5 := by
  intro x y z w hPart
  cases w
  exact hPart.1.trans hPart.2

/-- Proof that `sig3_5` satisfies (a50). -/
theorem ax50_sig3_5 : ax_a50 sig3_5 := by
  intro x y w
  cases w
  simp [sig3_5]

/-- Proof that `sig3_5` satisfies (a51). -/
theorem ax51_sig3_5 : ax_a51 sig3_5 := by
  intro x y w hNotPart
  cases w
  refine ⟨y, ?_, ?_⟩
  · simp [sig3_5]
  ·
    intro hEq
    exact hNotPart hEq

/-- Proof that `sig3_5` satisfies (a52). -/
theorem ax52_sig3_5 : ax_a52 sig3_5 := by
  intro x y w
  cases w
  simp
  intro h
  symm
  exact h

/-- Consistency witness: a concrete model of UFO subsection 3.5. -/
instance : UFOAxioms3_5 sig3_5 :=
by
  classical

  have h4 : UFOAxioms3_4 Model3_4.sig3_4 := inferInstance

  refine
  { -- inherited §3.1 + §3.2 + §3.3 + §3.4 fields
    ax1  := h4.ax1
    ax2  := h4.ax2
    ax3  := h4.ax3
    ax4  := h4.ax4
    ax5  := h4.ax5
    ax6  := h4.ax6
    ax7  := h4.ax7
    ax8  := h4.ax8
    ax9  := h4.ax9
    ax10 := h4.ax10
    ax11 := h4.ax11
    ax12 := h4.ax12
    ax13 := h4.ax13
    ax14 := h4.ax14
    ax15 := h4.ax15
    ax16 := h4.ax16
    ax17 := h4.ax17

    ax18 := h4.ax18
    ax19 := h4.ax19
    ax20 := h4.ax20
    ax21 := h4.ax21
    ax22 := h4.ax22
    ax23 := h4.ax23
    ax24 := h4.ax24
    ax25 := h4.ax25
    ax26 := h4.ax26
    ax27 := h4.ax27
    ax28 := h4.ax28
    ax29 := h4.ax29
    ax30 := h4.ax30
    ax31 := h4.ax31
    ax32 := h4.ax32
    ax33 := h4.ax33

    ax_instEndurant    := h4.ax_instEndurant
    ax_sub_kind_sortal := h4.ax_sub_kind_sortal
    ax_nonSortal_up    := h4.ax_nonSortal_up
    ax_kindStable      := h4.ax_kindStable

    ax34 := h4.ax34
    ax35 := h4.ax35
    ax36 := h4.ax36
    ax37 := h4.ax37
    ax38 := h4.ax38
    ax39 := h4.ax39
    ax40 := h4.ax40
    ax41 := h4.ax41
    ax42 := h4.ax42
    ax43 := h4.ax43

    ax44 := h4.ax44
    ax45 := h4.ax45
    ax46 := h4.ax46

    -- §3.5 axioms
    ax47 := ax47_sig3_5
    ax48 := ax48_sig3_5
    ax49 := ax49_sig3_5
    ax50 := ax50_sig3_5
    ax51 := ax51_sig3_5
    ax52 := ax52_sig3_5
  }

end Model3_5
