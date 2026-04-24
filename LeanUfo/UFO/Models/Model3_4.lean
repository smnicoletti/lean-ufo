import LeanUfo.UFO.Core.Section3_4
import LeanUfo.UFO.Models.Model3_3

universe u

namespace Model3_4

/-
  A concrete model for UFO §3.4 (Endurant types).

  Design choice (minimal extension of Model3_3):
  We reuse the same domain and single-world S5 frame from `Model3_3.sig3_3`,
  and we interpret the new §3.4 type-level refinements in the smallest way
  compatible with the axioms.

  Intuition:
  - there is exactly one endurant type, namely `K`,
  - its unique instance `I` is an Object,
  - so `K` is an ObjectType and, because `K` is already a Kind in `Model3_2`,
    it is also an ObjectKind,
  - all other specific endurant types and kinds are empty.
-/

/--
Signature interpretation for §3.4 extending the §3.3 concrete signature.

We classify the unique endurant type `K` as a `SubstantialType`, `ObjectType`,
and `ObjectKind`, leaving all other new predicates empty.
-/
def sig3_4 : UFOSignature3_4.{0,0} :=
{ toUFOSignature3_3 := Model3_3.sig3_3

  /- Additional type-level categories from §3.4 -/
  SubstantialType := fun t _w =>
    match t with
    | Model3_2.Thing3_2.K => True
    | Model3_2.Thing3_2.I => False

  MomentType := fun _t _w => False

  ObjectType := fun t _w =>
    match t with
    | Model3_2.Thing3_2.K => True
    | Model3_2.Thing3_2.I => False

  CollectiveType := fun _t _w => False
  QuantityType   := fun _t _w => False
  RelatorType    := fun _t _w => False
  ModeType       := fun _t _w => False
  QualityType    := fun _t _w => False

  /- Specific endurant kinds -/
  ObjectKind := fun t _w =>
    match t with
    | Model3_2.Thing3_2.K => True
    | Model3_2.Thing3_2.I => False

  CollectiveKind := fun _t _w => False
  QuantityKind   := fun _t _w => False
  RelatorKind    := fun _t _w => False
  ModeKind       := fun _t _w => False
}

attribute [simp] sig3_4

/-
  The new §3.4 axioms all hold definitionally in this model:

  - `K` is the only endurant type and all its instances are Objects,
    hence also Substantials and Endurants.
  - there are no moment-side or alternative leaf-type classifications.
  - `ObjectKind` is exactly `ObjectType ∧ Kind`.
  - every endurant (`I`) possibly instantiates the unique ObjectKind (`K`).
-/

/-- Proof that `sig3_4` satisfies (a44). -/
theorem ax44_sig3_4 : ax_a44 sig3_4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro _
          refine ⟨by simp [sig3_4, Model3_2.sig3_2], ?_⟩
          intro v hv x hx
          cases v
          cases x <;> simp [sig3_4, Model3_3.sig3_3, Model3_2.sig3_2] at hx ⊢
        · intro h
          simp [sig3_4, Model3_2.sig3_2]
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4, Model3_2.sig3_2] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro _
          refine ⟨by simp [sig3_4, Model3_2.sig3_2], ?_⟩
          intro v hv x hx
          cases v
          cases x <;> simp [sig3_4, Model3_3.sig3_3, Model3_2.sig3_2] at hx ⊢
        · intro h
          simp [sig3_4, Model3_2.sig3_2]
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro _
          refine ⟨by simp [sig3_4, Model3_2.sig3_2], ?_⟩
          intro v hv x hx
          cases v
          cases x <;> simp [sig3_4, Model3_3.sig3_3, Model3_2.sig3_2] at hx ⊢
        · intro h
          simp [sig3_4, Model3_2.sig3_2]
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

  · intro t w
    cases w
    cases t with
    | K =>
        constructor
        · intro h
          simp [sig3_4] at h
        · intro h
          rcases h with ⟨_, hBox⟩
          have := hBox () trivial Model3_2.Thing3_2.I (by simp [sig3_4, Model3_2.sig3_2])
          simp [sig3_4, Quality] at this
    | I =>
        simp [sig3_4, Model3_2.sig3_2]

/-- Proof that `sig3_4` satisfies (a45). -/
theorem ax45_sig3_4 : ax_a45 sig3_4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  intro t w <;>
  cases w <;>
  cases t <;>
  simp [sig3_4, Model3_2.sig3_2]

/-- Proof that `sig3_4` satisfies (a46). -/
theorem ax46_sig3_4 : ax_a46 sig3_4 := by
  intro x w hEnd
  cases w
  cases x with
  | K =>
      simp [sig3_4, Model3_3.sig3_3, Model3_2.sig3_2] at hEnd
  | I =>
      refine ⟨(), trivial, ?_⟩
      refine ⟨Model3_2.Thing3_2.K, ?_, ?_⟩
      · simp [sig3_4]
      · simp [sig3_4, Model3_2.sig3_2]

/-- Consistency witness: a concrete model of UFO subsection 3.4. -/
instance : UFOAxioms3_4 sig3_4 :=
by
  classical

  have h3 : UFOAxioms3_3 Model3_3.sig3_3 := inferInstance

  refine
  { -- inherited §3.1 + §3.2 + §3.3 fields
    ax1  := h3.ax1
    ax2  := h3.ax2
    ax3  := h3.ax3
    ax4  := h3.ax4
    ax5  := h3.ax5
    ax6  := h3.ax6
    ax7  := h3.ax7
    ax8  := h3.ax8
    ax9  := h3.ax9
    ax10 := h3.ax10
    ax11 := h3.ax11
    ax12 := h3.ax12
    ax13 := h3.ax13
    ax14 := h3.ax14
    ax15 := h3.ax15
    ax16 := h3.ax16
    ax17 := h3.ax17

    ax18 := h3.ax18
    ax19 := h3.ax19
    ax20 := h3.ax20
    ax21 := h3.ax21
    ax22 := h3.ax22
    ax23 := h3.ax23
    ax24 := h3.ax24
    ax25 := h3.ax25
    ax26 := h3.ax26
    ax27 := h3.ax27
    ax28 := h3.ax28
    ax29 := h3.ax29
    ax30 := h3.ax30
    ax31 := h3.ax31
    ax32 := h3.ax32
    ax33 := h3.ax33

    ax_instEndurant    := h3.ax_instEndurant
    ax_sub_kind_sortal := h3.ax_sub_kind_sortal
    ax_nonSortal_up    := h3.ax_nonSortal_up
    ax_kindStable      := h3.ax_kindStable

    ax34 := h3.ax34
    ax35 := h3.ax35
    ax36 := h3.ax36
    ax37 := h3.ax37
    ax38 := h3.ax38
    ax39 := h3.ax39
    ax40 := h3.ax40
    ax41 := h3.ax41
    ax42 := h3.ax42
    ax43 := h3.ax43

    -- §3.4 axioms
    ax44 := ax44_sig3_4
    ax45 := ax45_sig3_4
    ax46 := ax46_sig3_4
  }

end Model3_4
