import LeanUfo.UFO.Core.Section3_2

universe u

namespace Model3_2

/--
We construct a minimal S5 frame with a single world.
Modal operators collapse to ordinary truth at that world.
-/
def trivialFrame : S5Frame :=
{ World := Unit,
  R := fun _ _ => True,
  refl := by intro _; trivial,
  symm := by intro _ _ _; trivial,
  trans := by intro _ _ _ _ _; trivial }

/--
Domain of discourse for the model of subsection 3.2.

We use the smallest domain that can witness the new taxonomy. There is exactly
one EndurantType, it is a Kind, it is rigid and sortal, and it has exactly one instance.
That is the minimal consistency witness for §3.2.:

- `K` : a Kind (hence a rigid sortal)
- `I` : an Individual instantiating `K`
-/
inductive Thing3_2
| K   -- the unique Kind (also a Type)
| I   -- the unique Individual
deriving DecidableEq

/--
Interpretation of the UFO signature for subsection 3.2 on the tiny domain `Thing3_2`
over the single-world S5 frame `trivialFrame`.

All predicates ignore the world parameter since the frame has one world (`Unit`).
-/
def sig3_2 : UFOSignature3_2 :=
{ F := trivialFrame
  Thing := Thing3_2

  /- Section 3.1 core predicates -/
  Type_ := fun x _w =>
    match x with
    | .K => True
    | .I => False

  Individual := fun x _w =>
    match x with
    | .K => False
    | .I => True

  /- Instantiation: only `I :: K` holds. -/
  Inst := fun y x _w =>
    match y, x with
    | .I, .K => True
    | _,  _  => False

  /- Specialization: only `K ⊑ K` holds. -/
  Sub := fun x y _w =>
    match x, y with
    | .K, .K => True
    | _,  _  => False

  /- Individual classification -/
  ConcreteIndividual := fun x _w =>
    match x with
    | .I => True
    | .K => False

  AbstractIndividual := fun _x _w => False

  Endurant := fun x _w =>
    match x with
    | .I => True
    | .K => False

  Perdurant := fun _x _w => False

  /- Type classification (3.1) -/
  EndurantType := fun x _w =>
    match x with
    | .K => True
    | .I => False

  PerdurantType := fun _x _w => False

  /- Section 3.2 predicates: make `K` a rigid sortal Kind; everything else empty. -/
  Rigid := fun t _w =>
    match t with
    | .K => True
    | .I => False

  AntiRigid := fun _t _w => False
  SemiRigid := fun _t _w => False

  Sortal := fun t _w =>
    match t with
    | .K => True
    | .I => False

  NonSortal := fun _t _w => False

  Kind := fun t _w =>
    match t with
    | .K => True
    | .I => False

  SubKind := fun _t _w => False
  Role := fun _t _w => False
  Phase := fun _t _w => False

  SemiRigidSortal := fun _t _w => False
  Category := fun _t _w => False
  Mixin := fun _t _w => False
  PhaseMixin := fun _t _w => False
  RoleMixin := fun _t _w => False
}

attribute [simp] sig3_2 trivialFrame

/--
Note: `toUFOSignature3_1` is the coercion from `UFOSignature3_2` to its
Section 3.1 reduct, allowing us to reuse the earlier axioms unchanged.

Proof that `sig3_2` satisfies (a1) -/
theorem ax1_sig3_2 : ax_a1 sig3_2.toUFOSignature3_1 := by
  intro x w
  cases w
  cases x
  · -- K
    constructor
    · intro _
      refine ⟨(), trivial, ?_⟩
      refine ⟨Thing3_2.I, ?_⟩
      simp [sig3_2]
    · intro _
      simp [sig3_2]
  · -- I
    constructor
    · intro h
      simp [sig3_2] at h
    · intro h
      rcases h with ⟨v, _, ⟨y, hy⟩⟩
      cases v
      cases y <;> simp [sig3_2] at hy

/-- Proof that `sig3_2` satisfies (a2) -/
theorem ax2_sig3_2 : ax_a2 sig3_2.toUFOSignature3_1 := by
  intro x w
  cases w
  cases x with
  | K =>
      constructor
      · intro hInd
        -- Individual K is False, so anything follows
        simp [sig3_2] at hInd
      · intro hBox
        -- goal is Individual K (), i.e. False
        -- use hBox at the only world to get ¬∃y, y :: K, contradict I :: K
        have hNoInstAtW :
            ¬ ∃ y : Thing3_2, sig3_2.Inst y Thing3_2.K () :=
          by
            -- apply the box at w = ()
            have := hBox () (by trivial)
            -- this is exactly ¬∃y, Inst y K ()
            simpa [sig3_2] using this
        -- but I :: K holds
        exact hNoInstAtW ⟨Thing3_2.I, by simp [sig3_2]⟩
  | I =>
      constructor
      · intro hInd
        -- Individual I holds, prove □(¬∃y, y :: I)
        intro v hv
        cases v
        intro hEx
        rcases hEx with ⟨y, hy⟩
        cases y <;> simp [sig3_2] at hy
      · intro hBox
        -- goal is Individual I (), i.e. True
        simp [sig3_2]

/-- Proof that `sig3_2` satisfies (a3) -/
theorem ax3_sig3_2 : ax_a3 sig3_2.toUFOSignature3_1 := by
  intro x y w hInst
  cases w
  cases x <;> cases y
    <;> simp [sig3_2] at hInst ⊢

/-- Proof that `sig3_2` satisfies (a4) -/
theorem ax4_sig3_2 : ax_a4 sig3_2.toUFOSignature3_1 := by
  intro w
  cases w
  intro h
  rcases h with ⟨x, y, z, hx⟩
  cases x <;> cases y <;> cases z
    <;> simp [sig3_2] at hx

/-- Proof that `sig3_2` satisfies (a5) -/
theorem ax5_sig3_2 : ax_a5 sig3_2.toUFOSignature3_1 := by
  intro x y w
  cases w
  cases x <;> cases y
  · -- K ⊑ K
    constructor
    · -- (→)
      intro _hSub
      -- need: Type K ∧ Type K ∧ □(...)
      refine ⟨?_, ?_, ?_⟩
      · simp [sig3_2]          -- Type K
      · simp [sig3_2]          -- Type K
      · -- prove Box part
        intro v hv
        intro z hz
        exact hz               -- trivial implication
    · -- (←)
      intro h
      simp [sig3_2]
  · -- K ⊑ I (false)
    constructor <;> intro h <;> simp [sig3_2] at h
  · -- I ⊑ K (false)
    constructor <;> intro h <;> simp [sig3_2] at h
  · -- I ⊑ I (false)
    constructor <;> intro h <;> simp [sig3_2] at h

/-- Proof that `sig3_2` satisfies (a6) -/
theorem ax6_sig3_2 : ax_a6 sig3_2.toUFOSignature3_1 := by
  intro t1 t2 x w h
  cases w
  cases t1 <;> cases t2 <;> cases x
    <;> simp [sig3_2] at h ⊢

/-- Proof that `sig3_2` satisfies (a7) -/
theorem ax7_sig3_2 : ax_a7 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a8) -/
theorem ax8_sig3_2 : ax_a8 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a9) -/
theorem ax9_sig3_2 : ax_a9 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a10) -/
theorem ax10_sig3_2 : ax_a10 sig3_2.toUFOSignature3_1 := by
  intro x w
  cases w
  cases x <;> simp [sig3_2]

/-- Proof that `sig3_2` satisfies (a11) -/
theorem ax11_sig3_2 : ax_a11 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a12) -/
theorem ax12_sig3_2 : ax_a12 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a13) -/
theorem ax13_sig3_2 : ax_a13 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a14) -/
theorem ax14_sig3_2 : ax_a14 sig3_2.toUFOSignature3_1 := by
  intro x w
  cases w
  cases x <;> simp [sig3_2]

/-- Proof that `sig3_2` satisfies (a15) -/
theorem ax15_sig3_2 : ax_a15 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a16) -/
theorem ax16_sig3_2 : ax_a16 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a17) -/
theorem ax17_sig3_2 : ax_a17 sig3_2.toUFOSignature3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_2] at hx ⊢

/-- Proof that `sig3_2` satisfies (a18) -/
theorem ax18_sig3_2 : ax_a18 sig3_2 := by
  intro t w
  cases w
  cases t
  · -- K
    constructor
    · intro _
      refine ⟨?_, ?_⟩
      · simp [sig3_2]  -- EndurantType K
      · intro x hDia
        rcases hDia with ⟨v, hv, hx⟩
        cases v
        simp [sig3_2] at hx
        -- only possible instance is I
        intro v hv
        cases v
        exact hx
    · intro h
      simp [sig3_2] at h
      simp [sig3_2]
  · -- I
    constructor
    · intro h
      simp [sig3_2] at h
    · intro h
      simp [sig3_2] at h

/-- Proof that `sig3_2` satisfies (a19) -/
theorem ax19_sig3_2 : ax_a19 sig3_2 := by
  intro t w
  cases w
  cases t
  · -- t = K
    constructor
    · intro hAR
      simp [sig3_2] at hAR
    · intro hRHS
      -- show False, since AntiRigid K is False
      -- unpack RHS and refute using x := I
      rcases hRHS with ⟨hEnd, hCond⟩
      have hDia : S5Frame.Dia (F := sig3_2.F) (fun w' => sig3_2.Inst Thing3_2.I Thing3_2.K w') () := by
        refine ⟨(), trivial, ?_⟩
        simp [sig3_2]
      have hDiaNot := hCond Thing3_2.I hDia
      -- but ◇(¬ I :: K) is impossible in the 1-world model
      rcases hDiaNot with ⟨v, hv, hNot⟩
      cases v
      -- Inst I K () is True, so ¬Inst is False
      simp [sig3_2] at hNot
  · -- t = I
    constructor
    · intro hAR
      simp [sig3_2] at hAR
    · intro hRHS
      -- RHS contains EndurantType I, which is False
      rcases hRHS with ⟨hEnd, _⟩
      simp [sig3_2] at hEnd

/-- Proof that `sig3_2` satisfies (a20) -/
theorem ax20_sig3_2 : ax_a20 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

/-- Proof that `sig3_2` satisfies (a21) -/
theorem ax21_sig3_2 : ax_a21 sig3_2 := by
  intro x w hx
  cases w
  cases x
  · -- K not Endurant
    simp [sig3_2] at hx
  · -- I
    refine ⟨Thing3_2.K, ?_, ?_⟩
    · simp [sig3_2]
    · intro v hv
      cases v
      simp [sig3_2]

/-- Proof that `sig3_2` satisfies (a22) -/
theorem ax22_sig3_2 : ax_a22 sig3_2 := by
  intro k x w hkx
  cases w
  -- split on k and x; simplify hkx to kill impossible branches
  cases k <;> cases x
  · -- k=K, x=K : hkx is impossible because Inst K K is False
    simp [sig3_2] at hkx
  · -- k=K, x=I : the only nontrivial case (since Inst I K is True)
    -- need: ¬◇(∃ z, Kind z ∧ Inst I z ∧ z ≠ K)
    intro hDia
    rcases hDia with ⟨v, hvR, hEx⟩
    cases v
    rcases hEx with ⟨z, hKindz, hInstIz, hNe⟩
    cases z
    · -- z = K, but then z ≠ K is false
      simp [sig3_2] at hNe
    · -- z = I, but Kind I is false
      simp [sig3_2] at hKindz
  · -- k=I, x=K : hkx impossible because Kind I is False
    simp [sig3_2] at hkx
  · -- k=I, x=I : hkx impossible (this is the branch you were seeing)
    simp [sig3_2] at hkx

/-- Proof that `sig3_2` satisfies (a23) -/
theorem ax23_sig3_2 : ax_a23 sig3_2 := by
  intro t w
  cases w
  cases t
  · -- t = K
    constructor
    · intro hSortal
      refine ⟨?_, ?_⟩
      · simp [sig3_2]  -- EndurantType K
      · refine ⟨Thing3_2.K, ?_, ?_⟩
        · simp [sig3_2]  -- Kind K
        · -- Box: in the only world, Inst x K -> Inst x K
          intro v hv
          cases v
          intro x hx
          exact hx
    · intro hRHS
      -- RHS -> Sortal K (true in this model)
      simp [sig3_2]
  · -- t = I
    constructor
    · intro hSortal
      simp [sig3_2] at hSortal
    · intro hRHS
      -- RHS has EndurantType I, contradiction
      rcases hRHS with ⟨hEnd, _⟩
      simp [sig3_2] at hEnd

theorem ax24_sig3_2 : ax_a24 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax25_sig3_2 : ax_a25 sig3_2 := by
  intro w
  cases w
  simp [sig3_2]

theorem ax26_sig3_2 : ax_a26 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax27_sig3_2 : ax_a27 sig3_2 := by
  intro w
  cases w
  simp [sig3_2]

theorem ax28_sig3_2 : ax_a28 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax29_sig3_2 : ax_a29 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax30_sig3_2 : ax_a30 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax31_sig3_2 : ax_a31 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax32_sig3_2 : ax_a32 sig3_2 := by
  intro w
  cases w
  simp [sig3_2]

theorem ax33_sig3_2 : ax_a33 sig3_2 := by
  intro t w
  cases w
  cases t <;> simp [sig3_2]

theorem ax_instEndurant_sig3_2 :
  ax_instEndurant_of_EndurantType (Sig := sig3_2) := by
  intro t x w hEnd hInst
  cases w
  cases t <;> cases x <;> simp [sig3_2] at hEnd hInst ⊢

theorem ax_sub_kind_sortal_sig3_2 :
  ax_sub_of_kind_is_sortal (Sig := sig3_2) := by
  intro a k w hSub hKind
  cases w
  cases a <;> cases k <;> simp [sig3_2] at hSub hKind ⊢

theorem ax_nonSortal_up_sig3_2 :
  ax_nonSortal_upward (Sig := sig3_2) := by
  intro a b w hNon hSub
  cases w
  cases a <;> cases b <;> simp [sig3_2] at hNon hSub ⊢

theorem ax_kindStable_sig3_2 : ax_kindStable sig3_2 := by
  intro k w v hK hv
  cases w; cases v; cases k <;> simp [sig3_2] at hK ⊢

def model3_2 : UFOModel3_2 :=
{ toUFOSignature3_2 := sig3_2
  ax1 := ax1_sig3_2
  ax2 := ax2_sig3_2
  ax3 := ax3_sig3_2
  ax4 := ax4_sig3_2
  ax5 := ax5_sig3_2
  ax6 := ax6_sig3_2
  ax7 := ax7_sig3_2
  ax8 := ax8_sig3_2
  ax9 := ax9_sig3_2
  ax10 := ax10_sig3_2
  ax11 := ax11_sig3_2
  ax12 := ax12_sig3_2
  ax13 := ax13_sig3_2
  ax14 := ax14_sig3_2
  ax15 := ax15_sig3_2
  ax16 := ax16_sig3_2
  ax17 := ax17_sig3_2
  ax18 := ax18_sig3_2
  ax19 := ax19_sig3_2
  ax20 := ax20_sig3_2
  ax21 := ax21_sig3_2
  ax22 := ax22_sig3_2
  ax23 := ax23_sig3_2
  ax24 := ax24_sig3_2
  ax25 := ax25_sig3_2
  ax26 := ax26_sig3_2
  ax27 := ax27_sig3_2
  ax28 := ax28_sig3_2
  ax29 := ax29_sig3_2
  ax30 := ax30_sig3_2
  ax31 := ax31_sig3_2
  ax32 := ax32_sig3_2
  ax33 := ax33_sig3_2
  ax_instEndurant := ax_instEndurant_sig3_2
  ax_sub_kind_sortal := ax_sub_kind_sortal_sig3_2
  ax_nonSortal_up := ax_nonSortal_up_sig3_2
  ax_kindStable := ax_kindStable_sig3_2
}

end Model3_2
