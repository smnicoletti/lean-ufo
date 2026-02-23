import LeanUfo.UFO.Core.Section3_1

universe u

/--
We construct a minimal S5 frame with a single world.

Intuition:
- There is exactly one possible world.
- The accessibility relation is trivial (every world sees every world).
- Modal operators collapse to ordinary truth at that world.

This simplifies the interpretation of □ and ◇ and
allows us to focus on structural consistency of
the UFO axioms in subsection 3.1.
-/

def trivialFrame : S5Frame :=
{ World := Unit,
  R := fun _ _ => True,
  refl := by intro _; trivial,
  symm := by intro _ _ _; trivial,
  trans := by intro _ _ _ _ _; trivial }

/--
Domain of discourse for the model of subsection 3.1.

We use the smallest possible non-trivial domain:

- `T` : a Type
- `I` : an Individual instantiating `T`

This is sufficient to satisfy:
- the instantiation axioms (a1, a2),
- the classification axioms (a7–a17),
- and makes specialization and incomparability trivial.
-/
inductive Thing3_1
| T   -- the unique Type
| I   -- the unique Individual
deriving DecidableEq

/--
Interpretation of the UFO signature for subsection 3.1 on the tiny domain `Thing3_1`
over the single-world S5 frame `trivialFrame`.

All predicates ignore the world parameter since the frame has one world (`Unit`).
-/
def sig3_1 : UFOSignature3_1 :=
{ F := trivialFrame
  Thing := Thing3_1

  /- Core ontology predicates -/
  Type_ := fun x _w =>
    match x with
    | .T => True
    | .I => False

  Individual := fun x _w =>
    match x with
    | .T => False
    | .I => True

  /-
  Up until now we have:
  Thing = {T, I}
  Type = {T}
  Individual = {I}

  Instantiation: only `I :: T` holds.
  -/
  Inst := fun y x _w =>
    match y, x with
    | .I, .T => True
    | _,  _  => False

  /- Specialization: only `T ⊑ T` holds (trivial preorder on Types). -/
  Sub := fun x y _w =>
    match x, y with
    | .T, .T => True
    | _,  _  => False

  /-
  Individual classification: I is concrete, there are no abstract Individuals.
  I is and Endurant, there are no Perdurants. -/
  ConcreteIndividual := fun x _w =>
    match x with
    | .I => True
    | .T => False

  AbstractIndividual := fun _x _w => False

  Endurant := fun x _w =>
    match x with
    | .I => True
    | .T => False

  Perdurant := fun _x _w => False

  /- Type classification: T is EndurantType. There are no PerdurantTypes -/
  EndurantType := fun x _w =>
    match x with
    | .T => True
    | .I => False

  PerdurantType := fun _x _w => False
}

namespace Model3_1

-- We will repeatedly case-split on the unique world and on Things.
-- These simp lemmas make unfolding the signature convenient.
attribute [simp] sig3_1 trivialFrame

/-- Proof that `sig3_1` satisfies axiom (a1). -/
theorem ax1_sig3_1 : ax_a1 sig3_1 := by
  intro x w
  cases w
  cases x
  · -- case x = T
    constructor
    · intro _
      -- prove ◇(∃ y, y :: T)
      refine ⟨(), ?_, ?_⟩
      · trivial
      · refine ⟨Thing3_1.I, ?_⟩
        simp [sig3_1]
    · intro h
      -- if ∃ y, Inst y T, then Type(T)
      simp [sig3_1]
  · -- case x = I
    constructor
    · intro h
      simp [sig3_1] at h
    · intro h
      rcases h with ⟨v, _hvR, hvEx⟩
      cases v
      rcases hvEx with ⟨y, hy⟩
      cases y <;> simp [sig3_1] at hy

/-- Proof that `sig3_1` satisfies axiom (a2). -/
theorem ax2_sig3_1 : ax_a2 sig3_1 := by
  intro x w
  cases w
  cases x
  · -- case x = T
    constructor
    · intro h
      -- Individual(T) is False
      simp [sig3_1] at h
    · intro hBox
      -- We need to prove Individual(T), i.e. False, so derive contradiction.
      have hNoInst : ¬ ∃ y : Thing3_1, (sig3_1.Inst y Thing3_1.T ()) := by
        -- apply the Box hypothesis at the only world
        have := hBox () (by trivial)
        -- `this` is exactly ¬∃y, Inst y T ()
        simpa [sig3_1] using this
      -- But Inst I T () holds, contradiction.
      apply hNoInst
      refine ⟨Thing3_1.I, ?_⟩
      simp [sig3_1]
  · -- case x = I
    constructor
    · intro _
      -- need to prove □(¬∃ y, y :: I)
      intro v hvR
      cases v
      intro hEx
      rcases hEx with ⟨y, hy⟩
      cases y <;> simp [sig3_1] at hy
    · intro _
      -- need to prove Individual(I)
      simp [sig3_1]

/-- Proof that `sig3_1` satisfies axiom (a3). -/
theorem ax3_sig3_1 : ax_a3 sig3_1 := by
  intro x y w hInst
  cases w
  cases x <;> cases y
    <;> simp [sig3_1] at hInst ⊢


/-- Proof that `sig3_1` satisfies axiom (a4). -/
theorem ax4_sig3_1 : ax_a4 sig3_1 := by
  intro w
  cases w
  intro h
  rcases h with ⟨x, y, z, hx⟩
  cases x <;> cases y <;> cases z <;>
    simp [sig3_1] at hx

/-- Proof that `sig3_1` satisfies axiom (a5). -/
theorem ax5_sig3_1 : ax_a5 sig3_1 := by
  intro x y w
  cases w
  cases x <;> cases y
  simp [sig3_1]
  intro v hv
  trivial
  simp [sig3_1]
  simp
  simp

/-- Proof that `sig3_1` satisfies axiom (a6). -/
theorem ax6_sig3_1 : ax_a6 sig3_1 := by
  intro t1 t2 x w h
  cases w
  cases t1 <;> cases t2 <;> cases x <;>
    simp [sig3_1] at h ⊢

/-- Proof that `sig3_1` satisfies axiom (a7). -/
theorem ax7_sig3_1 : ax_a7 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a8). -/
theorem ax8_sig3_1 : ax_a8 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a9). -/
theorem ax9_sig3_1 : ax_a9 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a10). -/
theorem ax10_sig3_1 : ax_a10 sig3_1 := by
  intro x w
  cases w
  cases x <;> simp [sig3_1]

/-- Proof that `sig3_1` satisfies axiom (a11). -/
theorem ax11_sig3_1 : ax_a11 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a12). -/
theorem ax12_sig3_1 : ax_a12 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢


/-- Proof that `sig3_1` satisfies axiom (a13). -/
theorem ax13_sig3_1 : ax_a13 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a14). -/
theorem ax14_sig3_1 : ax_a14 sig3_1 := by
  intro x w
  cases w
  cases x <;> simp [sig3_1]

/-- Proof that `sig3_1` satisfies axiom (a15). -/
theorem ax15_sig3_1 : ax_a15 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a16). -/
theorem ax16_sig3_1 : ax_a16 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Proof that `sig3_1` satisfies axiom (a17). -/
theorem ax17_sig3_1 : ax_a17 sig3_1 := by
  intro x w hx
  cases w
  cases x <;> simp [sig3_1] at hx ⊢

/-- Consistency witness: a concrete model of UFO subsection 3.1. -/
def model3_1 : UFOModel3_1 :=
{ toUFOSignature3_1 := sig3_1
  ax1 := ax1_sig3_1
  ax2 := ax2_sig3_1
  ax3 := ax3_sig3_1
  ax4 := ax4_sig3_1
  ax5 := ax5_sig3_1
  ax6 := ax6_sig3_1
  ax7 := ax7_sig3_1
  ax8 := ax8_sig3_1
  ax9 := ax9_sig3_1
  ax10 := ax10_sig3_1
  ax11 := ax11_sig3_1
  ax12 := ax12_sig3_1
  ax13 := ax13_sig3_1
  ax14 := ax14_sig3_1
  ax15 := ax15_sig3_1
  ax16 := ax16_sig3_1
  ax17 := ax17_sig3_1 }
