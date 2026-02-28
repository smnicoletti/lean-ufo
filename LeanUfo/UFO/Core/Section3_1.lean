import LeanUfo.UFO.Core.Signature3_1
import LeanUfo.UFO.Modal.Basics
import LeanUfo.UFO.Modal.FirstOrder

universe u v

variable (Sig : UFOSignature3_1)

open UFOSignature3_1

/--
Axiom (a1):

Type(x) ↔ ◇(∃ y, y :: x)

A Thing x is a Type at world w
iff x is possibly instantiated.
-/
def ax_a1 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Type_ x w ↔
      S5Frame.Dia
        (fun w' => ∃ y : Sig.Thing, Sig.Inst y x w')
        w

/--
Axiom (a2):

Individual(x) ↔ □(¬∃ y, y :: x)

A Thing x is an Individual at world w
iff in every accessible world, nothing instantiates x.
-/
def ax_a2 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Individual x w ↔
      S5Frame.Box
        (fun w' => ¬ ∃ y : Sig.Thing, Sig.Inst y x w')
        w

/--
Axiom (a3):

x :: y → (Type(x) ∨ Individual(x))

If x instantiates y at world w,
then x is either a Type or an Individual at w.
-/
def ax_a3 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Inst x y w →
      (Sig.Type_ x w ∨ Sig.Individual x w)


/--
Axiom (a4):

¬∃ x y z, (Type(x) ∧ x :: y ∧ y :: z)

At no world w do there exist x, y, z such that
x is a Type at w, x instantiates y at w,
and y instantiates z at w.
-/
def ax_a4 : Prop :=
  ∀ (w : Sig.F.World),
    ¬ ∃ (x y z : Sig.Thing),
        Sig.Type_ x w ∧
        Sig.Inst x y w ∧
        Sig.Inst y z w

/-- Semantic duality: ¬◇ψ at w iff □(¬ψ) at w (Kripke semantics). Needed for next theorem. -/
theorem not_dia_iff_box_not
  {F : S5Frame} (ψ : F.World → Prop) (w : F.World) :
  (¬ S5Frame.Dia (F := F) ψ w) ↔
    S5Frame.Box (F := F) (fun v => ¬ ψ v) w :=
by
  constructor
  · intro h v hv
    intro hvψ
    exact h ⟨v, hv, hvψ⟩
  · intro h hdia
    rcases hdia with ⟨v, hv, hvψ⟩
    exact (h v hv) hvψ

/--
Theorem (t1):

Individual(x) ∨ Type(x)

Every Thing is either an Individual or a Type
at each world.
-/
theorem th_t1
  (hA1 : ax_a1 Sig) (hA2 : ax_a2 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Individual x w ∨ Sig.Type_ x w :=
by
  classical
  intro x w
  let ψ : Sig.F.World → Prop :=
    fun w' => ∃ y : Sig.Thing, Sig.Inst y x w'
  by_cases hDia : S5Frame.Dia (F := Sig.F) ψ w
  · right
    exact (hA1 x w).2 hDia
  · left
    have hBox :
      S5Frame.Box (F := Sig.F) (fun w' => ¬ ψ w') w :=
      (not_dia_iff_box_not (F := Sig.F) ψ w).1 hDia
    exact (hA2 x w).2 hBox

/--
Theorem (t2):

¬(Individual(x) ∧ Type(x))

No Thing is both an Individual and a Type
at any world.
-/
theorem th_t2
  (hA1 : ax_a1 Sig) (hA2 : ax_a2 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ¬ (Sig.Individual x w ∧ Sig.Type_ x w) :=
by
  intro x w h
  rcases h with ⟨hInd, hType⟩
  have hDia := (hA1 x w).1 hType
  have hBox := (hA2 x w).1 hInd
  rcases hDia with ⟨v, hvR, hvEx⟩
  exact (hBox v hvR) hvEx

/--
Axiom (a5):

x ⊑ y ↔
Type(x) ∧ Type(y) ∧
□(∀ z, z :: x → z :: y)

A type x specializes a type y at world w
iff x and y are Types at w and,
in every accessible world, every instance of x
is also an instance of y.
-/
def ax_a5 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Sub x y w ↔
      (Sig.Type_ x w ∧
       Sig.Type_ y w ∧
       S5Frame.Box
         (fun w' =>
            ∀ z : Sig.Thing,
              Sig.Inst z x w' →
              Sig.Inst z y w')
         w)

/--
Definition (d1): Proper specialization.

x ⊏ y  :=  (x ⊑ y) ∧ ¬(y ⊑ x)
-/
def ProperSub (Sig : UFOSignature3_1) (x y : Sig.Thing) (w : Sig.F.World) : Prop :=
  Sig.Sub x y w ∧ ¬ Sig.Sub y x w

/--
Theorem (t3):

x ⊑ y → (x ⊑ x ∧ y ⊑ y)

Specialization is quasi-reflexive.
-/
theorem th_t3
  (hA5 : ax_a5 Sig) :
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Sub x y w →
      (Sig.Sub x x w ∧ Sig.Sub y y w) :=
by
  intro x y w hSub
  have h := (hA5 x y w).mp hSub
  -- h : Type x w ∧ Type y w ∧ Box(...)
  rcases h with ⟨hTx, hTy, _⟩
  constructor
  ·
    -- prove x ⊑ x
    have hx := (hA5 x x w)
    apply hx.mpr
    constructor
    · exact hTx
    constructor
    · exact hTx
    ·
      intro v
      intro hv
      intro z
      intro hz
      exact hz
  ·
    -- prove y ⊑ y
    have hy := (hA5 y y w)
    apply hy.mpr
    constructor
    · exact hTy
    constructor
    · exact hTy
    ·
      intro v
      intro hv
      intro z
      intro hz
      exact hz

/--
Theorem (t4):

(x ⊑ y ∧ y ⊑ z) → (x ⊑ z)

Specialization is transitive.
-/
theorem th_t4
  (hA5 : ax_a5 Sig) :
  ∀ (x y z : Sig.Thing) (w : Sig.F.World),
    (Sig.Sub x y w ∧ Sig.Sub y z w) →
      Sig.Sub x z w :=
by
  intro x y z w hxy_yz
  rcases hxy_yz with ⟨hxy, hyz⟩

  -- unpack a5 for x ⊑ y
  have hxy' := (hA5 x y w).mp hxy
  rcases hxy' with ⟨hTx, hTy, hBox_xy⟩

  -- unpack a5 for y ⊑ z
  have hyz' := (hA5 y z w).mp hyz
  rcases hyz' with ⟨_, hTz, hBox_yz⟩

  -- prove x ⊑ z using a5 (→ direction)
  have hxz := (hA5 x z w)
  apply hxz.mpr
  constructor
  · exact hTx
  constructor
  · exact hTz
  ·
    -- Box condition: in every accessible world, instances of x are instances of z
    intro v
    intro hv
    intro t
    intro ht_x
    -- from x ⊑ y: t :: x → t :: y
    have ht_y : Sig.Inst t y v := (hBox_xy v hv) t ht_x
    -- from y ⊑ z: t :: y → t :: z
    have ht_z : Sig.Inst t z v := (hBox_yz v hv) t ht_y
    exact ht_z

/--
Axiom (a6):

If x instantiates both t₁ and t₂ at world w and t₁,t₂ are incomparable under ⊑,
then there exists a type t₃ such that x instantiates t₃ and either:
- t₁ ⊑ t₃ and t₂ ⊑ t₃ (common supertype), or
- t₃ ⊑ t₁ and t₃ ⊑ t₂ (common subtype).
-/
def ax_a6 : Prop :=
  ∀ (t1 t2 x : Sig.Thing) (w : Sig.F.World),
    (Sig.Inst x t1 w ∧
     Sig.Inst x t2 w ∧
     ¬ Sig.Sub t1 t2 w ∧
     ¬ Sig.Sub t2 t1 w) →
      ( (∃ t3 : Sig.Thing,
            Sig.Sub t1 t3 w ∧
            Sig.Sub t2 t3 w ∧
            Sig.Inst x t3 w)
        ∨
        (∃ t3 : Sig.Thing,
            Sig.Sub t3 t1 w ∧
            Sig.Sub t3 t2 w ∧
            Sig.Inst x t3 w) )

/--
Axiom (a7):

ConcreteIndividual(x) → Individual(x)

Every concrete individual is an individual.
-/
def ax_a7 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.ConcreteIndividual x w →
      Sig.Individual x w

/--
Axiom (a8):

AbstractIndividual(x) → Individual(x)

Every abstract individual is an individual.
-/
def ax_a8 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.AbstractIndividual x w →
      Sig.Individual x w

/--
Axiom (a9):

ConcreteIndividual(x) → ¬AbstractIndividual(x)

Concrete and abstract individuals are disjoint.
-/
def ax_a9 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.ConcreteIndividual x w →
      ¬ Sig.AbstractIndividual x w

/--
Axiom (a10):

Individual(x) ↔
ConcreteIndividual(x) ∨ AbstractIndividual(x)

Individuals are exactly the concrete or abstract individuals.
-/
def ax_a10 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Individual x w ↔
      (Sig.ConcreteIndividual x w ∨
       Sig.AbstractIndividual x w)

/--
Axiom (a11):

Endurant(x) → ConcreteIndividual(x)

Every endurant is a concrete individual.
-/
def ax_a11 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Endurant x w →
      Sig.ConcreteIndividual x w

/--
Axiom (a12):

Perdurant(x) → ConcreteIndividual(x)

Every perdurant is a concrete individual.
-/
def ax_a12 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Perdurant x w →
      Sig.ConcreteIndividual x w

/--
Axiom (a13):

Endurant(x) → ¬Perdurant(x)

Endurants and perdurants are disjoint.
-/
def ax_a13 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Endurant x w →
      ¬ Sig.Perdurant x w

/--
Axiom (a14):

ConcreteIndividual(x) ↔
Endurant(x) ∨ Perdurant(x)

Concrete individuals are exactly endurants or perdurants.
-/
def ax_a14 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.ConcreteIndividual x w ↔
      (Sig.Endurant x w ∨
       Sig.Perdurant x w)

/--
Axiom (a15):

EndurantType(x) → Type(x)

Every endurant type is a type.
-/
def ax_a15 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType x w →
      Sig.Type_ x w

/--
Axiom (a16):

PerdurantType(x) → Type(x)

Every perdurant type is a type.
-/
def ax_a16 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.PerdurantType x w →
      Sig.Type_ x w

/--
Axiom (a17):

EndurantType(x) → ¬PerdurantType(x)

Endurant types and perdurant types are disjoint.
-/
def ax_a17 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.EndurantType x w →
      ¬ Sig.PerdurantType x w

/--
A signature satisfies the axioms of §3.1.
-/
class UFOAxioms3_1 (Sig : UFOSignature3_1) : Prop where
  ax1  : ax_a1 Sig
  ax2  : ax_a2 Sig
  ax3  : ax_a3 Sig
  ax4  : ax_a4 Sig
  ax5  : ax_a5 Sig
  ax6  : ax_a6 Sig
  ax7  : ax_a7 Sig
  ax8  : ax_a8 Sig
  ax9  : ax_a9 Sig
  ax10 : ax_a10 Sig
  ax11 : ax_a11 Sig
  ax12 : ax_a12 Sig
  ax13 : ax_a13 Sig
  ax14 : ax_a14 Sig
  ax15 : ax_a15 Sig
  ax16 : ax_a16 Sig
  ax17 : ax_a17 Sig
