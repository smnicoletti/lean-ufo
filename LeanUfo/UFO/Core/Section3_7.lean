import LeanUfo.UFO.Core.Signature3_7
import LeanUfo.UFO.Core.Section3_6

universe u v

variable (Sig : UFOSignature3_7)

open UFOSignature3_7

/-
  §3.7 — Constitution

  This section adds the constitution vocabulary used in the paper.
-/

/--
(a56)

constitutedBy(x, y) →
  ((Endurant(x) ↔ Endurant(y)) ∧ (Perdurant(x) ↔ Perdurant(y)))

Natural language:
Constitution only holds between entities of the same ontological category.
-/
def ax_a56 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.ConstitutedBy x y w →
      ((Sig.Endurant x w ↔ Sig.Endurant y w) ∧
       (Sig.Perdurant x w ↔ Sig.Perdurant y w))

/--
(a57)

constitutedBy(x, y) ∧ (x :: x') ∧ (y :: y') ∧ Kind(x') ∧ Kind(y') → x' ≠ y'

Natural language:
Constitution holds only between instances of different kinds.
-/
def ax_a57 : Prop :=
  ∀ (x y x' y' : Sig.Thing) (w : Sig.F.World),
    (Sig.ConstitutedBy x y w ∧
     Sig.Inst x x' w ∧
     Sig.Inst y y' w ∧
     Sig.Kind x' w ∧
     Sig.Kind y' w) →
      x' ≠ y'

/--
(a58)

GCD(x', y') ↔ ∀x (x :: x' → ∃y (y :: y' ∧ constitutedBy(x, y)))

Natural language:
Type `x'` generically constitutionally depends on type `y'` exactly when every
instance of `x'` is constituted by some instance of `y'`.
-/
def ax_a58 : Prop :=
  ∀ (x' y' : Sig.Thing) (w : Sig.F.World),
    Sig.GenericConstitutionalDependence x' y' w ↔
      ∀ x : Sig.Thing,
        Sig.Inst x x' w →
          ∃ y : Sig.Thing,
            Sig.Inst y y' w ∧
            Sig.ConstitutedBy x y w

/--
(a59)

Constitution(x, x', y, y') ↔
  (x :: x') ∧ (y :: y') ∧ GCD(x', y') ∧ constitutedBy(x, y)

Natural language:
The type-level constitution relation holds exactly when the corresponding
instances are related by constitution and their types stand in generic
constitutional dependence.
-/
def ax_a59 : Prop :=
  ∀ (x x' y y' : Sig.Thing) (w : Sig.F.World),
    Sig.Constitution x x' y y' w ↔
      (Sig.Inst x x' w ∧
       Sig.Inst y y' w ∧
       Sig.GenericConstitutionalDependence x' y' w ∧
       Sig.ConstitutedBy x y w)

/--
(a60)

∀x,y Perdurant(x) ∧ constitutedBy(x, y) → □(ex(x) → constitutedBy(x, y))

Natural language:
For perdurants, constitution is necessary whenever the constituted entity
exists.
-/
def ax_a60 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    (Sig.Perdurant x w ∧ Sig.ConstitutedBy x y w) →
      Frame.Box (F := Sig.F)
        (fun w' => Sig.Ex x w' → Sig.ConstitutedBy x y w')
        w

/--
(a61)

constitutedBy(x, y) → ¬ constitutedBy(y, x)

Natural language:
Constitution is asymmetric.
-/
def ax_a61 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.ConstitutedBy x y w →
      ¬ Sig.ConstitutedBy y x w

/--
(t27)

¬ constitutedBy(x, x)

Natural language:
Constitution is non-reflexive.
-/
theorem th_t27
  (hA61 : ax_a61 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.ConstitutedBy x x w :=
by
  intro x w hConst
  exact (hA61 x x w hConst) hConst

/--
Axioms package for §3.7.

Extends §3.6 axioms with:
- (a56) same-category constitution,
- (a57) constitution between different kinds,
- (a58) generic constitutional dependence,
- (a59) constitution as the type-level relation,
- (a60) necessity of constitution for perdurants,
- (a61) asymmetry of constitution.
-/
class UFOAxioms3_7 (Sig : UFOSignature3_7) : Prop
  extends UFOAxioms3_6 Sig.toUFOSignature3_6 where

  -- §3.7 axioms
  ax56 : ax_a56 Sig
  ax57 : ax_a57 Sig
  ax58 : ax_a58 Sig
  ax59 : ax_a59 Sig
  ax60 : ax_a60 Sig
  ax61 : ax_a61 Sig
