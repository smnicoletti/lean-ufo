import LeanUfo.UFO.Core.Signature3_5
import LeanUfo.UFO.Core.Section3_4

universe u v

variable (Sig : UFOSignature3_5)

open UFOSignature3_5

/-
  §3.5 — Mereology

  This section introduces the core axioms of general extensional mereology
  used in the paper for subsequent definitions.
-/

/--
(a47)

Part(x, x)

Natural language:
Parthood is reflexive.
-/
def ax_a47 : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Part x x w

/--
(a48)

Part(x, y) ∧ Part(y, x) → x = y

Natural language:
Parthood is antisymmetric.
-/
def ax_a48 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Part x y w ∧ Sig.Part y x w →
      x = y

/--
(a49)

Part(x, y) ∧ Part(y, z) → Part(x, z)

Natural language:
Parthood is transitive.
-/
def ax_a49 : Prop :=
  ∀ (x y z : Sig.Thing) (w : Sig.F.World),
    Sig.Part x y w ∧ Sig.Part y z w →
      Sig.Part x z w

/--
(a50)

Overlap(x, y) ↔ ∃z (Part(z, x) ∧ Part(z, y))

Natural language:
Two things overlap exactly when they share a common part.
-/
def ax_a50 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Overlap x y w ↔
      ∃ z : Sig.Thing,
        Sig.Part z x w ∧
        Sig.Part z y w

/--
(a51)

¬Part(y, x) → ∃z (Part(z, y) ∧ ¬Overlap(z, x))

Natural language:
If `y` is not part of `x`, then `y` has a part that does not overlap `x`.
-/
def ax_a51 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Part y x w →
      ∃ z : Sig.Thing,
        Sig.Part z y w ∧
        ¬ Sig.Overlap z x w

/--
(a52)

ProperPart(x, y) ↔ Part(x, y) ∧ ¬Part(y, x)

Natural language:
Proper parthood is strict parthood.
-/
def ax_a52 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.ProperPart x y w ↔
      (Sig.Part x y w ∧ ¬ Sig.Part y x w)

/--
Axioms package for §3.5.

Extends §3.4 axioms with:
- (a47) reflexivity of parthood,
- (a48) antisymmetry of parthood,
- (a49) transitivity of parthood,
- (a50) definition of overlap by common part,
- (a51) strong supplementation,
- (a52) definition of proper part.
-/
class UFOAxioms3_5 (Sig : UFOSignature3_5) : Prop
  extends UFOAxioms3_4 Sig.toUFOSignature3_4 where

  -- §3.5 axioms
  ax47 : ax_a47 Sig
  ax48 : ax_a48 Sig
  ax49 : ax_a49 Sig
  ax50 : ax_a50 Sig
  ax51 : ax_a51 Sig
  ax52 : ax_a52 Sig
