import LeanUfo.UFO.Core.Signature3_13
import LeanUfo.UFO.Core.Section3_12

universe u v

variable (Sig : UFOSignature3_13)

open UFOSignature3_13

/-
  §3.13 — Endurants and perdurants

  This section adds the manifestation relation connecting perdurants to
  endurants, the life-of relation, and the temporal meet relation between
  perdurants.
-/

/--
(a102), printed version

manifests(x, y) → Endurant(x) ∧ Perdurant(y)

Formalization note:
The paper prints the arguments of `Endurant` and `Perdurant` in this order.
We keep that reading as a standalone, non-packaged proposition so the textual
source remains traceable.

The packaged axiom below uses the corrected order, because the natural-language
explanation and the use of `manifests(z, y)` in (a103) both require the first
argument to be a perdurant and the second argument to be an endurant.
-/
def ax_a102_printed : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Manifests x y w →
      (Sig.Endurant x w ∧ Sig.Perdurant y w)

/--
(a102), corrected encoding

manifests(x, y) → Perdurant(x) ∧ Endurant(y)

Natural language:
Manifestation relates a perdurant manifestation to the endurant it manifests.

Formalization note:
This swaps the predicates printed in the paper's displayed formula. The swap is
forced by (a103), where `manifests(z, y)` occurs under `Perdurant(z)` and
`Endurant(y)`, and by the surrounding prose about the life of an endurant.
-/
def ax_a102 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Manifests x y w →
      (Sig.Perdurant x w ∧ Sig.Endurant y w)

/--
(a103)

lifeOf(x, y) ↔ Perdurant(x) ∧ Endurant(y) ∧
  ∀z (Overlap(z, x) ↔ Perdurant(z) ∧ manifests(z, y))

Natural language:
The life of an endurant is the perdurant that overlaps exactly the perdurants
that manifest that endurant.
-/
def ax_a103 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.LifeOf x y w ↔
      (Sig.Perdurant x w ∧
       Sig.Endurant y w ∧
       ∀ z : Sig.Thing,
         Sig.Overlap z x w ↔
           (Sig.Perdurant z w ∧ Sig.Manifests z y w))

/--
(a104)

meet(x, y) → Perdurant(x) ∧ Perdurant(y)

Natural language:
The temporal meet relation only holds between perdurants.
-/
def ax_a104 : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.Meet x y w →
      (Sig.Perdurant x w ∧ Sig.Perdurant y w)

/--
Axioms package for §3.13.

Extends §3.12 axioms with:
- (a102), using the corrected argument order documented above,
- (a103) life-of,
- (a104) temporal meet.

The printed version of (a102) is encoded separately as `ax_a102_printed` but is
not included in this package.
-/
class UFOAxioms3_13 (Sig : UFOSignature3_13) : Prop
  extends UFOAxioms3_12 Sig.toUFOSignature3_12 where

  -- §3.13 axioms
  ax102 : ax_a102 Sig
  ax103 : ax_a103 Sig
  ax104 : ax_a104 Sig
