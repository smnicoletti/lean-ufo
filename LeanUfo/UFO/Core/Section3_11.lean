import LeanUfo.UFO.Core.Signature3_11
import LeanUfo.UFO.Core.Section3_10
import Mathlib.Logic.ExistsUnique

universe u v

variable (Sig : UFOSignature3_11)

open UFOSignature3_11

/-
  §3.11 — Characterization

  This section adds the characterization relation.
-/

/--
(a81)

characterization(t, m) →
  EndurantType(t) ∧ MomentType(m) ∧
  ∀x (x :: t → ∃y (y :: m ∧ inheresIn(y, x))) ∧
  ∀z (z :: m → ∃!w (w :: t ∧ inheresIn(z, w)))

Natural language:
If an endurant type is characterized by a moment type, then every instance of
the endurant type has an inhering instance of the moment type, and every
instance of the moment type inheres in a unique instance of the endurant type.
-/
def ax_a81 : Prop :=
  ∀ (t m : Sig.Thing) (w : Sig.F.World),
    Sig.Characterization t m w →
      (Sig.EndurantType t w ∧
       Sig.MomentType m w ∧
       (∀ x : Sig.Thing,
         Sig.Inst x t w →
           ∃ y : Sig.Thing,
             Sig.Inst y m w ∧
             Sig.InheresIn y x w) ∧
       (∀ z : Sig.Thing,
         Sig.Inst z m w →
           ∃! bearer : Sig.Thing,
             Sig.Inst bearer t w ∧
             Sig.InheresIn z bearer w))

/--
(a82)

characterization(t, q) ∧ QualityType(q) →
  ∀x :: q → ∃!y :: t ∧ inheresIn(x, y)

Natural language:
If a quality type characterizes an endurant type, then every quality instance
inheres in a unique instance of the characterized endurant type.
-/
def ax_a82 : Prop :=
  ∀ (t q : Sig.Thing) (w : Sig.F.World),
    (Sig.Characterization t q w ∧ Sig.QualityType q w) →
      (∀ x : Sig.Thing,
        Sig.Inst x q w →
          ∃! y : Sig.Thing,
            Sig.Inst y t w ∧
            Sig.InheresIn x y w)

/--
Axioms package for §3.11.

Extends §3.10 axioms with:
- (a81) characterization by moment types,
- (a82) uniqueness of bearers for characterizing quality types.
-/
class UFOAxioms3_11 (Sig : UFOSignature3_11) : Prop
  extends UFOAxioms3_10 Sig.toUFOSignature3_10 where

  -- §3.11 axioms
  ax81 : ax_a81 Sig
  ax82 : ax_a82 Sig
