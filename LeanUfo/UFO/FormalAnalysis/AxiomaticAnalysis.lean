import LeanUfo.UFO.Core.Section3_10

universe u v

variable (Sig : UFOSignature3_10)

open UFOSignature3_10

/-
Axiomatic-analysis results.

These theorems are not additional UFO axioms. They record consequences of the
current mechanized axiom set, especially places where the encoding may be more
constraining than intended by the informal theory.
-/

/--
Under the printed §3.10 relator, qua-individual, and mereology axioms, relators
are impossible.

Sketch:
- ax79 makes every relator have a proper part `p`, and every proper part of a
  relator is a qua individual.
- ax74 gives a bearer `b` with `QuaIndividualOf p b`.
- ax52 turns `ProperPart p x` into `Part p x`; ax47 gives `Part p p`; ax50 then
  gives `Overlap x p`.
- ax73 says every overlapper of qua individual `p` is an externally dependent
  mode inhering in `b`, so the relator `x` itself is an externally dependent
  mode.
- ax70 and ax42 make `x` an intrinsic moment.
- ax41 forbids an entity from being both a relator and an intrinsic moment.

This historical result explains why the printed (a73) was replaced.
-/
theorem no_relators_from_current_axioms
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA41 : ax_a41 Sig.toUFOSignature3_3)
  (hA42 : ax_a42 Sig.toUFOSignature3_3)
  (hA70 : ax_a70 Sig)
  (hA73 : ax_a73_printed Sig)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Relator x w :=
by
  intro x w hRel
  rcases (hA79 x w).1 hRel with ⟨⟨p, hPPp⟩, hPairwise, _hClosure⟩
  have hQuaP : Sig.QuaIndividual p w :=
    (hPairwise p p ⟨hPPp, hPPp⟩).1
  rcases (hA74 p w).1 hQuaP with ⟨b, hQuaOfP⟩
  have hPartPX : Sig.Part p x w :=
    (hA52 p x w).1 hPPp |>.1
  have hOverlapXP : Sig.Overlap x p w :=
    (hA50 x p w).2 ⟨p, hPartPX, hA47 p w⟩
  have hEDM_X : Sig.ExternallyDependentMode x w :=
    (((hA73 p b w).1 hQuaOfP x).1 hOverlapXP).1
  have hModeX : Sig.Mode x w :=
    ((hA70 x w).1 hEDM_X).1
  have hIntrinsicX : Sig.IntrinsicMoment x w :=
    (hA42 x w).1 (Or.inl hModeX)
  exact hA41 w ⟨x, hRel, hIntrinsicX⟩

/--
The source of the relator contradiction is independent of ax79. Under the
printed ax73, a relator cannot have an ordinary proper part that is a qua
individual. Any ax79 repair that retains such a constituent therefore leaves
the contradiction intact.
-/
theorem no_relator_with_quaIndividual_properPart
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA41 : ax_a41 Sig.toUFOSignature3_3)
  (hA42 : ax_a42 Sig.toUFOSignature3_3)
  (hA70 : ax_a70 Sig)
  (hA73 : ax_a73_printed Sig)
  (hA74 : ax_a74 Sig) :
  ∀ (r q : Sig.Thing) (w : Sig.F.World),
    Sig.Relator r w →
      Sig.ProperPart q r w →
        Sig.QuaIndividual q w → False :=
by
  intro r q w hRel hPP hQua
  rcases (hA74 q w).1 hQua with ⟨bearer, hQuaOf⟩
  have hPartQR : Sig.Part q r w :=
    (hA52 q r w).1 hPP |>.1
  have hOverlapRQ : Sig.Overlap r q w :=
    (hA50 r q w).2 ⟨q, hPartQR, hA47 q w⟩
  have hEDM_R : Sig.ExternallyDependentMode r w :=
    (((hA73 q bearer w).1 hQuaOf r).1 hOverlapRQ).1
  have hModeR : Sig.Mode r w :=
    ((hA70 r w).1 hEDM_R).1
  have hIntrinsicR : Sig.IntrinsicMoment r w :=
    (hA42 r w).1 (Or.inl hModeR)
  exact hA41 w ⟨r, hRel, hIntrinsicR⟩

/--
If the surrounding taxonomy and mereology are retained, a relator with a
qua-individual proper part refutes the printed ax73.
-/
theorem relator_composition_refutes_current_ax73
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA41 : ax_a41 Sig.toUFOSignature3_3)
  (hA42 : ax_a42 Sig.toUFOSignature3_3)
  (hA70 : ax_a70 Sig)
  (hA74 : ax_a74 Sig) :
  ∀ (r q : Sig.Thing) (w : Sig.F.World),
    Sig.Relator r w →
      Sig.ProperPart q r w →
        Sig.QuaIndividual q w → ¬ ax_a73_printed Sig :=
by
  intro r q w hRel hPP hQua hA73
  exact no_relator_with_quaIndividual_properPart
    (Sig := Sig) hA47 hA50 hA52 hA41 hA42 hA70 hA73 hA74
    r q w hRel hPP hQua

/-
Selected ax73 repair and comparison experiment
-----------------------------------------------

Guizzardi's thesis uses a different axiomatization, but its account motivates
the formulas below: qua individuals are potentially complex externally
dependent modes, and relators are integral wholes composed of qua individuals.
The part-based characterization is now the active (a73). The guarded-overlap
characterization is retained as historical evidence for the comparison reported
in the paper.
-/

/-- Analysis name retained for the active part-based ax73. -/
def ax_a73_part_characterization : Prop := ax_a73 Sig

/--
Guarded-overlap formula retained from the comparison experiment. It restricts
the overlap characterization to entities already known to be externally
dependent modes. The outer conjuncts preserve the typing and bearer information
for the qua individual itself.
-/
def ax_a73_guarded_overlap : Prop :=
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    Sig.QuaIndividualOf x y w ↔
      (Sig.ExternallyDependentMode x w ∧
       Sig.InheresIn x y w ∧
       ∀ z : Sig.Thing,
         Sig.ExternallyDependentMode z w →
           (Sig.Overlap z x w ↔
             (Sig.InheresIn z y w ∧
             FoundationOf Sig z w = FoundationOf Sig x w)))

/--
Analysis-only package containing every section 3.10 assumption except ax73.

Keeping the shared background separate lets the historical comparison models
select an (a73) formula explicitly.
-/
class UFOAxioms3_10WithoutA73 (Sig : UFOSignature3_10) : Prop
    extends UFOAxioms3_9 Sig.toUFOSignature3_9 where
  ax69 : ax_a69 Sig
  ax70 : ax_a70 Sig
  ax71 : ax_a71 Sig
  ax72 : ax_a72 Sig
  ax74 : ax_a74 Sig
  ax75 : ax_a75 Sig
  ax76 : ax_a76 Sig
  ax77 : ax_a77 Sig
  ax78 : ax_a78 Sig
  ax79 : ax_a79 Sig
  ax80 : ax_a80 Sig
  axQuaIndividualOfEndurant : ax_quaIndividualOf_endurant (Sig := Sig)

/-- Analysis package using the selected part-based ax73 repair. -/
class UFOAxioms3_10PartRepair (Sig : UFOSignature3_10) : Prop
    extends UFOAxioms3_10WithoutA73 Sig where
  ax73Part : ax_a73_part_characterization Sig

/-- Comparison package retained for the guarded-overlap experiment. -/
class UFOAxioms3_10GuardedOverlapRepair (Sig : UFOSignature3_10) : Prop
    extends UFOAxioms3_10WithoutA73 Sig where
  ax73GuardedOverlap : ax_a73_guarded_overlap Sig

/-- Historical package using the printed overlap-based ax73. -/
class UFOAxioms3_10PrintedA73 (Sig : UFOSignature3_10) : Prop
    extends UFOAxioms3_10WithoutA73 Sig where
  ax73Printed : ax_a73_printed Sig

/--
The selected part-based repair preserves theorem (t31) without overlap axioms:
every part of a qua individual shares its foundation.
-/
theorem th_t31_part_characterization
  (hA73 : ax_a73_part_characterization Sig) :
  ∀ (x x' y : Sig.Thing) (w : Sig.F.World),
    (Sig.QuaIndividualOf x y w ∧ Sig.Part x' x w) →
      FoundationOf Sig x w = FoundationOf Sig x' w :=
by
  intro x x' y w h
  exact (((hA73 x y w).1 h.1 x').1 h.2).2.2.symm

/--
The guarded-overlap experiment proves the (t31) conclusion only for parts that
are independently known to be externally dependent modes. Its countermodel is
recorded in `FormalAnalysis.Historical.GuardedOverlapCountermodel`.
-/
theorem th_t31_guarded_overlap
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA73 : ax_a73_guarded_overlap Sig) :
  ∀ (x x' y : Sig.Thing) (w : Sig.F.World),
    (Sig.QuaIndividualOf x y w ∧
     Sig.Part x' x w ∧
     Sig.ExternallyDependentMode x' w) →
      FoundationOf Sig x w = FoundationOf Sig x' w :=
by
  intro x x' y w h
  rcases h with ⟨hQua, hPart, hEDM⟩
  have hOverlap : Sig.Overlap x' x w :=
    (hA50 x' x w).2 ⟨x', hA47 x' w, hPart⟩
  exact (((hA73 x y w).1 hQua).2.2 x' hEDM).1 hOverlap |>.2.symm

/--
Package-level corollary for the historical package with printed (a73).
-/
theorem no_relators
  [UFOAxioms3_10PrintedA73 Sig] :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Relator x w :=
by
  let h10 := (inferInstance : UFOAxioms3_10PrintedA73 Sig)
  let hBase := h10.toUFOAxioms3_10WithoutA73
  let h9 := hBase.toUFOAxioms3_9
  let h8 := h9.toUFOAxioms3_8
  let h7 := h8.toUFOAxioms3_7
  let h6 := h7.toUFOAxioms3_6
  let h5 := h6.toUFOAxioms3_5
  let h4 := h5.toUFOAxioms3_4
  let h3 := h4.toUFOAxioms3_3
  exact no_relators_from_current_axioms (Sig := Sig)
    h5.ax47
    h5.ax50
    h5.ax52
    h3.ax41
    h3.ax42
    hBase.ax70
    h10.ax73Printed
    hBase.ax74
    hBase.ax79

/-
First repair attempt: guard ax79 by distinct proper parts
--------------------------------------------------------

The following proposition records an analysis-only variant of ax79 suggested
by Giancarlo Guizzardi. It adds a distinctness guard to the pairwise
proper-part clause, blocking the original proof's use of the same proper part
twice. This variant is not part of `UFOAxioms3_10`.
-/

/--
Analysis-only ax79 variant whose pairwise clause applies only to distinct
proper parts of the relator.
-/
def ax_a79_distinct_guard : Prop :=
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Relator x w ↔
      (∃ y : Sig.Thing,
        Sig.ProperPart y x w)
      ∧
      (∀ y z : Sig.Thing,
        (Sig.ProperPart y x w ∧ Sig.ProperPart z x w ∧ y ≠ z) →
          (Sig.QuaIndividual y w ∧
           Sig.QuaIndividual z w ∧
           (FoundationOf Sig y w = FoundationOf Sig z w) ∧
           Sig.ExistentialDependence y z w ∧
           Sig.ExistentialDependence z y w))
      ∧
      (∀ y z : Sig.Thing,
        (Sig.ProperPart y x w ∧
         Sig.QuaIndividual z w ∧
         (FoundationOf Sig y w = FoundationOf Sig z w) ∧
         Sig.ExistentialDependence y z w ∧
         Sig.ExistentialDependence z y w) →
          Sig.ProperPart z x w)

/--
In general extensional mereology, every proper part has a distinct companion
that is also a proper part of the same whole. Strong supplementation supplies
the companion, while transitivity and overlap rule out the whole being part of
that companion.
-/
theorem properPart_has_distinct_companion
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5) :
  ∀ {p x : Sig.Thing} {w : Sig.F.World},
    Sig.ProperPart p x w →
      ∃ q : Sig.Thing, Sig.ProperPart q x w ∧ p ≠ q :=
by
  intro p x w hPPp
  rcases (hA52 p x w).1 hPPp with ⟨hpPartx, hNotPartxp⟩
  rcases hA51 p x w hNotPartxp with ⟨q, hqPartx, hNoOvqp⟩
  have hNotPartxq : ¬ Sig.Part x q w := by
    intro hxq
    have hpq : Sig.Part p q w := hA49 p x q w ⟨hpPartx, hxq⟩
    have hOvqp : Sig.Overlap q p w :=
      (hA50 q p w).2 ⟨p, hpq, hA47 p w⟩
    exact hNoOvqp hOvqp
  have hPPq : Sig.ProperPart q x w :=
    (hA52 q x w).2 ⟨hqPartx, hNotPartxq⟩
  have hpNeq : p ≠ q := by
    intro hpq
    subst q
    have hOvpp : Sig.Overlap p p w :=
      (hA50 p p w).2 ⟨p, hA47 p w, hA47 p w⟩
    exact hNoOvqp hOvpp
  exact ⟨q, hPPq, hpNeq⟩

/--
The companion supplied by strong supplementation can be retained together
with the stronger fact needed below: it does not overlap the original part.
-/
theorem properPart_has_disjoint_companion
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5) :
  ∀ {p x : Sig.Thing} {w : Sig.F.World},
    Sig.ProperPart p x w →
      ∃ q : Sig.Thing, Sig.ProperPart q x w ∧ ¬ Sig.Overlap q p w :=
by
  intro p x w hPPp
  rcases (hA52 p x w).1 hPPp with ⟨hpPartx, hNotPartxp⟩
  rcases hA51 p x w hNotPartxp with ⟨q, hqPartx, hNoOverlap⟩
  have hNotPartxq : ¬ Sig.Part x q w := by
    intro hxq
    have hpq : Sig.Part p q w := hA49 p x q w ⟨hpPartx, hxq⟩
    have hOverlap : Sig.Overlap q p w :=
      (hA50 q p w).2 ⟨p, hpq, hA47 p w⟩
    exact hNoOverlap hOverlap
  exact ⟨q, (hA52 q x w).2 ⟨hqPartx, hNotPartxq⟩, hNoOverlap⟩

/--
Theorem (t32) is independent of ax73, so it is preserved by the selected repair
and by the comparison formula without changing its statement.
-/
theorem th_t32_without_current_ax73
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79 Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.Relator x w →
      ∃ x' x'' y' y'' : Sig.Thing,
        Sig.QuaIndividualOf x' y' w ∧ Sig.QuaIndividualOf x'' y'' w :=
  th_t32 (Sig := Sig) hA47 hA49 hA50 hA51 hA52 hA74 hA79

/-- The selected part-based ax73 repair preserves theorem (t33) unchanged. -/
theorem th_t33_part_characterization
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA73 : ax_a73_part_characterization Sig)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79 Sig)
  (hA80 : ax_a80 Sig)
  (hQuaEnd : ax_quaIndividualOf_endurant (Sig := Sig)) :
  ∀ (x : Sig.Thing) (w : Sig.F.World), Sig.Relator x w →
    ∃ y z : Sig.Thing, y ≠ z ∧ Sig.Mediates x y w ∧ Sig.Mediates x z w :=
by
  intro x w hRel
  rcases (hA79 x w).1 hRel with ⟨⟨p, hPPp⟩, hPairwise, _⟩
  rcases properPart_has_disjoint_companion (Sig := Sig)
      hA47 hA49 hA50 hA51 hA52 hPPp with ⟨q, hPPq, hDisjoint⟩
  rcases hPairwise p q ⟨hPPp, hPPq⟩ with
    ⟨hQp, hQq, hFoundation, _hEDpq, _hEDqp⟩
  rcases (hA74 p w).1 hQp with ⟨y, hQOfp⟩
  rcases (hA74 q w).1 hQq with ⟨z, hQOfq⟩
  have hyNez : y ≠ z := by
    intro hyz
    have hPartQQ : Sig.Part q q w := hA47 q w
    have hQData := ((hA73 q z w).1 hQOfq q).1 hPartQQ
    have hPartQP : Sig.Part q p w :=
      ((hA73 p y w).1 hQOfp q).2
        ⟨hQData.1, by simpa [hyz] using hQData.2.1,
          hFoundation.symm⟩
    exact hDisjoint ((hA50 q p w).2 ⟨q, hA47 q w, hPartQP⟩)
  exact ⟨y, z, hyNez,
    (hA80 x y w).2 ⟨hRel, hQuaEnd p y w hQOfp,
      ⟨p, hQOfp, (hA52 p x w).1 hPPp |>.1⟩⟩,
    (hA80 x z w).2 ⟨hRel, hQuaEnd q z w hQOfq,
      ⟨q, hQOfq, (hA52 q x w).1 hPPq |>.1⟩⟩⟩

/-- The guarded-overlap comparison also preserves theorem (t33) unchanged. -/
theorem th_t33_guarded_overlap
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA73 : ax_a73_guarded_overlap Sig)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79 Sig)
  (hA80 : ax_a80 Sig)
  (hQuaEnd : ax_quaIndividualOf_endurant (Sig := Sig)) :
  ∀ (x : Sig.Thing) (w : Sig.F.World), Sig.Relator x w →
    ∃ y z : Sig.Thing, y ≠ z ∧ Sig.Mediates x y w ∧ Sig.Mediates x z w :=
by
  intro x w hRel
  rcases (hA79 x w).1 hRel with ⟨⟨p, hPPp⟩, hPairwise, _⟩
  rcases properPart_has_disjoint_companion (Sig := Sig)
      hA47 hA49 hA50 hA51 hA52 hPPp with ⟨q, hPPq, hDisjoint⟩
  rcases hPairwise p q ⟨hPPp, hPPq⟩ with
    ⟨hQp, hQq, hFoundation, _hEDpq, _hEDqp⟩
  rcases (hA74 p w).1 hQp with ⟨y, hQOfp⟩
  rcases (hA74 q w).1 hQq with ⟨z, hQOfq⟩
  have hyNez : y ≠ z := by
    intro hyz
    have hQData := (hA73 q z w).1 hQOfq
    have hOverlap : Sig.Overlap q p w :=
      ((hA73 p y w).1 hQOfp).2.2 q hQData.1 |>.2
        ⟨by simpa [hyz] using hQData.2.1, hFoundation.symm⟩
    exact hDisjoint hOverlap
  exact ⟨y, z, hyNez,
    (hA80 x y w).2 ⟨hRel, hQuaEnd p y w hQOfp,
      ⟨p, hQOfp, (hA52 p x w).1 hPPp |>.1⟩⟩,
    (hA80 x z w).2 ⟨hRel, hQuaEnd q z w hQOfq,
      ⟨q, hQOfq, (hA52 q x w).1 hPPq |>.1⟩⟩⟩

/-- Existential dependence is reflexive under its defining axiom (a63). -/
theorem existentialDependence_self
  (hA63 : ax_a63 Sig.toUFOSignature3_8) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    Sig.ExistentialDependence x x w :=
by
  intro x w
  apply (hA63 x x w).2
  intro w' _hAccessible hExists
  exact hExists

/--
Under the existing mereology and the definition of existential dependence,
the original and distinctness-guarded formulations of ax79 are equivalent.
The guard is therefore a presentational clarification, not a semantic repair,
within the current background theory.
-/
theorem ax_a79_iff_distinct_guard
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA63 : ax_a63 Sig.toUFOSignature3_8) :
  ax_a79 Sig ↔ ax_a79_distinct_guard Sig :=
by
  have currentPairwise_of_guarded :
      ∀ (x : Sig.Thing) (w : Sig.F.World),
        (∀ y z : Sig.Thing,
          (Sig.ProperPart y x w ∧ Sig.ProperPart z x w ∧ y ≠ z) →
            (Sig.QuaIndividual y w ∧
             Sig.QuaIndividual z w ∧
             FoundationOf Sig y w = FoundationOf Sig z w ∧
             Sig.ExistentialDependence y z w ∧
             Sig.ExistentialDependence z y w)) →
        ∀ y z : Sig.Thing,
          (Sig.ProperPart y x w ∧ Sig.ProperPart z x w) →
            (Sig.QuaIndividual y w ∧
             Sig.QuaIndividual z w ∧
             FoundationOf Sig y w = FoundationOf Sig z w ∧
             Sig.ExistentialDependence y z w ∧
             Sig.ExistentialDependence z y w) := by
    intro x w hGuarded y z hParts
    by_cases hNe : y ≠ z
    · exact hGuarded y z ⟨hParts.1, hParts.2, hNe⟩
    · have hEq : y = z := Classical.not_not.mp hNe
      subst z
      rcases properPart_has_distinct_companion (Sig := Sig)
          hA47 hA49 hA50 hA51 hA52 hParts.1 with ⟨q, hPPq, hyNeq⟩
      have hInfo := hGuarded y q ⟨hParts.1, hPPq, hyNeq⟩
      have hSelfED := existentialDependence_self (Sig := Sig) hA63 y w
      exact ⟨hInfo.1, hInfo.1, rfl, hSelfED, hSelfED⟩
  constructor
  · intro hCurrent x w
    constructor
    · intro hRel
      rcases (hCurrent x w).1 hRel with ⟨hExists, hPairwise, hClosure⟩
      refine ⟨hExists, ?_, hClosure⟩
      intro y z hParts
      exact hPairwise y z ⟨hParts.1, hParts.2.1⟩
    · intro hData
      rcases hData with ⟨hExists, hPairwise, hClosure⟩
      exact (hCurrent x w).2
        ⟨hExists, currentPairwise_of_guarded x w hPairwise, hClosure⟩
  · intro hGuarded x w
    constructor
    · intro hRel
      rcases (hGuarded x w).1 hRel with ⟨hExists, hPairwise, hClosure⟩
      exact ⟨hExists, currentPairwise_of_guarded x w hPairwise, hClosure⟩
    · intro hData
      rcases hData with ⟨hExists, hPairwise, hClosure⟩
      apply (hGuarded x w).2
      refine ⟨hExists, ?_, hClosure⟩
      intro y z hParts
      exact hPairwise y z ⟨hParts.1, hParts.2.1⟩

/--
The distinctness guard does not repair relator emptiness. Mereological strong
supplementation supplies a second, distinct proper part, so the guarded
pairwise clause still makes the first proper part a qua individual. The
original overlap-to-mode contradiction then resumes.

The explicit assumptions include the guarded proposition and exclude the
original `ax_a79` and `UFOAxioms3_10` package.
-/
theorem no_relators_from_distinct_guard_attempt
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA49 : ax_a49 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA51 : ax_a51 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA41 : ax_a41 Sig.toUFOSignature3_3)
  (hA42 : ax_a42 Sig.toUFOSignature3_3)
  (hA70 : ax_a70 Sig)
  (hA73 : ax_a73_printed Sig)
  (hA74 : ax_a74 Sig)
  (hA79 : ax_a79_distinct_guard Sig) :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Relator x w :=
by
  intro x w hRel
  rcases (hA79 x w).1 hRel with ⟨⟨p, hPPp⟩, hPairwise, _hClosure⟩
  rcases properPart_has_distinct_companion (Sig := Sig)
      hA47 hA49 hA50 hA51 hA52 hPPp with ⟨q, hPPq, hpNeq⟩
  have hQuaP : Sig.QuaIndividual p w :=
    (hPairwise p q ⟨hPPp, hPPq, hpNeq⟩).1
  rcases (hA74 p w).1 hQuaP with ⟨b, hQuaOfP⟩
  have hPartPX : Sig.Part p x w :=
    (hA52 p x w).1 hPPp |>.1
  have hOverlapXP : Sig.Overlap x p w :=
    (hA50 x p w).2 ⟨p, hPartPX, hA47 p w⟩
  have hEDM_X : Sig.ExternallyDependentMode x w :=
    (((hA73 p b w).1 hQuaOfP x).1 hOverlapXP).1
  have hModeX : Sig.Mode x w :=
    ((hA70 x w).1 hEDM_X).1
  have hIntrinsicX : Sig.IntrinsicMoment x w :=
    (hA42 x w).1 (Or.inl hModeX)
  exact hA41 w ⟨x, hRel, hIntrinsicX⟩

/--
Since `Mediates(x, y)` is defined by ax80 with `Relator(x)` as a conjunct, the
relator impossibility also empties mediation.
-/
theorem no_mediates_from_current_axioms
  (hNoRel : ∀ (x : Sig.Thing) (w : Sig.F.World), ¬ Sig.Relator x w)
  (hA80 : ax_a80 Sig) :
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Mediates x y w :=
by
  intro x y w hMed
  have hRel : Sig.Relator x w := ((hA80 x y w).1 hMed).1
  exact hNoRel x w hRel

/--
Package-level corollary: the historical package with printed (a73) also forces
mediation to be empty.
-/
theorem no_mediates
  [UFOAxioms3_10PrintedA73 Sig] :
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Mediates x y w :=
  no_mediates_from_current_axioms (Sig := Sig)
    (no_relators (Sig := Sig))
    (inferInstance : UFOAxioms3_10PrintedA73 Sig).toUFOAxioms3_10WithoutA73.ax80

/--
Relator types are impossible too. Ax44 says a relator type must be a genuine
type, and ax1 then supplies a possible instance. But every instance of a
relator type must be a relator, contradicting `no_relators`.
-/
theorem no_relatorTypes_from_current_axioms
  (hA1 : ax_a1 Sig.toUFOSignature3_1)
  (hA44RelatorType : ax_a44_relatorType Sig.toUFOSignature3_4)
  (hNoRel : ∀ (x : Sig.Thing) (w : Sig.F.World), ¬ Sig.Relator x w) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.RelatorType t w :=
by
  intro t w hRelatorType
  rcases (hA44RelatorType t w).1 hRelatorType with ⟨hType, hAllInstancesRelators⟩
  rcases (hA1 t w).1 hType with ⟨v, hAccessible, x, hInst⟩
  exact hNoRel x v (hAllInstancesRelators v hAccessible x hInst)

/--
Relator kinds are impossible because ax45 makes every relator kind a relator
type.
-/
theorem no_relatorKinds_from_current_axioms
  (hNoRelatorType :
    ∀ (t : Sig.Thing) (w : Sig.F.World), ¬ Sig.RelatorType t w)
  (hA45RelatorKind : ax_a45_relatorKind Sig.toUFOSignature3_4) :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.RelatorKind t w :=
by
  intro t w hRelatorKind
  have hRelatorType : Sig.RelatorType t w :=
    ((hA45RelatorKind t w).1 hRelatorKind).1
  exact hNoRelatorType t w hRelatorType

/--
Package-level corollary: relator types are empty in the historical package.
-/
theorem no_relatorTypes
  [UFOAxioms3_10PrintedA73 Sig] :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.RelatorType t w :=
by
  let h10 := (inferInstance : UFOAxioms3_10PrintedA73 Sig)
  let h9 := h10.toUFOAxioms3_10WithoutA73.toUFOAxioms3_9
  let h8 := h9.toUFOAxioms3_8
  let h7 := h8.toUFOAxioms3_7
  let h6 := h7.toUFOAxioms3_6
  let h5 := h6.toUFOAxioms3_5
  let h4 := h5.toUFOAxioms3_4
  let h3 := h4.toUFOAxioms3_3
  let h2 := h3.toUFOAxioms3_2
  let h1 := h2.toUFOAxioms3_1
  exact no_relatorTypes_from_current_axioms (Sig := Sig)
    h1.ax1
    h4.ax44.2.2.2.2.2.2.2.1
    (no_relators (Sig := Sig))

/--
Package-level corollary: relator kinds are empty in the historical package.
-/
theorem no_relatorKinds
  [UFOAxioms3_10PrintedA73 Sig] :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.RelatorKind t w :=
by
  let h10 := (inferInstance : UFOAxioms3_10PrintedA73 Sig)
  let h9 := h10.toUFOAxioms3_10WithoutA73.toUFOAxioms3_9
  let h8 := h9.toUFOAxioms3_8
  let h7 := h8.toUFOAxioms3_7
  let h6 := h7.toUFOAxioms3_6
  let h5 := h6.toUFOAxioms3_5
  let h4 := h5.toUFOAxioms3_4
  exact no_relatorKinds_from_current_axioms (Sig := Sig)
    (no_relatorTypes (Sig := Sig))
    h4.ax45.2.2.2.1
