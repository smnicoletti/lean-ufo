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
Under the current §3.10 relator, qua-individual, and mereology axioms, relators
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

So the current formalization proves `¬ Relator x w` for every thing and world.
-/
theorem no_relators_from_current_axioms
  (hA47 : ax_a47 Sig.toUFOSignature3_5)
  (hA50 : ax_a50 Sig.toUFOSignature3_5)
  (hA52 : ax_a52 Sig.toUFOSignature3_5)
  (hA41 : ax_a41 Sig.toUFOSignature3_3)
  (hA42 : ax_a42 Sig.toUFOSignature3_3)
  (hA70 : ax_a70 Sig)
  (hA73 : ax_a73 Sig)
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
Package-level corollary: any model satisfying the current §3.10 axiom class has
an empty relator extension at every world.
-/
theorem no_relators
  [UFOAxioms3_10 Sig] :
  ∀ (x : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Relator x w :=
by
  let h10 := (inferInstance : UFOAxioms3_10 Sig)
  let h9 := h10.toUFOAxioms3_9
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
    h10.ax70
    h10.ax73
    h10.ax74
    h10.ax79

/-
Possible weakenings around relators
-----------------------------------

The contradiction above is driven by the way ax73 classifies every overlapper of
a qua individual. If `p` is a qua-individual proper part of relator `x`, ordinary
mereology gives `Overlap x p`; ax73 then turns the whole relator `x` into an
externally dependent mode.

The following are candidate repair directions for future axiom variants. They
are intentionally recorded as comments rather than implemented alternatives.

1. Guard ax73 by `ExternallyDependentMode`.

   Instead of:

     Overlap z x ↔
       ExternallyDependentMode z ∧ InheresIn z y ∧ sameFoundation z x

   use a guarded characterization:

     ExternallyDependentMode z →
       (Overlap z x ↔ InheresIn z y ∧ sameFoundation z x)

   or include `ExternallyDependentMode x` as an explicit condition on the
   qua-individual being characterized. This preserves the idea that a qua
   individual gathers externally dependent modes without reclassifying every
   ordinary overlapper, including the containing relator.

2. Make ax73 one-way.

   A weaker ax73 could keep only one implication, for example:

     Overlap z x ∧ ExternallyDependentMode z →
       InheresIn z y ∧ sameFoundation z x

   or:

     ExternallyDependentMode z ∧ InheresIn z y ∧ sameFoundation z x →
       Overlap z x

   This avoids the relator-as-mode collapse but gives up the current full
   extensional characterization of qua individuals.

3. Avoid ordinary mereological parthood in ax79.

   Current ax79 uses `ProperPart y x` to say qua individuals are parts of a
   relator. Together with ax50, that immediately creates overlap between the
   relator and its qua-individual parts. A dedicated relation such as
   `HasQuaPart(y, x)` or a guarded parthood notion could express relator
   composition without triggering the ordinary overlap clause.

4. Do not weaken ax50 first.

   Weakening `Overlap x y ↔ ∃z (Part z x ∧ Part z y)` would avoid the immediate
   overlap step, but it changes a central mereological principle and would have
   broad effects outside relators.

5. Do not make relators modes unless this is intended.

   Weakening ax41 or ax42 would allow the proof to stop after deriving that a
   relator is an externally dependent mode. That repair would collapse the
   current relator/intrinsic-moment taxonomy and is therefore a much larger
   ontological change than a local ax73/ax79 adjustment.
-/

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
Package-level corollary: the current §3.10 package also forces mediation to be
empty.
-/
theorem no_mediates
  [UFOAxioms3_10 Sig] :
  ∀ (x y : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.Mediates x y w :=
  no_mediates_from_current_axioms (Sig := Sig)
    (no_relators (Sig := Sig))
    (inferInstance : UFOAxioms3_10 Sig).ax80

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
Package-level corollary: relator types are empty in the current §3.10 package.
-/
theorem no_relatorTypes
  [UFOAxioms3_10 Sig] :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.RelatorType t w :=
by
  let h10 := (inferInstance : UFOAxioms3_10 Sig)
  let h9 := h10.toUFOAxioms3_9
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
Package-level corollary: relator kinds are empty in the current §3.10 package.
-/
theorem no_relatorKinds
  [UFOAxioms3_10 Sig] :
  ∀ (t : Sig.Thing) (w : Sig.F.World),
    ¬ Sig.RelatorKind t w :=
by
  let h10 := (inferInstance : UFOAxioms3_10 Sig)
  let h9 := h10.toUFOAxioms3_9
  let h8 := h9.toUFOAxioms3_8
  let h7 := h8.toUFOAxioms3_7
  let h6 := h7.toUFOAxioms3_6
  let h5 := h6.toUFOAxioms3_5
  let h4 := h5.toUFOAxioms3_4
  exact no_relatorKinds_from_current_axioms (Sig := Sig)
    (no_relatorTypes (Sig := Sig))
    h4.ax45.2.2.2.1
