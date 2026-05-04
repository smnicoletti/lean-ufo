import LeanUfo.UFO.Core.Section4
import LeanUfo.UFO.Models.Model3_13

universe u

namespace Model4

/-
  A concrete model for UFO §4 (Type structures).

  Design choice (minimal extension of Model3_13):
  we reuse the same tiny domain and single-world S5 frame from
  `Model3_13.sig3_13`, and interpret the §4 predicates exactly by the
  right-hand sides of axioms (a105)–(a108).

  This keeps the existing witness unchanged:
  - `K` is the only type,
  - `I` is the only individual,
  - `I :: K` is the only instantiation fact.

  Candidate-witness construction:
  the §4 predicates are new primitive symbols in the signature, but each §4
  axiom gives a biconditional definition-like constraint for one of them.
  For consistency, the simplest interpretation is therefore not to invent new
  independent structure, but to define each new primitive relation extensionally
  as exactly the condition that appears on the right-hand side of its axiom.

  With that choice, every §4 axiom reduces to `P ↔ P` after unfolding the
  concrete signature. The remaining case split only checks the inherited tiny
  domain:
  - `K` is a type and `I` is not,
  - `I` instantiates `K`,
  - `K` specializes only itself.
-/

/--
Signature interpretation for §4 extending the §3.13 concrete signature.

The inherited model already satisfies all axioms through §3.13. The fields
below only provide interpretations for the four new §4 relations. Each field is
defined by reusing the corresponding inherited predicates from
`Model3_13.sig3_13`; this avoids duplicating the whole inherited signature and
makes the candidate witness follow the displayed §4 formulas literally.
-/
def sig4 : UFOSignature4.{0,0} :=
{ toUFOSignature3_13 := Model3_13.sig3_13

  /-
    a105 witness:
    interpret disjointness of two entities as the right-hand side of (a105).
    In the tiny model this is false for `(K, K)`, because `I` is a common
    instance of `K`; it is also false whenever either argument is `I`, because
    `I` is not a type.
  -/
  IsDisjointWith := fun t t' w =>
    Model3_13.sig3_13.Type_ t w ∧
    Model3_13.sig3_13.Type_ t' w ∧
    ¬ ∃ x : Model3_13.sig3_13.Thing,
      Model3_13.sig3_13.Inst x t w ∧
      Model3_13.sig3_13.Inst x t' w

  /-
    a106 witness:
    interpret complete coverage directly as the coverage condition. For
    example, `K` is completely covered by `(K, K)` because its only instance
    `I` instantiates `K`. Most other triples hold vacuously when the first
    argument has no instances.
  -/
  IsCompletelyCoveredBy := fun t t' t'' w =>
    ∀ x : Model3_13.sig3_13.Thing,
      Model3_13.sig3_13.Inst x t w →
        Model3_13.sig3_13.Inst x t' w ∨
        Model3_13.sig3_13.Inst x t'' w

  /-
    a107 witness:
    interpret partitioning as the conjunction of the two previous
    right-hand-side conditions. This is deliberately written out instead of
    calling the fields above, so the signature value is self-contained and the
    later proof of (a107) reduces by unfolding `sig4`.
  -/
  IsPartitionedInto := fun t t' t'' w =>
    (∀ x : Model3_13.sig3_13.Thing,
      Model3_13.sig3_13.Inst x t w →
        Model3_13.sig3_13.Inst x t' w ∨
        Model3_13.sig3_13.Inst x t'' w) ∧
    (Model3_13.sig3_13.Type_ t' w ∧
     Model3_13.sig3_13.Type_ t'' w ∧
     ¬ ∃ x : Model3_13.sig3_13.Thing,
       Model3_13.sig3_13.Inst x t' w ∧
       Model3_13.sig3_13.Inst x t'' w)

  /-
    a108 witness:
    interpret categorization by the printed condition, with the final relation
    read as the existing specialization predicate `Sub`. In this model there
    are no type-level instances of `K` (`K`'s only instance is `I`, which is not
    a type and does not specialize anything), so most categorization claims are
    false because the first argument is not a type or because the specialization
    obligation fails on `I`.
  -/
  Categorizes := fun t1 t2 w =>
    Model3_13.sig3_13.Type_ t1 w ∧
    ∀ t3 : Model3_13.sig3_13.Thing,
      Model3_13.sig3_13.Inst t3 t1 w →
        Model3_13.sig3_13.Sub t3 t2 w
}

attribute [simp] sig4

/-- Proof that `sig4` satisfies (a105). -/
theorem ax105_sig4 : ax_a105 sig4 := by
  unfold ax_a105
  intro t t' w
  cases w
  cases t <;> cases t' <;>
    simp [sig4, Model3_13.sig3_13, Model3_12.sig3_12, Model3_11.sig3_11,
      Model3_10.sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7,
      Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3,
      Model3_2.sig3_2]

/-- Proof that `sig4` satisfies (a106). -/
theorem ax106_sig4 : ax_a106 sig4 := by
  unfold ax_a106
  intro t t' t'' w
  cases w
  cases t <;> cases t' <;> cases t'' <;>
    simp [sig4, Model3_13.sig3_13, Model3_12.sig3_12, Model3_11.sig3_11,
      Model3_10.sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7,
      Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3,
      Model3_2.sig3_2]

/-- Proof that `sig4` satisfies (a107). -/
theorem ax107_sig4 : ax_a107 sig4 := by
  unfold ax_a107
  intro t t' t'' w
  cases w
  cases t <;> cases t' <;> cases t'' <;>
    simp [sig4, Model3_13.sig3_13, Model3_12.sig3_12, Model3_11.sig3_11,
      Model3_10.sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7,
      Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3,
      Model3_2.sig3_2]

/-- Proof that `sig4` satisfies (a108). -/
theorem ax108_sig4 : ax_a108 sig4 := by
  unfold ax_a108
  intro t1 t2 w
  cases w
  cases t1 <;> cases t2 <;>
    simp [sig4, Model3_13.sig3_13, Model3_12.sig3_12, Model3_11.sig3_11,
      Model3_10.sig3_10, Model3_9.sig3_9, Model3_8.sig3_8, Model3_7.sig3_7,
      Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3,
      Model3_2.sig3_2]

/-- Consistency witness: a concrete model of UFO section 4. -/
instance : UFOAxioms4 sig4 :=
by
  classical

  have h13 : UFOAxioms3_13 sig4.toUFOSignature3_13 := by
    simpa [sig4] using (inferInstance : UFOAxioms3_13 Model3_13.sig3_13)

  refine
  { toUFOAxioms3_13 := h13
    -- §4 axioms
    ax105 := ax105_sig4
    ax106 := ax106_sig4
    ax107 := ax107_sig4
    ax108 := ax108_sig4
  }

end Model4
