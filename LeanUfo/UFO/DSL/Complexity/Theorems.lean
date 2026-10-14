import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Complexity.Compiler
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Complexity.Closure
import LeanUfo.UFO.DSL.Complexity.Tables
import LeanUfo.UFO.DSL.Complexity.Frontend
import LeanUfo.UFO.DSL.Complexity.Reuse
import LeanUfo.UFO.DSL.Checker.Axioms
import Mathlib.Tactic.Ring

/-!
# Public complexity theorem boundary

The module provides bounds for the counted executable components, including
data complexity for the fixed UFO registry. Separate results expose registry
and formula cost, following the distinction used by Vardi and Madelaine--Martin.
Script bounds cover corresponding native computations and their preparation
loop. `Complexity/Certification.lean` composes these components through the
shared frontend drivers into the source-to-workflow bound.
-/

namespace LeanUfo.UFO.DSL.Complexity

theorem closure_cost_cubic (n : Nat) (edge : Nat → Nat → Bool) :
    (warshallMatrixCosted n (fun i j => edge i.val j.val)).cost ≤
      10 * n ^ 3 + 7 * n ^ 2 + 3 * n :=
  warshallMatrixCosted_cost_le n _

theorem diagnostic_output_bound (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).value.items.size ≤ budget :=
  boundedEvidence_size_le_budget budget items

/-- Public multivariate bound for the actual short-circuiting source compiler. -/
theorem source_compiler_operational_bound (source : ModelSource) :
    compilerOperationalCost source ≤
      sourceCompilerPolynomial (sourceMetrics source) :=
  compilerOperationalCost_le source

/-- Scalar quartic corollary, derived from the explicit multivariate source
metrics only after all independently sized source components are included. -/
theorem source_compiler_scalar_polynomial_bound (source : ModelSource) :
    compilerOperationalCost source ≤
      511 * (sourceMetrics source).inputSize ^ 4 :=
  compilerOperationalCost_le_inputSize_pow4 source

/-- The frontend's guarded axiom-68 precheck has a source-size bound even
before model construction. The bound uses only the declared domain sizes; it
needs neither successful compilation nor positive domains. Other fields cost
two operations because they skip the search; this common upper bound still
allows the full search. -/
theorem source_field_precheck_scalar_bound
    (source : ModelSource) (tables : FactTables) (field : String) :
    (certificationFieldPrecheckCosted source.worlds.size source.things.size tables field).cost ≤
      124 * (sourceMetrics source).inputSize ^ 4 := by
  let n := (sourceMetrics source).inputSize
  have hn : 0 < n := sourceMetrics_inputSize_pos source
  have hw : source.worlds.size ≤ n := by
    simp only [n, SourceMetrics.inputSize, sourceMetrics]
    omega
  have ht : source.things.size ≤ n := by
    simp only [n, SourceMetrics.inputSize, sourceMetrics]
    omega
  have search := certificationFieldPrecheck_cost_le
    source.worlds.size source.things.size tables field
  have enlarged : source.worlds.size *
      (source.things.size * (source.things.size * (11 * source.things.size + 26) + 19) + 3) ≤
      n * (n * (n * (11 * n + 26) + 19) + 3) :=
    Nat.mul_le_mul hw (Nat.add_le_add_right
      (Nat.mul_le_mul ht (Nat.add_le_add_right
        (Nat.mul_le_mul ht (Nat.add_le_add_right (Nat.mul_le_mul_left 11 ht) 26)) 19)) 3)
  have expanded : 2 * (n * (n * (n * (11 * n + 26) + 19) + 3)) + 6 =
      22 * n ^ 4 + 52 * n ^ 3 + 38 * n ^ 2 + 6 * n + 6 := by ring
  have bounded := search.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 enlarged) 6)
  rw [expanded] at bounded
  have first : n ≤ n ^ 4 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right hn (show 1 ≤ 4 by omega)
  have square : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by omega)
  have cube : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by omega)
  change _ ≤ 124 * n ^ 4
  omega

/-- Representative per-axiom operational bound. The complete fixed-registry
result below composes this bound with the other 112 concrete entry bounds. -/
theorem axiom9_operational_bound (M : FiniteModel4) :
    (Checker.checkAx9Costed M).cost ≤
      M.thingCount * (M.worldCount * 21 + 2) :=
  Checker.checkAx9Costed_cost_le M

theorem axioms1_to_2_registry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms1To2Costed M).cost ≤ 2 *
      (M.thingCount * (M.worldCount *
        (M.worldCount * (M.thingCount * 13 + 2) +
          M.worldCount * (M.thingCount * 13 + 3) + 5) + 2) + 3) :=
  Checker.checkAxioms1To2Costed_cost_le M

theorem axiom3_operational_bound (M : FiniteModel4) :
    (Checker.checkAx3Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * (M.worldCount * (M.thingCount * 13 + 2)) + 17) + 2) + 2) :=
  Checker.checkAx3Costed_cost_le M

theorem axiom4_operational_bound (M : FiniteModel4) :
    (Checker.checkAx4Costed M).cost ≤ M.worldCount *
      (M.thingCount * (M.thingCount *
        (M.thingCount * (M.worldCount * (M.thingCount * 13 + 2) + 27) + 2) + 2) + 2) :=
  Checker.checkAx4Costed_cost_le M

theorem axiom5_operational_bound (M : FiniteModel4) :
    (Checker.checkAx5Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (2 * (M.worldCount * (M.thingCount * 13 + 2)) +
          M.worldCount * (M.thingCount * 26 + 2) + 17) + 2) + 2) :=
  Checker.checkAx5Costed_cost_le M

theorem axiom6_operational_bound (M : FiniteModel4) :
    (Checker.checkAx6Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (74 * M.thingCount + 54) + 2) + 2) + 2) :=
  Checker.checkAx6Costed_cost_le M

/-- Complete operational result for the first seventeen registered axioms. -/
theorem axioms1_to_17_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms1To17Costed M).cost ≤ Checker.axioms1To17CostBound M :=
  Checker.checkAxioms1To17Costed_cost_le M

/-- Operational bound for the ordered eleven-check slice, axioms 7 through 17. -/
theorem axioms7_to_17_registry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms7To17Costed M).cost ≤
      11 * (M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 13 + 2) + 29) + 2) + 3) :=
  Checker.checkAxioms7To17Costed_cost_le M

/--
Operational bound for the first modal-rigidity axiom.  Its semantic soundness
theorem is separate: this result only bounds the actual counted
thing/world scans and their short-circuiting Boolean composition.
-/
theorem axiom18_operational_bound (M : FiniteModel4) :
    (Checker.checkAx18Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (26 * M.worldCount + 4) + 21) + 2) :=
  Checker.checkAx18Costed_cost_le M

theorem axiom19_operational_bound (M : FiniteModel4) :
    (Checker.checkAx19Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (27 * M.worldCount + 4) + 21) + 2) :=
  Checker.checkAx19Costed_cost_le M

theorem axiom20_operational_bound (M : FiniteModel4) :
    (Checker.checkAx20Costed M).cost ≤
      M.thingCount * (M.worldCount * 40 + 2) :=
  Checker.checkAx20Costed_cost_le M

theorem axiom21_operational_bound (M : FiniteModel4) :
    (Checker.checkAx21Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (13 * M.worldCount + 11) + 12) + 2) :=
  Checker.checkAx21Costed_cost_le M

theorem axiom22_operational_bound (M : FiniteModel4) :
    (Checker.checkAx22Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 24 + 2) + 25) + 2) + 2) :=
  Checker.checkAx22Costed_cost_le M

theorem axiom23_operational_bound (M : FiniteModel4) :
    (Checker.checkAx23Costed M).cost ≤ M.thingCount *
      (M.worldCount *
        (M.thingCount * (M.worldCount * (M.thingCount * 26 + 2) + 11) + 21) + 2) :=
  Checker.checkAx23Costed_cost_le M

/-- Direct classification equivalence used by axioms 29--31. -/
theorem classification_iff_and_operational_bound (M : FiniteModel4) (left first second) :
    (Checker.checkUnaryIffAndCosted M left first second).cost ≤
      M.thingCount * (M.worldCount * 29 + 2) :=
  Checker.checkUnaryIffAndCosted_cost_le M left first second

/-- Negated classification equivalence used by axiom 24. -/
theorem classification_iff_and_not_operational_bound (M : FiniteModel4) (left first second) :
    (Checker.checkUnaryIffAndNotCosted M left first second).cost ≤
      M.thingCount * (M.worldCount * 30 + 2) :=
  Checker.checkUnaryIffAndNotCosted_cost_le M left first second

/-- Disjunction/conjunction classification equivalence used by axioms 26, 28, and 33. -/
theorem classification_iff_or_and_operational_bound (M : FiniteModel4)
    (leftA leftB rightA rightB) :
    (Checker.checkUnaryIffOrAndCosted M leftA leftB rightA rightB).cost ≤
      M.thingCount * (M.worldCount * 38 + 2) :=
  Checker.checkUnaryIffOrAndCosted_cost_le M leftA leftB rightA rightB

/-- World-first disjointness used by axioms 25, 27, 32, 35, 37–39, 41, and 85. -/
theorem classification_world_first_disjoint_operational_bound (M : FiniteModel4)
    (left right) :
    (Checker.checkWorldFirstDisjointCosted M left right).cost ≤
      M.worldCount * (M.thingCount * 20 + 2) :=
  Checker.checkWorldFirstDisjointCosted_cost_le M left right

/--
Operational bound for the delayed 16-check registry slice.  The factor 16 is
the explicit registry size. Each visited entry adds three operations for the
loop test, array read, and result test in `checkRegistryCosted`.
-/
theorem axioms18_to_33_registry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms18To33Costed M).cost ≤
      16 * (Checker.axioms18To33PerCheckBound M + 3) :=
  Checker.checkAxioms18To33Costed_cost_le M

/-- The two-thing bridge bound includes the costs supplied by all three predicates. -/
theorem two_things_worlds_bridge_operational_bound (M : FiniteModel4)
    (first second consequent :
      Fin M.thingCount → Fin M.thingCount → Fin M.worldCount → Costed Bool)
    (firstBound secondBound consequentBound : Nat)
    (hf : ∀ a b w, (first a b w).cost ≤ firstBound)
    (hs : ∀ a b w, (second a b w).cost ≤ secondBound)
    (hc : ∀ a b w, (consequent a b w).cost ≤ consequentBound) :
    (Checker.checkTwoThingsWorldsImpCosted M first second consequent).cost ≤
      M.thingCount * (M.thingCount *
        (M.worldCount * (firstBound + secondBound + consequentBound + 5) + 2) + 2) :=
  Checker.checkTwoThingsWorldsImpCosted_cost_le M first second consequent
    firstBound secondBound consequentBound hf hs hc

/-- Concrete quadratic bound for the production quality uniqueness predicate. -/
theorem quality_predicate_operational_bound (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (Checker.qualityBCosted M x w).cost ≤
      M.thingCount * (M.thingCount * 25 + 23) :=
  Checker.qualityBCosted_cost_le M x w

theorem axiom34_operational_bound (M : FiniteModel4) :
    (Checker.checkAx34Costed M).cost ≤
      M.thingCount * (M.worldCount * 29 + 2) :=
  Checker.checkAx34Costed_cost_le M

theorem axiom36_operational_bound (M : FiniteModel4) :
    (Checker.checkAx36Costed M).cost ≤
      M.thingCount * (M.worldCount * 38 + 2) :=
  Checker.checkAx36Costed_cost_le M

theorem axiom42_operational_bound (M : FiniteModel4) :
    (Checker.checkAx42Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (M.thingCount * 25 + 23) + 21) + 2) :=
  Checker.checkAx42Costed_cost_le M

theorem axiom43_operational_bound (M : FiniteModel4) :
    (Checker.checkAx43Costed M).cost ≤ M.worldCount *
      (M.thingCount * (M.thingCount * (M.thingCount * 25 + 23) + 12) + 2) :=
  Checker.checkAx43Costed_cost_le M

/--
Axiom 44 keeps the nine direct leaves separate from its counted quality
uniqueness leaf; `ax44CostBound` is their heterogeneous registry sum.
-/
theorem axiom44_operational_bound (M : FiniteModel4) :
    (Checker.checkAx44Costed M).cost ≤ Checker.ax44CostBound M :=
  Checker.checkAx44Costed_cost_le M

/-- Six delayed, equal-cost kind/type correspondence checks in axiom 45. -/
theorem axiom45_operational_bound (M : FiniteModel4) :
    (Checker.checkAx45Costed M).cost ≤
      6 * (M.thingCount * (M.worldCount * 29 + 2) + 3) :=
  Checker.checkAx45Costed_cost_le M

/-- Concrete nested witness-search bound for axiom 46. -/
theorem axiom46_operational_bound (M : FiniteModel4) :
    (Checker.checkAx46Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 67 + 2) + 12) + 2) :=
  Checker.checkAx46Costed_cost_le M

/-- Reflexive parthood checks coordinate equality and skips the table read. -/
theorem axiom47_operational_bound (M : FiniteModel4) :
    (Checker.checkAx47Costed M).cost ≤
      M.thingCount * (M.worldCount * 4 + 2) :=
  Checker.checkAx47Costed_cost_le M

/-- Antisymmetry scans two thing coordinates and one world coordinate. -/
theorem axiom48_operational_bound (M : FiniteModel4) :
    (Checker.checkAx48Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 32 + 2) + 2) :=
  Checker.checkAx48Costed_cost_le M

/-- Transitivity adds the third explicit thing coordinate. -/
theorem axiom49_operational_bound (M : FiniteModel4) :
    (Checker.checkAx49Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 44 + 2) + 2) + 2) :=
  Checker.checkAx49Costed_cost_le M

/-- Overlap equivalence includes its concrete existential common-part scan. -/
theorem axiom50_operational_bound (M : FiniteModel4) :
    (Checker.checkAx50Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 29 + 17) + 2) + 2) :=
  Checker.checkAx50Costed_cost_le M

/-- Weak supplementation includes its negated-overlap witness scan. -/
theorem axiom51_operational_bound (M : FiniteModel4) :
    (Checker.checkAx51Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 30 + 18) + 2) + 2) :=
  Checker.checkAx51Costed_cost_le M

/-- Proper parthood compares a direct read with two guarded part queries. -/
theorem axiom52_operational_bound (M : FiniteModel4) :
    (Checker.checkAx52Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 43 + 2) + 2) :=
  Checker.checkAx52Costed_cost_le M

/-- Axiom 53's source counter charges its generic dependence scan twice.
Native compilation can share identical calls; see `Complexity/Queries.lean`. -/
theorem axiom53_operational_bound (M : FiniteModel4) :
    (Checker.checkAx53Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * Checker.genericFunctionalDependenceBound M + 4) + 2) +
        2) :=
  Checker.checkAx53Costed_cost_le M

/-- Axiom 54's source counter charges its individual dependence predicate twice. -/
theorem axiom54_operational_bound (M : FiniteModel4) :
    (Checker.checkAx54Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * Checker.individualFunctionalDependenceBound M + 4) + 2) +
        2) + 2) + 2) :=
  Checker.checkAx54Costed_cost_le M

/-- Axiom 55 additionally charges the proper-part guard on both sides. -/
theorem axiom55_operational_bound (M : FiniteModel4) :
    (Checker.checkAx55Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * Checker.functionalComponentBound M + 4) + 2) + 2) +
        2) + 2) :=
  Checker.checkAx55Costed_cost_le M

theorem axiom56_operational_bound (M : FiniteModel4) :
    (Checker.checkAx56Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 52 + 2) + 2) :=
  Checker.checkAx56Costed_cost_le M

theorem axiom57_operational_bound (M : FiniteModel4) :
    (Checker.checkAx57Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 58 + 2) + 2) + 2) + 2) :=
  Checker.checkAx57Costed_cost_le M

/-- Axiom 58's source counter charges its generic constitutional scan twice. -/
theorem axiom58_operational_bound (M : FiniteModel4) :
    (Checker.checkAx58Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * Checker.genericConstitutionalDependenceBound M + 4) +
          2) + 2) :=
  Checker.checkAx58Costed_cost_le M

/-- Axiom 59's source counter charges the complete constitution predicate twice. -/
theorem axiom59_operational_bound (M : FiniteModel4) :
    (Checker.checkAx59Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * Checker.constitutionBound M + 4) + 2) + 2) + 2) + 2) :=
  Checker.checkAx59Costed_cost_le M

theorem axiom60_operational_bound (M : FiniteModel4) :
    (Checker.checkAx60Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.worldCount * 23 + 24) + 2) + 2) :=
  Checker.checkAx60Costed_cost_le M

theorem axiom61_operational_bound (M : FiniteModel4) :
    (Checker.checkAx61Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 27 + 2) + 2) :=
  Checker.checkAx61Costed_cost_le M

/-- The constant body is free, but axiom 62 still charges both finite scans. -/
theorem axiom62_operational_bound (M : FiniteModel4) :
    (Checker.checkAx62Costed M).cost ≤ M.thingCount * (M.worldCount * 2 + 2) :=
  Checker.checkAx62Costed_cost_le M

theorem axiom63_operational_bound (M : FiniteModel4) :
    (Checker.checkAx63Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * Checker.existentialDependenceBound M + 4) + 2) + 2) :=
  Checker.checkAx63Costed_cost_le M

theorem axiom64_operational_bound (M : FiniteModel4) :
    (Checker.checkAx64Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * Checker.existentialIndependenceBound M + 4) + 2) + 2) :=
  Checker.checkAx64Costed_cost_le M

theorem axiom65_operational_bound (M : FiniteModel4) :
    (Checker.checkAx65Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (Checker.existentialDependenceBound M + 15) + 2) + 2) :=
  Checker.checkAx65Costed_cost_le M

theorem axiom66_operational_bound (M : FiniteModel4) :
    (Checker.checkAx66Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 13 + 2) + 33) + 2) + 2) :=
  Checker.checkAx66Costed_cost_le M

theorem axiom67_operational_bound (M : FiniteModel4) :
    (Checker.checkAx67Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 28 + 2) + 2) + 2) :=
  Checker.checkAx67Costed_cost_le M

/--
The production axiom-68 checker charges both the cubic Warshall construction
and its subsequent short-circuiting uniqueness scan.  This is an operational
bound for one executable, not a recurrence attached to an abstract surrogate.
-/
theorem axiom68_operational_bound (M : FiniteModel4) :
    (Checker.checkAx68Costed M).cost ≤ Checker.checkAx68CostBound M :=
  Checker.checkAx68Costed_cost_le M

/-- Axiom 69 charges both evaluations of its external-dependence operand. -/
theorem axiom69_operational_bound (M : FiniteModel4) :
    (Checker.checkAx69Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (2 * Checker.externallyDependentBound M + 4) + 2) + 2) :=
  Checker.checkAx69Costed_cost_le M

/-- Axiom 70 charges both complete mode-and-dependent-witness searches. -/
theorem axiom70_operational_bound (M : FiniteModel4) :
    (Checker.checkAx70Costed M).cost ≤ M.thingCount *
      (M.worldCount * (2 * Checker.externallyDependentModeBound M + 4) + 2) :=
  Checker.checkAx70Costed_cost_le M

theorem axiom71_operational_bound (M : FiniteModel4) :
    (Checker.checkAx71Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.externallyDependentModeBound M + 33) + 2) + 2) :=
  Checker.checkAx71Costed_cost_le M

/-- Axiom 72 charges both its mode witness search and founded-by uniqueness scan. -/
theorem axiom72_operational_bound (M : FiniteModel4) :
    (Checker.checkAx72Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.externallyDependentModeBound M +
        Checker.existsUniqueFoundedByBound M + 4) + 2) :=
  Checker.checkAx72Costed_cost_le M

/-- Axiom 73 includes the full nested part/classification/foundation computation. -/
theorem axiom73_operational_bound (M : FiniteModel4) :
    (Checker.checkAx73Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax73PartsBound M + 15) + 2) + 2) :=
  Checker.checkAx73Costed_cost_le M

theorem axiom74_operational_bound (M : FiniteModel4) :
    (Checker.checkAx74Costed M).cost ≤ M.thingCount *
      (M.worldCount * (2 * Checker.quaIndividualExistsBound M + 4) + 2) :=
  Checker.checkAx74Costed_cost_le M

theorem axiom75_operational_bound (M : FiniteModel4) :
    (Checker.checkAx75Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.quaIndividualExistsBound M +
        Checker.externallyDependentModeBound M + 4) + 2) :=
  Checker.checkAx75Costed_cost_le M

theorem axiom76_operational_bound (M : FiniteModel4) :
    (Checker.checkAx76Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 28 + 2) + 2) + 2) :=
  Checker.checkAx76Costed_cost_le M

theorem axiom77_operational_bound (M : FiniteModel4) :
    (Checker.checkAx77Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.existsUniqueFoundedByBound M + 12) + 2) :=
  Checker.checkAx77Costed_cost_le M

theorem axiom78_operational_bound (M : FiniteModel4) :
    (Checker.checkAx78Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.sameFoundationBound M + 26) + 2) + 2) :=
  Checker.checkAx78Costed_cost_le M

/--
Axiom 79 composes the proper-part witness, pairwise compatibility, and closure
scans; modal existence implications are evaluated by the counted world scan.
-/
theorem axiom79_operational_bound (M : FiniteModel4) :
    (Checker.checkAx79Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.ax79CharacterizationBound M + 12) + 2) :=
  Checker.checkAx79Costed_cost_le M

/-- Axiom 80 explicitly charges the qua-individual/part mediation witness scan. -/
theorem axiom80_operational_bound (M : FiniteModel4) :
    (Checker.checkAx80Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax80CharacterizationBound M + 15) + 2) + 2) :=
  Checker.checkAx80Costed_cost_le M

/-- Axiom 81 charges both characterization witness directions and uniqueness. -/
theorem axiom81_operational_bound (M : FiniteModel4) :
    (Checker.checkAx81Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax81ConsequentBound M + 15) + 2) + 2) :=
  Checker.checkAx81Costed_cost_le M

/-- Axiom 82 reuses the explicit quadratic instance/inherence uniqueness scan. -/
theorem axiom82_operational_bound (M : FiniteModel4) :
    (Checker.checkAx82Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax82InstancesBound M + 24) + 2) + 2) :=
  Checker.checkAx82Costed_cost_le M

theorem axiom83_operational_bound (M : FiniteModel4) :
    (Checker.checkAx83Costed M).cost ≤
      M.thingCount * (M.worldCount * 20 + 2) :=
  Checker.checkAx83Costed_cost_le M

theorem axiom84_operational_bound (M : FiniteModel4) :
    (Checker.checkAx84Costed M).cost ≤
      M.thingCount * (M.worldCount * 20 + 2) :=
  Checker.checkAx84Costed_cost_le M

theorem axiom85_operational_bound (M : FiniteModel4) :
    (Checker.checkAx85Costed M).cost ≤
      M.worldCount * (M.thingCount * 20 + 2) :=
  Checker.checkAx85Costed_cost_le M

theorem axiom86_operational_bound (M : FiniteModel4) :
    (Checker.checkAx86Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.qualityStructureBound M +
        Checker.nonEmptySetBound M + 13) + 2) :=
  Checker.checkAx86Costed_cost_le M

/-- Nested uniqueness: a unique structure containing the quale, where each
structure test is itself an explicit unique quality-type witness search. -/
theorem axiom87_operational_bound (M : FiniteModel4) :
    (Checker.checkAx87Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.existsUniqueQualityStructureMemberBound M + 12) + 2) :=
  Checker.checkAx87Costed_cost_le M

theorem axiom88_operational_bound (M : FiniteModel4) :
    (Checker.checkAx88Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.qualityStructureBound M + 21) + 2) :=
  Checker.checkAx88Costed_cost_le M

theorem axiom89_operational_bound (M : FiniteModel4) :
    (Checker.checkAx89Costed M).cost ≤
      M.thingCount * (M.worldCount * 21 + 2) :=
  Checker.checkAx89Costed_cost_le M

/-- Axiom 90 charges four nested thing scans, its world scan, and both complete
membership scans used to decide proper subset. -/
theorem axiom90_operational_bound (M : FiniteModel4) :
    (Checker.checkAx90Costed M).cost ≤ Checker.checkAx90Bound M :=
  Checker.checkAx90Costed_cost_le M

/-- Axiom 91 exposes the nested uniqueness search for the quality structure
associated with each quality type. -/
theorem axiom91_operational_bound (M : FiniteModel4) :
    (Checker.checkAx91Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.existsUniqueQualityStructureForTypeBound M + 21) + 2) :=
  Checker.checkAx91Costed_cost_le M

theorem axiom92_operational_bound (M : FiniteModel4) :
    (Checker.checkAx92Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (Checker.qualityBound M + 24) + 2) + 2) :=
  Checker.checkAx92Costed_cost_le M

/-- Axiom 93 replaces the semantic `∃!` decision with explicit candidate and
uniqueness traversals over the finite `hasValue` table. -/
theorem axiom93_operational_bound (M : FiniteModel4) :
    (Checker.checkAx93Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.qualityBound M +
        Checker.existsUniqueHasValueBound M + 4) + 2) :=
  Checker.checkAx93Costed_cost_le M

/-- Axiom 94 charges both nested witness dimensions and the three table reads
that establish each candidate. -/
theorem axiom94_operational_bound (M : FiniteModel4) :
    (Checker.checkAx94Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (Checker.ax94WitnessBound M + 15) + 2) + 2) :=
  Checker.checkAx94Costed_cost_le M

/-- Axiom 95 includes the complete instance scan and the concrete unique-quality
classification used to recognize a simple quality type. -/
theorem axiom95_operational_bound (M : FiniteModel4) :
    (Checker.checkAx95Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.simpleQualityTypeBound M + 25) + 2) + 2) :=
  Checker.checkAx95Costed_cost_le M

/-- Axiom 96 charges the current repeated simple/complex-quality computation
inside every instance test; no unproved cache is assumed. -/
theorem axiom96_operational_bound (M : FiniteModel4) :
    (Checker.checkAx96Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.complexQualityTypeBound M + 25) + 2) + 2) :=
  Checker.checkAx96Costed_cost_le M

/-- Axiom 97 charges all five finite thing dimensions, equality tests, table
reads, and the full complex-quality computation in its antecedent. -/
theorem axiom97_operational_bound (M : FiniteModel4) :
    (Checker.checkAx97Costed M).cost ≤ Checker.checkAx97Bound M :=
  Checker.checkAx97Costed_cost_le M

/-- Axiom 98 charges every inhering candidate and its complete simple-quality
classification after recognizing the containing complex quality. -/
theorem axiom98_operational_bound (M : FiniteModel4) :
    (Checker.checkAx98Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.complexQualityBound M +
        Checker.ax98PartsBound M + 4) + 2) :=
  Checker.checkAx98Costed_cost_le M

/-- Axiom 99 uses a heterogeneous sum over actual product-family arities.  The
bound therefore charges every family and dimension slot without replacing
variable-size witness arrays by the global thing count. -/
theorem axiom99_operational_bound (M : FiniteModel4) :
    (Checker.checkAx99Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.productFamilySearchBound M + 24) + 2) + 2) :=
  Checker.checkAx99Costed_cost_le M

/-- Axiom 100 charges the common-quality-structure witness scan for every
distance tuple. -/
theorem axiom100_operational_bound (M : FiniteModel4) :
    (Checker.checkAx100Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * (25 * M.thingCount + 36) + 2) + 2) + 2) :=
  Checker.checkAx100Costed_cost_le M

/-- Axiom 101 searches for exactly one distance result through counted
candidate and uniqueness scans. -/
theorem axiom101_operational_bound (M : FiniteModel4) :
    (Checker.checkAx101Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.existsUniqueDistanceBound M + 21) + 2) + 2) :=
  Checker.checkAx101Costed_cost_le M

theorem axiom102_operational_bound (M : FiniteModel4) :
    (Checker.checkAx102Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 32 + 2) + 2) :=
  Checker.checkAx102Costed_cost_le M

/-- Axiom 103 charges its nested overlap/manifests equivalence scan. -/
theorem axiom103_operational_bound (M : FiniteModel4) :
    (Checker.checkAx103Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 37 + 33) + 2) + 2) :=
  Checker.checkAx103Costed_cost_le M

theorem axiom104_operational_bound (M : FiniteModel4) :
    (Checker.checkAx104Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 32 + 2) + 2) :=
  Checker.checkAx104Costed_cost_le M

theorem axiom105_operational_cost (M : FiniteModel4) :
    (Checker.checkAx105Costed M).cost = 0 := Checker.checkAx105Costed_cost M

theorem axiom106_operational_cost (M : FiniteModel4) :
    (Checker.checkAx106Costed M).cost = 0 := Checker.checkAx106Costed_cost M

theorem axiom107_operational_cost (M : FiniteModel4) :
    (Checker.checkAx107Costed M).cost = 0 := Checker.checkAx107Costed_cost M

theorem axiom108_operational_cost (M : FiniteModel4) :
    (Checker.checkAx108Costed M).cost = 0 := Checker.checkAx108Costed_cost M

theorem qua_individual_endurant_operational_bound (M : FiniteModel4) :
    (Checker.checkAxQuaIndividualOfEndurantCosted M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 23 + 2) + 2) :=
  Checker.checkAxQuaIndividualOfEndurantCosted_cost_le M

theorem distance_identity_operational_bound (M : FiniteModel4) :
    (Checker.checkAxDistanceIdentityCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 28 + 2) + 2) + 2) :=
  Checker.checkAxDistanceIdentityCosted_cost_le M

theorem distance_symmetry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxDistanceSymmetryCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 32 + 2) + 2) + 2) :=
  Checker.checkAxDistanceSymmetryCosted_cost_le M

theorem distance_triangle_operational_bound (M : FiniteModel4) :
    (Checker.checkAxDistanceTriangleCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.thingCount * (M.thingCount *
        (M.thingCount * (M.thingCount * (M.worldCount * 74 + 2) + 2) + 2) + 2) + 2) + 2) + 2) :=
  Checker.checkAxDistanceTriangleCosted_cost_le M

/-!
## Scalar checker ingredients

The scalar checker size includes dense relation cells and product-family
witness arrays. Axiom 99 is the only fixed-registry entry whose concrete bound
depends on those arrays, so its search bound is discharged separately before
the heterogeneous 113-entry sum is majorized. This preserves the concrete
computation rather than silently treating witnesses as an oracle.
-/

theorem product_family_witness_bound_le_checkerInputSize_cube
    (M : FiniteModel4) (i : Fin M.productFamilies.size) :
    Checker.productFamilyWitnessBound M M.productFamilies[i] ≤
      154 * checkerInputSize M ^ 3 := by
  let n := checkerInputSize M
  have hn : 1 ≤ n := checkerInputSize_pos M
  have ht : M.thingCount ≤ n := thingCount_le_checkerInputSize M
  have hd : M.productFamilies[i].dimensionThings.size ≤ n :=
    productFamilyDimension_le_checkerInputSize M i
  have hn2 : n ≤ n ^ 2 := by
    simpa [Nat.pow_two] using Nat.mul_le_mul_left n hn
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n ^ 2 * 1 := by omega
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left (n ^ 2) hn
      _ = n ^ 3 := by ring
  calc
    Checker.productFamilyWitnessBound M M.productFamilies[i] ≤
        9 + n * (25 * n + 15) + n * (n * (25 * n + 18) + 15) +
          n * 28 + n * (4 * n + 15) := by
      unfold Checker.productFamilyWitnessBound
      repeat' first
        | assumption
        | exact Nat.le_refl _
        | apply Nat.add_le_add
        | apply Nat.mul_le_mul
    _ ≤ 154 * n ^ 3 := by
      ring_nf
      omega

private theorem list_sum_map_le_const (xs : List α) (f : α → Nat) (bound : Nat)
    (h : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, f y ≤ bound := by
        intro y hy
        exact h y (by simp [hy])
      have htail := ih hxs
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

theorem product_family_search_bound_le_checkerInputSize_pow4 (M : FiniteModel4) :
    Checker.productFamilySearchBound M ≤ 157 * checkerInputSize M ^ 4 := by
  let n := checkerInputSize M
  have hn : 1 ≤ n := by
    have := checkerInputSize_pos M
    simp only [n]
    omega
  have hn_sq : 1 ≤ n ^ 3 := by
    exact Nat.one_le_pow _ _ hn
  have hcount : M.productFamilies.size ≤ n := by
    simpa [n] using productFamilyCount_le_checkerInputSize M
  unfold Checker.productFamilySearchBound
  calc
    ((List.finRange M.productFamilies.size).map fun i =>
        Checker.productFamilyWitnessBound M M.productFamilies[i] + 3).sum ≤
        (List.finRange M.productFamilies.size).length * (157 * n ^ 3) := by
      apply list_sum_map_le_const
      intro i hi
      have hw := product_family_witness_bound_le_checkerInputSize_cube M i
      change Checker.productFamilyWitnessBound M M.productFamilies[i] ≤ 154 * n ^ 3 at hw
      change Checker.productFamilyWitnessBound M M.productFamilies[i] + 3 ≤
        157 * n ^ 3
      omega
    _ = M.productFamilies.size * (157 * n ^ 3) := by simp
    _ ≤ n * (157 * n ^ 3) := Nat.mul_le_mul_right (157 * n ^ 3) hcount
    _ = 157 * n ^ 4 := by
      simp [Nat.pow_succ]
      ac_rfl

private theorem one_le_pow_of_one_le (n k : Nat) (hn : 1 ≤ n) : 1 ≤ n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      exact Nat.mul_le_mul ih hn

/-- One explicit finite scan raises the scalar degree by one. The added two
units are the actual loop/short-circuit bookkeeping charged by the executable
quantifier combinators. -/
private theorem scan_layer_scalar_bound
    (n coefficient degree extent inner : Nat)
    (hn : 1 ≤ n) (hextent : extent ≤ n)
    (hinner : inner ≤ coefficient * n ^ degree) :
    extent * (inner + 2) ≤ (coefficient + 2) * n ^ (degree + 1) := by
  have hpow : 1 ≤ n ^ degree := one_le_pow_of_one_le n degree hn
  have hplus : inner + 2 ≤ (coefficient + 2) * n ^ degree := by
    calc
      inner + 2 ≤ coefficient * n ^ degree + 2 * n ^ degree := by omega
      _ = (coefficient + 2) * n ^ degree := by rw [Nat.add_mul]
  calc
    extent * (inner + 2) ≤ n * ((coefficient + 2) * n ^ degree) :=
      Nat.mul_le_mul hextent hplus
    _ = (coefficient + 2) * n ^ (degree + 1) := by
      rw [Nat.pow_succ]
      ac_rfl

theorem axiom99_scalar_operational_bound (M : FiniteModel4) :
    (Checker.checkAx99Costed M).cost ≤ 185 * checkerInputSize M ^ 7 := by
  let n := checkerInputSize M
  have hn : 1 ≤ n := by
    have := checkerInputSize_pos M
    simp only [n]
    omega
  have ht : M.thingCount ≤ n := by
    simpa [n] using thingCount_le_checkerInputSize M
  have hw : M.worldCount ≤ n := by
    simpa [n] using worldCount_le_checkerInputSize M
  have hsearch := product_family_search_bound_le_checkerInputSize_pow4 M
  change Checker.productFamilySearchBound M ≤ 157 * n ^ 4 at hsearch
  have hcube : 1 ≤ n ^ 4 := one_le_pow_of_one_le n 4 hn
  have hbase : Checker.productFamilySearchBound M + 22 ≤ 179 * n ^ 4 := by
    omega
  have hworld :
      M.worldCount * (Checker.productFamilySearchBound M + 24) ≤
        181 * n ^ 5 := by
    exact scan_layer_scalar_bound n 179 4 M.worldCount
      (Checker.productFamilySearchBound M + 22) hn hw hbase
  have hthingInner :
      M.thingCount *
          (M.worldCount * (Checker.productFamilySearchBound M + 24) + 2) ≤
        183 * n ^ 6 := by
    exact scan_layer_scalar_bound n 181 5 M.thingCount
      (M.worldCount * (Checker.productFamilySearchBound M + 24)) hn ht hworld
  have hthingOuter : M.thingCount *
      (M.thingCount *
          (M.worldCount * (Checker.productFamilySearchBound M + 24) + 2) + 2) ≤
        185 * n ^ 7 := by
    exact scan_layer_scalar_bound n 183 6 M.thingCount
      (M.thingCount *
        (M.worldCount * (Checker.productFamilySearchBound M + 24) + 2)) hn ht hthingInner
  exact (Checker.checkAx99Costed_cost_le M).trans hthingOuter

/-- The production checker is the erasure of the exact, delayed 113-check registry. -/
theorem fixed_registry_size (M : FiniteModel4) :
    (Checker.checkAxioms4BoundedRegistry M).size = 113 :=
  Checker.checkAxioms4BoundedRegistry_size M

theorem fixed_registry_erases_to_legacy (M : FiniteModel4) :
    Checker.checkAxioms4 M = (Checker.checkAxioms4Checks M).all id :=
  Checker.checkAxioms4_eq_legacy M

/-- Fixed-formula data-complexity theorem. The right side expands to the sum
of the 113 per-check bounds and the registry traversal charges. Atomic queries
use the checker interface documented in the complexity guide. -/
theorem fixed_registry_data_complexity_bound (M : FiniteModel4) :
    (Checker.checkAxioms4Costed M).cost ≤
      Checker.checkAxioms4OperationalBound M :=
  Checker.checkAxioms4Costed_cost_le M

private theorem thing_world_monomial_le
    (n things worlds thingDegree worldDegree totalDegree : Nat)
    (hn : 0 < n) (hthings : things ≤ n) (hworlds : worlds ≤ n)
    (hdegree : thingDegree + worldDegree ≤ totalDegree) :
    things ^ thingDegree * worlds ^ worldDegree ≤ n ^ totalDegree := by
  calc
    things ^ thingDegree * worlds ^ worldDegree ≤
        n ^ thingDegree * n ^ worldDegree :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hthings thingDegree)
        (Nat.pow_le_pow_left hworlds worldDegree)
    _ = n ^ (thingDegree + worldDegree) := by rw [Nat.pow_add]
    _ ≤ n ^ totalDegree := Nat.pow_le_pow_right hn hdegree

/-- The exact heterogeneous 113-entry production bound is at most a degree-eight
polynomial in the complete explicit checker encoding. Unfolding the registry
gives ordinary monomial coefficient sum 8164; axiom 99 contributes at most 157
more after its separately proved witness-search bound. The coefficient 8367
leaves 46 units of slack. -/
theorem fixed_registry_operational_bound_le_checkerInputSize_pow8
    (M : FiniteModel4) :
    Checker.checkAxioms4OperationalBound M ≤ 8367 * checkerInputSize M ^ 8 := by
  let n := checkerInputSize M
  have hn : 0 < n := by simpa [n] using checkerInputSize_pos M
  have ht : M.thingCount ≤ n := by
    simpa [n] using thingCount_le_checkerInputSize M
  have hw : M.worldCount ≤ n := by
    simpa [n] using worldCount_le_checkerInputSize M
  have hmono (a b : Nat) (hab : a + b ≤ 8) :
      M.thingCount ^ a * M.worldCount ^ b ≤ n ^ 8 :=
    thing_world_monomial_le n M.thingCount M.worldCount a b 8 hn ht hw hab
  have h01 := hmono 0 1 (by omega)
  have h10 := hmono 1 0 (by omega)
  have h11 := hmono 1 1 (by omega)
  have h12 := hmono 1 2 (by omega)
  have h20 := hmono 2 0 (by omega)
  have h21 := hmono 2 1 (by omega)
  have h22 := hmono 2 2 (by omega)
  have h30 := hmono 3 0 (by omega)
  have h31 := hmono 3 1 (by omega)
  have h32 := hmono 3 2 (by omega)
  have h40 := hmono 4 0 (by omega)
  have h41 := hmono 4 1 (by omega)
  have h42 := hmono 4 2 (by omega)
  have h50 := hmono 5 0 (by omega)
  have h51 := hmono 5 1 (by omega)
  have h52 := hmono 5 2 (by omega)
  have h60 := hmono 6 0 (by omega)
  have h61 := hmono 6 1 (by omega)
  have h70 := hmono 7 0 (by omega)
  have h71 := hmono 7 1 (by omega)
  have hone : 1 ≤ n ^ 8 := one_le_pow_of_one_le n 8 (by omega)
  have hsearch := product_family_search_bound_le_checkerInputSize_pow4 M
  change Checker.productFamilySearchBound M ≤ 157 * n ^ 4 at hsearch
  have h21degree3 : M.thingCount ^ 2 * M.worldCount ≤ n ^ 3 := by
    simpa using thing_world_monomial_le n M.thingCount M.worldCount 2 1 3
      hn ht hw (by omega)
  have hpow7to8 : n ^ 7 ≤ n ^ 8 := Nat.pow_le_pow_right hn (by omega)
  have hproduct : M.thingCount ^ 2 * M.worldCount *
      Checker.productFamilySearchBound M ≤ 157 * n ^ 8 := by
    calc
      M.thingCount ^ 2 * M.worldCount * Checker.productFamilySearchBound M ≤
          n ^ 3 * (157 * n ^ 4) := Nat.mul_le_mul h21degree3 hsearch
      _ = 157 * n ^ 7 := by
        simp [Nat.pow_succ]
        ac_rfl
      _ ≤ 157 * n ^ 8 := Nat.mul_le_mul_left 157 hpow7to8
  simp [Checker.checkAxioms4OperationalBound,
    Complexity.boundedRegistryCostBound,
    Checker.checkAxioms4BoundedRegistry,
    Complexity.BoundedCheck.of,
    Checker.ultimateBearerUniquenessBound,
    Checker.ax44DirectFamilyBound, Checker.ax44QualityFamilyBound,
    Checker.ax44CostBound, Checker.genericFunctionalDependenceBound,
    Checker.individualFunctionalDependenceBound, Checker.functionalComponentBound,
    Checker.genericConstitutionalDependenceBound, Checker.constitutionBound,
    Checker.existentialDependenceBound, Checker.existentialIndependenceBound,
    Checker.checkAx68EvaluationBound, Checker.checkAx68CostBound,
    Checker.existenceDifferenceBound, Checker.externalSeparationBound,
    Checker.externallyDependentBound, Checker.externallyDependentModeBound,
    Checker.existsUniqueFoundedByBound, Checker.sameFoundationBound,
    Checker.ax73ClassificationBound, Checker.ax73PartsBound,
    Checker.quaIndividualExistsBound, Checker.properPartExistsBound,
    Checker.ax79PairCompatibilityBound, Checker.ax79PairConditionBound,
    Checker.ax79PairwiseBound, Checker.ax79ClosurePremiseBound,
    Checker.ax79ClosureConditionBound, Checker.ax79ClosureBound,
    Checker.ax79CharacterizationBound, Checker.mediationWitnessBound,
    Checker.ax80CharacterizationBound, Checker.existsUniqueInstInheresBound,
    Checker.ax82InstancesBound, Checker.ax81MomentWitnessBound,
    Checker.ax81TypeInstancesBound, Checker.ax81ConsequentBound,
    Checker.qualityStructureBound, Checker.nonEmptySetBound,
    Checker.qualityStructureMemberUniqueForBound,
    Checker.existsUniqueQualityStructureMemberBound, Checker.checkAx90Bound,
    Checker.qualityStructureForTypeUniqueBound,
    Checker.existsUniqueQualityStructureForTypeBound, Checker.qualityBound,
    Checker.existsUniqueHasValueBound, Checker.ax94WitnessBound,
    Checker.simpleQualityBound, Checker.complexQualityBound,
    Checker.simpleQualityTypeBound, Checker.complexQualityTypeBound,
    Checker.checkAx97Bound, Checker.ax98PartsBound,
    Checker.existsUniqueDistanceBound]
  ring_nf at hone h01 h10 h11 h12 h20 h21 h22 h30 h31 h32 h40 h41 h42 h50 h51 h52 h60 h61 h70 h71 hproduct
  ring_nf
  change _ ≤ n ^ 8 * 8367
  omega

/-- Headline one-variable data-complexity corollary for the production checker. -/
theorem fixed_registry_scalar_data_complexity_bound (M : FiniteModel4) :
    (Checker.checkAxioms4Costed M).cost ≤ 8367 * checkerInputSize M ^ 8 :=
  (fixed_registry_data_complexity_bound M).trans
    (fixed_registry_operational_bound_le_checkerInputSize_pow8 M)

/-- The frontend can call one registered check without running earlier fields.
Use the proved registry budget, not the aggregate checker's early-exit count. -/
theorem registered_check_scalar_bound (M : FiniteModel4) (check : BoundedCheck)
    (member : check ∈ (Checker.checkAxioms4BoundedRegistry M).toList) :
    (check.run ()).cost ≤ 8367 * checkerInputSize M ^ 8 :=
  (boundedCheck_cost_le_registryBound _ check member).trans
    (fixed_registry_operational_bound_le_checkerInputSize_pow8 M)

/-- Any registered call on the actual successful compiler output has a bound
in that source's size. This is a per-call bound, excluding construction and
frontend scheduling. The model-size bound 3N² gives degree sixteen in N. -/
theorem source_registered_check_scalar_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let M := compiled.tables.toFiniteModel4Cached
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    ∀ check : BoundedCheck,
      check ∈ (Checker.checkAxioms4BoundedRegistry M).toList →
      (check.run ()).cost ≤ 54895887 * (sourceMetrics source).inputSize ^ 16 := by
  dsimp only
  intro check member
  have checked := registered_check_scalar_bound _ check member
  have size := finiteModelInputSize_le_sourceInputSize_sq source compiled success hw ht
  have bound := checked.trans (Nat.mul_le_mul_left 8367 (Nat.pow_le_pow_left size 8))
  calc
    _ ≤ 8367 * (3 * (sourceMetrics source).inputSize ^ 2) ^ 8 := bound
    _ = 54895887 * (sourceMetrics source).inputSize ^ 16 := by ring

/-- One registered checker call, including rebuilding its tables and finite
model, has a bound in the original source size. Compiler success connects all
three computations to that source. This is a per-call bound: a frontend bound
must also account for how often certification executes these computations. -/
theorem source_registered_reconstruction_scalar_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let construction := compiled.tables.toFiniteModel4CachedCosted
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    ∀ check : BoundedCheck,
      check ∈ (Checker.checkAxioms4BoundedRegistry construction.value).toList →
      (compileExplicitModelASTCosted compiled.ast).cost + construction.cost + (check.run ()).cost ≤
        54896424 * (sourceMetrics source).inputSize ^ 16 := by
  dsimp only
  intro check member
  let n := (sourceMetrics source).inputSize
  have hn : 0 < n := sourceMetrics_inputSize_pos source
  have tables := explicitCompilation_source_scalar_bound source compiled success
  have construction := finiteModelConstructionCost_le_sourceInputSize_sq source compiled success hw ht
  have checker := source_registered_check_scalar_bound source compiled success hw ht check member
  have square : n ^ 2 ≤ n ^ 16 := Nat.pow_le_pow_right hn (by omega)
  have fourth : n ^ 4 ≤ n ^ 16 := Nat.pow_le_pow_right hn (by omega)
  have tableBound := tables.trans (Nat.mul_le_mul_left 511 fourth)
  have constructionBound := construction.trans (Nat.mul_le_mul_left 26 square)
  change _ ≤ 54895887 * n ^ 16 at checker
  change _ ≤ 54896424 * n ^ 16
  omega

/-- Reconstruct the actual successful source, then execute a registered
checker on the returned model. Membership constrains the full counted result,
not merely its Boolean value or an assumed bound for an arbitrary callback. -/
theorem reconstructedCheck_source_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (check : FiniteModel4 → Costed Bool)
    (registered : ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success))).toList ∧
      check (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success)) = entry.run ()) :
    (reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) check).cost ≤
      54896424 * (sourceMetrics source).inputSize ^ 16 := by
  obtain ⟨entry, member, same⟩ := registered
  have checkBound := registered_check_scalar_bound _ entry member
  rw [← same] at checkBound
  have modelSize := compileVerifiedModel_source_inputSize_bound source compiled success hw ht
  have checked := checkBound.trans
    (Nat.mul_le_mul_left 8367 (Nat.pow_le_pow_left modelSize 8))
  have expansion : 8367 * (3 * (sourceMetrics source).inputSize ^ 2) ^ 8 =
      54895887 * (sourceMetrics source).inputSize ^ 16 := by ring
  rw [expansion] at checked
  have construction := compileVerifiedModelCosted_source_bound source compiled success hw ht
  have fourth : (sourceMetrics source).inputSize ^ 4 ≤ (sourceMetrics source).inputSize ^ 16 :=
    Nat.pow_le_pow_right (sourceMetrics_inputSize_pos source) (by omega)
  have built := construction.trans (Nat.mul_le_mul_left 537 fourth)
  rw [reconstructedCheck_cost]
  omega

/-- An expected-answer native request includes one concrete reconstruction,
one registered checker, and its Boolean comparison. The unused parent thunk
needs no bound because this request cannot execute it. -/
theorem nativeExpected_reconstructed_source_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (check : FiniteModel4 → Costed Bool)
    (registered : ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success))).toList ∧
      check (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success)) = entry.run ())
    (field : String) (answer : Bool) (parent : Unit → Costed Bool) :
    (nativeRequestCosted (.expect field answer)
      (fun _ => reconstructedCheckCosted compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success) check) parent).cost ≤
      54896424 * (sourceMetrics source).inputSize ^ 16 + 1 := by
  have checked := reconstructedCheck_source_bound source compiled success hw ht check registered
  rw [nativeRequest_cost]
  dsimp only
  omega

/-- An agreement request runs the same registered checker on both source
models. Each operand includes its own reconstruction allowance; only one
Boolean comparison follows. These premises concern actual compiled sources,
not independent oracle-valued models or arbitrary callback cost assumptions. -/
theorem nativeAgreement_reconstructed_source_bound
    (childSource parentSource : ModelSource) (child parent : CompiledModelSource)
    (childSuccess : compileModelSource childSource = .ok child)
    (parentSuccess : compileModelSource parentSource = .ok parent)
    (cw : 0 < child.ast.worldCount) (ct : 0 < child.ast.thingCount)
    (pw : 0 < parent.ast.worldCount) (pt : 0 < parent.ast.thingCount)
    (check : FiniteModel4 → Costed Bool)
    (childRegistered : ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess))).toList ∧
      check (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess)) = entry.run ())
    (parentRegistered : ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess))).toList ∧
      check (compileVerifiedModel parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess)) = entry.run ())
    (field : String) (parentName : Lean.Name) :
    (nativeRequestCosted (.agree field parentName)
      (fun _ => reconstructedCheckCosted child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess) check)
      (fun _ => reconstructedCheckCosted parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess) check)).cost ≤
      54896424 * (sourceMetrics childSource).inputSize ^ 16 +
        54896424 * (sourceMetrics parentSource).inputSize ^ 16 + 1 := by
  have childBound := reconstructedCheck_source_bound childSource child childSuccess cw ct
    check childRegistered
  have parentBound := reconstructedCheck_source_bound parentSource parent parentSuccess pw pt
    check parentRegistered
  rw [nativeRequest_cost]
  dsimp only
  omega

/-- A supplied prefix of a generated script has a source-size bound on its
native algorithm work. Each requested checker includes its concrete model
construction, and each decision adds one comparison. `checks` supplies the
computations resolved by the emitter; membership constrains their full counted
results. An expected-answer request needs no parent membership proof.

The bound uses the script's full request count so it also covers shorter
prefixes. It does not establish which prefix Lean's proof engine reaches or
charge traversal of this mathematical request list as production work.
Summing component costs follows Niu et al.'s compositional cost semantics
(POPL 2022), with the concrete operand correspondences proved above. -/
theorem nativeScript_prefix_source_bound
    (childSource parentSource : ModelSource) (child parent : CompiledModelSource)
    (childSuccess : compileModelSource childSource = .ok child)
    (parentSuccess : compileModelSource parentSource = .ok parent)
    (cw : 0 < child.ast.worldCount) (ct : 0 < child.ast.thingCount)
    (pw : 0 < parent.ast.worldCount) (pt : 0 < parent.ast.thingCount)
    (script : CertificateChecking.ProofScript) (limit : Nat)
    (checks : CertificateChecking.NativeCall → FiniteModel4 → Costed Bool)
    (childRegistered : ∀ request ∈ script.nativeCalls, ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess))).toList ∧
      checks request (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess)) = entry.run ())
    (parentRegistered : ∀ request ∈ script.nativeCalls,
      match request with
      | .expect .. => True
      | .agree .. => ∃ entry : BoundedCheck,
          entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel parent.ast pw pt
            (compileModelSource_ok_wellBounded parentSource parent parentSuccess))).toList ∧
          checks request (compileVerifiedModel parent.ast pw pt
            (compileModelSource_ok_wellBounded parentSource parent parentSuccess)) = entry.run ()) :
    ((script.nativeCalls.take limit).map (fun request =>
      (nativeRequestCosted request
        (fun _ => reconstructedCheckCosted child.ast cw ct
          (compileModelSource_ok_wellBounded childSource child childSuccess) (checks request))
        (fun _ => reconstructedCheckCosted parent.ast pw pt
          (compileModelSource_ok_wellBounded parentSource parent parentSuccess) (checks request))).cost)).sum ≤
      script.checkerCalls * (54896424 *
        (max (sourceMetrics childSource).inputSize (sourceMetrics parentSource).inputSize) ^ 16) +
        script.nativeCalls.length := by
  let budget := 54896424 *
    (max (sourceMetrics childSource).inputSize (sourceMetrics parentSource).inputSize) ^ 16
  let runRequest := fun request => nativeRequestCosted request
    (fun _ => reconstructedCheckCosted child.ast cw ct
      (compileModelSource_ok_wellBounded childSource child childSuccess) (checks request))
    (fun _ => reconstructedCheckCosted parent.ast pw pt
      (compileModelSource_ok_wellBounded parentSource parent parentSuccess) (checks request))
  have childSize : 54896424 * (sourceMetrics childSource).inputSize ^ 16 ≤ budget :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_max_left _ _) _)
  have parentSize : 54896424 * (sourceMetrics parentSource).inputSize ^ 16 ≤ budget :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_max_right _ _) _)
  have one (request) (member : request ∈ script.nativeCalls) :
      (runRequest request).cost ≤ request.checkerCalls * budget + 1 := by
    have childBound := (reconstructedCheck_source_bound childSource child childSuccess cw ct
      (checks request) (childRegistered request member)).trans childSize
    cases request with
    | expect field answer =>
        simp only [runRequest, nativeRequest_cost, CertificateChecking.NativeCall.checkerCalls]
        omega
    | agree field name =>
        have parentBound := (reconstructedCheck_source_bound parentSource parent parentSuccess pw pt
          (checks (.agree field name)) (parentRegistered (.agree field name) member)).trans parentSize
        simp only [runRequest, nativeRequest_cost, CertificateChecking.NativeCall.checkerCalls]
        omega
  have sumBound (requests : List CertificateChecking.NativeCall)
      (included : ∀ request ∈ requests, request ∈ script.nativeCalls) :
      (requests.map (fun request => (runRequest request).cost)).sum ≤
        (requests.map CertificateChecking.NativeCall.checkerCalls).sum * budget + requests.length := by
    induction requests with
    | nil => simp
    | cons request rest ih =>
        have headBound := one request (included request (by simp))
        have tailBound := ih (fun r hr => included r (by simp [hr]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
        omega
  have prefixBound := sumBound (script.nativeCalls.take limit)
    (fun _ member => List.mem_of_mem_take member)
  have count := Nat.mul_le_mul_right budget (script_prefix_checkerCalls_le script limit)
  have length : (script.nativeCalls.take limit).length ≤ script.nativeCalls.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  change _ ≤ script.checkerCalls * budget + script.nativeCalls.length
  change ((script.nativeCalls.take limit).map (fun request => (runRequest request).cost)).sum ≤ _
  omega

/-- Source-size bound for the shared preparation loop, including its control
operations. Each native request runs the concrete reconstruction/check/comparison
expression above. `proofResult` represents excluded native proof production:
it can return a proof or an error, but adds no algorithm cost. Thus an error can
stop later requests without a hypothesis about an arbitrary callback's cost.

For K checker invocations and R requests, the bound is K times the common
source-check budget, plus 4R + 1. Each request contributes one comparison and
at most three loop operations. This composes the operands and loop; the full
frontend still needs the surrounding attempt and diagnostic composition. -/
theorem nativeScript_prepare_source_bound {ε : Type}
    (childSource parentSource : ModelSource) (child parent : CompiledModelSource)
    (childSuccess : compileModelSource childSource = .ok child)
    (parentSuccess : compileModelSource parentSource = .ok parent)
    (cw : 0 < child.ast.worldCount) (ct : 0 < child.ast.thingCount)
    (pw : 0 < parent.ast.worldCount) (pt : 0 < parent.ast.thingCount)
    (script : CertificateChecking.ProofScript)
    (checks : CertificateChecking.NativeCall → FiniteModel4 → Costed Bool)
    (proofResult : CertificateChecking.NativeCall → Bool → Except ε String)
    (childRegistered : ∀ request ∈ script.nativeCalls, ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess))).toList ∧
      checks request (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess)) = entry.run ())
    (parentRegistered : ∀ request ∈ script.nativeCalls,
      match request with
      | .expect .. => True
      | .agree .. => ∃ entry : BoundedCheck,
          entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel parent.ast pw pt
            (compileModelSource_ok_wellBounded parentSource parent parentSuccess))).toList ∧
          checks request (compileVerifiedModel parent.ast pw pt
            (compileModelSource_ok_wellBounded parentSource parent parentSuccess)) = entry.run ()) :
    (script.prepareCosted (fun request => Costed.map (proofResult request)
      (nativeRequestCosted request
        (fun _ => reconstructedCheckCosted child.ast cw ct
          (compileModelSource_ok_wellBounded childSource child childSuccess) (checks request))
        (fun _ => reconstructedCheckCosted parent.ast pw pt
          (compileModelSource_ok_wellBounded parentSource parent parentSuccess) (checks request))))).cost ≤
      script.checkerCalls * (54896424 *
        (max (sourceMetrics childSource).inputSize (sourceMetrics parentSource).inputSize) ^ 16) +
        4 * script.nativeCalls.length + 1 := by
  have operands := nativeScript_prefix_source_bound childSource parentSource child parent
    childSuccess parentSuccess cw ct pw pt script script.nativeCalls.length checks
    childRegistered parentRegistered
  simp only [List.take_length] at operands
  have preparation := proofScriptPrepare_cost_le script (fun request => Costed.map
    (proofResult request) (nativeRequestCosted request
      (fun _ => reconstructedCheckCosted child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess) (checks request))
      (fun _ => reconstructedCheckCosted parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess) (checks request))))
  simp only [Costed.map_cost] at preparation
  omega

/-- Growing either source-size parameter cannot reduce the script bound.
This concerns the upper bound, not exact counts, which can decrease when a
checker finds an answer earlier. -/
theorem nativeScript_source_bound_mono (script : CertificateChecking.ProofScript)
    {child parent largerChild largerParent : Nat}
    (childGrows : child ≤ largerChild) (parentGrows : parent ≤ largerParent) :
    script.checkerCalls * (54896424 * (max child parent) ^ 16) + script.nativeCalls.length ≤
      script.checkerCalls * (54896424 * (max largerChild largerParent) ^ 16) +
        script.nativeCalls.length := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (max_le_max childGrows parentGrows) 16))) _

/-- The preparation bound is monotone in both source sizes, independently of
which native proof productions fail and stop the loop. -/
theorem nativeScript_prepare_source_bound_mono (script : CertificateChecking.ProofScript)
    {child parent largerChild largerParent : Nat}
    (childGrows : child ≤ largerChild) (parentGrows : parent ≤ largerParent) :
    script.checkerCalls * (54896424 * (max child parent) ^ 16) +
        4 * script.nativeCalls.length + 1 ≤
      script.checkerCalls * (54896424 * (max largerChild largerParent) ^ 16) +
        4 * script.nativeCalls.length + 1 := by
  have bound := nativeScript_source_bound_mono script childGrows parentGrows
  omega

/-- The shared checked-attempt driver includes one actual reuse-planner run.
Successful parent compilation bounds that planner by the two source sizes.
The proof callbacks retain their costs here: this is not a bound on arbitrary
elaboration or a substitute for connecting those callbacks to checker calls. -/
theorem source_planned_checked_bound (parentName : Lean.Name)
    (parentSource childSource : ModelSource) (parent : CompiledModelSource)
    (childTables : FactTables) (fresh : Bool) (field : String)
    (success : compileModelSource parentSource = .ok parent)
    (p d : Option Lean.Name → Costed Bool) (fp fd : Unit → Costed Bool) :
    let plan := fun _ : Unit => certificateReuseSourceCosted parentName parentSource
      childSource parent.tables childTables fresh field
    (CertificateChecking.runCosted plan p d fp fd).cost ≤
      18 * (sourceMetrics childSource).inputSize +
        11023 * (sourceMetrics parentSource).inputSize +
        (p (plan ()).value).cost + (d (plan ()).value).cost +
        (fp ()).cost + (fd ()).cost + 5 := by
  dsimp only
  have driver := checkedField_cost_le
    (fun _ => certificateReuseSourceCosted parentName parentSource
      childSource parent.tables childTables fresh field) p d fp fd
  have planner := certificateReuseSource_source_bound parentName parentSource
    childSource parent childTables fresh field success
  omega

/-- Source-linked bound for initial checked proofs and fresh fallback.
The counted native operands reconstruct and check the actual compiler outputs;
the bound permits one reconstruction per operand, even if native execution
shares the model. Full counted registry membership supplies each checker bound.
Proof-production and subsequent
elaboration outcomes may select any failure branch. No callback-cost hypothesis
is needed. The actual reuse planner runs once, and at most six checker operands
run across trial/declaration and fallback. Semantic proofs and diagnostics are
composed separately. -/
theorem source_prepared_checked_bound {ε : Type}
    (childSource parentSource : ModelSource) (child parent : CompiledModelSource)
    (childSuccess : compileModelSource childSource = .ok child)
    (parentSuccess : compileModelSource parentSource = .ok parent)
    (cw : 0 < child.ast.worldCount) (ct : 0 < child.ast.thingCount)
    (pw : 0 < parent.ast.worldCount) (pt : 0 < parent.ast.thingCount)
    (parentName : Lean.Name) (fresh : Bool) (field : CertField)
    (check : FiniteModel4 → Costed Bool)
    (proofResult : Bool → Option Lean.Name → CertificateChecking.NativeCall → Bool → Except ε String)
    (proofFailed : Bool → Option Lean.Name → Bool)
    (childRegistered : ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess))).toList ∧
      check (compileVerifiedModel child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess)) = entry.run ())
    (parentRegistered : ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess))).toList ∧
      check (compileVerifiedModel parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess)) = entry.run ()) :
    let plan := fun _ : Unit => certificateReuseSourceCosted parentName parentSource
      childSource parent.tables child.tables fresh field.field
    let native := fun declaration reuse request => Costed.map (proofResult declaration reuse request)
      (nativeRequestCosted request
        (fun _ => reconstructedCheckCosted child.ast cw ct
          (compileModelSource_ok_wellBounded childSource child childSuccess) check)
        (fun _ => reconstructedCheckCosted parent.ast pw pt
          (compileModelSource_ok_wellBounded parentSource parent parentSuccess) check))
    (preparedCheckedAttemptsCosted field plan native proofFailed).cost ≤
      18 * (sourceMetrics childSource).inputSize +
        11023 * (sourceMetrics parentSource).inputSize +
        6 * (54896424 *
          (max (sourceMetrics childSource).inputSize (sourceMetrics parentSource).inputSize) ^ 16) + 25 := by
  let budget := 54896424 *
    (max (sourceMetrics childSource).inputSize (sourceMetrics parentSource).inputSize) ^ 16
  let plan := fun _ : Unit => certificateReuseSourceCosted parentName parentSource
    childSource parent.tables child.tables fresh field.field
  let native := fun declaration reuse request => Costed.map (proofResult declaration reuse request)
    (nativeRequestCosted request
      (fun _ => reconstructedCheckCosted child.ast cw ct
        (compileModelSource_ok_wellBounded childSource child childSuccess) check)
      (fun _ => reconstructedCheckCosted parent.ast pw pt
        (compileModelSource_ok_wellBounded parentSource parent parentSuccess) check))
  have childBound := (reconstructedCheck_source_bound childSource child childSuccess cw ct
    check childRegistered).trans (Nat.mul_le_mul_left 54896424
      (Nat.pow_le_pow_left (Nat.le_max_left _ (sourceMetrics parentSource).inputSize) 16))
  have parentBound := (reconstructedCheck_source_bound parentSource parent parentSuccess pw pt
    check parentRegistered).trans (Nat.mul_le_mul_left 54896424
      (Nat.pow_le_pow_left (Nat.le_max_right (sourceMetrics childSource).inputSize _) 16))
  have nativeBound (declaration) (reuse) :
      (native declaration reuse (match reuse with
        | none => .expect field.field true
        | some name => .agree field.field name)).cost ≤
          (if reuse.isSome then 2 else 1) * budget + 1 := by
    cases reuse <;>
      simp only [native, Costed.map_cost, nativeRequest_cost, Option.isSome_none,
        Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
    all_goals dsimp only [budget] at *; omega
  have attempts := preparedCheckedAttempts_cost_le field plan native proofFailed budget nativeBound
  have planner := certificateReuseSource_source_bound parentName parentSource
    childSource parent child.tables fresh field.field parentSuccess
  change (preparedCheckedAttemptsCosted field plan native proofFailed).cost ≤ _
  dsimp only [plan, budget] at attempts ⊢
  omega

/-- Preparing a proof over one compiled source charges its actual registered
checker operands and the shared request loop. The same source supplies both
operands if a script requests an agreement. Proof production and elaboration
can fail, but their outcomes do not add work to this algorithmic cost model. -/
theorem source_prepared_proof_bound {ε : Type}
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (proofSource : CertificateChecking.ProofSource)
    (checks : CertificateChecking.NativeCall → FiniteModel4 → Costed Bool)
    (proofResult : CertificateChecking.NativeCall → Bool → Except ε String)
    (proofFailed : Bool)
    (registered : ∀ request ∈ proofSource.script.nativeCalls, ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success))).toList ∧
      checks request (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success)) = entry.run ()) :
    let operand := fun request (_ : Unit) => reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) (checks request)
    (preparedProofAttemptCosted proofSource (fun request => Costed.map (proofResult request)
      (nativeRequestCosted request (operand request) (operand request))) proofFailed).cost ≤
      proofSource.script.checkerCalls * (54896424 * (sourceMetrics source).inputSize ^ 16) +
        4 * proofSource.script.nativeCalls.length + 1 := by
  have bound := nativeScript_prepare_source_bound source source compiled compiled
    success success hw ht hw ht proofSource.script checks proofResult registered (by
      intro request member
      cases request with
      | expect field answer => trivial
      | agree field name => exact registered (.agree field name) member)
  simpa only [preparedProofAttempt_cost, Nat.max_self] using bound

/-- Either semantic proof form needs at most one registered checker operand.
This source-only bound includes reconstruction, that checker, its comparison,
and preparation control. It holds for every observed proof outcome, including
failure before the declaration can be accepted. -/
theorem source_prepared_semantic_bound {ε : Type}
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (field : CertField) (declaration : Bool)
    (checks : CertificateChecking.NativeCall → FiniteModel4 → Costed Bool)
    (proofResult : CertificateChecking.NativeCall → Bool → Except ε String)
    (proofFailed : Bool)
    (registered : ∀ request ∈ (if declaration then
        certAxiomTheorem compiled.ast.worldCount compiled.ast.thingCount compiled.tables field
      else certAxiomProofCheck compiled.ast.worldCount compiled.ast.thingCount compiled.tables field
      ).script.nativeCalls, ∃ entry : BoundedCheck,
      entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success))).toList ∧
      checks request (compileVerifiedModel compiled.ast hw ht
        (compileModelSource_ok_wellBounded source compiled success)) = entry.run ()) :
    let proofSource := if declaration then
      certAxiomTheorem compiled.ast.worldCount compiled.ast.thingCount compiled.tables field
      else certAxiomProofCheck compiled.ast.worldCount compiled.ast.thingCount compiled.tables field
    let operand := fun request (_ : Unit) => reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) (checks request)
    (preparedProofAttemptCosted proofSource (fun request => Costed.map (proofResult request)
      (nativeRequestCosted request (operand request) (operand request))) proofFailed).cost ≤
      54896424 * (sourceMetrics source).inputSize ^ 16 + 5 := by
  let proofSource := if declaration then
    certAxiomTheorem compiled.ast.worldCount compiled.ast.thingCount compiled.tables field
    else certAxiomProofCheck compiled.ast.worldCount compiled.ast.thingCount compiled.tables field
  have bound := source_prepared_proof_bound source compiled success hw ht proofSource checks
    proofResult proofFailed registered
  have count : proofSource.script.checkerCalls ≤ 1 := semanticProofSource_checkerCalls
    compiled.ast.worldCount compiled.ast.thingCount compiled.tables field declaration
  have requests := (script_nativeCalls_le_checkerCalls proofSource.script).trans count
  have scaled := Nat.mul_le_mul_right (54896424 * (sourceMetrics source).inputSize ^ 16) count
  dsimp only [proofSource] at bound count requests scaled ⊢
  omega

/-- The failed field's counterexample probe prepares at most two registered
checker operands. The bound includes both reconstructions, comparisons, and
request-loop control. It excludes proof search and the subsequent diagnostic
report, whose cost is bounded separately. -/
theorem source_prepared_counterexample_bound {ε : Type}
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < compiled.ast.worldCount) (ht : 0 < compiled.ast.thingCount)
    (field : CertField)
    (checks : CertificateChecking.NativeCall → FiniteModel4 → Costed Bool)
    (proofResult : CertificateChecking.NativeCall → Bool → Except ε String)
    (proofFailed : Bool)
    (registered : ∀ request ∈ (certAxiomCounterexampleCheck field).script.nativeCalls,
      ∃ entry : BoundedCheck,
        entry ∈ (Checker.checkAxioms4BoundedRegistry (compileVerifiedModel compiled.ast hw ht
          (compileModelSource_ok_wellBounded source compiled success))).toList ∧
        checks request (compileVerifiedModel compiled.ast hw ht
          (compileModelSource_ok_wellBounded source compiled success)) = entry.run ()) :
    let operand := fun request (_ : Unit) => reconstructedCheckCosted compiled.ast hw ht
      (compileModelSource_ok_wellBounded source compiled success) (checks request)
    (preparedProofAttemptCosted (certAxiomCounterexampleCheck field)
      (fun request => Costed.map (proofResult request)
        (nativeRequestCosted request (operand request) (operand request))) proofFailed).cost ≤
      2 * (54896424 * (sourceMetrics source).inputSize ^ 16) + 9 := by
  have bound := source_prepared_proof_bound source compiled success hw ht
    (certAxiomCounterexampleCheck field) checks proofResult proofFailed registered
  have count := counterexampleProofSource_checkerCalls field
  have requests := (script_nativeCalls_le_checkerCalls
    (certAxiomCounterexampleCheck field).script).trans count
  have scaled := Nat.mul_le_mul_right (54896424 * (sourceMetrics source).inputSize ^ 16) count
  dsimp only at bound ⊢
  omega

/-- A reuse comparison includes the selected child and parent computations.
Their membership premises prevent substituting an unbounded callback. Model
construction is separate; both explicit model sizes occur in this bound. -/
theorem registered_reuse_comparison_bound
    (childModel parentModel : FiniteModel4) (child parent : BoundedCheck)
    (childMember : child ∈ (Checker.checkAxioms4BoundedRegistry childModel).toList)
    (parentMember : parent ∈ (Checker.checkAxioms4BoundedRegistry parentModel).toList) :
    (CertificateChecking.compareChecksCosted child.run parent.run).cost ≤
      8367 * checkerInputSize childModel ^ 8 +
      8367 * checkerInputSize parentModel ^ 8 + 1 := by
  rw [reuseComparison_cost]
  have hc := registered_check_scalar_bound childModel child childMember
  have hp := registered_check_scalar_bound parentModel parent parentMember
  omega

/-- Successful source compilation supplies the exact tables and cached model
used by this component sum. The bound charges compilation, model construction,
and one aggregate checker invocation. It does not describe the frontend's
per-field proof driver, which can repeat checks and emit diagnostic reports. -/
theorem source_linked_component_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let construction := compiled.tables.toFiniteModel4CachedCosted
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    let m := sourceMetrics source
    compilerOperationalCost source + construction.cost +
      (Checker.checkAxioms4Costed construction.value).cost ≤
      sourceCompilerPolynomial m +
        (4 + m.worlds * (7 * m.productFamilySlots + 20 * m.productFamilies) +
          2 * m.productFamilies) + 8367 * (3 * m.inputSize ^ 2) ^ 8 := by
  dsimp only
  apply Nat.add_le_add
  · exact Nat.add_le_add (compilerOperationalCost_le source)
      (finiteModelConstructionCost_le_sourceMetrics source compiled success hw ht)
  · apply (fixed_registry_scalar_data_complexity_bound _).trans
    apply Nat.mul_le_mul_left 8367
    apply Nat.pow_le_pow_left
    exact finiteModelInputSize_le_sourceInputSize_sq source compiled success hw ht

/-- A source-only corollary for one compiler/construction/checker sequence.
The model is the successful compiler's output, not an independent input.
Model size is at most 3N², so the degree-eight checker bound gives degree
sixteen in source size N. This theorem bounds one source-operation sequence;
`Complexity/Certification.lean` separately composes the frontend's repeated
calls. Neither result measures further native optimization or instruction counts. -/
theorem source_linked_component_scalar_bound
    (source : ModelSource) (compiled : CompiledModelSource)
    (success : compileModelSource source = .ok compiled)
    (hw : 0 < source.worlds.size) (ht : 0 < source.things.size) :
    let construction := compiled.tables.toFiniteModel4CachedCosted
      source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2
    compilerOperationalCost source + construction.cost +
      (Checker.checkAxioms4Costed construction.value).cost ≤
      54896424 * (sourceMetrics source).inputSize ^ 16 := by
  dsimp only
  let n := (sourceMetrics source).inputSize
  have hn : 0 < n := sourceMetrics_inputSize_pos source
  have compiler := source_compiler_scalar_polynomial_bound source
  have construction := finiteModelConstructionCost_le_sourceInputSize_sq
    source compiled success hw ht
  have checker := fixed_registry_scalar_data_complexity_bound
    (compiled.tables.toFiniteModel4Cached source.worlds.size source.things.size hw ht
      (compileModelSource_ok_lookups_agree source compiled success)
      (compileModelSource_ok_inherenceCacheValid source compiled success)
      (compileModelSource_ok_tableDimensions source compiled success).1
      (compileModelSource_ok_tableDimensions source compiled success).2)
  have size := finiteModelInputSize_le_sourceInputSize_sq source compiled success hw ht
  have checkerBound := checker.trans (Nat.mul_le_mul_left 8367 (Nat.pow_le_pow_left size 8))
  have square : n ^ 2 ≤ n ^ 16 := Nat.pow_le_pow_right hn (by omega)
  have fourth : n ^ 4 ≤ n ^ 16 := Nat.pow_le_pow_right hn (by omega)
  have compilerBound := compiler.trans (Nat.mul_le_mul_left 511 fourth)
  have constructionBound := construction.trans (Nat.mul_le_mul_left 26 square)
  have power : (3 * n ^ 2) ^ 8 = 6561 * n ^ 16 := by ring
  change _ ≤ 8367 * (3 * n ^ 2) ^ 8 at checkerBound
  rw [power] at checkerBound
  change _ ≤ 54896424 * n ^ 16
  simp only [FactTables.toFiniteModel4Cached] at checkerBound
  omega

/-- Sum of the source compiler and checker counters on independent inputs.
This definition does not require M to come from source. A pipeline theorem
must establish that connection and include model-conversion work. -/
def sourceToCertificationCost (source : ModelSource) (M : FiniteModel4) : Nat :=
  compilerOperationalCost source + (Checker.checkAxioms4Costed M).cost

/-- Polynomial bound on the independent counter sum. Both input sizes appear
explicitly. This arithmetic result alone does not prove a source-to-result
execution bound: it neither connects M to source nor charges model conversion. -/
theorem combined_source_to_certification_scalar_bound
    (source : ModelSource) (M : FiniteModel4) :
    sourceToCertificationCost source M ≤
      8878 * ((sourceMetrics source).inputSize + checkerInputSize M) ^ 8 := by
  let sourceSize := (sourceMetrics source).inputSize
  let modelSize := checkerInputSize M
  let totalSize := sourceSize + modelSize
  have hsource : sourceSize ≤ totalSize := by
    simp only [totalSize]
    omega
  have hmodel : modelSize ≤ totalSize := by
    simp only [totalSize]
    omega
  have htotal : 0 < totalSize := by
    have hs : 0 < sourceSize := sourceMetrics_inputSize_pos source
    simp only [totalSize]
    omega
  have hcompiler := source_compiler_scalar_polynomial_bound source
  change compilerOperationalCost source ≤ 511 * sourceSize ^ 4 at hcompiler
  have hsourcePow : sourceSize ^ 4 ≤ totalSize ^ 4 :=
    Nat.pow_le_pow_left hsource 4
  have hpow4to8 : totalSize ^ 4 ≤ totalSize ^ 8 :=
    Nat.pow_le_pow_right htotal (by omega)
  have hcompilerTotal : compilerOperationalCost source ≤ 511 * totalSize ^ 8 :=
    hcompiler.trans <| (Nat.mul_le_mul_left 511 <| hsourcePow.trans hpow4to8)
  have hchecker := fixed_registry_scalar_data_complexity_bound M
  change (Checker.checkAxioms4Costed M).cost ≤ 8367 * modelSize ^ 8 at hchecker
  have hmodelPow : modelSize ^ 8 ≤ totalSize ^ 8 :=
    Nat.pow_le_pow_left hmodel 8
  have hcheckerTotal : (Checker.checkAxioms4Costed M).cost ≤
      8367 * totalSize ^ 8 :=
    hchecker.trans (Nat.mul_le_mul_left 8367 hmodelPow)
  unfold sourceToCertificationCost
  change _ ≤ 8878 * totalSize ^ 8
  omega

/-- Compose the supplied cost proof for each executable check. These checks
can have different bounds. This theorem does not infer a bound from formula
syntax; that is an obligation of the check or formula interpreter. -/
theorem heterogeneous_registry_operational_bound
    (checks : Array BoundedCheck) :
    (checkBoundedRegistryCosted checks).cost ≤ boundedRegistryCostBound checks :=
  checkBoundedRegistryCosted_cost_le checks

/-- A variable-size registry bound assuming a uniform bound on each check.
Following Vardi's data/combined-complexity distinction, registry length alone
does not bound arbitrary formula evaluation: `hCheck` must be supplied. -/
theorem parameterized_registry_operational_bound (checks : Array CheckThunk)
    (perCheck : Nat) (hCheck : ∀ check ∈ checks, (check ()).cost ≤ perCheck) :
    (checkRegistryCosted checks).cost ≤ checks.size * (perCheck + 3) :=
  checkRegistryCosted_cost_le checks perCheck hCheck

end LeanUfo.UFO.DSL.Complexity
