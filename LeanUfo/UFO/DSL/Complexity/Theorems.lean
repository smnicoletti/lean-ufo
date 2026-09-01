import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Complexity.Compiler
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Complexity.Closure
import LeanUfo.UFO.DSL.Complexity.Tables
import LeanUfo.UFO.DSL.Checker.Axioms
import Mathlib.Tactic.Ring

/-!
# Public complexity theorem boundary

Only operational results are exported here. The module provides a
data-complexity theorem for the fixed UFO registry. Separate results expose
registry and formula cost, following the distinction used by Vardi and
Madelaine--Martin.
-/

namespace LeanUfo.UFO.DSL.Complexity

theorem closure_cost_cubic (n : Nat) (edge : Nat → Nat → Bool) :
    (warshallMatrixCosted n (fun i j => edge i.val j.val)).cost =
      7 * n ^ 3 + 5 * n ^ 2 := by rfl

theorem diagnostic_output_bound (budget : Nat) (items : Array α) :
    (boundedEvidenceCosted budget items).value.items.size ≤ budget := by
  simp [boundedEvidenceCosted]

/-- Public multivariate bound for the actual short-circuiting source compiler. -/
theorem source_compiler_operational_bound (source : ModelSource) :
    compilerOperationalCost source ≤
      sourceCompilerPolynomial (sourceMetrics source) :=
  compilerOperationalCost_le source

/-- Scalar quartic corollary, derived from the explicit multivariate source
metrics only after all independently sized source components are included. -/
theorem source_compiler_scalar_polynomial_bound (source : ModelSource) :
    compilerOperationalCost source ≤
      80 * (sourceMetrics source).inputSize ^ 4 :=
  compilerOperationalCost_le_inputSize_pow4 source

/-- Representative per-axiom operational bound. The complete fixed-registry
result below composes this bound with the other 115 concrete entry bounds. -/
theorem axiom9_operational_bound (M : FiniteModel4) :
    (Checker.checkAx9Costed M).cost ≤
      M.thingCount * (M.worldCount * 7 + 2) :=
  Checker.checkAx9Costed_cost_le M

theorem axioms1_to_2_registry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms1To2Costed M).cost ≤ 2 *
      (M.thingCount * (M.worldCount *
        (M.worldCount * (M.thingCount * 3 + 2) +
          M.worldCount * (M.thingCount * 3 + 3) + 5) + 2) + 2) :=
  Checker.checkAxioms1To2Costed_cost_le M

theorem axiom3_operational_bound (M : FiniteModel4) :
    (Checker.checkAx3Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * (M.worldCount * (M.thingCount * 3 + 2)) + 7) + 2) + 2) :=
  Checker.checkAx3Costed_cost_le M

theorem axiom4_operational_bound (M : FiniteModel4) :
    (Checker.checkAx4Costed M).cost ≤ M.worldCount *
      (M.thingCount * (M.thingCount *
        (M.thingCount * (M.worldCount * (M.thingCount * 3 + 2) + 7) + 2) + 2) + 2) :=
  Checker.checkAx4Costed_cost_le M

theorem axiom5_operational_bound (M : FiniteModel4) :
    (Checker.checkAx5Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (2 * (M.worldCount * (M.thingCount * 3 + 2)) +
          M.worldCount * (M.thingCount * 6 + 2) + 7) + 2) + 2) :=
  Checker.checkAx5Costed_cost_le M

theorem axiom6_operational_bound (M : FiniteModel4) :
    (Checker.checkAx6Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (14 * M.thingCount + 14) + 2) + 2) + 2) :=
  Checker.checkAx6Costed_cost_le M

/-- Complete operational result for the first seventeen registered axioms. -/
theorem axioms1_to_17_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms1To17Costed M).cost ≤ Checker.axioms1To17CostBound M :=
  Checker.checkAxioms1To17Costed_cost_le M

/-- Operational bound for the first five-check, genuinely short-circuiting slice. -/
theorem axioms7_to_17_registry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms7To17Costed M).cost ≤
      11 * (M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 8) + 2) + 2) :=
  Checker.checkAxioms7To17Costed_cost_le M

/--
Operational bound for the first modal-rigidity axiom.  Its semantic soundness
theorem is separate: this result only bounds the actual counted
thing/world scans and their short-circuiting Boolean composition.
-/
theorem axiom18_operational_bound (M : FiniteModel4) :
    (Checker.checkAx18Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (6 * M.worldCount + 4) + 7) + 2) :=
  Checker.checkAx18Costed_cost_le M

theorem axiom19_operational_bound (M : FiniteModel4) :
    (Checker.checkAx19Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (7 * M.worldCount + 4) + 7) + 2) :=
  Checker.checkAx19Costed_cost_le M

theorem axiom20_operational_bound (M : FiniteModel4) :
    (Checker.checkAx20Costed M).cost ≤
      M.thingCount * (M.worldCount * 12 + 2) :=
  Checker.checkAx20Costed_cost_le M

theorem axiom21_operational_bound (M : FiniteModel4) :
    (Checker.checkAx21Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (3 * M.worldCount + 4) + 5) + 2) :=
  Checker.checkAx21Costed_cost_le M

theorem axiom22_operational_bound (M : FiniteModel4) :
    (Checker.checkAx22Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (M.worldCount * (M.thingCount * 7 + 2) + 8) + 2) + 2) :=
  Checker.checkAx22Costed_cost_le M

theorem axiom23_operational_bound (M : FiniteModel4) :
    (Checker.checkAx23Costed M).cost ≤ M.thingCount *
      (M.worldCount *
        (M.thingCount * (M.worldCount * (M.thingCount * 6 + 2) + 4) + 7) + 2) :=
  Checker.checkAx23Costed_cost_le M

/-- Direct classification equivalence used by axioms 29--31. -/
theorem classification_iff_and_operational_bound (M : FiniteModel4) (left first second) :
    (Checker.checkUnaryIffAndCosted M left first second).cost ≤
      M.thingCount * (M.worldCount * 8 + 2) :=
  Checker.checkUnaryIffAndCosted_cost_le M left first second

/-- Negated classification equivalence used by axiom 24. -/
theorem classification_iff_and_not_operational_bound (M : FiniteModel4) (left first second) :
    (Checker.checkUnaryIffAndNotCosted M left first second).cost ≤
      M.thingCount * (M.worldCount * 9 + 2) :=
  Checker.checkUnaryIffAndNotCosted_cost_le M left first second

/-- Disjunction/conjunction classification equivalence used by axioms 26, 28, and 33. -/
theorem classification_iff_or_and_operational_bound (M : FiniteModel4)
    (leftA leftB rightA rightB) :
    (Checker.checkUnaryIffOrAndCosted M leftA leftB rightA rightB).cost ≤
      M.thingCount * (M.worldCount * 10 + 2) :=
  Checker.checkUnaryIffOrAndCosted_cost_le M leftA leftB rightA rightB

/-- World-first disjointness used by axioms 25, 27, and 32. -/
theorem classification_world_first_disjoint_operational_bound (M : FiniteModel4)
    (left right) :
    (Checker.checkWorldFirstDisjointCosted M left right).cost ≤
      M.worldCount * (M.thingCount * 6 + 2) :=
  Checker.checkWorldFirstDisjointCosted_cost_le M left right

/--
Operational bound for the delayed 16-check registry slice.  The factor 16 is
the explicit registry size; the additional two units per entry are traversal
and short-circuit bookkeeping from `checkRegistryCosted`.
-/
theorem axioms18_to_33_registry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxioms18To33Costed M).cost ≤
      16 * (Checker.axioms18To33PerCheckBound M + 2) :=
  Checker.checkAxioms18To33Costed_cost_le M

/-- Shared operational bound for the three post-33 two-thing bridge checks. -/
theorem two_things_worlds_bridge_operational_bound (M : FiniteModel4)
    (first second consequent) :
    (Checker.checkTwoThingsWorldsImpCosted M first second consequent).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  Checker.checkTwoThingsWorldsImpCosted_cost_le M first second consequent

/-- Operational bound for the post-33 kind-stability bridge. -/
theorem kind_stability_bridge_operational_bound (M : FiniteModel4) :
    (Checker.checkAxKindStableCosted M).cost ≤
      M.thingCount * (M.worldCount * (M.worldCount * 6 + 2) + 2) :=
  Checker.checkAxKindStableCosted_cost_le M

/-- Concrete quadratic bound for the production quality uniqueness predicate. -/
theorem quality_predicate_operational_bound (M : FiniteModel4)
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (Checker.qualityBCosted M x w).cost ≤
      M.thingCount * (M.thingCount * 8 + 6) :=
  Checker.qualityBCosted_cost_le M x w

theorem axiom34_operational_bound (M : FiniteModel4) :
    (Checker.checkAx34Costed M).cost ≤
      M.thingCount * (M.worldCount * 8 + 2) :=
  Checker.checkAx34Costed_cost_le M

theorem axiom36_operational_bound (M : FiniteModel4) :
    (Checker.checkAx36Costed M).cost ≤
      M.thingCount * (M.worldCount * 10 + 2) :=
  Checker.checkAx36Costed_cost_le M

theorem axiom42_operational_bound (M : FiniteModel4) :
    (Checker.checkAx42Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.thingCount * (M.thingCount * 8 + 6) + 7) + 2) :=
  Checker.checkAx42Costed_cost_le M

theorem axiom43_operational_bound (M : FiniteModel4) :
    (Checker.checkAx43Costed M).cost ≤ M.worldCount *
      (M.thingCount * (M.thingCount * (M.thingCount * 8 + 6) + 5) + 2) :=
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
      6 * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  Checker.checkAx45Costed_cost_le M

/-- Concrete nested witness-search bound for axiom 46. -/
theorem axiom46_operational_bound (M : FiniteModel4) :
    (Checker.checkAx46Costed M).cost ≤ M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 15 + 2) + 5) + 2) :=
  Checker.checkAx46Costed_cost_le M

/-- Reflexive parthood scans one explicit table cell per thing/world pair. -/
theorem axiom47_operational_bound (M : FiniteModel4) :
    (Checker.checkAx47Costed M).cost ≤
      M.thingCount * (M.worldCount * 3 + 2) :=
  Checker.checkAx47Costed_cost_le M

/-- Antisymmetry scans two thing coordinates and one world coordinate. -/
theorem axiom48_operational_bound (M : FiniteModel4) :
    (Checker.checkAx48Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  Checker.checkAx48Costed_cost_le M

/-- Transitivity adds the third explicit thing coordinate. -/
theorem axiom49_operational_bound (M : FiniteModel4) :
    (Checker.checkAx49Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
  Checker.checkAx49Costed_cost_le M

/-- Overlap equivalence includes its concrete existential common-part scan. -/
theorem axiom50_operational_bound (M : FiniteModel4) :
    (Checker.checkAx50Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 5 + 5) + 2) + 2) :=
  Checker.checkAx50Costed_cost_le M

/-- Weak supplementation includes its negated-overlap witness scan. -/
theorem axiom51_operational_bound (M : FiniteModel4) :
    (Checker.checkAx51Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 6 + 6) + 2) + 2) :=
  Checker.checkAx51Costed_cost_le M

/-- Proper parthood is a direct three-cell, negation-aware equivalence. -/
theorem axiom52_operational_bound (M : FiniteModel4) :
    (Checker.checkAx52Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 9 + 2) + 2) :=
  Checker.checkAx52Costed_cost_le M

/-- Axiom 53 evaluates its generic functional-dependence scan twice. -/
theorem axiom53_operational_bound (M : FiniteModel4) :
    (Checker.checkAx53Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * Checker.genericFunctionalDependenceBound M + 4) + 2) +
        2) :=
  Checker.checkAx53Costed_cost_le M

/-- Axiom 54 evaluates its individual functional-dependence predicate twice. -/
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
      M.thingCount * (M.thingCount * (M.worldCount * 14 + 2) + 2) :=
  Checker.checkAx56Costed_cost_le M

theorem axiom57_operational_bound (M : FiniteModel4) :
    (Checker.checkAx57Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 14 + 2) + 2) + 2) + 2) :=
  Checker.checkAx57Costed_cost_le M

/-- Axiom 58 evaluates its generic constitutional-dependence scan twice. -/
theorem axiom58_operational_bound (M : FiniteModel4) :
    (Checker.checkAx58Costed M).cost ≤ M.thingCount *
      (M.thingCount *
        (M.worldCount * (2 * Checker.genericConstitutionalDependenceBound M + 4) +
          2) + 2) :=
  Checker.checkAx58Costed_cost_le M

/-- Axiom 59 evaluates the complete constitution predicate twice. -/
theorem axiom59_operational_bound (M : FiniteModel4) :
    (Checker.checkAx59Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.thingCount *
        (M.worldCount * (2 * Checker.constitutionBound M + 4) + 2) + 2) + 2) + 2) :=
  Checker.checkAx59Costed_cost_le M

theorem axiom60_operational_bound (M : FiniteModel4) :
    (Checker.checkAx60Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.worldCount * 6 + 7) + 2) + 2) :=
  Checker.checkAx60Costed_cost_le M

theorem axiom61_operational_bound (M : FiniteModel4) :
    (Checker.checkAx61Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 7 + 2) + 2) :=
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
        (M.worldCount * (Checker.existentialDependenceBound M + 5) + 2) + 2) :=
  Checker.checkAx65Costed_cost_le M

theorem axiom66_operational_bound (M : FiniteModel4) :
    (Checker.checkAx66Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (M.worldCount * (M.thingCount * 3 + 2) + 9) + 2) + 2) :=
  Checker.checkAx66Costed_cost_le M

theorem axiom67_operational_bound (M : FiniteModel4) :
    (Checker.checkAx67Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
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
      (M.worldCount * (Checker.externallyDependentModeBound M + 9) + 2) + 2) :=
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
      (M.worldCount * (Checker.ax73PartsBound M + 5) + 2) + 2) :=
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
      (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
  Checker.checkAx76Costed_cost_le M

theorem axiom77_operational_bound (M : FiniteModel4) :
    (Checker.checkAx77Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.existsUniqueFoundedByBound M + 5) + 2) :=
  Checker.checkAx77Costed_cost_le M

theorem axiom78_operational_bound (M : FiniteModel4) :
    (Checker.checkAx78Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.sameFoundationBound M + 7) + 2) + 2) :=
  Checker.checkAx78Costed_cost_le M

/--
Axiom 79 composes the proper-part witness, pairwise compatibility, and closure
scans; modal existence implications are evaluated by the counted world scan.
-/
theorem axiom79_operational_bound (M : FiniteModel4) :
    (Checker.checkAx79Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.ax79CharacterizationBound M + 5) + 2) :=
  Checker.checkAx79Costed_cost_le M

/-- Axiom 80 explicitly charges the qua-individual/part mediation witness scan. -/
theorem axiom80_operational_bound (M : FiniteModel4) :
    (Checker.checkAx80Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax80CharacterizationBound M + 5) + 2) + 2) :=
  Checker.checkAx80Costed_cost_le M

/-- Axiom 81 charges both characterization witness directions and uniqueness. -/
theorem axiom81_operational_bound (M : FiniteModel4) :
    (Checker.checkAx81Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax81ConsequentBound M + 5) + 2) + 2) :=
  Checker.checkAx81Costed_cost_le M

/-- Axiom 82 reuses the explicit quadratic instance/inherence uniqueness scan. -/
theorem axiom82_operational_bound (M : FiniteModel4) :
    (Checker.checkAx82Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.worldCount * (Checker.ax82InstancesBound M + 7) + 2) + 2) :=
  Checker.checkAx82Costed_cost_le M

theorem axiom83_operational_bound (M : FiniteModel4) :
    (Checker.checkAx83Costed M).cost ≤
      M.thingCount * (M.worldCount * 6 + 2) :=
  Checker.checkAx83Costed_cost_le M

theorem axiom84_operational_bound (M : FiniteModel4) :
    (Checker.checkAx84Costed M).cost ≤
      M.thingCount * (M.worldCount * 6 + 2) :=
  Checker.checkAx84Costed_cost_le M

theorem axiom85_operational_bound (M : FiniteModel4) :
    (Checker.checkAx85Costed M).cost ≤
      M.worldCount * (M.thingCount * 6 + 2) :=
  Checker.checkAx85Costed_cost_le M

theorem axiom86_operational_bound (M : FiniteModel4) :
    (Checker.checkAx86Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.qualityStructureBound M +
        Checker.nonEmptySetBound M + 6) + 2) :=
  Checker.checkAx86Costed_cost_le M

/-- Nested uniqueness: a unique structure containing the quale, where each
structure test is itself an explicit unique quality-type witness search. -/
theorem axiom87_operational_bound (M : FiniteModel4) :
    (Checker.checkAx87Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.existsUniqueQualityStructureMemberBound M + 5) + 2) :=
  Checker.checkAx87Costed_cost_le M

theorem axiom88_operational_bound (M : FiniteModel4) :
    (Checker.checkAx88Costed M).cost ≤ M.thingCount *
      (M.worldCount * (Checker.qualityStructureBound M + 7) + 2) :=
  Checker.checkAx88Costed_cost_le M

theorem axiom89_operational_bound (M : FiniteModel4) :
    (Checker.checkAx89Costed M).cost ≤
      M.thingCount * (M.worldCount * 7 + 2) :=
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
      (M.worldCount * (Checker.existsUniqueQualityStructureForTypeBound M + 7) + 2) :=
  Checker.checkAx91Costed_cost_le M

theorem axiom92_operational_bound (M : FiniteModel4) :
    (Checker.checkAx92Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (Checker.qualityBound M + 7) + 2) + 2) :=
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
      (M.thingCount * (M.worldCount * (Checker.ax94WitnessBound M + 5) + 2) + 2) :=
  Checker.checkAx94Costed_cost_le M

/-- Axiom 95 includes the complete instance scan and the concrete unique-quality
classification used to recognize a simple quality type. -/
theorem axiom95_operational_bound (M : FiniteModel4) :
    (Checker.checkAx95Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.simpleQualityTypeBound M + 8) + 2) + 2) :=
  Checker.checkAx95Costed_cost_le M

/-- Axiom 96 charges the current repeated simple/complex-quality computation
inside every instance test; no unproved cache is assumed. -/
theorem axiom96_operational_bound (M : FiniteModel4) :
    (Checker.checkAx96Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.complexQualityTypeBound M + 8) + 2) + 2) :=
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
        (Checker.productFamilySearchBound M + 7) + 2) + 2) :=
  Checker.checkAx99Costed_cost_le M

/-- Axiom 100 charges the common-quality-structure witness scan for every
distance tuple. -/
theorem axiom100_operational_bound (M : FiniteModel4) :
    (Checker.checkAx100Costed M).cost ≤ M.thingCount * (M.thingCount *
      (M.thingCount * (M.worldCount * (5 * M.thingCount + 9) + 2) + 2) + 2) :=
  Checker.checkAx100Costed_cost_le M

/-- Axiom 101 replaces its `∃! distance` decision with explicit distance
candidate and uniqueness scans. -/
theorem axiom101_operational_bound (M : FiniteModel4) :
    (Checker.checkAx101Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount *
        (Checker.existsUniqueDistanceBound M + 7) + 2) + 2) :=
  Checker.checkAx101Costed_cost_le M

theorem axiom102_operational_bound (M : FiniteModel4) :
    (Checker.checkAx102Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
  Checker.checkAx102Costed_cost_le M

/-- Axiom 103 charges its nested overlap/manifests equivalence scan. -/
theorem axiom103_operational_bound (M : FiniteModel4) :
    (Checker.checkAx103Costed M).cost ≤ M.thingCount *
      (M.thingCount * (M.worldCount * (M.thingCount * 8 + 9) + 2) + 2) :=
  Checker.checkAx103Costed_cost_le M

theorem axiom104_operational_bound (M : FiniteModel4) :
    (Checker.checkAx104Costed M).cost ≤
      M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) :=
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
      M.thingCount * (M.thingCount * (M.worldCount * 6 + 2) + 2) :=
  Checker.checkAxQuaIndividualOfEndurantCosted_cost_le M

theorem distance_identity_operational_bound (M : FiniteModel4) :
    (Checker.checkAxDistanceIdentityCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 8 + 2) + 2) + 2) :=
  Checker.checkAxDistanceIdentityCosted_cost_le M

theorem distance_symmetry_operational_bound (M : FiniteModel4) :
    (Checker.checkAxDistanceSymmetryCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.worldCount * 6 + 2) + 2) + 2) :=
  Checker.checkAxDistanceSymmetryCosted_cost_le M

theorem distance_triangle_operational_bound (M : FiniteModel4) :
    (Checker.checkAxDistanceTriangleCosted M).cost ≤ M.thingCount *
      (M.thingCount * (M.thingCount * (M.thingCount * (M.thingCount *
        (M.thingCount * (M.thingCount * (M.worldCount * 12 + 2) + 2) + 2) + 2) + 2) + 2) + 2) :=
  Checker.checkAxDistanceTriangleCosted_cost_le M

/-!
## Scalar checker ingredients

The scalar checker size includes dense relation cells and product-family
witness arrays. Axiom 99 is the only fixed-registry entry whose concrete bound
depends on those arrays, so its search bound is discharged separately before
the heterogeneous 116-entry sum is majorized. This preserves the concrete
computation rather than silently treating witnesses as an oracle.
-/

theorem product_family_witness_bound_le_checkerInputSize_sq
    (M : FiniteModel4) (i : Fin M.productFamilies.size) :
    Checker.productFamilyWitnessBound M M.productFamilies[i] ≤
      40 * checkerInputSize M ^ 2 := by
  let n := checkerInputSize M
  have hn : 1 ≤ n := by
    have := checkerInputSize_pos M
    simp only [n]
    omega
  have ht : M.thingCount ≤ n := by
    simpa [n] using thingCount_le_checkerInputSize M
  have hd : M.productFamilies[i].dimensionThings.size ≤ n := by
    simpa [n] using productFamilyDimension_le_checkerInputSize M i
  have htd : M.thingCount * M.productFamilies[i].dimensionThings.size ≤ n ^ 2 := by
    simpa [Nat.pow_two] using Nat.mul_le_mul ht hd
  have hn_sq : n ≤ n ^ 2 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * n := Nat.mul_le_mul_left n hn
      _ = n ^ 2 := by simp [Nat.pow_two]
  have ht_sq : M.thingCount ≤ n ^ 2 := ht.trans hn_sq
  have hone_sq : 1 ≤ n ^ 2 := hn.trans hn_sq
  have hprojection :
      M.thingCount * (5 * M.productFamilies[i].dimensionThings.size + 5) ≤
        10 * n ^ 2 := by
    calc
      M.thingCount * (5 * M.productFamilies[i].dimensionThings.size + 5) =
          5 * (M.thingCount * M.productFamilies[i].dimensionThings.size) +
            5 * M.thingCount := by
        rw [Nat.mul_add]
        congr 1 <;> ac_rfl
      _ ≤ 5 * n ^ 2 + 5 * n ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left 5 htd)
          (Nat.mul_le_mul_left 5 ht_sq)
      _ = 10 * n ^ 2 := by omega
  have hslots : M.productFamilies[i].dimensionThings.size * 8 ≤ 8 * n ^ 2 := by
    have := hd.trans hn_sq
    omega
  have hcoverage :
      M.thingCount * (4 * M.productFamilies[i].dimensionThings.size + 5) ≤
        9 * n ^ 2 := by
    calc
      M.thingCount * (4 * M.productFamilies[i].dimensionThings.size + 5) =
          4 * (M.thingCount * M.productFamilies[i].dimensionThings.size) +
            5 * M.thingCount := by
        rw [Nat.mul_add]
        congr 1 <;> ac_rfl
      _ ≤ 4 * n ^ 2 + 5 * n ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_left 4 htd)
          (Nat.mul_le_mul_left 5 ht_sq)
      _ = 9 * n ^ 2 := by omega
  change 8 + M.thingCount * (5 * M.productFamilies[i].dimensionThings.size + 5) +
      M.productFamilies[i].dimensionThings.size * 8 +
      M.thingCount * (4 * M.productFamilies[i].dimensionThings.size + 5) ≤
    40 * n ^ 2
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

theorem product_family_search_bound_le_checkerInputSize_cube (M : FiniteModel4) :
    Checker.productFamilySearchBound M ≤ 42 * checkerInputSize M ^ 3 := by
  let n := checkerInputSize M
  have hn : 1 ≤ n := by
    have := checkerInputSize_pos M
    simp only [n]
    omega
  have hn_sq : 1 ≤ n ^ 2 := by
    simpa [Nat.pow_two] using Nat.mul_le_mul hn hn
  have hcount : M.productFamilies.size ≤ n := by
    simpa [n] using productFamilyCount_le_checkerInputSize M
  unfold Checker.productFamilySearchBound
  calc
    ((List.finRange M.productFamilies.size).map fun i =>
        Checker.productFamilyWitnessBound M M.productFamilies[i] + 2).sum ≤
        (List.finRange M.productFamilies.size).length * (42 * n ^ 2) := by
      apply list_sum_map_le_const
      intro i hi
      have hw := product_family_witness_bound_le_checkerInputSize_sq M i
      change Checker.productFamilyWitnessBound M M.productFamilies[i] ≤ 40 * n ^ 2 at hw
      change Checker.productFamilyWitnessBound M M.productFamilies[i] + 2 ≤
        42 * n ^ 2
      omega
    _ = M.productFamilies.size * (42 * n ^ 2) := by simp
    _ ≤ n * (42 * n ^ 2) := Nat.mul_le_mul_right (42 * n ^ 2) hcount
    _ = 42 * n ^ 3 := by
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
    (Checker.checkAx99Costed M).cost ≤ 53 * checkerInputSize M ^ 6 := by
  let n := checkerInputSize M
  have hn : 1 ≤ n := by
    have := checkerInputSize_pos M
    simp only [n]
    omega
  have ht : M.thingCount ≤ n := by
    simpa [n] using thingCount_le_checkerInputSize M
  have hw : M.worldCount ≤ n := by
    simpa [n] using worldCount_le_checkerInputSize M
  have hsearch := product_family_search_bound_le_checkerInputSize_cube M
  change Checker.productFamilySearchBound M ≤ 42 * n ^ 3 at hsearch
  have hcube : 1 ≤ n ^ 3 := one_le_pow_of_one_le n 3 hn
  have hbase : Checker.productFamilySearchBound M + 5 ≤ 47 * n ^ 3 := by
    omega
  have hworld :
      M.worldCount * (Checker.productFamilySearchBound M + 7) ≤
        49 * n ^ 4 := by
    exact scan_layer_scalar_bound n 47 3 M.worldCount
      (Checker.productFamilySearchBound M + 5) hn hw hbase
  have hthingInner :
      M.thingCount *
          (M.worldCount * (Checker.productFamilySearchBound M + 7) + 2) ≤
        51 * n ^ 5 := by
    exact scan_layer_scalar_bound n 49 4 M.thingCount
      (M.worldCount * (Checker.productFamilySearchBound M + 7)) hn ht hworld
  have hthingOuter : M.thingCount *
      (M.thingCount *
          (M.worldCount * (Checker.productFamilySearchBound M + 7) + 2) + 2) ≤
        53 * n ^ 6 := by
    exact scan_layer_scalar_bound n 51 5 M.thingCount
      (M.thingCount *
        (M.worldCount * (Checker.productFamilySearchBound M + 7) + 2)) hn ht hthingInner
  exact (Checker.checkAx99Costed_cost_le M).trans hthingOuter

/-- The production checker is the erasure of the exact, delayed 116-check registry. -/
theorem fixed_registry_size (M : FiniteModel4) :
    (Checker.checkAxioms4BoundedRegistry M).size = 116 :=
  Checker.checkAxioms4BoundedRegistry_size M

theorem fixed_registry_erases_to_legacy (M : FiniteModel4) :
    Checker.checkAxioms4 M = (Checker.checkAxioms4Checks M).all id :=
  Checker.checkAxioms4_eq_legacy M

/-- Fixed-formula data-complexity theorem. The right side definitionally
expands to the heterogeneous sum of all 116 concrete per-check polynomials and
the registry traversal charges; it is not a separately postulated envelope. -/
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

/-- The exact heterogeneous 116-entry production bound is at most a degree-eight
polynomial in the complete explicit checker encoding. Unfolding the registry
gives ordinary monomial coefficient sum 2898; axiom 99 contributes at most 42
more after its separately proved witness-search bound. -/
theorem fixed_registry_operational_bound_le_checkerInputSize_pow8
    (M : FiniteModel4) :
    Checker.checkAxioms4OperationalBound M ≤ 2940 * checkerInputSize M ^ 8 := by
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
  have hsearch := product_family_search_bound_le_checkerInputSize_cube M
  change Checker.productFamilySearchBound M ≤ 42 * n ^ 3 at hsearch
  have h21degree3 : M.thingCount ^ 2 * M.worldCount ≤ n ^ 3 := by
    simpa using thing_world_monomial_le n M.thingCount M.worldCount 2 1 3
      hn ht hw (by omega)
  have hpow6to8 : n ^ 6 ≤ n ^ 8 := Nat.pow_le_pow_right hn (by omega)
  have hproduct : M.thingCount ^ 2 * M.worldCount *
      Checker.productFamilySearchBound M ≤ 42 * n ^ 8 := by
    calc
      M.thingCount ^ 2 * M.worldCount * Checker.productFamilySearchBound M ≤
          n ^ 3 * (42 * n ^ 3) := Nat.mul_le_mul h21degree3 hsearch
      _ = 42 * n ^ 6 := by
        simp [Nat.pow_succ]
        ac_rfl
      _ ≤ 42 * n ^ 8 := Nat.mul_le_mul_left 42 hpow6to8
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
  change _ ≤ n ^ 8 * 2940
  omega

/-- Headline one-variable data-complexity corollary for the production checker. -/
theorem fixed_registry_scalar_data_complexity_bound (M : FiniteModel4) :
    (Checker.checkAxioms4Costed M).cost ≤ 2940 * checkerInputSize M ^ 8 :=
  (fixed_registry_data_complexity_bound M).trans
    (fixed_registry_operational_bound_le_checkerInputSize_pow8 M)

/-- Concrete cost of the two production stages on a successfully compiled
source/model pair. The compiler and checker retain their separate counted
executions; this definition only composes their accumulated costs. -/
def sourceToCertificationCost (source : ModelSource) (M : FiniteModel4) : Nat :=
  compilerOperationalCost source + (Checker.checkAxioms4Costed M).cost

/-- Combined source-to-certification polynomial. Both the explicit named source
and explicit compiled checker model are independently sized because compilation
may expand scopes, taxonomy facts, specialization, and per-world product-family
witnesses. No succinct output representation is assumed. -/
theorem combined_source_to_certification_scalar_bound
    (source : ModelSource) (M : FiniteModel4) :
    sourceToCertificationCost source M ≤
      3020 * ((sourceMetrics source).inputSize + checkerInputSize M) ^ 8 := by
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
  change compilerOperationalCost source ≤ 80 * sourceSize ^ 4 at hcompiler
  have hsourcePow : sourceSize ^ 4 ≤ totalSize ^ 4 :=
    Nat.pow_le_pow_left hsource 4
  have hpow4to8 : totalSize ^ 4 ≤ totalSize ^ 8 :=
    Nat.pow_le_pow_right htotal (by omega)
  have hcompilerTotal : compilerOperationalCost source ≤ 80 * totalSize ^ 8 :=
    hcompiler.trans <| (Nat.mul_le_mul_left 80 <| hsourcePow.trans hpow4to8)
  have hchecker := fixed_registry_scalar_data_complexity_bound M
  change (Checker.checkAxioms4Costed M).cost ≤ 2940 * modelSize ^ 8 at hchecker
  have hmodelPow : modelSize ^ 8 ≤ totalSize ^ 8 :=
    Nat.pow_le_pow_left hmodel 8
  have hcheckerTotal : (Checker.checkAxioms4Costed M).cost ≤
      2940 * totalSize ^ 8 :=
    hchecker.trans (Nat.mul_le_mul_left 2940 hmodelPow)
  unfold sourceToCertificationCost
  change _ ≤ 3020 * totalSize ^ 8
  omega

/-- Heterogeneous combined-complexity form: both registry length and each
registered formula's proved operational bound remain explicit inputs. -/
theorem heterogeneous_registry_operational_bound
    (checks : Array BoundedCheck) :
    (checkBoundedRegistryCosted checks).cost ≤ boundedRegistryCostBound checks :=
  checkBoundedRegistryCosted_cost_le checks

/-- Combined-complexity theorem for an arbitrary delayed registry. Registry
size remains an input and no fixed-formula assumption is hidden. -/
theorem parameterized_registry_operational_bound (checks : Array CheckThunk)
    (perCheck : Nat) (hCheck : ∀ check ∈ checks, (check ()).cost ≤ perCheck) :
    (checkRegistryCosted checks).cost ≤ checks.size * (perCheck + 2) :=
  checkRegistryCosted_cost_le checks perCheck hCheck

end LeanUfo.UFO.DSL.Complexity
