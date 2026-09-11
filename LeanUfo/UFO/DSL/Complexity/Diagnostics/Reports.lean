import LeanUfo.UFO.DSL.Complexity.Diagnostics.Formula

/-!
# Formula-size bounds for generic diagnostic reports

`diagnosticGenericReport_cost_le_size` bounds the public producer for a registered
formula without a specialized analyzer. It includes registry lookup, variable
extraction, assignment search, failure minimization, evidence, text, and output
copying. The result concerns executed costs under the documented unit-cost model.

Let `V` be the number of leading universal variables, `s` the residual formula's
node count, and `q` its quantifier depth. With `B = W + T + 1`, assignment search
adds a factor `B^V` and nested formula traversal adds `B^q`. Fixed formulas give
polynomial bounds in model and source-fact counts. Unrestricted input formulas
can increase both exponents, so no uniform combined polynomial follows.

The proof composes bounds for the existing counted functions. This use of
compositional costs follows Niu et al., *A Cost-Aware Logical Framework*
(POPL 2022, doi:10.1145/3498670). The fixed-formula qualification follows Vardi's
data/combined-complexity distinction. See `docs/dsl/complexity.md` for references,
primitive charges, and the derivation. These are operation bounds, not
wall-clock, string-character, allocator, or kernel-checking bounds.
-/

namespace LeanUfo.UFO.DSL
open private DiagFormula DiagFormula.nodeCount DiagFormula.evalCostBound
  DiagFormula.failingAtomCountBound DiagFormula.failingAtomsCostBound
  DiagFormula.atom DiagFormula.eqThing DiagFormula.eqWorld DiagFormula.not
  DiagFormula.and DiagFormula.or DiagFormula.imp DiagFormula.iff
  DiagFormula.forallThing DiagFormula.existsThing DiagFormula.forallWorld
  DiagFormula.existsWorld DiagFormula.box DiagFormula.dia
  diagAtomCostBound evalDiagAtomCosted_cost_le minimizeFailureCosted
  MinimizedFailure.formula failedHere withContext
  failingAtomsCosted failingAtomsCosted_cost_le failingAtomsCosted_size_le
  genericDiagnosticVisitCosted genericDiagnosticWitnessesCosted DiagVar DiagTrace
  DiagTrace.formula DiagTrace.env MinimizedFailure.env MinimizedFailure.context
  minimizeFailureCosted_formula_nodeCount_le minimizeFailureCosted_trace_bounds
  evalDiagFormulaCosted evalDiagFormulaCosted_concrete_cost_le
  minimizeFailureCosted_cost_le diagnosticEnvVarsCosted diagnosticEnvVarsCosted_size_le
  diagnosticEnvVarsCosted_cost_le diagnosticEnvVarsCostBound diagnosticEnvVarsCostBound_mono
  envSummaryCosted envSummaryCosted_cost_le envSummaryCostBound_mono
  renderDiagnosticConditionLineCosted renderDiagnosticConditionLineCosted_cost_le
  renderDiagnosticConditionLineCostBound_mono suggestionForFailureCosted
  suggestionForFailureCosted_cost_le DiagFormula.suggestionCostBound
  appendContextEvidenceCosted appendContextEvidenceCosted_cost_le
  appendFailingAtomEvidenceCosted appendFailingAtomEvidenceCosted_cost_le
  appendFailingAtomEvidenceCostBound_mono appendDiagnosticPreambleCosted
  appendDiagnosticPreambleCosted_cost_le
  derivedLookupCostBound DiagVar.domainSize
  diagEnvDependentFoldCostBound foldDiagEnvsUntilCosted_dependent_cost_le
  diagnosticWitnessesInnerCosted diagnosticFormula? diagnosticFormulaRegistry
  diagnosticFormulaCosted diagnosticFormulaCosted_value diagnosticFormulaCosted_cost_le
  DiagFormula.forallVars DiagFormula.stripForalls DiagFormula.peelForallsCosted
  DiagFormula.peelForallsCosted_value DiagFormula.peelForallsCosted_cost
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis
namespace Complexity
open private diagnosticEval_le_reportBound from LeanUfo.UFO.DSL.Complexity.Diagnostics.Formula

/-- Failure selection never adds quantifier nesting. This permits the evidence
bound to reuse the original formula's exponent, even after environments merge. -/
theorem diagnosticFailureMinimize_depth_le (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    diagnosticQuantifierDepth (MinimizedFailure.formula
      (minimizeFailureCosted W T tables env formula).value) ≤ diagnosticQuantifierDepth formula := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals simp_all (config := { zetaDelta := true })
    [failedHere, withContext, Costed.charge_value, diagnosticQuantifierDepth]
  all_goals omega

-- A domain loop pays for child discovery and repeated evaluation. The extra
-- local budget absorbs loop control and any evaluation of the enclosing formula.
private theorem evidence_quantifier_step (c v u n L U B D : Nat)
    (hc : c ≤ n * L) (hv : v ≤ U) (hu : u ≤ U * B)
    (hL : 2 * U + 8 ≤ L) (hD : D ≤ B) (hB : 1 ≤ B) :
    u + D * (c + v + 6) + 2 ≤ (n + 1) * (L * B) := by
  have hm := Nat.mul_le_mul hD (Nat.add_le_add_right (Nat.add_le_add hc hv) 6)
  have hl := Nat.mul_le_mul_right B hL
  have expanded : D * (c + v + 6) ≤ n * (L * B) + U * B + 6 * B := by
    apply hm.trans_eq
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  have reserved : 2 * (U * B) + 8 * B ≤ L * B := by
    simpa only [Nat.add_mul, Nat.mul_assoc] using hl
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Each formula node receives a discovery budget at the largest permitted
environment size. Binary branches add budgets; quantifiers multiply by a domain
size. Both kinds of work occur in the executable discovery recurrence. -/
theorem diagnosticFailingAtoms_recurrence_le_size (W T : Nat) (tables : FactTables)
    (E s : Nat) (formula : DiagFormula) (e : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E)
    (hSize : DiagFormula.nodeCount formula ≤ s) :
    DiagFormula.failingAtomsCostBound W T (diagAtomCostBound W T tables) e formula ≤
      DiagFormula.nodeCount formula * ((3 * s + 3) *
        ((diagAtomCostBound W T tables E + 8 * E + 10) *
          (W + T + 1) ^ diagnosticQuantifierDepth formula)) := by
  let factor (q : Nat) := (diagAtomCostBound W T tables E + 8 * E + 10) * (W + T + 1) ^ q
  have floor (q : Nat) : 10 ≤ factor q := by
    have hp := Nat.one_le_pow q (W + T + 1) (by omega)
    have hm := Nat.mul_le_mul_left (diagAtomCostBound W T tables E + 8 * E + 10) hp
    simp only [Nat.mul_one] at hm
    dsimp only [factor]
    omega
  have localBudget (q : Nat) : s * factor q + 2 * s + 6 ≤ (3 * s + 3) * factor q := by
    have hf := floor q
    have hs := Nat.mul_le_mul_left s (show 2 ≤ factor q by omega)
    simp only [Nat.add_mul, Nat.mul_assoc] at hs ⊢
    omega
  have quantBudget (q : Nat) : 2 * (s * factor q) + 8 ≤ (3 * s + 3) * factor q := by
    have hf := floor q
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  have checked (f : DiagFormula) (e : Nat)
      (he : e + diagnosticQuantifierDepth f ≤ E) (hs : DiagFormula.nodeCount f ≤ s) :
      DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e f ≤
        s * factor (diagnosticQuantifierDepth f) :=
    diagnosticEval_le_reportBound W T tables E s (diagnosticQuantifierDepth f)
      f e he hs (Nat.le_refl _)
  change _ ≤ DiagFormula.nodeCount formula * ((3 * s + 3) * factor (diagnosticQuantifierDepth formula))
  induction formula generalizing e with
  | atom a =>
    have hc := checked (DiagFormula.atom a) e hEnv hSize
    have hl := localBudget 0
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.evalCostBound,
      DiagFormula.nodeCount, diagnosticQuantifierDepth, Nat.one_mul] at hc ⊢
    simp only [Nat.add_mul, Nat.mul_assoc] at *
    omega
  | eqThing a b | eqWorld a b =>
    have hl := localBudget 0
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_assoc] at *
    omega
  | not p ih =>
    have hc := checked (DiagFormula.not p) e hEnv hSize
    have hl := localBudget (diagnosticQuantifierDepth p)
    simp only [diagnosticQuantifierDepth] at hc
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    omega
  | and p r ihp ihr =>
    have hl := localBudget (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize
    have hpr : factor (diagnosticQuantifierDepth p) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
    have hrr : factor (diagnosticQuantifierDepth r) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hp := (ihp e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount p) (Nat.mul_le_mul_left (3 * s + 3) hpr))
    have hr := (ihr e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount r) (Nat.mul_le_mul_left (3 * s + 3) hrr))
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    omega
  | or p r ihp ihr =>
    have hc := checked (DiagFormula.or p r) e hEnv hSize
    have hl := localBudget (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hpr : factor (diagnosticQuantifierDepth p) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
    have hrr : factor (diagnosticQuantifierDepth r) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hp := (ihp e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount p) (Nat.mul_le_mul_left (3 * s + 3) hpr))
    have hr := (ihr e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount r) (Nat.mul_le_mul_left (3 * s + 3) hrr))
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    omega
  | imp p r ihp ihr =>
    have hc := checked (DiagFormula.imp p r) e hEnv hSize
    have hl := localBudget (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hrr : factor (diagnosticQuantifierDepth r) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hr := (ihr e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount r) (Nat.mul_le_mul_left (3 * s + 3) hrr))
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    omega
  | iff p r ihp ihr =>
    have hc := checked (DiagFormula.iff p r) e hEnv hSize
    have hl := localBudget (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hpr : factor (diagnosticQuantifierDepth p) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
    have hrr : factor (diagnosticQuantifierDepth r) ≤ factor
        (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hp := (ihp e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount p) (Nat.mul_le_mul_left (3 * s + 3) hpr))
    have hr := (ihr e (by omega) (by omega)).trans
      (Nat.mul_le_mul_left (DiagFormula.nodeCount r) (Nat.mul_le_mul_left (3 * s + 3) hrr))
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
    omega
  | forallThing name p ih =>
    have hc := checked (DiagFormula.forallThing name p) e hEnv hSize
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hp := ih (e + 1) (by omega) (by omega)
    have hb := checked p (e + 1) (by omega) (by omega)
    have shifted : factor (diagnosticQuantifierDepth p + 1) =
        factor (diagnosticQuantifierDepth p) * (W + T + 1) := by
      simp only [factor, Nat.pow_succ, Nat.mul_assoc]
    rw [shifted] at hc
    have h := evidence_quantifier_step _ _ _ (DiagFormula.nodeCount p)
      ((3 * s + 3) * factor (diagnosticQuantifierDepth p))
      (s * factor (diagnosticQuantifierDepth p)) (W + T + 1) T hp hb
      (by simpa only [Nat.mul_assoc] using hc) (quantBudget _) (by omega) (by omega)
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth,
      shifted, Nat.mul_assoc] at h ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega
  | forallWorld name p ih =>
    have hc := checked (DiagFormula.forallWorld name p) e hEnv hSize
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hp := ih (e + 1) (by omega) (by omega)
    have hb := checked p (e + 1) (by omega) (by omega)
    have shifted : factor (diagnosticQuantifierDepth p + 1) =
        factor (diagnosticQuantifierDepth p) * (W + T + 1) := by
      simp only [factor, Nat.pow_succ, Nat.mul_assoc]
    rw [shifted] at hc
    have h := evidence_quantifier_step _ _ _ (DiagFormula.nodeCount p)
      ((3 * s + 3) * factor (diagnosticQuantifierDepth p))
      (s * factor (diagnosticQuantifierDepth p)) (W + T + 1) W hp hb
      (by simpa only [Nat.mul_assoc] using hc) (quantBudget _) (by omega) (by omega)
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth,
      shifted, Nat.mul_assoc] at h ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega
  | existsThing name p ih =>
    have hc := checked (DiagFormula.existsThing name p) e hEnv hSize
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hp := ih (e + 1) (by omega) (by omega)
    have hb := checked p (e + 1) (by omega) (by omega)
    have shifted : factor (diagnosticQuantifierDepth p + 1) =
        factor (diagnosticQuantifierDepth p) * (W + T + 1) := by
      simp only [factor, Nat.pow_succ, Nat.mul_assoc]
    rw [shifted] at hc
    have h := evidence_quantifier_step _ _ _ (DiagFormula.nodeCount p)
      ((3 * s + 3) * factor (diagnosticQuantifierDepth p))
      (s * factor (diagnosticQuantifierDepth p)) (W + T + 1) T hp hb
      (by simpa only [Nat.mul_assoc] using hc) (quantBudget _) (by omega) (by omega)
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth,
      shifted, Nat.mul_assoc] at h ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega
  | existsWorld name p ih =>
    have hc := checked (DiagFormula.existsWorld name p) e hEnv hSize
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hp := ih (e + 1) (by omega) (by omega)
    have hb := checked p (e + 1) (by omega) (by omega)
    have shifted : factor (diagnosticQuantifierDepth p + 1) =
        factor (diagnosticQuantifierDepth p) * (W + T + 1) := by
      simp only [factor, Nat.pow_succ, Nat.mul_assoc]
    rw [shifted] at hc
    have h := evidence_quantifier_step _ _ _ (DiagFormula.nodeCount p)
      ((3 * s + 3) * factor (diagnosticQuantifierDepth p))
      (s * factor (diagnosticQuantifierDepth p)) (W + T + 1) W hp hb
      (by simpa only [Nat.mul_assoc] using hc) (quantBudget _) (by omega) (by omega)
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth,
      shifted, Nat.mul_assoc] at h ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega
  | box current name p ih =>
    have hc := checked (DiagFormula.box current name p) e hEnv hSize
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hp := ih (e + 1) (by omega) (by omega)
    have hb := checked p (e + 1) (by omega) (by omega)
    have shifted : factor (diagnosticQuantifierDepth p + 1) =
        factor (diagnosticQuantifierDepth p) * (W + T + 1) := by
      simp only [factor, Nat.pow_succ, Nat.mul_assoc]
    rw [shifted] at hc
    have h := evidence_quantifier_step _ _ _ (DiagFormula.nodeCount p)
      ((3 * s + 3) * factor (diagnosticQuantifierDepth p))
      (s * factor (diagnosticQuantifierDepth p)) (W + T + 1) W hp hb
      (by simpa only [Nat.mul_assoc] using hc) (quantBudget _) (by omega) (by omega)
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth,
      shifted, Nat.mul_assoc] at h ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega
  | dia current name p ih =>
    have hc := checked (DiagFormula.dia current name p) e hEnv hSize
    simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hc
    have hp := ih (e + 1) (by omega) (by omega)
    have hb := checked p (e + 1) (by omega) (by omega)
    have shifted : factor (diagnosticQuantifierDepth p + 1) =
        factor (diagnosticQuantifierDepth p) * (W + T + 1) := by
      simp only [factor, Nat.pow_succ, Nat.mul_assoc]
    rw [shifted] at hc
    have h := evidence_quantifier_step _ _ _ (DiagFormula.nodeCount p)
      ((3 * s + 3) * factor (diagnosticQuantifierDepth p))
      (s * factor (diagnosticQuantifierDepth p)) (W + T + 1) W hp hb
      (by simpa only [Nat.mul_assoc] using hc) (quantBudget _) (by omega) (by omega)
    simp only [DiagFormula.failingAtomsCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth,
      shifted, Nat.mul_assoc] at h ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
    omega

/-- Each leaf can contribute across at most one domain product per quantifier
path. This bounds the actual evidence array through its structural size bound. -/
theorem diagnosticFailingAtomCount_le_size (W T : Nat) (formula : DiagFormula) :
    DiagFormula.failingAtomCountBound W T formula ≤
      DiagFormula.nodeCount formula * (W + T + 1) ^ diagnosticQuantifierDepth formula := by
  have positive (q : Nat) : 1 ≤ (W + T + 1) ^ q := Nat.one_le_pow q _ (by omega)
  induction formula with
  | atom a | eqThing a b | eqWorld a b =>
    simp [DiagFormula.failingAtomCountBound, DiagFormula.nodeCount, diagnosticQuantifierDepth]
  | not p ih =>
    have hp := positive (diagnosticQuantifierDepth p)
    simp only [DiagFormula.failingAtomCountBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    omega
  | and p r ihp ihr | or p r ihp ihr | iff p r ihp ihr =>
    have hp := ihp.trans (Nat.mul_le_mul_left (DiagFormula.nodeCount p)
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_left (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))))
    have hr := ihr.trans (Nat.mul_le_mul_left (DiagFormula.nodeCount r)
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))))
    simp only [DiagFormula.failingAtomCountBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    omega
  | imp p r ihp ihr =>
    have hp := Nat.mul_le_mul_left (DiagFormula.nodeCount p)
      (positive (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r)))
    have hr := ihr.trans (Nat.mul_le_mul_left (DiagFormula.nodeCount r)
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth r))))
    simp only [Nat.mul_one] at hp
    simp only [DiagFormula.failingAtomCountBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.add_mul, Nat.one_mul]
    omega
  | forallThing name p ih | existsThing name p ih =>
    have product := Nat.mul_le_mul (show T ≤ W + T + 1 by omega) ih
    have enlarged := Nat.mul_le_mul_right ((W + T + 1) ^ diagnosticQuantifierDepth p * (W + T + 1))
      (Nat.le_succ (DiagFormula.nodeCount p))
    simp only [DiagFormula.failingAtomCountBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.pow_succ]
    apply product.trans
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using enlarged
  | forallWorld name p ih | existsWorld name p ih
  | box current name p ih | dia current name p ih =>
    have product := Nat.mul_le_mul (show W ≤ W + T + 1 by omega) ih
    have enlarged := Nat.mul_le_mul_right ((W + T + 1) ^ diagnosticQuantifierDepth p * (W + T + 1))
      (Nat.le_succ (DiagFormula.nodeCount p))
    simp only [DiagFormula.failingAtomCountBound, DiagFormula.nodeCount,
      diagnosticQuantifierDepth, Nat.pow_succ]
    apply product.trans
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using enlarged

/-- Uniform discovery bound for subformulas within common size/depth limits. -/
theorem diagnosticFailingAtoms_recurrence_le_limits (W T : Nat) (tables : FactTables)
    (E s q : Nat) (formula : DiagFormula) (e : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E)
    (hSize : DiagFormula.nodeCount formula ≤ s)
    (hDepth : diagnosticQuantifierDepth formula ≤ q) :
    DiagFormula.failingAtomsCostBound W T (diagAtomCostBound W T tables) e formula ≤
      (3 * s + 3) * diagnosticReportEvalBound W T tables E s q := by
  apply (diagnosticFailingAtoms_recurrence_le_size W T tables E s formula e hEnv hSize).trans
  have h := Nat.mul_le_mul hSize (Nat.mul_le_mul_left (3 * s + 3)
    (Nat.mul_le_mul_left (diagAtomCostBound W T tables E + 8 * E + 10)
      (Nat.pow_le_pow_right (by omega : 0 < W + T + 1) hDepth)))
  simpa only [diagnosticReportEvalBound, Nat.mul_left_comm] using h

/-- Cost of executed atom discovery, including its initial output array. -/
theorem diagnosticFailingAtoms_cost_le_size (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let q := diagnosticQuantifierDepth formula
    (failingAtomsCosted W T tables env formula).cost ≤
      (3 * s + 3) * diagnosticReportEvalBound W T tables (env.size + q) s q + 1 := by
  apply (failingAtomsCosted_cost_le W T tables (diagAtomCostBound W T tables)
    (evalDiagAtomCosted_cost_le W T tables) env formula).trans
  apply Nat.add_le_add_right
  exact diagnosticFailingAtoms_recurrence_le_limits W T tables _ _ _ formula env.size
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Number of atom records returned by the executed discovery function. -/
theorem diagnosticFailingAtoms_size_le (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsCosted W T tables env formula).value.size ≤
      DiagFormula.nodeCount formula * (W + T + 1) ^ diagnosticQuantifierDepth formula :=
  (failingAtomsCosted_size_le W T tables env formula).trans
    (diagnosticFailingAtomCount_le_size W T formula)

/-- Bound for one assignment visit. `vars` bounds both declared variables and
initial bindings. `E` includes quantified bindings, `M` includes merged failure
environments, and `H` also covers context traces. `R` bounds evaluation and
`L` is the minimizer's per-node budget. `facts` counts named source facts.
The summands include eager text and scans even when no output row fits. -/
def diagnosticGenericVisitBound (W T : Nat) (tables : FactTables)
    (facts vars s q : Nat) : Nat :=
  let E := vars + q
  let M := s * E
  let H := M + E + s
  let R := diagnosticReportEvalBound W T tables H s q
  let L := 3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * H) + 10
  R + s * L + (2 * s + 1 + M * (4 * M + 8 * (vars + s) + 5)) +
    M * (4 * M + 13) + s * (20 * M + 56) + 27 +
    s * s * (s * (diagAtomCostBound W T tables H + 60 * H + 115 + 275 * facts) + 21) +
    (s * (W + T + 1) ^ q) * (40 * M + 76 + 275 * facts) +
    2 * (R + (3 * s + 3) * R) + 8 * s + 20 * M + 53

/-- The bound applies to every initial report array and every budget.
Successful assignments pay only evaluation and branch selection. Failed ones
also pay for the actual minimized formula, its context, and its source evidence. -/
theorem diagnosticGenericVisit_cost_le_size (budget : Nat)
    (worldNames thingNames : Array Lean.Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula)
    (out : Array String) (env : Array (String × Nat)) (V : Nat)
    (hVars : vars.size ≤ V) (hEnv : env.size ≤ V) :
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body out env).cost ≤
      diagnosticGenericVisitBound worldNames.size thingNames.size tables namedFacts.size
        V (DiagFormula.nodeCount body) (diagnosticQuantifierDepth body) := by
  let W := worldNames.size
  let T := thingNames.size
  let s := DiagFormula.nodeCount body
  let q := diagnosticQuantifierDepth body
  let E := V + q
  let M := s * E
  let H := M + E + s
  let R := diagnosticReportEvalBound W T tables H s q
  let L := 3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * H) + 10
  have within : env.size + q ≤ E := by dsimp [E]; omega
  have expanded : E ≤ H := by dsimp [H]; omega
  have checked : (evalDiagFormulaCosted W T tables env body).cost ≤ R :=
    (evalDiagFormulaCosted_concrete_cost_le W T tables env body).trans
      (diagnosticEval_le_reportBound W T tables H s q body env.size
        (by omega) (Nat.le_refl _) (Nat.le_refl _))
  simp only [genericDiagnosticVisitCosted]
  split
  · change (evalDiagFormulaCosted W T tables env body).cost + 1 ≤ _
    unfold diagnosticGenericVisitBound
    dsimp only
    dsimp only [R, H, M, E, W, T, s, q] at checked ⊢
    omega
  · let failed := (minimizeFailureCosted W T tables env body).value
    let failedEnv := MinimizedFailure.env failed
    let failedFormula := MinimizedFailure.formula failed
    let context := MinimizedFailure.context failed
    have nodeLimit : DiagFormula.nodeCount failedFormula ≤ s :=
      minimizeFailureCosted_formula_nodeCount_le W T tables env body
    have depthLimit : diagnosticQuantifierDepth failedFormula ≤ q :=
      diagnosticFailureMinimize_depth_le W T tables env body
    have sizes := diagnosticFailureMinimize_storage_le_size W T tables env body
    have envLimit : failedEnv.size ≤ M := sizes.1.trans (Nat.mul_le_mul_left s within)
    have contextLimit : context.size ≤ s * s := sizes.2
    have failedWithin : failedEnv.size + diagnosticQuantifierDepth failedFormula ≤ H := by
      dsimp only [H, E] at *
      omega
    have minimized : (minimizeFailureCosted W T tables env body).cost ≤ s * L :=
      (minimizeFailureCosted_cost_le W T tables env body).trans
        (diagnosticFailureMinimize_le_size W T tables H s q body env.size
          (by omega) (Nat.le_refl _) (Nat.le_refl _))
    have failedEval : DiagFormula.evalCostBound W T (diagAtomCostBound W T tables)
        failedEnv.size failedFormula ≤ R :=
      diagnosticEval_le_reportBound W T tables H s q failedFormula failedEnv.size
        failedWithin nodeLimit depthLimit
    have discovery : DiagFormula.failingAtomsCostBound W T (diagAtomCostBound W T tables)
        failedEnv.size failedFormula ≤ (3 * s + 3) * R :=
      diagnosticFailingAtoms_recurrence_le_limits W T tables H s q failedFormula failedEnv.size
        failedWithin nodeLimit depthLimit
    have atomCount : (failingAtomsCosted W T tables failedEnv failedFormula).value.size ≤
        s * (W + T + 1) ^ q :=
      (diagnosticFailingAtoms_size_le W T tables failedEnv failedFormula).trans
        (Nat.mul_le_mul nodeLimit (Nat.pow_le_pow_right (by omega) depthLimit))
    have discovered := (diagnosticEnvVarsCosted_cost_le vars failedFormula failedEnv).trans
      (diagnosticEnvVarsCostBound_mono nodeLimit hVars envLimit)
    have varLimit := (diagnosticEnvVarsCosted_size_le vars failedFormula failedEnv).trans envLimit
    have summary := (envSummaryCosted_cost_le worldNames thingNames
      (diagnosticEnvVarsCosted vars failedFormula failedEnv).value failedEnv).trans
      (envSummaryCostBound_mono varLimit envLimit)
    have condition := (renderDiagnosticConditionLineCosted_cost_le worldNames thingNames
      failedEnv failedFormula).trans (renderDiagnosticConditionLineCostBound_mono nodeLimit envLimit)
    have suggestion := suggestionForFailureCosted_cost_le worldNames thingNames W T tables
      (diagAtomCostBound W T tables) (evalDiagAtomCosted_cost_le W T tables) failedEnv failedFormula
    simp only [DiagFormula.suggestionCostBound] at suggestion
    have nodeScaled := Nat.mul_le_mul_left 8 nodeLimit
    have envScaled := Nat.mul_le_mul_left 20 envLimit
    have suggestionBound : (suggestionForFailureCosted worldNames thingNames W T tables
        failedEnv failedFormula).cost ≤ (3 * s + 3) * R + R + 8 * s + 20 * M + 51 := by omega
    have atomsCost : (failingAtomsCosted W T tables failedEnv failedFormula).cost ≤
        (3 * s + 3) * R + 1 :=
      (failingAtomsCosted_cost_le W T tables (diagAtomCostBound W T tables)
        (evalDiagAtomCosted_cost_le W T tables) failedEnv failedFormula).trans
        (Nat.add_le_add_right discovery 1)
    have atomEvidence (out : Array String) :=
      (appendFailingAtomEvidenceCosted_cost_le budget worldNames thingNames namedFacts
        failedEnv out (failingAtomsCosted W T tables failedEnv failedFormula).value).trans
        (appendFailingAtomEvidenceCostBound_mono atomCount envLimit (Nat.le_refl namedFacts.size))
    have traces : ∀ trace ∈ context,
        DiagFormula.nodeCount (DiagTrace.formula trace) ≤ s ∧ (DiagTrace.env trace).size ≤ H := by
      intro trace member
      have bounds := minimizeFailureCosted_trace_bounds W T tables env body trace member
      refine ⟨bounds.1, bounds.2.trans ?_⟩
      change env.size + s ≤ H
      dsimp only [H, E]
      omega
    have contextEvidence (out : Array String) :=
      (appendContextEvidenceCosted_cost_le budget worldNames thingNames namedFacts tables
        out context s H traces).trans (Nat.mul_le_mul_right _ contextLimit)
    change _ ≤ diagnosticGenericVisitBound W T tables namedFacts.size V s q
    unfold diagnosticGenericVisitBound
    change _ ≤ R + s * L + (2 * s + 1 + M * (4 * M + 8 * (V + s) + 5)) +
      M * (4 * M + 13) + s * (20 * M + 56) + 27 +
      s * s * (s * (diagAtomCostBound W T tables H + 60 * H + 115 + 275 * namedFacts.size) + 21) +
      (s * (W + T + 1) ^ q) * (40 * M + 76 + 275 * namedFacts.size) +
      2 * (R + (3 * s + 3) * R) + 8 * s + 20 * M + 53
    simp only [diagnosticEnvVarsCostBound] at discovered
    grind [appendDiagnosticPreambleCosted_cost_le, Costed.appendString_cost, Costed.pure_cost]

/-- All independent size parameters are monotone; table contents are irrelevant
except for the number of stored derived propositions. -/
theorem diagnosticGenericVisitBound_mono {W W' T T' F F' V V' s s' q q' : Nat}
    {tables tables' : FactTables}
    (hW : W ≤ W') (hT : T ≤ T') (hF : F ≤ F') (hV : V ≤ V')
    (hs : s ≤ s') (hq : q ≤ q')
    (hDerived : tables.derivedProps.size ≤ tables'.derivedProps.size) :
    diagnosticGenericVisitBound W T tables F V s q ≤
      diagnosticGenericVisitBound W' T' tables' F' V' s' q' := by
  have hPower : (W + T + 1) ^ q ≤ (W' + T' + 1) ^ q' :=
    (Nat.pow_le_pow_left (by omega : W + T + 1 ≤ W' + T' + 1) q).trans
      (Nat.pow_le_pow_right (by omega) hq)
  unfold diagnosticGenericVisitBound diagnosticReportEvalBound diagAtomCostBound derivedLookupCostBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

-- One more variable adds domain iterations. Eleven extra operations per
-- expanded node cover the six fixed operations and five per-iteration operations.
private theorem assignment_quantifier_step (c P n B D : Nat)
    (hc : c ≤ (P + 11 * (n + 1)) * B^n) (hD : D ≤ B) (hB : 1 ≤ B) :
    6 + D * (c + 5) ≤ (P + 11 * (n + 1 + 1)) * B^(n + 1) := by
  have multiplied := Nat.mul_le_mul hD (Nat.add_le_add_right hc 5)
  have reserve : B ≤ B^n * B := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right B (Nat.one_le_pow n B hB)
  have scaled := Nat.mul_le_mul_left 11 reserve
  simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at multiplied scaled ⊢
  omega

-- Bound the existing assignment-loop recurrence. The visitor premise is
-- needed only at reachable environment lengths, including the initial length.
private theorem diagnosticAssignments_recurrence_le_size (W T V P : Nat)
    (visitBound : Nat → Nat) (hVisit : ∀ e, e ≤ V → visitBound e ≤ P)
    (vars : List DiagVar) (e : Nat) (hEnv : e + vars.length ≤ V) :
    diagEnvDependentFoldCostBound W T visitBound e vars ≤
      (P + 11 * (vars.length + 1)) * (W + T + 1) ^ vars.length := by
  induction vars generalizing e with
  | nil =>
    have hv := hVisit e (by simpa using hEnv)
    simp only [diagEnvDependentFoldCostBound, List.length_nil, Nat.pow_zero, Nat.mul_one]
    omega
  | cons var rest ih =>
    have child := ih (e + 1) (by simp only [List.length_cons] at hEnv; omega)
    have hd : DiagVar.domainSize W T var ≤ W + T + 1 := by
      unfold DiagVar.domainSize
      split <;> omega
    exact assignment_quantifier_step _ P rest.length (W + T + 1) _ child hd (by omega)

/-- Bound the executed assignment search, including its two initial arrays.
The visitor bound uses twice the declared variable count to cover both the
fixed variable array and every environment length passed to the loop theorem. -/
theorem diagnosticGenericWitnesses_cost_le_size (budget : Nat)
    (worldNames thingNames : Array Lean.Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    let V := vars.size
    let P := diagnosticGenericVisitBound worldNames.size thingNames.size tables
      namedFacts.size (2 * V) (DiagFormula.nodeCount body) (diagnosticQuantifierDepth body)
    (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).cost ≤
      (P + 11 * (V + 1)) * (worldNames.size + thingNames.size + 1)^V + 2 := by
  let visitBound (e : Nat) := diagnosticGenericVisitBound worldNames.size thingNames.size tables
    namedFacts.size (vars.size + e) (DiagFormula.nodeCount body) (diagnosticQuantifierDepth body)
  have folded := foldDiagEnvsUntilCosted_dependent_cost_le worldNames.size thingNames.size
    vars 0 #[] (#[] : Array String) (fun out => budget ≤ out.size)
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body)
    visitBound (by
      intro out env
      exact diagnosticGenericVisit_cost_le_size budget worldNames thingNames namedFacts tables
        vars body out env (vars.size + env.size) (by omega) (by omega))
  have sized := diagnosticAssignments_recurrence_le_size worldNames.size thingNames.size vars.size
    (diagnosticGenericVisitBound worldNames.size thingNames.size tables namedFacts.size (2 * vars.size)
      (DiagFormula.nodeCount body) (diagnosticQuantifierDepth body)) visitBound
    (by
      intro e he
      exact diagnosticGenericVisitBound_mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    vars.toList 0 (by simp)
  simp only [Array.size_empty, List.drop_zero] at folded
  have composed := folded.trans sized
  simpa only [genericDiagnosticWitnessesCosted, Costed.charge_cost,
    Array.length_toList, Nat.add_comm] using Nat.add_le_add_left composed 2

/-- Public generic-report bound with independent formula and input sizes.
`registry` counts registry entries and `emitted` counts retained output rows.
The final 28 operations cover traversal setup, dispatch, fallback, and copying. -/
def diagnosticGenericReportBound (W T : Nat) (tables : FactTables)
    (facts V s q registry emitted : Nat) : Nat :=
  (diagnosticGenericVisitBound W T tables facts (2 * V) s q + 11 * (V + 1)) *
    (W + T + 1) ^ V + 3 * V + 8 * registry + 4 * emitted + 28

/-- Public production-cost bound for the generic dispatcher branch. The formula
must be the registry's actual selection. Specialized analyzers keep their own
bounds. The output term counts retained rows after the public prefix copy. -/
theorem diagnosticGenericReport_cost_le_size (budget : Nat)
    (worldNames thingNames : Array Lean.Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) (formula : DiagFormula)
    (hGeneric : field ∉ ["ax68", "ax71", "ax73", "ax78", "ax79", "ax99"])
    (hFormula : diagnosticFormula? field = some formula) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).cost ≤
      diagnosticGenericReportBound worldNames.size thingNames.size tables namedFacts.size
        (DiagFormula.forallVars formula).size (DiagFormula.nodeCount (DiagFormula.stripForalls formula))
        (diagnosticQuantifierDepth (DiagFormula.stripForalls formula)) diagnosticFormulaRegistry.size
        (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size := by
  have hLookup := diagnosticFormulaCosted_cost_le field
  have hReport := diagnosticGenericWitnesses_cost_le_size budget worldNames thingNames namedFacts
    tables (DiagFormula.forallVars formula) (DiagFormula.stripForalls formula)
  have hInner : (diagnosticWitnessesInnerCosted budget worldNames thingNames namedFacts tables field).cost ≤
      (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables
        (DiagFormula.forallVars formula) (DiagFormula.stripForalls formula)).cost +
      3 * (DiagFormula.forallVars formula).size + 8 * diagnosticFormulaRegistry.size + 22 := by
    simp only [List.mem_cons, not_or] at hGeneric
    simp only [diagnosticWitnessesInnerCosted, beq_iff_eq, hGeneric.1, hGeneric.2.1,
      hGeneric.2.2.1, hGeneric.2.2.2.1, hGeneric.2.2.2.2.1, hGeneric.2.2.2.2.2,
      ↓reduceIte, Costed.charge_cost, Bind.bind, Costed.bind_cost,
      diagnosticFormulaCosted_value, hFormula, DiagFormula.peelForallsCosted_value,
      DiagFormula.peelForallsCosted_cost]
    split
    · simp only [Costed.bind_cost, Costed.tick_cost]
      omega
    · simp only [Costed.pure_cost]
      omega
  rw [diagnosticWitnessesBudgetedCosted_cost_eq_inner_add_emitted]
  unfold diagnosticGenericReportBound
  dsimp only at hReport
  omega

/-- Monotonicity of the whole report bound, including registry size and output. -/
theorem diagnosticGenericReportBound_mono {W W' T T' F F' V V' s s' q q' r r' e e' : Nat}
    {tables tables' : FactTables}
    (hW : W ≤ W') (hT : T ≤ T') (hF : F ≤ F') (hV : V ≤ V')
    (hs : s ≤ s') (hq : q ≤ q') (hr : r ≤ r') (he : e ≤ e')
    (hDerived : tables.derivedProps.size ≤ tables'.derivedProps.size) :
    diagnosticGenericReportBound W T tables F V s q r e ≤
      diagnosticGenericReportBound W' T' tables' F' V' s' q' r' e' := by
  have hVisit := diagnosticGenericVisitBound_mono hW hT hF (Nat.mul_le_mul_left 2 hV) hs hq hDerived
  have hPower : (W + T + 1) ^ V ≤ (W' + T' + 1) ^ V' :=
    (Nat.pow_le_pow_left (by omega : W + T + 1 ≤ W' + T' + 1) V).trans
      (Nat.pow_le_pow_right (by omega) hV)
  unfold diagnosticGenericReportBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

end Complexity
end LeanUfo.UFO.DSL
