import LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis
import Batteries.Tactic.OpenPrivate

/-!
# Formula-size bounds for diagnostic evaluation and failure selection

Evaluation costs at most `s * (A + 8E + 4) * (W + T + 1)^q`, where `s` is
the number of formula nodes, `q` is the maximum number of nested quantifiers,
and `W` and `T` are the world and thing counts. `E` bounds the environment
length throughout evaluation. `A` bounds an atomic query in any such environment.
Modal operators also quantify over worlds, so they contribute to `q`.

The proof bounds the existing executable evaluator through its proved structural
recurrence. A connective adds its child costs. A quantifier multiplies its body
bound by its domain size. Early exits can reduce the actual count.

This is the data/combined-complexity distinction discussed by Vardi (see
`docs/dsl/complexity.md`): a fixed formula fixes the exponent, but an input
formula can increase it. No uniform polynomial in unrestricted formula and
model input follows. Failure minimization also has explicit bounds for repeated
evaluation, successful context, witness scans, and merged arrays. If `R` bounds
one full evaluation or witness scan, the minimizer costs at most
`s * (3R + 2s(2R + 5) + 6s² + 3sE + 10)`. Its returned environment has at most
`sE` entries and its context at most `s²` traces. A trace stores a successful
subformula with the variable assignment that made it true.

`Complexity/Diagnostics/Reports.lean` composes these bounds with evidence
rendering and outer assignment enumeration. The formula language remains private.
-/

namespace LeanUfo.UFO.DSL

open private DiagFormula DiagFormula.nodeCount DiagFormula.evalCostBound
  DiagFormula.atom DiagFormula.eqThing DiagFormula.eqWorld DiagFormula.not
  DiagFormula.and DiagFormula.or DiagFormula.imp DiagFormula.iff
  DiagFormula.forallThing DiagFormula.existsThing DiagFormula.forallWorld
  DiagFormula.existsWorld DiagFormula.box DiagFormula.dia
  evalDiagFormulaCosted evalDiagFormulaCosted_cost_le
  diagAtomCostBound evalDiagAtomCosted_cost_le
  DiagFormula.successTraceCostBound DiagFormula.failureEnvSizeBound
  DiagFormula.failureContextSizeBound DiagFormula.failureMinimizeCostBound
  firstMatchCostBound derivedLookupCostBound DiagVarKind DiagVarKind.domainSize
  DiagVarKind.thing DiagVarKind.world successTracesCosted successTracesCosted_cost_le
  minimizeFailureCosted minimizeFailureCosted_cost_le minimizeFailureCosted_env_size_le
  minimizeFailureCosted_context_size_le MinimizedFailure.env MinimizedFailure.context
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

namespace Complexity

/-- Maximum number of domain loops along one root-to-leaf formula path.
Negation and binary connectives add no variable bindings. -/
def diagnosticQuantifierDepth : DiagFormula → Nat
  | DiagFormula.atom _ | DiagFormula.eqThing _ _ | DiagFormula.eqWorld _ _ => 0
  | DiagFormula.not p => diagnosticQuantifierDepth p
  | DiagFormula.and p q | DiagFormula.or p q | DiagFormula.imp p q | DiagFormula.iff p q =>
      max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth q)
  | DiagFormula.forallThing _ p | DiagFormula.existsThing _ p | DiagFormula.forallWorld _ p
  | DiagFormula.existsWorld _ p | DiagFormula.box _ _ p | DiagFormula.dia _ _ p =>
      diagnosticQuantifierDepth p + 1

private theorem formula_quantifier_bound (cost nodes factor domain base : Nat)
    (hcost : cost ≤ nodes * factor) (hfactor : 4 ≤ factor)
    (hdomain : domain ≤ base) (hbase : 1 ≤ base) :
    domain * (cost + 3) + 1 ≤ (nodes + 1) * (factor * base) := by
  have h := Nat.mul_le_mul hdomain (Nat.add_le_add_right hcost 3)
  have hf := Nat.mul_le_mul_left base hfactor
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm] at h hf ⊢
  omega

/-- The environment premise includes every binding that nested quantifiers
can append. The atomic bound is required only up to that environment limit. -/
theorem diagnosticFormula_recurrence_le_size (W T E A : Nat)
    (atomBound : Nat → Nat) (hAtom : ∀ e, e ≤ E → atomBound e ≤ A)
    (formula : DiagFormula) (e : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E) :
    DiagFormula.evalCostBound W T atomBound e formula ≤
      (DiagFormula.nodeCount formula) * ((A + 8 * E + 4) * (W + T + 1) ^ diagnosticQuantifierDepth formula) := by
  have hbase : 0 < W + T + 1 := by omega
  have factor_ge (q : Nat) : 4 ≤ (A + 8 * E + 4) * (W + T + 1) ^ q := by
    have hp : 1 ≤ (W + T + 1) ^ q := Nat.one_le_pow q _ hbase
    exact (show 4 ≤ A + 8 * E + 4 by omega).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A + 8 * E + 4) hp)
  induction formula generalizing e with
  | atom atom =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have ha := hAtom e (by omega)
      simp only [DiagFormula.evalCostBound, DiagFormula.nodeCount,
        diagnosticQuantifierDepth, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
      omega
  | eqThing left right | eqWorld left right =>
      simp only [diagnosticQuantifierDepth] at hEnv
      simp only [DiagFormula.evalCostBound, DiagFormula.nodeCount,
        diagnosticQuantifierDepth, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
      omega
  | not p ih =>
      have hp := ih e hEnv
      have hf := factor_ge (diagnosticQuantifierDepth p)
      simp only [DiagFormula.evalCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth]
      rw [Nat.add_mul, Nat.one_mul]
      omega
  | and p q ihp ihq | or p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have hp := ihp e (by omega)
      have hq := ihq e (by omega)
      have hpowp := Nat.pow_le_pow_right hbase (Nat.le_max_left
        (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth q))
      have hpowq := Nat.pow_le_pow_right hbase (Nat.le_max_right
        (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth q))
      have hp' := hp.trans (Nat.mul_le_mul_left (DiagFormula.nodeCount p)
        (Nat.mul_le_mul_left (A + 8 * E + 4) hpowp))
      have hq' := hq.trans (Nat.mul_le_mul_left (DiagFormula.nodeCount q)
        (Nat.mul_le_mul_left (A + 8 * E + 4) hpowq))
      have hf := factor_ge (max (diagnosticQuantifierDepth p) (diagnosticQuantifierDepth q))
      simp only [DiagFormula.evalCostBound, DiagFormula.nodeCount, diagnosticQuantifierDepth]
      rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
      omega
  | forallThing name p ih | existsThing name p ih =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have hp := ih (e + 1) (by omega)
      have hf := factor_ge (diagnosticQuantifierDepth p)
      simpa only [DiagFormula.evalCostBound, DiagFormula.nodeCount,
        diagnosticQuantifierDepth, Nat.pow_succ, Nat.mul_assoc] using
        formula_quantifier_bound _ _ _ T (W + T + 1) hp hf (by omega) (by omega)
  | forallWorld name p ih | existsWorld name p ih
  | box current name p ih | dia current name p ih =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have hp := ih (e + 1) (by omega)
      have hf := factor_ge (diagnosticQuantifierDepth p)
      simpa only [DiagFormula.evalCostBound, DiagFormula.nodeCount,
        diagnosticQuantifierDepth, Nat.pow_succ, Nat.mul_assoc] using
        formula_quantifier_bound _ _ _ W (W + T + 1) hp hf (by omega) (by omega)

/-- Increasing any size parameter or the atomic-cost bound cannot decrease
this upper bound. Exact execution counts can still fall after an early exit. -/
theorem diagnosticFormula_sizeBound_mono
    {s s' A A' E E' W W' T T' q q' : Nat}
    (hs : s ≤ s') (hA : A ≤ A') (hE : E ≤ E')
    (hW : W ≤ W') (hT : T ≤ T') (hq : q ≤ q') :
    s * ((A + 8 * E + 4) * (W + T + 1) ^ q) ≤
      s' * ((A' + 8 * E' + 4) * (W' + T' + 1) ^ q') := by
  apply Nat.mul_le_mul hs
  apply Nat.mul_le_mul (by omega)
  exact (Nat.pow_le_pow_left (by omega : W + T + 1 ≤ W' + T' + 1) q).trans
    (Nat.pow_le_pow_right (by omega) hq)

/-- Bound on the actual interpreter, with explicit formula and environment
sizes. The existing atom theorem supplies the cost of dense queries, derived
predicate searches, and environment lookup. String characters remain excluded. -/
theorem diagnosticFormula_cost_le_size (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    let E := env.size + diagnosticQuantifierDepth formula
    (evalDiagFormulaCosted W T tables env formula).cost ≤
      (DiagFormula.nodeCount formula) * ((diagAtomCostBound W T tables E + 8 * E + 4) *
        (W + T + 1) ^ diagnosticQuantifierDepth formula) := by
  apply (evalDiagFormulaCosted_cost_le W T tables (diagAtomCostBound W T tables)
    (evalDiagAtomCosted_cost_le W T tables) env formula).trans
  apply diagnosticFormula_recurrence_le_size
  · intro e he
    simp only [diagAtomCostBound]
    omega
  · exact Nat.le_refl _

/-!
## Failure selection and successful context

The same evaluation can run more than once while selecting a useful failure.
For example, an existential first establishes success and then searches again
for the assignment stored in its explanatory trace. The bounds below retain
both calls. They follow the cost-aware composition used by Niu et al. (POPL
2022), cited in `Diagnostic/AxiomAnalysis.lean`, without changing those calls.
-/

/-- Common evaluation and witness-search bound for subformulas with at most
`s` nodes and quantifier depth `q`, with environment length bounded by `E`.
The extra constant covers the witness scan's six operations per visited value
and its final test. It enlarges a proved bound, not the executed counter. -/
def diagnosticReportEvalBound (W T : Nat) (tables : FactTables) (E s q : Nat) : Nat :=
  s * ((diagAtomCostBound W T tables E + 8 * E + 10) * (W + T + 1) ^ q)

/-- Lift the evaluator bound to the enclosing formula's size limits. -/
private theorem diagnosticEval_le_reportBound (W T : Nat) (tables : FactTables)
    (E s q : Nat) (formula : DiagFormula) (e : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E)
    (hSize : (DiagFormula.nodeCount formula) ≤ s) (hDepth : diagnosticQuantifierDepth formula ≤ q) :
    DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e formula ≤
      diagnosticReportEvalBound W T tables E s q := by
  have result := diagnosticFormula_recurrence_le_size W T E (diagAtomCostBound W T tables E)
    (diagAtomCostBound W T tables) (by intro i hi; simp only [diagAtomCostBound]; omega)
    formula e hEnv
  apply result.trans
  apply Nat.mul_le_mul hSize
  apply Nat.mul_le_mul (by omega)
  exact Nat.pow_le_pow_right (by omega) hDepth

/-- A witness scan adds one domain loop around its body. That loop consumes
one unit of the supplied quantifier-depth limit, including for empty domains. -/
private theorem diagnosticFirstMatch_le_reportBound (W T : Nat) (tables : FactTables)
    (E s q : Nat) (kind : DiagVarKind) (body : DiagFormula) (e : Nat)
    (hEnv : e + 1 + diagnosticQuantifierDepth body ≤ E)
    (hSize : (DiagFormula.nodeCount body) + 1 ≤ s)
    (hDepth : diagnosticQuantifierDepth body + 1 ≤ q) :
    firstMatchCostBound W T tables kind e body ≤ diagnosticReportEvalBound W T tables E s q := by
  let K := (diagAtomCostBound W T tables E + 8 * E + 10) *
    (W + T + 1) ^ diagnosticQuantifierDepth body
  have bodyCost := diagnosticEval_le_reportBound W T tables E (DiagFormula.nodeCount body)
    (diagnosticQuantifierDepth body) body (e + 1) hEnv (Nat.le_refl _) (Nat.le_refl _)
  change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) (e + 1) body ≤ (DiagFormula.nodeCount body) * K at bodyCost
  have lower : 7 ≤ K := by
    have hp := Nat.one_le_pow (diagnosticQuantifierDepth body) (W + T + 1) (by omega)
    have hm := Nat.mul_le_mul_left (diagAtomCostBound W T tables E + 8 * E + 10) hp
    dsimp [K]
    simp only [Nat.mul_one] at hm
    omega
  have domain : DiagVarKind.domainSize W T kind ≤ W + T + 1 := by cases kind <;> simp [DiagVarKind.domainSize] <;> omega
  have result : firstMatchCostBound W T tables kind e body ≤
      ((DiagFormula.nodeCount body) + 1) * (K * (W + T + 1)) := by
    have h := Nat.mul_le_mul domain (Nat.add_le_add_right bodyCost 6)
    have hk := Nat.mul_le_mul_left (W + T + 1) lower
    simp only [firstMatchCostBound, Nat.mul_add, Nat.add_mul, Nat.one_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at h hk ⊢
    omega
  apply result.trans
  apply Nat.mul_le_mul hSize
  dsimp only [K]
  rw [Nat.mul_assoc, ← Nat.pow_succ]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hDepth)

/-- Each retained formula node contributes at most `E` environment entries.
This includes the two environments copied when a disjunction fails on both sides. -/
theorem diagnosticFailureEnv_le_size (formula : DiagFormula) (e E : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E) :
    DiagFormula.failureEnvSizeBound e formula ≤ (DiagFormula.nodeCount formula) * E := by
  induction formula generalizing e with
  | atom | eqThing | eqWorld =>
      simp only [DiagFormula.failureEnvSizeBound, DiagFormula.nodeCount, Nat.one_mul]
      simp only [diagnosticQuantifierDepth] at hEnv
      omega
  | not p ih =>
      have hp := ih e hEnv
      simp only [DiagFormula.failureEnvSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | and p q ihp ihq | or p q ihp ihq | iff p q ihp ihq =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have hp := ihp e (by omega)
      have hq := ihq e (by omega)
      simp only [DiagFormula.failureEnvSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | imp p q ihp ihq =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have hq := ihq e (by omega)
      simp only [DiagFormula.failureEnvSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | forallThing name p ih | existsThing name p ih | forallWorld name p ih
  | existsWorld name p ih | box current name p ih | dia current name p ih =>
      simp only [diagnosticQuantifierDepth] at hEnv
      have hp := ih (e + 1) (by omega)
      simp only [DiagFormula.failureEnvSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega

/-- A context array stores successful subformulas. At most `s` traces are
charged to each input node, giving a quadratic bound when `s` is the full size. -/
theorem diagnosticFailureContext_le_size (s : Nat) (formula : DiagFormula)
    (hSize : (DiagFormula.nodeCount formula) ≤ s) :
    DiagFormula.failureContextSizeBound formula ≤ (DiagFormula.nodeCount formula) * s := by
  induction formula with
  | atom | eqThing | eqWorld => simp [DiagFormula.failureContextSizeBound]
  | not p ih =>
      simp only [DiagFormula.nodeCount] at hSize
      have hp := ih (by omega)
      simp only [DiagFormula.failureContextSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | and p q ihp ihq | or p q ihp ihq | iff p q ihp ihq =>
      simp only [DiagFormula.nodeCount] at hSize
      have hp := ihp (by omega)
      have hq := ihq (by omega)
      simp only [DiagFormula.failureContextSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | imp p q ihp ihq =>
      simp only [DiagFormula.nodeCount] at hSize
      have hq := ihq (by omega)
      simp only [DiagFormula.failureContextSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | forallThing name p ih | existsThing name p ih | forallWorld name p ih
  | existsWorld name p ih | box current name p ih | dia current name p ih =>
      simp only [DiagFormula.nodeCount] at hSize
      have hp := ih (by omega)
      simp only [DiagFormula.failureContextSizeBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega

/-- Per formula node, context collection performs at most two computations
bounded by `R` and five control/output operations. Recursive branches retain
their own node budget, including the repeated witness scan for an existential. -/
theorem diagnosticSuccessTrace_le_size (W T : Nat) (tables : FactTables)
    (E s q : Nat) (formula : DiagFormula) (e : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E)
    (hSize : DiagFormula.nodeCount formula ≤ s)
    (hDepth : diagnosticQuantifierDepth formula ≤ q) :
    DiagFormula.successTraceCostBound W T tables e formula ≤
      DiagFormula.nodeCount formula * (2 * diagnosticReportEvalBound W T tables E s q + 5) := by
  let R := diagnosticReportEvalBound W T tables E s q
  have checked := diagnosticEval_le_reportBound W T tables E s q
  have simple (f : DiagFormula) (e : Nat)
      (he : e + diagnosticQuantifierDepth f ≤ E) (hs : DiagFormula.nodeCount f ≤ s)
      (hd : diagnosticQuantifierDepth f ≤ q) :
      DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e f + 4 ≤
        DiagFormula.nodeCount f * (2 * R + 5) := by
    have hc := checked f e he hs hd
    have hn : 1 ≤ DiagFormula.nodeCount f := by cases f <;> simp [DiagFormula.nodeCount]
    have hm := Nat.mul_le_mul_right (2 * R + 5) hn
    simp only [Nat.one_mul] at hm
    change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e f ≤ R at hc
    omega
  change _ ≤ DiagFormula.nodeCount formula * (2 * R + 5)
  induction formula generalizing e with
  | atom a => exact simple (DiagFormula.atom a) e hEnv hSize hDepth
  | eqThing a b => exact simple (DiagFormula.eqThing a b) e hEnv hSize hDepth
  | eqWorld a b => exact simple (DiagFormula.eqWorld a b) e hEnv hSize hDepth
  | not p ih => exact simple (DiagFormula.not p) e hEnv hSize hDepth
  | iff p r ihp ihr => exact simple (DiagFormula.iff p r) e hEnv hSize hDepth
  | forallThing name p ih => exact simple (DiagFormula.forallThing name p) e hEnv hSize hDepth
  | forallWorld name p ih => exact simple (DiagFormula.forallWorld name p) e hEnv hSize hDepth
  | box current name p ih => exact simple (DiagFormula.box current name p) e hEnv hSize hDepth
  | and p r ihp ihr =>
      have hc := checked (DiagFormula.and p r) e hEnv hSize hDepth
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e (DiagFormula.and p r) ≤ R at hc
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ihp e (by omega) (by omega) (by omega)
      have hr := ihr e (by omega) (by omega) (by omega)
      simp only [DiagFormula.successTraceCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | or p r ihp ihr =>
      have hc := checked (DiagFormula.or p r) e hEnv hSize hDepth
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e (DiagFormula.or p r) ≤ R at hc
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ihp e (by omega) (by omega) (by omega)
      have hleft := checked p e (by omega) (by omega) (by omega)
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e p ≤ R at hleft
      have hr := ihr e (by omega) (by omega) (by omega)
      simp only [DiagFormula.successTraceCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | imp p r ihp ihr =>
      have hc := checked (DiagFormula.imp p r) e hEnv hSize hDepth
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e (DiagFormula.imp p r) ≤ R at hc
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hleft := checked p e (by omega) (by omega) (by omega)
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e p ≤ R at hleft
      have hr := ihr e (by omega) (by omega) (by omega)
      simp only [DiagFormula.successTraceCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | existsThing name p ih =>
      have hc := checked (DiagFormula.existsThing name p) e hEnv hSize hDepth
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e (DiagFormula.existsThing name p) ≤ R at hc
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.thing p e
        (by omega) hSize hDepth
      change firstMatchCostBound W T tables DiagVarKind.thing e p ≤ R at hm
      have hp := ih (e + 1) (by omega) (by omega) (by omega)
      simp only [DiagFormula.successTraceCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | existsWorld name p ih =>
      have hc := checked (DiagFormula.existsWorld name p) e hEnv hSize hDepth
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e (DiagFormula.existsWorld name p) ≤ R at hc
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.world p e
        (by omega) hSize hDepth
      change firstMatchCostBound W T tables DiagVarKind.world e p ≤ R at hm
      have hp := ih (e + 1) (by omega) (by omega) (by omega)
      simp only [DiagFormula.successTraceCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
  | dia current name p ih =>
      have hc := checked (DiagFormula.dia current name p) e hEnv hSize hDepth
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e (DiagFormula.dia current name p) ≤ R at hc
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.world p e
        (by omega) hSize hDepth
      change firstMatchCostBound W T tables DiagVarKind.world e p ≤ R at hm
      have hp := ih (e + 1) (by omega) (by omega) (by omega)
      simp only [DiagFormula.successTraceCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega

/-- Bound the minimizer's structural recurrence by a budget per formula node.
The local budget covers three evaluations, two context collections, context
copies, environment copies, and fixed control operations. Strong induction on
node count also covers negations that recurse into a quantifier's body. -/
theorem diagnosticFailureMinimize_le_size (W T : Nat) (tables : FactTables)
    (E s q : Nat) (formula : DiagFormula) (e : Nat)
    (hEnv : e + diagnosticQuantifierDepth formula ≤ E)
    (hSize : DiagFormula.nodeCount formula ≤ s)
    (hDepth : diagnosticQuantifierDepth formula ≤ q) :
    let R := diagnosticReportEvalBound W T tables E s q
    DiagFormula.failureMinimizeCostBound W T tables e formula ≤
      DiagFormula.nodeCount formula *
        (3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10) := by
  let R := diagnosticReportEvalBound W T tables E s q
  let L := 3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10
  have budget : 3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10 = L := rfl
  have checked := diagnosticEval_le_reportBound W T tables E s q
  have traced (f : DiagFormula) (e : Nat)
      (he : e + diagnosticQuantifierDepth f ≤ E) (hs : DiagFormula.nodeCount f ≤ s)
      (hd : diagnosticQuantifierDepth f ≤ q) :
      DiagFormula.successTraceCostBound W T tables e f ≤ s * (2 * R + 5) :=
    (diagnosticSuccessTrace_le_size W T tables E s q f e he hs hd).trans
      (Nat.mul_le_mul_right _ hs)
  have context (f : DiagFormula) (hs : DiagFormula.nodeCount f ≤ s) :
      DiagFormula.failureContextSizeBound f ≤ s * s :=
    (diagnosticFailureContext_le_size s f hs).trans (Nat.mul_le_mul_right s hs)
  have environment (f : DiagFormula) (e : Nat)
      (he : e + diagnosticQuantifierDepth f ≤ E) (hs : DiagFormula.nodeCount f ≤ s) :
      DiagFormula.failureEnvSizeBound e f ≤ s * E :=
    (diagnosticFailureEnv_le_size f e E he).trans (Nat.mul_le_mul_right E hs)
  change _ ≤ DiagFormula.nodeCount formula * L
  induction formula using (measure DiagFormula.nodeCount).wf.induction generalizing e with
  | h formula ih =>
    have hc := checked formula e hEnv hSize hDepth
    change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e formula ≤ R at hc
    cases formula with
    | atom a | eqThing a b | eqWorld a b =>
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.one_mul]
      omega
    | and p r =>
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have hr := ih r (by change DiagFormula.nodeCount r < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have ep := checked p e (by omega) (by omega) (by omega)
      have er := checked r e (by omega) (by omega) (by omega)
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e p ≤ R at ep
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e r ≤ R at er
      have tp := traced p e (by omega) (by omega) (by omega)
      have cr := context r (by omega)
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
    | or p r =>
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have hr := ih r (by change DiagFormula.nodeCount r < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have er := environment r e (by omega) (by omega)
      have cr := context r (by omega)
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
    | imp p r =>
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hr := ih r (by change DiagFormula.nodeCount r < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have tp := traced p e (by omega) (by omega) (by omega)
      have cr := context r (by omega)
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
    | iff p r =>
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have hr := ih r (by change DiagFormula.nodeCount r < DiagFormula.nodeCount p + DiagFormula.nodeCount r + 1; omega)
        e (by omega) (by omega) (by omega)
      have ep := checked p e (by omega) (by omega) (by omega)
      have er := checked r e (by omega) (by omega) (by omega)
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e p ≤ R at ep
      change DiagFormula.evalCostBound W T (diagAtomCostBound W T tables) e r ≤ R at er
      have tp := traced p e (by omega) (by omega) (by omega)
      have tr := traced r e (by omega) (by omega) (by omega)
      have cp := context p (by omega)
      have cr := context r (by omega)
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
    | forallThing name p | existsThing name p =>
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + 1; omega)
        (e + 1) (by omega) (by omega) (by omega)
      have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.thing p e
        (by omega) hSize hDepth
      change firstMatchCostBound W T tables DiagVarKind.thing e p ≤ R at hm
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
    | forallWorld name p | existsWorld name p
    | box current name p | dia current name p =>
      simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
      have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + 1; omega)
        (e + 1) (by omega) (by omega) (by omega)
      have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.world p e
        (by omega) hSize hDepth
      change firstMatchCostBound W T tables DiagVarKind.world e p ≤ R at hm
      simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega
    | not p =>
      cases p with
      | not p =>
        simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
        have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + 1 + 1; omega)
          e hEnv (by omega) hDepth
        simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
        omega
      | forallThing name p | existsThing name p =>
        simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
        have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + 1 + 1; omega)
          (e + 1) (by omega) (by omega) (by omega)
        have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.thing p e
          (by omega) (by omega) hDepth
        change firstMatchCostBound W T tables DiagVarKind.thing e p ≤ R at hm
        simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
        omega
      | forallWorld name p | existsWorld name p
      | box current name p | dia current name p =>
        simp only [DiagFormula.nodeCount, diagnosticQuantifierDepth] at hEnv hSize hDepth
        have hp := ih p (by change DiagFormula.nodeCount p < DiagFormula.nodeCount p + 1 + 1; omega)
          (e + 1) (by omega) (by omega) (by omega)
        have hm := diagnosticFirstMatch_le_reportBound W T tables E s q DiagVarKind.world p e
          (by omega) (by omega) hDepth
        change firstMatchCostBound W T tables DiagVarKind.world e p ≤ R at hm
        simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
        omega
      | atom a | eqThing a b | eqWorld a b | and p r | or p r | imp p r | iff p r =>
        simp only [DiagFormula.failureMinimizeCostBound, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
        omega

/-- Cost of the executed successful-context collector. The final unit charges
initialization of its output array, even when it returns no traces. -/
theorem diagnosticSuccessTraces_cost_le_size (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let q := diagnosticQuantifierDepth formula
    let R := diagnosticReportEvalBound W T tables (env.size + q) s q
    (successTracesCosted W T tables env formula).cost ≤ s * (2 * R + 5) + 1 := by
  apply (successTracesCosted_cost_le W T tables env formula).trans
  apply Nat.add_le_add_right
  exact diagnosticSuccessTrace_le_size W T tables _ _ _ formula env.size
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Cost of the executed failure minimizer, including repeated evaluations,
witness searches, successful context, and copied environment/context arrays.
This does not include rendering or source-fact evidence collection. -/
theorem diagnosticFailureMinimize_cost_le_size (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let q := diagnosticQuantifierDepth formula
    let E := env.size + q
    let R := diagnosticReportEvalBound W T tables E s q
    (minimizeFailureCosted W T tables env formula).cost ≤
      s * (3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10) := by
  apply (minimizeFailureCosted_cost_le W T tables env formula).trans
  exact diagnosticFailureMinimize_le_size W T tables _ _ _ formula env.size
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Size bounds for the arrays actually returned by minimization. These count
stored entries, not the character lengths of names or the allocator's bytes. -/
theorem diagnosticFailureMinimize_storage_le_size (W T : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let failed := (minimizeFailureCosted W T tables env formula).value
    (MinimizedFailure.env failed).size ≤ s * (env.size + diagnosticQuantifierDepth formula) ∧
      (MinimizedFailure.context failed).size ≤ s * s := by
  constructor
  · exact (minimizeFailureCosted_env_size_le W T tables env formula).trans
      (diagnosticFailureEnv_le_size formula env.size _ (Nat.le_refl _))
  · exact (minimizeFailureCosted_context_size_le W T tables env formula).trans
      (diagnosticFailureContext_le_size _ formula (Nat.le_refl _))

/-- The common bound is monotone in formula, domain, environment, and stored
derived-proposition counts. Table contents cannot reduce this upper bound. -/
theorem diagnosticReportEvalBound_mono {W W' T T' E E' s s' q q' : Nat}
    {tables tables' : FactTables}
    (hW : W ≤ W') (hT : T ≤ T') (hE : E ≤ E') (hs : s ≤ s') (hq : q ≤ q')
    (hDerived : tables.derivedProps.size ≤ tables'.derivedProps.size) :
    diagnosticReportEvalBound W T tables E s q ≤
      diagnosticReportEvalBound W' T' tables' E' s' q' := by
  unfold diagnosticReportEvalBound
  apply Nat.mul_le_mul hs
  apply Nat.mul_le_mul
  · unfold diagAtomCostBound derivedLookupCostBound
    repeat' first
      | assumption
      | exact Nat.le_refl _
      | apply Nat.add_le_add
      | apply Nat.mul_le_mul
  · exact (Nat.pow_le_pow_left (by omega : W + T + 1 ≤ W' + T' + 1) q).trans
      (Nat.pow_le_pow_right (by omega) hq)

/-- Monotonicity of the full minimization bound. Exact counts can decrease
when a changed model causes an earlier decisive result. -/
theorem diagnosticFailureMinimize_sizeBound_mono {s s' R R' E E' : Nat}
    (hs : s ≤ s') (hR : R ≤ R') (hE : E ≤ E') :
    s * (3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10) ≤
      s' * (3 * R' + 2 * (s' * (2 * R' + 5)) + 6 * (s' * s') + 3 * (s' * E') + 10) := by
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

end Complexity
end LeanUfo.UFO.DSL
