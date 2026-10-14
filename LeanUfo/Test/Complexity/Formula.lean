import LeanUfo.UFO.DSL.Complexity

/-!
# Formula-size cost regressions

These tests connect the general size theorem to the production diagnostic
interpreter. Exact counts cover full nested loops, empty domains, and skipped
subformulas. Quantifier depth counts nesting, not the total number of loops
written in separate branches.
-/

namespace LeanUfo.Test.Complexity.Formula

open LeanUfo.UFO.DSL
open LeanUfo.UFO.DSL.Complexity

open private DiagFormula DiagFormula.nodeCount DiagFormula.evalCostBound
  DiagFormula.eqThing DiagFormula.not DiagFormula.and DiagFormula.or
  DiagFormula.forallThing DiagFormula.existsThing DiagFormula.forallWorld
  DiagFormula.box DiagFormula.dia evalDiagFormulaCosted diagAtomCostBound
  successTracesCosted minimizeFailureCosted MinimizedFailure.env MinimizedFailure.context
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

private def equality : DiagFormula := DiagFormula.eqThing "x" "x"
private def nested : DiagFormula :=
  DiagFormula.forallWorld "w" (DiagFormula.forallThing "x" equality)

example : diagnosticQuantifierDepth equality = 0 := rfl
example : diagnosticQuantifierDepth nested = 2 := rfl
example : DiagFormula.nodeCount nested = 3 := rfl
example : diagnosticQuantifierDepth
    (DiagFormula.and nested (DiagFormula.existsThing "x" equality)) = 2 := rfl
example : diagnosticQuantifierDepth (DiagFormula.box "w" "v"
    (DiagFormula.dia "v" "u" equality)) = 2 := rfl

-- Two environment reads cost 4e+1 each. Equality adds two operations.
-- The inner loop costs 3*(20+3)+1=70. The outer loop costs 2*(70+3)+1=147.
example : evalDiagFormulaCosted 2 3 {} #[] nested = ⟨true, 147⟩ := by native_decide
example : DiagFormula.evalCostBound 2 3 (fun _ => 0) 0 nested = 147 := rfl
example : DiagFormula.evalCostBound 2 3 (fun _ => 0) 0 nested ≤
    3 * ((0 + 8 * 2 + 4) * 6 ^ 2) :=
  diagnosticFormula_recurrence_le_size 2 3 2 0 (fun _ => 0)
    (by intros; exact Nat.le_refl _) nested 0 (by decide)

example : evalDiagFormulaCosted 0 3 {} #[] nested = ⟨true, 1⟩ := by native_decide
example : evalDiagFormulaCosted 2 0 {} #[] nested = ⟨true, 9⟩ := by native_decide
example : evalDiagFormulaCosted 0 0 {} #[]
    (DiagFormula.existsThing "x" equality) = ⟨false, 1⟩ := by native_decide

-- These right operands would scan large domains, but Boolean evaluation
-- already knows the answer from the left operand and never calls them.
example : evalDiagFormulaCosted 1000000 1000000 {} #[]
    (DiagFormula.and (DiagFormula.not equality) nested) = ⟨false, 8⟩ := by native_decide
example : evalDiagFormulaCosted 1000000 1000000 {} #[]
    (DiagFormula.or equality nested) = ⟨true, 6⟩ := by native_decide

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (formula : DiagFormula) :
    let E := env.size + diagnosticQuantifierDepth formula
    (evalDiagFormulaCosted W T tables env formula).cost ≤
      DiagFormula.nodeCount formula * ((diagAtomCostBound W T tables E + 8 * E + 4) *
        (W + T + 1) ^ diagnosticQuantifierDepth formula) :=
  diagnosticFormula_cost_le_size W T tables env formula

example {s s' A A' E E' W W' T T' q q' : Nat}
    (hs : s ≤ s') (hA : A ≤ A') (hE : E ≤ E')
    (hW : W ≤ W') (hT : T ≤ T') (hq : q ≤ q') :
    s * ((A + 8 * E + 4) * (W + T + 1) ^ q) ≤
      s' * ((A' + 8 * E' + 4) * (W' + T' + 1) ^ q') :=
  diagnosticFormula_sizeBound_mono hs hA hE hW hT hq

-- Equality costs four with an empty environment. Context collection adds
-- four operations for the successful trace and one for its output array.
example : (successTracesCosted 1 1 {} #[] equality).cost = 9 := by native_decide

-- The false left conjunct prevents the million-element loops from running.
-- Evaluation costs eight; rejection and array initialization add three.
example : (successTracesCosted 1000000 1000000 {} #[]
    (DiagFormula.and (DiagFormula.not equality) nested)).cost = 11 := by native_decide

private def falseFormula : DiagFormula := DiagFormula.not equality
private def bothFalse : DiagFormula := DiagFormula.or falseFormula falseFormula

-- Each failed negation costs 6+4=10. The disjunction evaluates both (14),
-- minimizes both (20), and assembles the result (2). Both copied arrays are empty.
example : (minimizeFailureCosted 1 1 {} #[] bothFalse).cost = 36 := by native_decide

-- With one binding, evaluation costs 30 and each minimization costs 18.
-- Copying the right environment adds three, so the total is 30+36+3+2=71.
example : (minimizeFailureCosted 1 1 {} #[("x", 0)] bothFalse).cost = 71 := by native_decide
example : MinimizedFailure.env (minimizeFailureCosted 1 1 {} #[("x", 0)] bothFalse).value =
    #[("x", 0), ("x", 0)] := by native_decide

-- The successful left side becomes context: 4+6 for evaluation, 9 for its
-- trace, 10 for the right failure, and 5 control operations. No context is copied.
example : (minimizeFailureCosted 1 1 {} #[]
    (DiagFormula.and equality falseFormula)).cost = 34 := by native_decide
example : (MinimizedFailure.context (minimizeFailureCosted 1 1 {} #[]
    (DiagFormula.and equality falseFormula)).value).size = 1 := by native_decide

-- The outer two negations disappear during minimization. Their full evaluation
-- costs ten, branch selection adds three, and the remaining failure costs ten.
example : (minimizeFailureCosted 1 1 {} #[]
    (DiagFormula.not (DiagFormula.not falseFormula))).cost = 23 := by native_decide

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let q := diagnosticQuantifierDepth formula
    let R := diagnosticReportEvalBound W T tables (env.size + q) s q
    (successTracesCosted W T tables env formula).cost ≤ s * (2 * R + 5) + 1 :=
  diagnosticSuccessTraces_cost_le_size W T tables env formula

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let q := diagnosticQuantifierDepth formula
    let E := env.size + q
    let R := diagnosticReportEvalBound W T tables E s q
    (minimizeFailureCosted W T tables env formula).cost ≤
      s * (3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10) :=
  diagnosticFailureMinimize_cost_le_size W T tables env formula

example (W T : Nat) (tables : FactTables) (env : Array (String × Nat))
    (formula : DiagFormula) :
    let s := DiagFormula.nodeCount formula
    let failed := (minimizeFailureCosted W T tables env formula).value
    (MinimizedFailure.env failed).size ≤ s * (env.size + diagnosticQuantifierDepth formula) ∧
      (MinimizedFailure.context failed).size ≤ s * s :=
  diagnosticFailureMinimize_storage_le_size W T tables env formula

example {W W' T T' E E' s s' q q' : Nat} {tables tables' : FactTables}
    (hW : W ≤ W') (hT : T ≤ T') (hE : E ≤ E') (hs : s ≤ s') (hq : q ≤ q')
    (hDerived : tables.derivedProps.size ≤ tables'.derivedProps.size) :
    diagnosticReportEvalBound W T tables E s q ≤
      diagnosticReportEvalBound W' T' tables' E' s' q' :=
  diagnosticReportEvalBound_mono hW hT hE hs hq hDerived

example {s s' R R' E E' : Nat} (hs : s ≤ s') (hR : R ≤ R') (hE : E ≤ E') :
    s * (3 * R + 2 * (s * (2 * R + 5)) + 6 * (s * s) + 3 * (s * E) + 10) ≤
      s' * (3 * R' + 2 * (s' * (2 * R' + 5)) + 6 * (s' * s') + 3 * (s' * E') + 10) :=
  diagnosticFailureMinimize_sizeBound_mono hs hR hE

end LeanUfo.Test.Complexity.Formula
