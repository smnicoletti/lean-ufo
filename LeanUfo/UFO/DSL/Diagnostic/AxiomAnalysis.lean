import Lean
import LeanUfo.UFO.DSL.Compiler
import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Complexity.Diagnostics
import LeanUfo.UFO.DSL.Complexity.Diagnostics.ProductFamily
import LeanUfo.UFO.DSL.Frontend.ModelText

/-!
# Axiom-failure diagnostics for finite UFO DSL models

This module reconstructs explanatory evidence from compiled finite tables after
a generated certificate fails. It also supplies the axiom-68 precheck, which
can stop certification before a proof attempt. Neither the precheck nor a
report establishes a semantic theorem: Lean checks the generated proofs.

The data flow is:

```text
failed checker field
  -> diagnostic formula and finite environment
  -> selected failing subformula and successful context
  -> source names, evidence, and suggested assertions
  -> bounded rows for the editor widget
```

A diagnostic formula is an **intermediate representation**: a small language
used between the semantic checker and displayed text. An environment assigns a
concrete world or thing to each formula variable. Quantifiers extend that
environment using lexical shadowing, meaning that an inner variable temporarily
replaces an outer variable with the same name.

The analysis reuses compiler tables, closure matrices, and recorded witnesses.
It does not repeat unbounded graph searches merely to explain a failure. Output
uses accumulators and an evidence budget. The public truncation theorem charges
each retained row. The dispatcher adds the returned costs of its selected
evaluation, search, and report calls under the documented primitive-call model.
The cost-aware-semantics references in `docs/dsl/complexity.md` explain the
separation between returned evidence and its cost. Production entry points
return the counted execution's value. Cost instrumentation does not change
which result they return.
-/

open Lean

namespace LeanUfo.UFO.DSL

-- Cost proofs can use range lists as specifications. Evaluation uses the
-- finite loops, whose equality proofs include the visited-prefix costs.
attribute [local simp] Complexity.allListCosted_range_eq_fin
  Complexity.anyListCosted_range_eq_fin

/-!
## Diagnostic formula language

The small formula language below mirrors selected UFO axiom shapes over finite
tables.  It lets diagnostics evaluate an axiom-like condition, minimize the
failing subformula, and render the result in DSL terms.
-/

private inductive DiagVarKind where
  | thing | world
  deriving Repr, Inhabited, DecidableEq

private structure DiagVar where
  name : String
  kind : DiagVarKind
  deriving Repr, Inhabited

/--
Small first-order diagnostic language used only by the widget.

The formulas below mirror selected UFO axioms over the generated finite tables.
They do not replace the trusted axiom statements: they are for
counterexample localization and user-facing explanations, not for certification.
-/
private inductive DiagAtom where
  | typeSem (thing world : String)
  | individualSem (thing world : String)
  | unary (field : UnaryField) (thing world : String)
  | derivedUnary (field thing world : String)
  | binary (field : BinaryField) (left right world : String)
  | ternary (field : TernaryField) (first second third world : String)
  | derivedBinary (field left right world : String)
  | quaternary (field first second third fourth world : String)
  deriving Repr, Inhabited

private inductive DiagFormula where
  | atom (atom : DiagAtom)
  | eqThing (left right : String)
  | eqWorld (left right : String)
  | not (p : DiagFormula)
  | and (p q : DiagFormula)
  | or (p q : DiagFormula)
  | imp (p q : DiagFormula)
  | iff (p q : DiagFormula)
  | forallThing (name : String) (body : DiagFormula)
  | forallWorld (name : String) (body : DiagFormula)
  | existsThing (name : String) (body : DiagFormula)
  | existsWorld (name : String) (body : DiagFormula)
  | box (currentWorld witnessWorld : String) (body : DiagFormula)
  | dia (currentWorld witnessWorld : String) (body : DiagFormula)
  deriving Repr, Inhabited

private def DiagFormula.nodeCount : DiagFormula → Nat
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => 1
  | .not p | .forallThing _ p | .forallWorld _ p | .existsThing _ p |
      .existsWorld _ p | .box _ _ p | .dia _ _ p => p.nodeCount + 1
  | .and p q | .or p q | .imp p q | .iff p q => p.nodeCount + q.nodeCount + 1

/-- Proof specifications for the leading universal variables and residual
body. Production obtains both results in one counted traversal below. -/
private def DiagFormula.forallVarsInto
    (out : Array DiagVar) : DiagFormula → Array DiagVar
  | .forallThing name body => body.forallVarsInto (out.push ⟨name, .thing⟩)
  | .forallWorld name body => body.forallVarsInto (out.push ⟨name, .world⟩)
  | _ => out

private def DiagFormula.forallVars (formula : DiagFormula) : Array DiagVar :=
  formula.forallVarsInto #[]

private def DiagFormula.stripForalls : DiagFormula → DiagFormula
  | .forallThing _ body => body.stripForalls
  | .forallWorld _ body => body.stripForalls
  | formula => formula

/-- Split a formula at its first non-universal node. Each universal costs a
constructor selection, a variable append, and a loop step. A final selection
costs one. The cost accumulator advances before the tail call, as in the
numeric diagnostic loops, so long prefixes do not defer cost additions. -/
private def DiagFormula.peelForallsCosted.go (out : Array DiagVar) (cost : Nat) :
    DiagFormula → Complexity.Costed (Array DiagVar × DiagFormula)
  | .forallThing name body => go (out.push ⟨name, .thing⟩) (cost + 3) body
  | .forallWorld name body => go (out.push ⟨name, .world⟩) (cost + 3) body
  | body => ⟨(out, body), cost + 1⟩

private def DiagFormula.peelForallsCosted (formula : DiagFormula) :
    Complexity.Costed (Array DiagVar × DiagFormula) :=
  peelForallsCosted.go #[] 1 formula

private theorem DiagFormula.peelForallsCosted_go_value
    (out : Array DiagVar) (cost : Nat) (formula : DiagFormula) :
    (peelForallsCosted.go out cost formula).value =
      (formula.forallVarsInto out, formula.stripForalls) := by
  induction formula generalizing out cost <;>
    simp_all only [peelForallsCosted.go, forallVarsInto, stripForalls]

private theorem DiagFormula.peelForallsCosted_value (formula : DiagFormula) :
    formula.peelForallsCosted.value = (formula.forallVars, formula.stripForalls) :=
  peelForallsCosted_go_value #[] 1 formula

private theorem DiagFormula.peelForallsCosted_go_cost
    (out : Array DiagVar) (cost : Nat) (formula : DiagFormula) :
    (peelForallsCosted.go out cost formula).cost + 3 * out.size =
      cost + 3 * (peelForallsCosted.go out cost formula).value.1.size + 1 := by
  induction formula generalizing out cost with
  | forallThing name body ih =>
      have h := ih (out.push ⟨name, .thing⟩) (cost + 3)
      simp only [peelForallsCosted.go, Array.size_push] at h ⊢
      omega
  | forallWorld name body ih =>
      have h := ih (out.push ⟨name, .world⟩) (cost + 3)
      simp only [peelForallsCosted.go, Array.size_push] at h ⊢
      omega
  | _ => simp only [peelForallsCosted.go]; omega

/-- For K leading universal variables, extraction costs exactly 3K+2.
The fixed two operations initialize the array and inspect the residual body. -/
private theorem DiagFormula.peelForallsCosted_cost (formula : DiagFormula) :
    formula.peelForallsCosted.cost = 3 * formula.forallVars.size + 2 := by
  have h := peelForallsCosted_go_cost #[] 1 formula
  rw [peelForallsCosted_go_value] at h
  simp only [Array.size_empty, Nat.mul_zero, Nat.add_zero] at h
  unfold peelForallsCosted forallVars
  omega

/--
Scan the environment from left to right and retain the last matching binding.
Nested diagnostic quantifiers append bindings, so the last match implements
ordinary lexical shadowing. Each entry costs an iteration, an array read, a
name comparison, and a conditional selection. The final default lookup costs
one more operation. String-character comparison costs are outside this model.
-/
private def lookupVarCosted (env : Array (String × Nat)) (name : String) :
    Complexity.Costed Nat := do
  let found ← Complexity.Costed.foldArray env (none : Option Nat) fun found entry =>
    .tick (if entry.1 == name then some entry.2 else found) 2
  .tick (found.getD 0) 1

private def lookupVar (env : Array (String × Nat)) (name : String) : Nat :=
  (lookupVarCosted env name).value

@[simp] private theorem lookupVarCosted_value
    (env : Array (String × Nat)) (name : String) :
    (lookupVarCosted env name).value = lookupVar env name := rfl

/-- The list fold specifies last-binding selection. It is used only in the
proof: production traverses the supplied array without copying its entries. -/
private theorem lookupVarCosted_eq_lastBinding
    (env : Array (String × Nat)) (name : String) :
    (lookupVarCosted env name).value =
      (env.toList.foldl (fun found entry =>
        if entry.1 == name then some entry.2 else found) none).getD 0 := by
  simp only [lookupVarCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArray_value,
    Array.foldl_toList]

private theorem lookupVarCosted_push_same
    (env : Array (String × Nat)) (name : String) (value : Nat) :
    (lookupVarCosted (env.push (name, value)) name).value = value := by
  rw [lookupVarCosted_eq_lastBinding]
  simp [List.foldl_append]

private theorem lookupVarCosted_cost
    (env : Array (String × Nat)) (name : String) :
    (lookupVarCosted env name).cost = 4 * env.size + 1 := by
  have scan := Complexity.Costed.foldArray_cost_eq env (none : Option Nat)
    (fun found entry =>
      Complexity.Costed.tick (if entry.1 == name then some entry.2 else found) 2)
    2 (by intros; rfl)
  simpa [lookupVarCosted, Bind.bind, Complexity.Costed.bind_cost, Nat.mul_comm] using scan

/-- Read and render a source name, or display an out-of-range coordinate as
`#n`. Both branches cost four primitive calls: comparison and branch, then
either array read and name rendering, or decimal rendering and concatenation.
Name/string character work is outside the primitive-call cost model. -/
private def indexedNameCosted (names : Array Name) (idx : Nat) : Complexity.Costed String :=
  if h : idx < names.size then
    Complexity.Costed.charge 2 do
      let name ← Complexity.Costed.tick names[idx] 1
      Complexity.Costed.tick name.toString 1
  else
    Complexity.Costed.charge 2 do
      let digits ← Complexity.Costed.tick (toString idx) 1
      Complexity.Costed.tick ("#" ++ digits) 1

@[simp] private theorem indexedNameCosted_value (names : Array Name) (idx : Nat) :
    (indexedNameCosted names idx).value = indexedName names idx := by
  unfold indexedNameCosted indexedName
  split <;> simp_all [Bind.bind, Complexity.Costed.bind_value]
  all_goals rfl

@[simp] private theorem indexedNameCosted_cost (names : Array Name) (idx : Nat) :
    (indexedNameCosted names idx).cost = 4 := by
  unfold indexedNameCosted
  split <;> rfl

/-- Join candidate names in their supplied order. The optional accumulator
distinguishes an empty list from an empty first name, so separators remain
correct even for unusual names. The loop allocates no intermediate name list. -/
private def joinIndexedNamesCosted (names : Array Name) (indices : Array Nat)
    (separator : String := ", ") :
    Complexity.Costed String := do
  let joined ← Complexity.Costed.foldArray indices (none : Option String) fun out i => do
    let name ← indexedNameCosted names i
    Complexity.Costed.charge 1 <| match out with
    | none => Complexity.Costed.pure (some name)
    | some text => do
        let text ← Complexity.Costed.tick (text ++ separator) 1
        let text ← Complexity.Costed.tick (text ++ name) 1
        Complexity.Costed.pure (some text)
  Complexity.Costed.tick (joined.getD "") 1

private theorem joinIndexedNamesCosted_cost_le (names : Array Name) (indices : Array Nat)
    (separator : String := ", ") :
    (joinIndexedNamesCosted names indices separator).cost ≤ 9 * indices.size + 1 := by
  have h := Complexity.Costed.foldArray_cost_le indices (none : Option String)
    (fun out i => do
      let name ← indexedNameCosted names i
      Complexity.Costed.charge 1 <| match out with
      | none => Complexity.Costed.pure (some name)
      | some text => do
          let text ← Complexity.Costed.tick (text ++ separator) 1
          let text ← Complexity.Costed.tick (text ++ name) 1
          Complexity.Costed.pure (some text))
    7 (by
      intro out i hi
      simp only [Bind.bind, Complexity.Costed.bind_cost, indexedNameCosted_cost,
        Complexity.Costed.charge_cost]
      cases out <;> simp)
  simp only [Bind.bind] at h
  simp only [joinIndexedNamesCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost]
  omega

/-- A prefix invariant proves the joined string equals intercalation of the
rendered names. The prefix list is proof-only; the executable stores a string. -/
private theorem joinIndexedNamesCosted_value (names : Array Name) (indices : Array Nat)
    (separator : String := ", ") :
    (joinIndexedNamesCosted names indices separator).value =
      String.intercalate separator (indices.toList.map (indexedName names)) := by
  have fold (xs prefixNames : List String) :
      (xs.foldl (fun out name => match out with
        | none => some name
        | some text => some (text ++ separator ++ name))
        (if prefixNames = [] then none else some (String.intercalate separator prefixNames))).getD "" =
        String.intercalate separator (prefixNames ++ xs) := by
    induction xs generalizing prefixNames with
    | nil => cases prefixNames <;> simp
    | cons name xs ih =>
        rw [List.append_cons, ← ih, List.foldl_cons]
        congr
        cases prefixNames with
        | nil => simp
        | cons first rest =>
            simp only [List.cons_ne_nil, ↓reduceIte,
              List.cons_append, Option.some.injEq]
            rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
              String.intercalate_singleton]
  have h := fold (indices.toList.map (indexedName names)) []
  simp only [List.nil_append, ↓reduceIte, List.foldl_map] at h
  simp only [joinIndexedNamesCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArray_value, ← Array.foldl_toList,
    indexedNameCosted_value, Complexity.Costed.charge_value]
  convert h using 1
  congr 2
  funext out i
  cases out <;> rfl

/-- Formatting charges one decimal-format call and two concatenations.
Character traversal, decimal digit work, and allocation are outside this
unit-cost interface; the count is not a constant-time string theorem. -/
private def diagFinThingTermCosted (idx : Nat) : Complexity.Costed String := do
  let digits ← Complexity.Costed.tick (toString idx) 1
  let text ← Complexity.Costed.tick ("(⟨" ++ digits) 1
  Complexity.Costed.tick (text ++ ", by decide⟩ : Fin data.thingCount)") 1

private def diagFinWorldTermCosted (idx : Nat) : Complexity.Costed String := do
  let digits ← Complexity.Costed.tick (toString idx) 1
  let text ← Complexity.Costed.tick ("(⟨" ++ digits) 1
  Complexity.Costed.tick (text ++ ", by decide⟩ : Fin data.worldCount)") 1

private def diagFinThingTerm (idx : Nat) : String := (diagFinThingTermCosted idx).value

private def diagFinWorldTerm (idx : Nat) : String := (diagFinWorldTermCosted idx).value

@[simp] private theorem diagFinThingTermCosted_value (idx : Nat) :
    (diagFinThingTermCosted idx).value = diagFinThingTerm idx := rfl

@[simp] private theorem diagFinWorldTermCosted_value (idx : Nat) :
    (diagFinWorldTermCosted idx).value = diagFinWorldTerm idx := rfl

private theorem diagFinThingTerm_eq (idx : Nat) :
    diagFinThingTerm idx = s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)" := rfl

private theorem diagFinWorldTerm_eq (idx : Nat) :
    diagFinWorldTerm idx = s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)" := rfl

@[simp] private theorem diagFinThingTermCosted_cost (idx : Nat) :
    (diagFinThingTermCosted idx).cost = 3 := rfl

@[simp] private theorem diagFinWorldTermCosted_cost (idx : Nat) :
    (diagFinWorldTermCosted idx).cost = 3 := rfl

/-- Append one space-separated argument to an assertion key. The argument
keeps its own formatting cost; this step adds two concatenations. -/
private def appendDiagTermCosted (text : String) (term : Complexity.Costed String) :
    Complexity.Costed String := do
  let term ← term
  let text ← Complexity.Costed.tick (text ++ " ") 1
  Complexity.Costed.tick (text ++ term) 1

@[simp] private theorem appendDiagTermCosted_value
    (text : String) (term : Complexity.Costed String) :
    (appendDiagTermCosted text term).value = text ++ " " ++ term.value := rfl

@[simp] private theorem appendDiagTermCosted_cost
    (text : String) (term : Complexity.Costed String) :
    (appendDiagTermCosted text term).cost = term.cost + 2 := rfl

private def hasPossibleInstanceCosted
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) :
    Complexity.Costed Bool :=
  Complexity.anyFinCosted worldCount fun w =>
    let w := w.val
    Complexity.anyFinCosted thingCount fun x =>
      let x := x.val
      Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x thing w

private def hasPossibleInstance
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) : Bool :=
  (hasPossibleInstanceCosted worldCount thingCount tables thing).value

/-- Dense search reports a possible instance exactly when the sparse relation
contains an instance in some world. The queried thing must lie in the finite
domain, and representation agreement is an explicit proof obligation. -/
private theorem hasPossibleInstanceCosted_eq_true_iff
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (thing : Fin thingCount) :
    (hasPossibleInstanceCosted worldCount thingCount tables thing.val).value = true ↔
      ∃ w : Fin worldCount, ∃ x : Fin thingCount,
        tables.binaryLookup "inst" x.val thing.val w.val = true := by
  unfold hasPossibleInstanceCosted
  simp only [Complexity.anyFinCosted_eq_list, Complexity.anyListCosted_eq_true_iff,
    List.mem_finRange, true_and]
  simp only [Complexity.diagnosticBinaryCosted_value _ _ tables agreement .inst,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem hasPossibleInstanceCosted_compiled
    (ast : ModelAST) (bounded : Complexity.Production.explicitModelWellBounded ast)
    (thing : Fin ast.thingCount) :
    (hasPossibleInstanceCosted ast.worldCount ast.thingCount
      (compileExplicitModelAST ast) thing.val).value = true ↔
      ∃ w : Fin ast.worldCount, ∃ x : Fin ast.thingCount,
        (compileExplicitModelAST ast).binaryLookup "inst" x.val thing.val w.val = true :=
  hasPossibleInstanceCosted_eq_true_iff _ _ _ (compiledLookups_agree ast bounded) thing

@[simp] private theorem hasPossibleInstanceCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) :
    (hasPossibleInstanceCosted worldCount thingCount tables thing).value =
      hasPossibleInstance worldCount thingCount tables thing := rfl

/-- Possible-instance search charges the actual guarded dense query (at most
17 operations) and two operations per finite-loop visit at each level. -/
private theorem hasPossibleInstanceCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) :
    (hasPossibleInstanceCosted worldCount thingCount tables thing).cost ≤
      worldCount * (thingCount * 19 + 2) := by
  unfold hasPossibleInstanceCosted
  have outer := Complexity.anyListCosted_cost_le
    (List.range worldCount)
    (fun w => Complexity.anyListCosted (List.range thingCount) fun x =>
      Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x thing w)
    (thingCount * 19)
    (by
      intro w hw
      have inner := Complexity.anyListCosted_cost_le
        (List.range thingCount)
        (fun x => Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x thing w)
        17
        (by intro x hx; exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
      simpa using inner)
  simpa using outer

private def boxExImpLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  Complexity.allFinCosted worldCount fun w =>
    let w := w.val
    Complexity.Costed.implies
      (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex x w)
      (fun _ => Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex y w)

private def boxExImpLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  (boxExImpLookupCosted worldCount thingCount tables x y).value

@[simp] private theorem boxExImpLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (boxExImpLookupCosted worldCount thingCount tables x y).value =
      boxExImpLookup worldCount thingCount tables x y := rfl

/-- Modal existence implication reads at most two guarded `Ex` cells per world.
Each read costs at most 12; implication and loop control add four operations.
If the antecedent is false, the consequent read is skipped. -/
private theorem boxExImpLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (boxExImpLookupCosted worldCount thingCount tables x y).cost ≤ 28 * worldCount := by
  unfold boxExImpLookupCosted
  have scan := Complexity.allListCosted_cost_le
    (List.range worldCount)
    (fun w => Complexity.Costed.implies
      (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex x w)
      (fun _ => Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex y w))
    26
    (by
      intro w hw
      exact Complexity.Costed.implies_cost_le _ _ 12 12
        (Complexity.diagnosticUnaryCosted_cost_le _ _ _ _ _ _)
        (Complexity.diagnosticUnaryCosted_cost_le _ _ _ _ _ _))
  simpa [Nat.mul_comm] using scan

private def existentialDependenceLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  boxExImpLookupCosted worldCount thingCount tables x y

private def existentialDependenceLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  (existentialDependenceLookupCosted worldCount thingCount tables x y).value

private def existentialIndependenceLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.not <| existentialDependenceLookupCosted worldCount thingCount tables x y)
    (fun _ => Complexity.Costed.not <|
      existentialDependenceLookupCosted worldCount thingCount tables y x)

private def existentialIndependenceLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  (existentialIndependenceLookupCosted worldCount thingCount tables x y).value

private def existsWithoutLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  Complexity.anyFinCosted worldCount fun w =>
    let w := w.val
    Complexity.Costed.andThen
      (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex x w)
      (fun _ => Complexity.Costed.not <| Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex y w)

private def externallyDependentLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (boxExImpLookupCosted worldCount thingCount tables x y)
    (fun _ => Complexity.allFinCosted thingCount fun z =>
      let z := z.val
      Complexity.Costed.implies
        (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inheresIn x z w)
        (fun _ => Complexity.Costed.andThen
          (existsWithoutLookupCosted worldCount thingCount tables y z)
          (fun _ => existsWithoutLookupCosted worldCount thingCount tables z y)))

private def externallyDependentLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) : Bool :=
  (externallyDependentLookupCosted worldCount thingCount tables x y w).value

private def externallyDependentModeLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.diagnosticUnaryCosted worldCount thingCount tables .mode x w)
    (fun _ => Complexity.anyFinCosted thingCount fun y =>
      let y := y.val
      externallyDependentLookupCosted worldCount thingCount tables x y w)

private def externallyDependentModeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (externallyDependentModeLookupCosted worldCount thingCount tables x w).value

@[simp] private theorem existentialDependenceLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (existentialDependenceLookupCosted worldCount thingCount tables x y).value =
      existentialDependenceLookup worldCount thingCount tables x y := rfl

@[simp] private theorem existentialIndependenceLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceLookupCosted worldCount thingCount tables x y).value =
      existentialIndependenceLookup worldCount thingCount tables x y := rfl

@[simp] private theorem externallyDependentLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (externallyDependentLookupCosted worldCount thingCount tables x y w).value =
      externallyDependentLookup worldCount thingCount tables x y w := rfl

@[simp] private theorem externallyDependentModeLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (externallyDependentModeLookupCosted worldCount thingCount tables x w).value =
      externallyDependentModeLookup worldCount thingCount tables x w := rfl

private theorem existsWithoutLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (existsWithoutLookupCosted worldCount thingCount tables x y).cost ≤ 28 * worldCount := by
  unfold existsWithoutLookupCosted
  have scan := Complexity.anyListCosted_cost_le
    (List.range worldCount)
    (fun w => Complexity.Costed.andThen
      (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex x w)
      (fun _ => Complexity.Costed.not <| Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex y w))
    26
    (by
      intro w hw
      exact Complexity.Costed.andThen_cost_le _ _ 12 13
        (Complexity.diagnosticUnaryCosted_cost_le _ _ _ _ _ _)
        (by
          simpa using Nat.add_le_add_right
            (Complexity.diagnosticUnaryCosted_cost_le worldCount thingCount tables .ex y w) 1))
  simpa [Nat.mul_comm] using scan

private theorem existentialIndependenceLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceLookupCosted worldCount thingCount tables x y).cost ≤
      56 * worldCount + 3 := by
  unfold existentialIndependenceLookupCosted existentialDependenceLookupCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _ (28 * worldCount + 1)
      (28 * worldCount + 1) ?_ ?_) ?_
  · simpa using Nat.add_le_add_right
      (boxExImpLookupCosted_cost_le worldCount thingCount tables x y) 1
  · simpa using Nat.add_le_add_right
      (boxExImpLookupCosted_cost_le worldCount thingCount tables y x) 1
  · omega

private theorem externallyDependentLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (externallyDependentLookupCosted worldCount thingCount tables x y w).cost ≤
      28 * worldCount + thingCount * (56 * worldCount + 22) + 1 := by
  unfold externallyDependentLookupCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _ (28 * worldCount)
      (thingCount * (56 * worldCount + 22)) ?_ ?_) ?_
  · exact boxExImpLookupCosted_cost_le worldCount thingCount tables x y
  · have scan := Complexity.allListCosted_cost_le
      (List.range thingCount)
      (fun z => Complexity.Costed.implies
        (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inheresIn x z w)
        (fun _ => Complexity.Costed.andThen
          (existsWithoutLookupCosted worldCount thingCount tables y z)
          (fun _ => existsWithoutLookupCosted worldCount thingCount tables z y)))
      (56 * worldCount + 20)
      (by
        intro z hz
        refine le_trans
          (Complexity.Costed.implies_cost_le _ _ 17 (56 * worldCount + 1) ?_ ?_) ?_
        · exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _
        · refine le_trans
            (Complexity.Costed.andThen_cost_le _ _ (28 * worldCount) (28 * worldCount)
              ?_ ?_) ?_
          · exact existsWithoutLookupCosted_cost_le worldCount thingCount tables y z
          · exact existsWithoutLookupCosted_cost_le worldCount thingCount tables z y
          · omega
        · omega)
    simpa using scan
  · omega

private theorem externallyDependentModeLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (externallyDependentModeLookupCosted worldCount thingCount tables x w).cost ≤
      thingCount *
        (28 * worldCount + thingCount * (56 * worldCount + 22) + 3) + 13 := by
  unfold externallyDependentModeLookupCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _ 12
      (thingCount * (28 * worldCount + thingCount * (56 * worldCount + 22) + 3))
      ?_ ?_) ?_
  · exact Complexity.diagnosticUnaryCosted_cost_le _ _ _ _ _ _
  · have scan := Complexity.anyListCosted_cost_le
      (List.range thingCount)
      (fun y => externallyDependentLookupCosted worldCount thingCount tables x y w)
      (28 * worldCount + thingCount * (56 * worldCount + 22) + 1)
      (by
        intro y hy
        exact externallyDependentLookupCosted_cost_le worldCount thingCount tables x y w)
    simpa using scan
  · omega

/-- Modal searches use the declared finite domains. Under table agreement,
their dense reads return the sparse relation values at every visited coordinate.
The list on the right is a proof specification, not an allocated search domain. -/
private theorem boxExImpLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x y : Fin thingCount) :
    (boxExImpLookupCosted worldCount thingCount tables x.val y.val).value =
      (List.finRange worldCount).all (fun w =>
        !tables.unaryLookup "ex" x.val w.val || tables.unaryLookup "ex" y.val w.val) := by
  simp only [boxExImpLookupCosted, Complexity.allFinCosted_eq_list,
    Complexity.allListCosted_value, Complexity.Costed.implies_value,
    Complexity.diagnosticUnaryCosted_value _ _ tables agreement,
    FactTables.unaryTypedTable, UnaryField.toTableField]

private theorem existsWithoutLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x y : Fin thingCount) :
    (existsWithoutLookupCosted worldCount thingCount tables x.val y.val).value =
      (List.finRange worldCount).any (fun w =>
        tables.unaryLookup "ex" x.val w.val && !tables.unaryLookup "ex" y.val w.val) := by
  simp only [existsWithoutLookupCosted, Complexity.anyFinCosted_eq_list,
    Complexity.anyListCosted_value, Complexity.Costed.andThen_value,
    Complexity.Costed.not_value,
    Complexity.diagnosticUnaryCosted_value _ _ tables agreement,
    FactTables.unaryTypedTable, UnaryField.toTableField]

private theorem existentialIndependenceLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x y : Fin thingCount) :
    (existentialIndependenceLookupCosted worldCount thingCount tables x.val y.val).value =
      (!(List.finRange worldCount).all (fun w =>
        !tables.unaryLookup "ex" x.val w.val || tables.unaryLookup "ex" y.val w.val) &&
       !(List.finRange worldCount).all (fun w =>
        !tables.unaryLookup "ex" y.val w.val || tables.unaryLookup "ex" x.val w.val)) := by
  simp only [existentialIndependenceLookupCosted, existentialDependenceLookupCosted,
    Complexity.Costed.andThen_value, Complexity.Costed.not_value,
    boxExImpLookupCosted_sparse_value _ _ tables agreement]

private theorem externallyDependentLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x y : Fin thingCount) (w : Fin worldCount) :
    (externallyDependentLookupCosted worldCount thingCount tables x.val y.val w.val).value =
      ((List.finRange worldCount).all (fun v =>
        !tables.unaryLookup "ex" x.val v.val || tables.unaryLookup "ex" y.val v.val) &&
       (List.finRange thingCount).all (fun z =>
         !tables.binaryLookup "inheresIn" x.val z.val w.val ||
           ((List.finRange worldCount).any (fun v =>
             tables.unaryLookup "ex" y.val v.val && !tables.unaryLookup "ex" z.val v.val) &&
            (List.finRange worldCount).any (fun v =>
             tables.unaryLookup "ex" z.val v.val && !tables.unaryLookup "ex" y.val v.val)))) := by
  simp only [externallyDependentLookupCosted, Complexity.Costed.andThen_value,
    boxExImpLookupCosted_sparse_value _ _ tables agreement,
    Complexity.allFinCosted_eq_list, Complexity.allListCosted_value,
    Complexity.Costed.implies_value,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    existsWithoutLookupCosted_sparse_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem externallyDependentModeLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x : Fin thingCount) (w : Fin worldCount) :
    (externallyDependentModeLookupCosted worldCount thingCount tables x.val w.val).value =
      (tables.unaryLookup "mode" x.val w.val &&
       (List.finRange thingCount).any (fun y =>
         (List.finRange worldCount).all (fun v =>
           !tables.unaryLookup "ex" x.val v.val || tables.unaryLookup "ex" y.val v.val) &&
         (List.finRange thingCount).all (fun z =>
           !tables.binaryLookup "inheresIn" x.val z.val w.val ||
             ((List.finRange worldCount).any (fun v =>
               tables.unaryLookup "ex" y.val v.val && !tables.unaryLookup "ex" z.val v.val) &&
              (List.finRange worldCount).any (fun v =>
               tables.unaryLookup "ex" z.val v.val && !tables.unaryLookup "ex" y.val v.val))))) := by
  simp only [externallyDependentModeLookupCosted, Complexity.Costed.andThen_value,
    Complexity.diagnosticUnaryCosted_value _ _ tables agreement,
    Complexity.anyFinCosted_eq_list, Complexity.anyListCosted_value,
    externallyDependentLookupCosted_sparse_value _ _ tables agreement,
    FactTables.unaryTypedTable, UnaryField.toTableField]

private def genericFunctionalDependenceLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.allFinCosted thingCount fun x =>
    let x := x.val
    Complexity.Costed.implies
      (Complexity.Costed.andThen
        (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x x' w)
        (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs x x' w))
      (fun _ => Complexity.anyFinCosted thingCount fun y =>
        let y := y.val
        Complexity.Costed.andThen
          (.tick (y != x) 1)
          (fun _ => Complexity.Costed.andThen
            (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
            (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs y y' w)))

private def genericFunctionalDependenceLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Bool :=
  (genericFunctionalDependenceLookupCosted worldCount thingCount tables x' y' w).value

private def individualFunctionalDependenceLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (genericFunctionalDependenceLookupCosted worldCount thingCount tables x' y' w)
    (fun _ => Complexity.Costed.andThen
      (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x x' w)
      (fun _ => Complexity.Costed.andThen
        (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
        (fun _ => Complexity.Costed.implies
          (Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs x x' w)
          (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs y y' w))))

private def individualFunctionalDependenceLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  (individualFunctionalDependenceLookupCosted worldCount thingCount tables x x' y y' w).value

private def componentOfLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.diagnosticBinaryCosted worldCount thingCount tables .properPart x y w)
    (fun _ => individualFunctionalDependenceLookupCosted worldCount thingCount tables x x' y y' w)

private def componentOfLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  (componentOfLookupCosted worldCount thingCount tables x x' y y' w).value

private def genericConstitutionalDependenceLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.allFinCosted thingCount fun x =>
    let x := x.val
    Complexity.Costed.implies
      (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x x' w)
      (fun _ => Complexity.anyFinCosted thingCount fun y =>
        let y := y.val
        Complexity.Costed.andThen
          (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
          (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .constitutedBy x y w))

private def genericConstitutionalDependenceLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Bool :=
  (genericConstitutionalDependenceLookupCosted worldCount thingCount tables x' y' w).value

private def constitutionLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x x' w)
    (fun _ => Complexity.Costed.andThen
      (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
      (fun _ => Complexity.Costed.andThen
        (genericConstitutionalDependenceLookupCosted worldCount thingCount tables x' y' w)
        (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .constitutedBy x y w)))

private def constitutionLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  (constitutionLookupCosted worldCount thingCount tables x x' y y' w).value

private def quaIndividualLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed Bool :=
  Complexity.anyFinCosted thingCount fun y =>
    let y := y.val
    Complexity.diagnosticBinaryCosted worldCount thingCount tables .quaIndividualOf x y w

/-- Search asserted proposition text in source order. Each visited entry costs
an array read, a comparison, a loop iteration, and an early-exit test. Character
work inside the string comparison remains outside the unit-cost model. -/
private def assertedDerivedPropLookupCosted
    (tables : FactTables) (target : String) : Complexity.Costed Bool :=
  Complexity.anyArrayCosted tables.derivedProps fun prop =>
    .tick (prop == target) 1

private theorem assertedDerivedPropLookupCosted_value
    (tables : FactTables) (target : String) :
    (assertedDerivedPropLookupCosted tables target).value =
      tables.derivedProps.any (fun prop => prop == target) := by
  apply Bool.eq_iff_iff.mpr
  simp [assertedDerivedPropLookupCosted, Complexity.anyArrayCosted_eq_list,
    Complexity.anyListCosted_eq_true_iff, Array.mem_iff_getElem]

/-- Functional dependence searches target instances in coordinate order and
excludes the source instance itself. These equalities connect guarded dense
execution to the sparse relation formulas, assuming bounded coordinates and
table agreement. They make no claim that sparse and dense reads cost the same. -/
private theorem genericFunctionalDependenceLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x' y' : Fin thingCount) (w : Fin worldCount) :
    (genericFunctionalDependenceLookupCosted worldCount thingCount tables
      x'.val y'.val w.val).value =
      (List.finRange thingCount).all (fun x =>
        !(tables.binaryLookup "inst" x.val x'.val w.val &&
          tables.binaryLookup "functionsAs" x.val x'.val w.val) ||
        (List.finRange thingCount).any (fun y => y.val != x.val &&
          (tables.binaryLookup "inst" y.val y'.val w.val &&
           tables.binaryLookup "functionsAs" y.val y'.val w.val))) := by
  simp only [genericFunctionalDependenceLookupCosted, Complexity.allFinCosted_eq_list,
    Complexity.anyFinCosted_eq_list, Complexity.allListCosted_value,
    Complexity.anyListCosted_value, Complexity.Costed.implies_value,
    Complexity.Costed.andThen_value, Complexity.Costed.tick_value,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem genericConstitutionalDependenceLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x' y' : Fin thingCount) (w : Fin worldCount) :
    (genericConstitutionalDependenceLookupCosted worldCount thingCount tables
      x'.val y'.val w.val).value =
      (List.finRange thingCount).all (fun x =>
        !tables.binaryLookup "inst" x.val x'.val w.val ||
        (List.finRange thingCount).any (fun y =>
          tables.binaryLookup "inst" y.val y'.val w.val &&
          tables.binaryLookup "constitutedBy" x.val y.val w.val)) := by
  simp only [genericConstitutionalDependenceLookupCosted, Complexity.allFinCosted_eq_list,
    Complexity.anyFinCosted_eq_list, Complexity.allListCosted_value,
    Complexity.anyListCosted_value, Complexity.Costed.implies_value,
    Complexity.Costed.andThen_value,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem quaIndividualLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x : Fin thingCount) (w : Fin worldCount) :
    (quaIndividualLookupCosted worldCount thingCount tables x.val w.val).value =
      (List.finRange thingCount).any (fun y =>
        tables.binaryLookup "quaIndividualOf" x.val y.val w.val) := by
  simp only [quaIndividualLookupCosted, Complexity.anyFinCosted_eq_list,
    Complexity.anyListCosted_value,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem individualFunctionalDependenceLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x x' y y' : Fin thingCount) (w : Fin worldCount) :
    (individualFunctionalDependenceLookupCosted worldCount thingCount tables
      x.val x'.val y.val y'.val w.val).value =
      ((List.finRange thingCount).all (fun a =>
        !(tables.binaryLookup "inst" a.val x'.val w.val &&
          tables.binaryLookup "functionsAs" a.val x'.val w.val) ||
        (List.finRange thingCount).any (fun b => b.val != a.val &&
          (tables.binaryLookup "inst" b.val y'.val w.val &&
           tables.binaryLookup "functionsAs" b.val y'.val w.val))) &&
       (tables.binaryLookup "inst" x.val x'.val w.val &&
        (tables.binaryLookup "inst" y.val y'.val w.val &&
         (!tables.binaryLookup "functionsAs" x.val x'.val w.val ||
           tables.binaryLookup "functionsAs" y.val y'.val w.val)))) := by
  simp only [individualFunctionalDependenceLookupCosted, Complexity.Costed.andThen_value,
    Complexity.Costed.implies_value,
    genericFunctionalDependenceLookupCosted_sparse_value _ _ tables agreement,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem componentOfLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x x' y y' : Fin thingCount) (w : Fin worldCount) :
    (componentOfLookupCosted worldCount thingCount tables
      x.val x'.val y.val y'.val w.val).value =
      (tables.binaryLookup "properPart" x.val y.val w.val &&
       ((List.finRange thingCount).all (fun a =>
         !(tables.binaryLookup "inst" a.val x'.val w.val &&
           tables.binaryLookup "functionsAs" a.val x'.val w.val) ||
         (List.finRange thingCount).any (fun b => b.val != a.val &&
           (tables.binaryLookup "inst" b.val y'.val w.val &&
            tables.binaryLookup "functionsAs" b.val y'.val w.val))) &&
        (tables.binaryLookup "inst" x.val x'.val w.val &&
         (tables.binaryLookup "inst" y.val y'.val w.val &&
          (!tables.binaryLookup "functionsAs" x.val x'.val w.val ||
            tables.binaryLookup "functionsAs" y.val y'.val w.val))))) := by
  simp only [componentOfLookupCosted, Complexity.Costed.andThen_value,
    individualFunctionalDependenceLookupCosted_sparse_value _ _ tables agreement,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem constitutionLookupCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x x' y y' : Fin thingCount) (w : Fin worldCount) :
    (constitutionLookupCosted worldCount thingCount tables
      x.val x'.val y.val y'.val w.val).value =
      (tables.binaryLookup "inst" x.val x'.val w.val &&
       (tables.binaryLookup "inst" y.val y'.val w.val &&
        ((List.finRange thingCount).all (fun a =>
          !tables.binaryLookup "inst" a.val x'.val w.val ||
          (List.finRange thingCount).any (fun b =>
            tables.binaryLookup "inst" b.val y'.val w.val &&
            tables.binaryLookup "constitutedBy" a.val b.val w.val)) &&
         tables.binaryLookup "constitutedBy" x.val y.val w.val))) := by
  simp only [constitutionLookupCosted, Complexity.Costed.andThen_value,
    genericConstitutionalDependenceLookupCosted_sparse_value _ _ tables agreement,
    Complexity.diagnosticBinaryCosted_value _ _ tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

/-- Each source instance costs at most 35 for its two guarded reads, two for
implication, and two for loop control. Each target candidate costs at most 39,
including its distinctness test, two guarded reads, and scan control. -/
private theorem genericFunctionalDependenceLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    (genericFunctionalDependenceLookupCosted worldCount thingCount tables x' y' w).cost ≤
      thingCount * (39 * thingCount + 39) := by
  unfold genericFunctionalDependenceLookupCosted
  have h := Complexity.allListCosted_cost_le (List.range thingCount)
    (fun x => Complexity.Costed.implies
      (Complexity.Costed.andThen
        (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x x' w)
        (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs x x' w))
      (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
        Complexity.Costed.andThen (.tick (y != x) 1) (fun _ =>
          Complexity.Costed.andThen
            (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
            (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs y y' w))))
    (39 * thingCount + 37) (by
      intro x hx
      refine le_trans
        (Complexity.Costed.implies_cost_le _ _ 35 (39 * thingCount) ?_ ?_) ?_
      · exact Complexity.Costed.andThen_cost_le _ _ 17 17
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
      · have hscan := Complexity.anyListCosted_cost_le (List.range thingCount)
          (fun y => Complexity.Costed.andThen (.tick (y != x) 1) (fun _ =>
            Complexity.Costed.andThen
              (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
              (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .functionsAs y y' w)))
          37 (by
            intro y hy
            refine Complexity.Costed.andThen_cost_le _ _ 1 35 (by simp) ?_
            exact Complexity.Costed.andThen_cost_le _ _ 17 17
              (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
              (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
        simpa [Nat.mul_comm] using hscan
      · omega)
  have hadd : 39 * thingCount + 37 + 2 = 39 * thingCount + 39 := by omega
  simpa only [Complexity.allListCosted_range_eq_fin,
    Complexity.anyListCosted_range_eq_fin, List.length_range, hadd] using h

private theorem genericConstitutionalDependenceLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    (genericConstitutionalDependenceLookupCosted worldCount thingCount tables x' y' w).cost ≤
      thingCount * (37 * thingCount + 21) := by
  unfold genericConstitutionalDependenceLookupCosted
  have h := Complexity.allListCosted_cost_le (List.range thingCount)
    (fun x => Complexity.Costed.implies
      (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst x x' w)
      (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
        Complexity.Costed.andThen
          (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
          (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .constitutedBy x y w)))
    (37 * thingCount + 19) (by
      intro x hx
      refine le_trans
        (Complexity.Costed.implies_cost_le _ _ 17 (37 * thingCount)
          (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _) ?_) ?_
      · have hscan := Complexity.anyListCosted_cost_le (List.range thingCount)
          (fun y => Complexity.Costed.andThen
            (Complexity.diagnosticBinaryCosted worldCount thingCount tables .inst y y' w)
            (fun _ => Complexity.diagnosticBinaryCosted worldCount thingCount tables .constitutedBy x y w))
          35 (by
            intro y hy
            exact Complexity.Costed.andThen_cost_le _ _ 17 17
              (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
              (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _))
        simpa [Nat.mul_comm] using hscan
      · omega)
  have hadd : 37 * thingCount + 19 + 2 = 37 * thingCount + 21 := by omega
  simpa only [Complexity.allListCosted_range_eq_fin,
    Complexity.anyListCosted_range_eq_fin, List.length_range, hadd] using h

private theorem quaIndividualLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualLookupCosted worldCount thingCount tables x w).cost ≤ 19 * thingCount := by
  unfold quaIndividualLookupCosted
  have h := Complexity.anyListCosted_cost_le (List.range thingCount)
    (fun y => Complexity.diagnosticBinaryCosted worldCount thingCount tables .quaIndividualOf x y w)
    17 (by intro y hy; exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
  simpa [Nat.mul_comm] using h

private theorem assertedDerivedPropLookupCosted_cost_le
    (tables : FactTables) (target : String) :
    (assertedDerivedPropLookupCosted tables target).cost ≤
      4 * tables.derivedProps.size := by
  unfold assertedDerivedPropLookupCosted
  have h := Complexity.anyArrayCosted_cost_le tables.derivedProps
    (fun prop => Complexity.Costed.tick (prop == target) 1) 1
    (by intro prop hp; simp)
  simpa [Nat.mul_comm] using h

private theorem individualFunctionalDependenceLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    (individualFunctionalDependenceLookupCosted worldCount thingCount tables x x' y y' w).cost ≤
      thingCount * (39 * thingCount + 39) + 73 := by
  unfold individualFunctionalDependenceLookupCosted
  refine le_trans (Complexity.Costed.andThen_cost_le _ _
    (thingCount * (39 * thingCount + 39)) 72 ?_ ?_) ?_
  · exact genericFunctionalDependenceLookupCosted_cost_le worldCount thingCount tables x' y' w
  · refine Complexity.Costed.andThen_cost_le _ _ 17 54
      (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _) ?_
    refine Complexity.Costed.andThen_cost_le _ _ 17 36
      (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _) ?_
    exact Complexity.Costed.implies_cost_le _ _ 17 17
      (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
      (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
  · omega

private theorem componentOfLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    (componentOfLookupCosted worldCount thingCount tables x x' y y' w).cost ≤
      thingCount * (39 * thingCount + 39) + 91 := by
  unfold componentOfLookupCosted
  refine le_trans (Complexity.Costed.andThen_cost_le _ _ 17
    (thingCount * (39 * thingCount + 39) + 73)
    (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _) ?_) ?_
  · exact individualFunctionalDependenceLookupCosted_cost_le worldCount thingCount tables x x' y y' w
  · omega

private theorem constitutionLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    (constitutionLookupCosted worldCount thingCount tables x x' y y' w).cost ≤
      thingCount * (37 * thingCount + 21) + 54 := by
  unfold constitutionLookupCosted
  refine le_trans (Complexity.Costed.andThen_cost_le _ _ 17
    (thingCount * (37 * thingCount + 21) + 36)
    (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _) ?_) ?_
  · refine le_trans (Complexity.Costed.andThen_cost_le _ _ 17
      (thingCount * (37 * thingCount + 21) + 18)
      (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _) ?_) ?_
    · refine Complexity.Costed.andThen_cost_le _ _
        (thingCount * (37 * thingCount + 21)) 17 ?_
        (Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
      exact genericConstitutionalDependenceLookupCosted_cost_le worldCount thingCount tables x' y' w
    · omega
  · omega

/-- One explicit bound that covers every derived-predicate implementation.
It is a sum of the concrete component bounds, rather than a postulated maximum;
this keeps each source of work visible for the later formula theorem. -/
private def derivedLookupCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  (thingCount *
      (28 * worldCount + thingCount * (56 * worldCount + 22) + 3) + 13) +
    (56 * worldCount + 3) +
    (28 * worldCount + thingCount * (56 * worldCount + 22) + 1) +
    thingCount * (39 * thingCount + 39) +
    thingCount * (37 * thingCount + 21) +
    19 * thingCount + 4 * tables.derivedProps.size + 26

/-- Compare derived names in declaration order, charging one string comparison
and one branch at each test. The binary dispatcher has at most five tests.
Character work within a comparison is outside the unit-cost model. -/
private def derivedUnaryLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.charge 2 <|
    if field == "ExternallyDependentMode" then
      externallyDependentModeLookupCosted worldCount thingCount tables x w
    else Complexity.Costed.charge 2 <|
      if field == "QuaIndividual" then
        quaIndividualLookupCosted worldCount thingCount tables x w
      else do
        let text ← Complexity.Costed.tick ("sig." ++ field) 1
        let text ← appendDiagTermCosted text (diagFinThingTermCosted x)
        let target ← appendDiagTermCosted text (diagFinWorldTermCosted w)
        assertedDerivedPropLookupCosted tables target

private def derivedUnaryLookup
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) : Bool :=
  (derivedUnaryLookupCosted worldCount thingCount tables field x w).value

/-- Build a binary assertion key once, then scan stored assertions in order.
Duplicate assertions stop at their first match and do not duplicate a witness. -/
private def assertedDerivedBinaryLookupCosted
    (tables : FactTables) (field : String) (x y w : Nat) : Complexity.Costed Bool := do
  let text ← Complexity.Costed.tick ("sig." ++ field) 1
  let text ← appendDiagTermCosted text (diagFinThingTermCosted x)
  let text ← appendDiagTermCosted text (diagFinThingTermCosted y)
  let target ← appendDiagTermCosted text (diagFinWorldTermCosted w)
  assertedDerivedPropLookupCosted tables target

private def assertedDerivedBinaryLookup
    (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  (assertedDerivedBinaryLookupCosted tables field x y w).value

private theorem assertedDerivedBinaryLookupCosted_eq_any
    (tables : FactTables) (field : String) (x y w : Nat) :
    (assertedDerivedBinaryLookupCosted tables field x y w).value =
      tables.derivedProps.any (fun prop =>
        prop == s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}") := by
  simp only [assertedDerivedBinaryLookupCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, appendDiagTermCosted_value,
    diagFinThingTermCosted_value, diagFinWorldTermCosted_value,
    assertedDerivedPropLookupCosted_value]
  rfl

private theorem assertedDerivedBinaryLookupCosted_cost_le
    (tables : FactTables) (field : String) (x y w : Nat) :
    (assertedDerivedBinaryLookupCosted tables field x y w).cost ≤
      16 + 4 * tables.derivedProps.size := by
  have h := assertedDerivedPropLookupCosted_cost_le tables
    ("sig." ++ field ++ " " ++ diagFinThingTerm x ++ " " ++ diagFinThingTerm y ++
      " " ++ diagFinWorldTerm w)
  simp only [assertedDerivedBinaryLookupCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_value, Complexity.Costed.tick_cost,
    appendDiagTermCosted_cost, appendDiagTermCosted_value,
    diagFinThingTermCosted_cost, diagFinThingTermCosted_value,
    diagFinWorldTermCosted_cost, diagFinWorldTermCosted_value]
  omega

private def derivedBinaryLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x y w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.charge 2 <|
    if field == "ExistentialDependence" then
      existentialDependenceLookupCosted worldCount thingCount tables x y
    else Complexity.Costed.charge 2 <|
      if field == "ExistentialIndependence" then
        existentialIndependenceLookupCosted worldCount thingCount tables x y
      else Complexity.Costed.charge 2 <|
        if field == "ExternallyDependent" then
          externallyDependentLookupCosted worldCount thingCount tables x y w
        else Complexity.Costed.charge 2 <|
          if field == "GenericFunctionalDependence" then
            genericFunctionalDependenceLookupCosted worldCount thingCount tables x y w
          else Complexity.Costed.charge 2 <|
            if field == "GenericConstitutionalDependence" then
              genericConstitutionalDependenceLookupCosted worldCount thingCount tables x y w
            else assertedDerivedBinaryLookupCosted tables field x y w

private def derivedBinaryLookup
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  (derivedBinaryLookupCosted worldCount thingCount tables field x y w).value

/-- Counted name selection preserves the declared predicates and the fallback
for user-written assertions. Matching remains case-sensitive. -/
private theorem derivedUnaryLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) :
    (derivedUnaryLookupCosted worldCount thingCount tables field x w).value =
      match field with
      | "ExternallyDependentMode" =>
          (externallyDependentModeLookupCosted worldCount thingCount tables x w).value
      | "QuaIndividual" => (quaIndividualLookupCosted worldCount thingCount tables x w).value
      | _ => tables.derivedProps.any (fun prop =>
          prop == s!"sig.{field} {diagFinThingTerm x} {diagFinWorldTerm w}") := by
  unfold derivedUnaryLookupCosted
  split_ifs <;> simp only [Complexity.Costed.charge_value,
    Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
    appendDiagTermCosted_value, diagFinThingTermCosted_value, diagFinWorldTermCosted_value,
    assertedDerivedPropLookupCosted_value] <;> split <;> simp_all
  rfl

private theorem derivedBinaryLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x y w : Nat) :
    (derivedBinaryLookupCosted worldCount thingCount tables field x y w).value =
      match field with
      | "ExistentialDependence" =>
          (existentialDependenceLookupCosted worldCount thingCount tables x y).value
      | "ExistentialIndependence" =>
          (existentialIndependenceLookupCosted worldCount thingCount tables x y).value
      | "ExternallyDependent" =>
          (externallyDependentLookupCosted worldCount thingCount tables x y w).value
      | "GenericFunctionalDependence" =>
          (genericFunctionalDependenceLookupCosted worldCount thingCount tables x y w).value
      | "GenericConstitutionalDependence" =>
          (genericConstitutionalDependenceLookupCosted worldCount thingCount tables x y w).value
      | _ => tables.derivedProps.any (fun prop =>
          prop == s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}") := by
  unfold derivedBinaryLookupCosted
  split_ifs <;> simp only [Complexity.Costed.charge_value,
    assertedDerivedBinaryLookupCosted_eq_any] <;> split <;> simp_all

private theorem derivedUnaryLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) :
    (derivedUnaryLookupCosted worldCount thingCount tables field x w).cost ≤
      derivedLookupCostBound worldCount thingCount tables := by
  have hmode := externallyDependentModeLookupCosted_cost_le worldCount thingCount tables x w
  have hqua := quaIndividualLookupCosted_cost_le worldCount thingCount tables x w
  have hassert := assertedDerivedPropLookupCosted_cost_le tables
    s!"sig.{field} {diagFinThingTerm x} {diagFinWorldTerm w}"
  dsimp only [toString] at hassert
  unfold derivedUnaryLookupCosted
  split_ifs <;> simp only [Complexity.Costed.charge_cost, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.tick_value,
    Complexity.Costed.tick_cost, appendDiagTermCosted_value, appendDiagTermCosted_cost,
    diagFinThingTermCosted_value, diagFinWorldTermCosted_value,
    diagFinThingTermCosted_cost, diagFinWorldTermCosted_cost] <;>
    unfold derivedLookupCostBound <;> omega

private theorem derivedBinaryLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (field : String) (x y w : Nat) :
    (derivedBinaryLookupCosted worldCount thingCount tables field x y w).cost ≤
      derivedLookupCostBound worldCount thingCount tables := by
  have hdep : (existentialDependenceLookupCosted worldCount thingCount tables x y).cost ≤
      28 * worldCount := boxExImpLookupCosted_cost_le worldCount thingCount tables x y
  have hind := existentialIndependenceLookupCosted_cost_le worldCount thingCount tables x y
  have hext := externallyDependentLookupCosted_cost_le worldCount thingCount tables x y w
  have hfunc := genericFunctionalDependenceLookupCosted_cost_le worldCount thingCount tables x y w
  have hconst := genericConstitutionalDependenceLookupCosted_cost_le worldCount thingCount tables x y w
  have hassert := assertedDerivedBinaryLookupCosted_cost_le tables field x y w
  unfold derivedBinaryLookupCosted
  split_ifs <;> simp only [Complexity.Costed.charge_cost] <;>
    unfold derivedLookupCostBound <;> omega

/-- Each atom visit charges one constructor test. Binary atoms also inspect
their field constructor to select the reflexive part/overlap behavior.
These tests occur before variable lookup, even when a later query stops early. -/
private def evalDiagAtomCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagAtom → Complexity.Costed Bool
  | .typeSem thing _world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env thing >>= fun thingIdx =>
          hasPossibleInstanceCosted worldCount thingCount tables thingIdx
  | .individualSem thing _world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env thing >>= fun thingIdx =>
          Complexity.Costed.not <|
            hasPossibleInstanceCosted worldCount thingCount tables thingIdx
  | .unary field thing world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env thing >>= fun thingIdx =>
        lookupVarCosted env world >>= fun worldIdx =>
          Complexity.diagnosticUnaryCosted worldCount thingCount tables field thingIdx worldIdx
  | .derivedUnary field thing world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env thing >>= fun thingIdx =>
        lookupVarCosted env world >>= fun worldIdx =>
          derivedUnaryLookupCosted worldCount thingCount tables field thingIdx worldIdx
  | .binary (.part) left right world =>
      Complexity.Costed.charge 2 <|
        lookupVarCosted env left >>= fun leftIdx =>
        lookupVarCosted env right >>= fun rightIdx =>
          Complexity.Costed.orElse
            (.tick (leftIdx == rightIdx) 1)
            (fun _ => lookupVarCosted env world >>= fun worldIdx =>
              Complexity.diagnosticBinaryCosted worldCount thingCount tables .part leftIdx rightIdx worldIdx)
  | .binary (.overlap) left right world =>
      Complexity.Costed.charge 2 <|
        lookupVarCosted env left >>= fun leftIdx =>
        lookupVarCosted env right >>= fun rightIdx =>
          Complexity.Costed.orElse
            (.tick (leftIdx == rightIdx) 1)
            (fun _ => lookupVarCosted env world >>= fun worldIdx =>
              Complexity.diagnosticBinaryCosted worldCount thingCount tables .overlap leftIdx rightIdx worldIdx)
  | .binary field left right world =>
      Complexity.Costed.charge 2 <|
        lookupVarCosted env left >>= fun leftIdx =>
        lookupVarCosted env right >>= fun rightIdx =>
        lookupVarCosted env world >>= fun worldIdx =>
          Complexity.diagnosticBinaryCosted worldCount thingCount tables field leftIdx rightIdx worldIdx
  | .ternary field first second third world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env first >>= fun firstIdx =>
        lookupVarCosted env second >>= fun secondIdx =>
        lookupVarCosted env third >>= fun thirdIdx =>
        lookupVarCosted env world >>= fun worldIdx =>
          Complexity.diagnosticTernaryCosted worldCount thingCount tables field
            firstIdx secondIdx thirdIdx worldIdx
  | .derivedBinary field left right world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env left >>= fun leftIdx =>
        lookupVarCosted env right >>= fun rightIdx =>
        lookupVarCosted env world >>= fun worldIdx =>
          derivedBinaryLookupCosted worldCount thingCount tables field leftIdx rightIdx worldIdx
  | .quaternary field first second third fourth world =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env first >>= fun firstIdx =>
        lookupVarCosted env second >>= fun secondIdx =>
        lookupVarCosted env third >>= fun thirdIdx =>
        lookupVarCosted env fourth >>= fun fourthIdx =>
        lookupVarCosted env world >>= fun worldIdx =>
          do
            let text ← Complexity.Costed.tick ("sig." ++ field) 1
            let text ← appendDiagTermCosted text (diagFinThingTermCosted firstIdx)
            let text ← appendDiagTermCosted text (diagFinThingTermCosted secondIdx)
            let text ← appendDiagTermCosted text (diagFinThingTermCosted thirdIdx)
            let text ← appendDiagTermCosted text (diagFinThingTermCosted fourthIdx)
            let target ← appendDiagTermCosted text (diagFinWorldTermCosted worldIdx)
            assertedDerivedPropLookupCosted tables target

private theorem evalDiagAtomCosted_quaternary_value
    (worldCount thingCount : Nat) (tables : FactTables) (env : Array (String × Nat))
    (field first second third fourth world : String) :
    (evalDiagAtomCosted worldCount thingCount tables env
      (.quaternary field first second third fourth world)).value =
      tables.derivedProps.any (fun prop => prop ==
        s!"sig.{field} {diagFinThingTerm (lookupVarCosted env first).value} {diagFinThingTerm (lookupVarCosted env second).value} {diagFinThingTerm (lookupVarCosted env third).value} {diagFinThingTerm (lookupVarCosted env fourth).value} {diagFinWorldTerm (lookupVarCosted env world).value}") := by
  simp only [evalDiagAtomCosted, Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, appendDiagTermCosted_value,
    diagFinThingTermCosted_value, diagFinWorldTermCosted_value,
    assertedDerivedPropLookupCosted_value]
  rfl

/-- Primitive atom evaluation agrees with the sparse relation when the
environment supplies in-domain coordinates and the tables have a correspondence
proof. Variable resolution is the same computation on both sides. -/
private theorem evalDiagAtomCosted_unary_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (env : Array (String × Nat)) (field : UnaryField) (thing world : String)
    (hx : (lookupVarCosted env thing).value < thingCount)
    (hw : (lookupVarCosted env world).value < worldCount) :
    (evalDiagAtomCosted worldCount thingCount tables env (.unary field thing world)).value =
      tables.unaryLookup field.toTableField
        (lookupVarCosted env thing).value (lookupVarCosted env world).value := by
  simp only [evalDiagAtomCosted, Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value]
  exact Complexity.diagnosticUnaryCosted_value _ _ _ agreement field ⟨_, hx⟩ ⟨_, hw⟩

private theorem evalDiagAtomCosted_binary_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (env : Array (String × Nat)) (field : BinaryField) (left right world : String)
    (hx : (lookupVarCosted env left).value < thingCount)
    (hy : (lookupVarCosted env right).value < thingCount)
    (hw : (lookupVarCosted env world).value < worldCount) :
    (evalDiagAtomCosted worldCount thingCount tables env (.binary field left right world)).value =
      let x := (lookupVarCosted env left).value
      let y := (lookupVarCosted env right).value
      let w := (lookupVarCosted env world).value
      match field with
      | .part | .overlap => (x == y) || tables.binaryLookup field.toTableField x y w
      | _ => tables.binaryLookup field.toTableField x y w := by
  have query (relation : BinaryField) :
      (Complexity.diagnosticBinaryCosted worldCount thingCount tables relation
        (lookupVarCosted env left).value (lookupVarCosted env right).value
        (lookupVarCosted env world).value).value =
      tables.binaryLookup relation.toTableField (lookupVarCosted env left).value
        (lookupVarCosted env right).value (lookupVarCosted env world).value :=
    Complexity.diagnosticBinaryCosted_value _ _ _ agreement relation ⟨_, hx⟩ ⟨_, hy⟩ ⟨_, hw⟩
  cases field <;>
    simp only [evalDiagAtomCosted, Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value,
      Complexity.Costed.orElse, Complexity.Costed.tick, query]
  all_goals
    cases (lookupVarCosted env left).value == (lookupVarCosted env right).value <;> simp

private theorem evalDiagAtomCosted_ternary_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (env : Array (String × Nat)) (field : TernaryField) (first second third world : String)
    (hx : (lookupVarCosted env first).value < thingCount)
    (hy : (lookupVarCosted env second).value < thingCount)
    (hz : (lookupVarCosted env third).value < thingCount)
    (hw : (lookupVarCosted env world).value < worldCount) :
    (evalDiagAtomCosted worldCount thingCount tables env
      (.ternary field first second third world)).value =
      tables.ternaryLookup field.toTableField
        (lookupVarCosted env first).value (lookupVarCosted env second).value
        (lookupVarCosted env third).value (lookupVarCosted env world).value := by
  simp only [evalDiagAtomCosted, Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value]
  exact Complexity.diagnosticTernaryCosted_value _ _ _ agreement field ⟨_, hx⟩ ⟨_, hy⟩
    ⟨_, hz⟩ ⟨_, hw⟩

private def evalDiagAtom
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (atom : DiagAtom) : Bool :=
  (evalDiagAtomCosted worldCount thingCount tables env atom).value

/-- Bound for the diagnostic atom counter. At most five variable lookups each
visit the full environment. Primitive atoms and possible-instance search include
guarded dense reads and constructor tests. Computed derived predicates compose
guarded queries; asserted derived predicates scan stored strings. -/
private def diagAtomCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (envSize : Nat) : Nat :=
  20 * envSize +
    worldCount * (thingCount * 19 + 2) +
    derivedLookupCostBound worldCount thingCount tables + 32

private theorem evalDiagAtomCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤
      diagAtomCostBound worldCount thingCount tables env.size := by
  cases atom with
  | typeSem thing world =>
      change 1 + ((lookupVarCosted env thing).cost +
          (hasPossibleInstanceCosted worldCount thingCount tables
            (lookupVarCosted env thing).value).cost) ≤ _
      rw [lookupVarCosted_cost]
      have h := hasPossibleInstanceCosted_cost_le worldCount thingCount tables
        (lookupVarCosted env thing).value
      unfold diagAtomCostBound
      omega
  | individualSem thing world =>
      change 1 + ((lookupVarCosted env thing).cost +
          (hasPossibleInstanceCosted worldCount thingCount tables
            (lookupVarCosted env thing).value).cost + 1) ≤ _
      rw [lookupVarCosted_cost]
      have h := hasPossibleInstanceCosted_cost_le worldCount thingCount tables
        (lookupVarCosted env thing).value
      unfold diagAtomCostBound
      omega
  | unary field thing world =>
      simp only [evalDiagAtomCosted, Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      have hquery := Complexity.diagnosticUnaryCosted_cost_le worldCount thingCount tables field
        (lookupVarCosted env thing).value (lookupVarCosted env world).value
      rw [lookupVarCosted_cost, lookupVarCosted_cost]
      unfold diagAtomCostBound
      omega
  | derivedUnary field thing world =>
      change 1 + ((lookupVarCosted env thing).cost +
          ((lookupVarCosted env world).cost +
            (derivedUnaryLookupCosted worldCount thingCount tables field
              (lookupVarCosted env thing).value (lookupVarCosted env world).value).cost)) ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost]
      have h := derivedUnaryLookupCosted_cost_le worldCount thingCount tables field
        (lookupVarCosted env thing).value (lookupVarCosted env world).value
      unfold diagAtomCostBound
      omega
  | binary field left right world =>
      have special (relation : BinaryField) :
          (do
            let leftIdx ← lookupVarCosted env left
            let rightIdx ← lookupVarCosted env right
            Complexity.Costed.orElse
              (.tick (leftIdx == rightIdx) 1)
              (fun _ => lookupVarCosted env world >>= fun worldIdx =>
                Complexity.diagnosticBinaryCosted worldCount thingCount tables relation
                  leftIdx rightIdx worldIdx)).cost + 2 ≤
            diagAtomCostBound worldCount thingCount tables env.size := by
        change (lookupVarCosted env left).cost +
            ((lookupVarCosted env right).cost +
              (Complexity.Costed.orElse _ _).cost) + 2 ≤ _
        have hr : (do
            let worldIdx ← lookupVarCosted env world
            Complexity.diagnosticBinaryCosted worldCount thingCount tables relation
              (lookupVarCosted env left).value (lookupVarCosted env right).value worldIdx).cost ≤
              4 * env.size + 18 := by
          simp only [Bind.bind, Complexity.Costed.bind_cost]
          have hquery := Complexity.diagnosticBinaryCosted_cost_le worldCount thingCount tables relation
            (lookupVarCosted env left).value (lookupVarCosted env right).value
            (lookupVarCosted env world).value
          rw [lookupVarCosted_cost]
          omega
        have hor := Complexity.Costed.orElse_cost_le
          (Complexity.Costed.tick
            ((lookupVarCosted env left).value == (lookupVarCosted env right).value) 1)
          (fun _ => do
            let worldIdx ← lookupVarCosted env world
            Complexity.diagnosticBinaryCosted worldCount thingCount tables relation
              (lookupVarCosted env left).value (lookupVarCosted env right).value worldIdx)
          1 (4 * env.size + 18) (by simp) hr
        rw [lookupVarCosted_cost, lookupVarCosted_cost]
        unfold diagAtomCostBound
        omega
      have ordinary (relation : BinaryField) :
          (do
            let leftIdx ← lookupVarCosted env left
            let rightIdx ← lookupVarCosted env right
            let worldIdx ← lookupVarCosted env world
            Complexity.diagnosticBinaryCosted worldCount thingCount tables relation
              leftIdx rightIdx worldIdx).cost + 2 ≤
            diagAtomCostBound worldCount thingCount tables env.size := by
        simp only [Bind.bind, Complexity.Costed.bind_cost]
        have hquery := Complexity.diagnosticBinaryCosted_cost_le worldCount thingCount tables relation
          (lookupVarCosted env left).value (lookupVarCosted env right).value
          (lookupVarCosted env world).value
        rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost]
        unfold diagAtomCostBound
        omega
      cases field <;> simp only [evalDiagAtomCosted, Complexity.Costed.charge_cost]
      case part => simpa only [Nat.add_comm] using special .part
      case overlap => simpa only [Nat.add_comm] using special .overlap
      all_goals simpa only [Nat.add_comm] using ordinary _
  | ternary field first second third world =>
      simp only [evalDiagAtomCosted, Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      have hquery := Complexity.diagnosticTernaryCosted_cost_le worldCount thingCount tables field
        (lookupVarCosted env first).value (lookupVarCosted env second).value
        (lookupVarCosted env third).value (lookupVarCosted env world).value
      rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost,
        lookupVarCosted_cost]
      unfold diagAtomCostBound
      omega
  | derivedBinary field left right world =>
      change 1 + ((lookupVarCosted env left).cost +
          ((lookupVarCosted env right).cost +
            ((lookupVarCosted env world).cost +
              (derivedBinaryLookupCosted worldCount thingCount tables field
                (lookupVarCosted env left).value (lookupVarCosted env right).value
                (lookupVarCosted env world).value).cost))) ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost]
      have h := derivedBinaryLookupCosted_cost_le worldCount thingCount tables field
        (lookupVarCosted env left).value (lookupVarCosted env right).value
        (lookupVarCosted env world).value
      unfold diagAtomCostBound
      omega
  | quaternary field first second third fourth world =>
      simp only [evalDiagAtomCosted, Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost,
        Complexity.Costed.tick_cost, Complexity.Costed.tick_value,
        appendDiagTermCosted_cost, appendDiagTermCosted_value,
        diagFinThingTermCosted_cost, diagFinThingTermCosted_value,
        diagFinWorldTermCosted_cost, diagFinWorldTermCosted_value]
      rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost,
        lookupVarCosted_cost, lookupVarCosted_cost]
      have h := assertedDerivedPropLookupCosted_cost_le tables
        s!"sig.{field} {diagFinThingTerm (lookupVarCosted env first).value} {diagFinThingTerm (lookupVarCosted env second).value} {diagFinThingTerm (lookupVarCosted env third).value} {diagFinThingTerm (lookupVarCosted env fourth).value} {diagFinWorldTerm (lookupVarCosted env world).value}"
      dsimp only [toString] at h
      unfold diagAtomCostBound derivedLookupCostBound
      omega

@[simp] private theorem evalDiagAtomCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (evalDiagAtomCosted worldCount thingCount tables env atom).value =
      evalDiagAtom worldCount thingCount tables env atom := rfl

/-- Count the constructor test at every visited formula node. A skipped
subformula contributes no cost. An empty quantifier still selects its outer
constructor, though its domain loop performs no body evaluations. -/
private def evalDiagFormulaCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → Complexity.Costed Bool
  | .atom atom => Complexity.Costed.charge 1 <| evalDiagAtomCosted worldCount thingCount tables env atom
  | .eqThing left right | .eqWorld left right =>
      Complexity.Costed.charge 1 <|
        lookupVarCosted env left >>= fun leftIdx =>
        lookupVarCosted env right >>= fun rightIdx =>
          .tick (leftIdx == rightIdx) 1
  | .not p =>
      Complexity.Costed.charge 1 <|
        Complexity.Costed.not <| evalDiagFormulaCosted worldCount thingCount tables env p
  | .and p q =>
      Complexity.Costed.charge 1 <|
        Complexity.Costed.andThen
          (evalDiagFormulaCosted worldCount thingCount tables env p)
          (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .or p q =>
      Complexity.Costed.charge 1 <|
        Complexity.Costed.orElse
          (evalDiagFormulaCosted worldCount thingCount tables env p)
          (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .imp p q =>
      Complexity.Costed.charge 1 <|
        Complexity.Costed.implies
          (evalDiagFormulaCosted worldCount thingCount tables env p)
          (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .iff p q =>
      Complexity.Costed.charge 1 <|
        Complexity.Costed.iff
          (evalDiagFormulaCosted worldCount thingCount tables env p)
          (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .forallThing name body =>
      Complexity.Costed.charge 1 <|
        Complexity.allFinCosted thingCount fun x =>
          let x := x.val
          Complexity.Costed.charge 1 <|
            evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body
  | .forallWorld name body =>
      Complexity.Costed.charge 1 <|
        Complexity.allFinCosted worldCount fun w =>
          let w := w.val
          Complexity.Costed.charge 1 <|
            evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body
  | .existsThing name body =>
      Complexity.Costed.charge 1 <|
        Complexity.anyFinCosted thingCount fun x =>
          let x := x.val
          Complexity.Costed.charge 1 <|
            evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body
  | .existsWorld name body =>
      Complexity.Costed.charge 1 <|
        Complexity.anyFinCosted worldCount fun w =>
          let w := w.val
          Complexity.Costed.charge 1 <|
            evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body
  | .box _currentWorld witnessWorld body =>
      Complexity.Costed.charge 1 <|
        Complexity.allFinCosted worldCount fun w =>
          let w := w.val
          Complexity.Costed.charge 1 <|
            evalDiagFormulaCosted worldCount thingCount tables
              (env.push (witnessWorld, w)) body
  | .dia _currentWorld witnessWorld body =>
      Complexity.Costed.charge 1 <|
        Complexity.anyFinCosted worldCount fun w =>
          let w := w.val
          Complexity.Costed.charge 1 <|
            evalDiagFormulaCosted worldCount thingCount tables
              (env.push (witnessWorld, w)) body

private def evalDiagFormula
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Bool :=
  (evalDiagFormulaCosted worldCount thingCount tables env formula).value

/-- Structural evaluator bound parameterized by the cost of one atom at a
given environment size. This recurrence follows the executable connective and
quantifier order; it does not replace evaluation with an unrelated counter. -/
private def DiagFormula.evalCostBound
    (worldCount thingCount : Nat) (atomBound : Nat → Nat) (envSize : Nat) :
    DiagFormula → Nat
  | .atom _ => atomBound envSize + 1
  | .eqThing _ _ | .eqWorld _ _ => 8 * envSize + 4
  | .not p => p.evalCostBound worldCount thingCount atomBound envSize + 2
  | .and p q | .or p q =>
      p.evalCostBound worldCount thingCount atomBound envSize +
        q.evalCostBound worldCount thingCount atomBound envSize + 2
  | .imp p q | .iff p q =>
      p.evalCostBound worldCount thingCount atomBound envSize +
        q.evalCostBound worldCount thingCount atomBound envSize + 3
  | .forallThing _ body | .existsThing _ body =>
      thingCount * (body.evalCostBound worldCount thingCount atomBound (envSize + 1) + 3) + 1
  | .forallWorld _ body | .existsWorld _ body | .box _ _ body | .dia _ _ body =>
      worldCount * (body.evalCostBound worldCount thingCount atomBound (envSize + 1) + 3) + 1

private theorem evalDiagFormulaCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost ≤
      formula.evalCostBound worldCount thingCount atomBound env.size := by
  induction formula generalizing env with
  | atom atom =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := hAtom env atom
      omega
  | eqThing left right | eqWorld left right =>
      change 1 + ((lookupVarCosted env left).cost +
          (lookupVarCosted env right).cost + 1) ≤ 8 * env.size + 4
      rw [lookupVarCosted_cost, lookupVarCosted_cost]
      omega
  | not p ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost,
        Complexity.Costed.not_cost]
      have h := ih env
      omega
  | and p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.Costed.andThen_cost_le
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
        (p.evalCostBound worldCount thingCount atomBound env.size)
        (q.evalCostBound worldCount thingCount atomBound env.size)
        (ihp env) (ihq env)
      omega
  | or p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.Costed.orElse_cost_le
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
        (p.evalCostBound worldCount thingCount atomBound env.size)
        (q.evalCostBound worldCount thingCount atomBound env.size)
        (ihp env) (ihq env)
      omega
  | imp p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.Costed.implies_cost_le
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q) _ _ (ihp env) (ihq env)
      omega
  | iff p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.Costed.iff_cost_le
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q) _ _ (ihp env) (ihq env)
      omega
  | forallThing name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.allListCosted_cost_le (List.range thingCount)
        (fun x => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro x hx
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, x))
          simp only [Array.size_push] at hbody
          omega)
      simp [Nat.add_assoc] at h
      omega
  | existsThing name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.anyListCosted_cost_le (List.range thingCount)
        (fun x => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro x hx
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, x))
          simp only [Array.size_push] at hbody
          omega)
      simp [Nat.add_assoc] at h
      omega
  | forallWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.allListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simp [Nat.add_assoc] at h
      omega
  | existsWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.anyListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simp [Nat.add_assoc] at h
      omega
  | box currentWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.allListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simp [Nat.add_assoc] at h
      omega
  | dia currentWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound, Complexity.Costed.charge_cost]
      have h := Complexity.anyListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simp [Nat.add_assoc] at h
      omega

/-- Evaluator bound instantiated with the diagnostic atom counter. The bound
depends on the formula, model dimensions, environment size, and tables.
It includes atom/formula constructor tests and nested binary-field selection. -/
private theorem evalDiagFormulaCosted_concrete_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost ≤
      formula.evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) env.size := by
  exact evalDiagFormulaCosted_cost_le worldCount thingCount tables
    (diagAtomCostBound worldCount thingCount tables)
    (evalDiagAtomCosted_cost_le worldCount thingCount tables) env formula

@[simp] private theorem evalDiagFormulaCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).value =
      evalDiagFormula worldCount thingCount tables env formula := rfl

private theorem evalDiagFormulaCosted_concrete_cost_le_of_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) (result : Bool)
    (_hValue : evalDiagFormula worldCount thingCount tables env formula = result) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost ≤
      formula.evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) env.size :=
  evalDiagFormulaCosted_concrete_cost_le worldCount thingCount tables env formula

/-- Visit ascending coordinates and return as soon as the evidence budget is
full. Each visited coordinate charges the loop iteration, the stop predicate
call, and its Boolean branch. The production stop predicate is one size
comparison. Visitor costs are accumulated before the tail call. -/
private def foldDiagDomainCosted.go (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) :
    Nat → Nat → σ → Nat → Complexity.Costed σ
  | _, 0, state, cost => ⟨state, cost⟩
  | start, remaining + 1, state, cost =>
      if stop state then ⟨state, cost + 3⟩
      else
        let child := visit state start
        foldDiagDomainCosted.go stop visit (start + 1) remaining child.value
          (cost + child.cost + 3)

private def foldDiagDomainCosted
    (start count : Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) : Complexity.Costed σ :=
  foldDiagDomainCosted.go stop visit start count state 0

/-- A stopped state remains unchanged throughout a list fold. This gives a
specification for early return without assuming anything about visitor values. -/
private theorem foldDiagDomainCosted_go_value
    (stop : σ → Bool) (visit : σ → Nat → Complexity.Costed σ)
    (start count : Nat) (state : σ) (cost : Nat) :
    (foldDiagDomainCosted.go stop visit start count state cost).value =
      (List.range' start count).foldl
        (fun state i => if stop state then state else (visit state i).value) state := by
  have stopped (xs : List Nat) (state : σ) (h : stop state = true) :
      xs.foldl (fun state i => if stop state then state else (visit state i).value) state =
        state := by
    induction xs with
    | nil => rfl
    | cons i xs ih => simpa [h] using ih
  induction count generalizing start state cost with
  | zero => simp [foldDiagDomainCosted.go]
  | succ count ih =>
      cases hs : stop state <;>
        simp [foldDiagDomainCosted.go, List.range'_succ, hs, stopped, ih]

private theorem foldDiagDomainCosted_value
    (start count : Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) :
    (foldDiagDomainCosted start count state stop visit).value =
      (List.range' start count).foldl
        (fun state i => if stop state then state else (visit state i).value) state :=
  foldDiagDomainCosted_go_value stop visit start count state 0

/-- List specification for the indexed assignment traversal. Its charges match
the array implementation, including the variable read and next-index step.
Production starts at `foldDiagEnvsUntilCosted` and does not build this list. -/
private def foldDiagVarsCosted
    (worldCount thingCount : Nat) (vars : List DiagVar)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ) :
    Complexity.Costed σ :=
  if stop state then
    -- The size comparison and the branch on its result.
    ⟨state, 2⟩
  else
    match vars with
    | [] =>
        -- Stop and array-bound comparisons, with a branch for each.
        Complexity.Costed.charge 4 (visit state env)
    | List.cons var rest =>
        let bound :=
          match var.kind with
          | .thing => thingCount
          | .world => worldCount
        Complexity.Costed.charge 6 <|
          foldDiagDomainCosted 0 bound state stop fun state i =>
            Complexity.Costed.charge 2 <| foldDiagVarsCosted worldCount thingCount rest
              (env.push (var.name, i)) state stop visit

/-- Enumerate assignments without copying the variable array or its prefix.
A stopped state returns before the first read. Otherwise a variable costs
six operations: stop and index comparisons, their branches, an array read,
and kind selection. Each child adds an environment push and a next-index
increment. Exhausting the variables costs four operations before the visit. -/
private def foldDiagEnvsUntilCosted
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ)
    (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ) :
    Complexity.Costed σ :=
  if stop state then ⟨state, 2⟩
  else if h : index < vars.size then
    let var := vars[index]
    let bound := match var.kind with
      | .thing => thingCount
      | .world => worldCount
    Complexity.Costed.charge 6 <|
      foldDiagDomainCosted 0 bound state stop fun state i =>
        Complexity.Costed.charge 2 <|
          foldDiagEnvsUntilCosted worldCount thingCount vars (index + 1)
            (env.push (var.name, i)) state stop visit
  else Complexity.Costed.charge 4 (visit state env)
termination_by vars.size - index

/-- The array implementation preserves the complete counted list recurrence.
In particular, deleting the skipped prefix changes neither witness order nor
the environment passed to a visitor. Lists occur only in this specification. -/
private theorem foldDiagEnvsUntilCosted_eq_list
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ) :
    foldDiagEnvsUntilCosted worldCount thingCount vars index env state stop visit =
      foldDiagVarsCosted worldCount thingCount (vars.toList.drop index) env state stop visit := by
  induction hremaining : vars.size - index generalizing index env state with
  | zero =>
      have hindex : ¬ index < vars.size := by omega
      have hdrop : vars.toList.drop index = [] := by
        apply List.drop_eq_nil_of_le
        simpa using (show vars.size ≤ index by omega)
      rw [foldDiagEnvsUntilCosted, hdrop, foldDiagVarsCosted]
      simp only [dite_eq_right hindex]
  | succ remaining ih =>
      have hindex : index < vars.size := by omega
      have hdrop : vars.toList.drop index = vars[index] :: vars.toList.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hindex)]
        exact congrArg (fun var => var :: vars.toList.drop (index + 1))
          (Array.getElem_toList _)
      rw [foldDiagEnvsUntilCosted, hdrop, foldDiagVarsCosted]
      simp only [dite_eq_left hindex]
      split
      · rfl
      · congr 2
        funext state i
        rw [ih (index + 1) (env.push (vars[index].name, i)) state (by omega)]

private theorem foldDiagDomainCosted_go_cost_le
    (start count : Nat) (state : σ) (cost : Nat) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) (perItem : Nat)
    (hVisit : ∀ state i, start ≤ i → i < start + count →
      (visit state i).cost ≤ perItem) :
    (foldDiagDomainCosted.go stop visit start count state cost).cost ≤
      cost + count * (perItem + 3) := by
  induction count generalizing start state cost with
  | zero => simp [foldDiagDomainCosted.go]
  | succ count ih =>
      rw [foldDiagDomainCosted.go]
      split
      · simp only [Nat.succ_mul]
        omega
      · have hhead := hVisit state start (by omega) (by omega)
        have htail := ih (start + 1) (visit state start).value
          (cost + (visit state start).cost + 3) (by
            intro state' i hlo hhi
            exact hVisit state' i (by omega) (by omega))
        simp only [Nat.succ_mul]
        omega

private theorem foldDiagDomainCosted_cost_le
    (start count : Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) (perItem : Nat)
    (hVisit : ∀ state i, start ≤ i → i < start + count →
      (visit state i).cost ≤ perItem) :
    (foldDiagDomainCosted start count state stop visit).cost ≤
      count * (perItem + 3) := by
  simpa [foldDiagDomainCosted] using
    foldDiagDomainCosted_go_cost_le start count state 0 stop visit perItem hVisit

/-- An optional-result visitor keeps its first successful result, including
any evidence computed during that visit. Later coordinates are not evaluated.
The list specifies ordering without allocating a list during execution. -/
private theorem foldDiagDomainCosted_firstSome_value
    (count : Nat) (visit : Nat → Complexity.Costed (Option α)) (spec : Nat → Option α)
    (agreement : ∀ i, i < count → (visit i).value = spec i) :
    (foldDiagDomainCosted 0 count none Option.isSome (fun _ i => visit i)).value =
      (List.range count).findSome? spec := by
  have hfold (xs : List Nat) (state : Option α)
      (bounded : ∀ i ∈ xs, i < count) :
      xs.foldl (fun state i => if state.isSome then state else (visit i).value) state =
        state.orElse (fun _ => xs.findSome? spec) := by
    induction xs generalizing state with
    | nil => cases state <;> rfl
    | cons i xs ih =>
        have hi := agreement i (bounded i (by simp))
        have hxs : ∀ j ∈ xs, j < count := by
          intro j hj
          exact bounded j (by simp [hj])
        cases state with
        | some a => simpa using ih (some a) hxs
        | none =>
            cases hs : spec i <;> simp [hi, hs, ih _ hxs]
  rw [foldDiagDomainCosted_value, ← List.range_eq_range']
  exact hfold _ none (by intro i hi; exact List.mem_range.mp hi)


/-- Return the first successful coordinate. The shared numeric loop retains
the witness and stops before another predicate call. Each evaluated coordinate
adds one result branch and three loop operations to the predicate cost. If
coordinates remain after a match, the next stop check costs three operations. -/
private def findDiagDomainCosted (count : Nat)
    (predicate : Nat → Complexity.Costed Bool) : Complexity.Costed (Option Nat) :=
  foldDiagDomainCosted 0 count none Option.isSome fun _ i => do
    let found ← predicate i
    Complexity.Costed.tick (if found then some i else none) 1

private theorem findDiagDomainCosted_cost_le (count : Nat)
    (predicate : Nat → Complexity.Costed Bool) (perItem : Nat)
    (bounded : ∀ i, i < count → (predicate i).cost ≤ perItem) :
    (findDiagDomainCosted count predicate).cost ≤ count * (perItem + 4) := by
  unfold findDiagDomainCosted
  have h := foldDiagDomainCosted_cost_le 0 count (none : Option Nat) Option.isSome
    (fun _ i => predicate i >>= fun found =>
      Complexity.Costed.tick (if found then some i else none) 1)
    (perItem + 1) (by
      intro state i hlo hhi
      have hi := bounded i (by omega)
      simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
      omega)
  simpa [Nat.add_assoc] using h

/-- The list fixes first-witness order only in the specification. No list is
allocated by the executable search. Predicate correspondence is needed only
on the coordinates that the loop can visit. -/
private theorem findDiagDomainCosted_value (count : Nat)
    (predicate : Nat → Complexity.Costed Bool) (spec : Nat → Bool)
    (agreement : ∀ i, i < count → (predicate i).value = spec i) :
    (findDiagDomainCosted count predicate).value = (List.range count).find? spec := by
  have h := foldDiagDomainCosted_firstSome_value count
    (fun i => predicate i >>= fun found =>
      Complexity.Costed.tick (if found then some i else none) 1)
    (fun i => Option.guard spec i) (by
      intro i hi
      simp only [Bind.bind, Complexity.Costed.bind_value,
        Complexity.Costed.tick_value, agreement i hi]
      rfl)
  simpa only [findDiagDomainCosted, List.findSome?_guard] using h

private def DiagVar.domainSize (worldCount thingCount : Nat) (var : DiagVar) : Nat :=
  match var.kind with
  | .thing => thingCount
  | .world => worldCount

/-- A domain collector appends at most `maxAppend` items per visit. Early
stopping can only reduce the number of visits and thus the output size. -/
private theorem foldDiagDomainCosted_array_size_le
    (start count : Nat) (out : Array α) (stop : Array α → Bool)
    (visit : Array α → Nat → Complexity.Costed (Array α))
    (maxAppend : Nat)
    (hVisit : ∀ out i, (visit out i).value.size ≤ out.size + maxAppend) :
    (foldDiagDomainCosted start count out stop visit).value.size ≤ out.size + count * maxAppend := by
  have go (start count : Nat) (out : Array α) (cost : Nat) :
      (foldDiagDomainCosted.go stop visit start count out cost).value.size ≤
        out.size + count * maxAppend := by
    induction count generalizing start out cost with
    | zero => simp [foldDiagDomainCosted.go]
    | succ count ih =>
        rw [foldDiagDomainCosted.go]
        split
        · simp
        · have htail := ih (start + 1) (visit out start).value
            (cost + (visit out start).cost + 3)
          have hhead := hVisit out start
          dsimp only
          rw [Nat.succ_mul]
          omega
  exact go start count out 0

/-- A state invariant survives a numeric traversal when every visited step
preserves it. The visitor obligation applies only before the stop condition
holds, so a budget invariant can use the available space at that step. -/
private theorem foldDiagDomainCosted_preserves
    (start count : Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) (invariant : σ → Prop)
    (initial : invariant state)
    (step : ∀ state i, invariant state → stop state = false → invariant (visit state i).value) :
    invariant (foldDiagDomainCosted start count state stop visit).value := by
  have go (start count : Nat) (state : σ) (cost : Nat) (holds : invariant state) :
      invariant (foldDiagDomainCosted.go stop visit start count state cost).value := by
    induction count generalizing start state cost with
    | zero => exact holds
    | succ count ih =>
        cases hs : stop state <;> simp only [foldDiagDomainCosted.go, hs,
          Bool.false_eq_true, ↓reduceIte]
        · exact ih (start + 1) (visit state start).value
            (cost + (visit state start).cost + 3) (step state start holds hs)
        · exact holds
  exact go start count state 0 initial

/-- Traverse an array until the stop predicate holds. Each visited entry pays
three loop/control operations and three for the checked array read. The guard
keeps the visitor total even outside the loop's proved index range. -/
private def foldDiagArrayCosted (items : Array α) (state : σ) (stop : σ → Bool)
    (visit : σ → α → Complexity.Costed σ) : Complexity.Costed σ :=
  foldDiagDomainCosted 0 items.size state stop fun state i =>
    Complexity.Costed.charge 2 <| if h : i < items.size then do
      let item ← Complexity.Costed.tick items[i] 1
      visit state item
    else .pure state

private theorem foldDiagArrayCosted_value (items : Array α) (state : σ) (stop : σ → Bool)
    (visit : σ → α → Complexity.Costed σ) :
    (foldDiagArrayCosted items state stop visit).value =
      items.toList.foldl (fun state item => if stop state then state else (visit state item).value) state := by
  let step (state : σ) (item : Option α) :=
    match item with
    | none => state
    | some item => if stop state then state else (visit state item).value
  have indices : (List.range' 0 items.size).map (fun i => items[i]?) = items.toList.map some := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp_all
  have read (state : σ) (i : Nat) :
      (if stop state then state else
        (Complexity.Costed.charge 2 <| if h : i < items.size then do
          let item ← Complexity.Costed.tick items[i] 1
          visit state item
        else Complexity.Costed.pure state).value) = step state items[i]? := by
    by_cases h : i < items.size <;> cases hs : stop state <;>
      simp [step, h, hs, Bind.bind, Complexity.Costed.bind_value]
  simp only [foldDiagArrayCosted, foldDiagDomainCosted_value, read]
  change (List.range' 0 items.size).foldl (fun s i => step s items[i]?) state = _
  rw [← List.foldl_map, indices, List.foldl_map]

private theorem foldDiagArrayCosted_cost_le (items : Array α) (state : σ) (stop : σ → Bool)
    (visit : σ → α → Complexity.Costed σ) (perItem : Nat)
    (hVisit : ∀ state item, item ∈ items → (visit state item).cost ≤ perItem) :
    (foldDiagArrayCosted items state stop visit).cost ≤ items.size * (perItem + 6) := by
  have bound := foldDiagDomainCosted_cost_le 0 items.size state stop
    (fun state i => Complexity.Costed.charge 2 <| if h : i < items.size then do
      let item ← Complexity.Costed.tick items[i] 1
      visit state item
    else .pure state) (perItem + 3) (by
      intro state i hlo hhi
      have hi : i < items.size := by omega
      have h := hVisit state items[i] (by simp)
      simp [hi, Bind.bind, Complexity.Costed.bind_cost]
      omega)
  simpa [foldDiagArrayCosted, Nat.add_assoc] using bound

private theorem foldDiagArrayCosted_preserves (items : Array α) (state : σ) (stop : σ → Bool)
    (visit : σ → α → Complexity.Costed σ) (invariant : σ → Prop)
    (initial : invariant state)
    (step : ∀ state item, invariant state → stop state = false → invariant (visit state item).value) :
    invariant (foldDiagArrayCosted items state stop visit).value := by
  unfold foldDiagArrayCosted
  apply foldDiagDomainCosted_preserves _ _ _ _ _ invariant initial
  intro state i holds stopped
  split <;> simp only [Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.pure_value]
  · exact step state _ holds stopped
  · exact holds

/-- Cost recurrence for the executable environment traversal. It preserves the
individual domain size of every quantified variable. A leaf adds four control
operations to the visit. A variable adds six setup operations, then the child
cost plus five for domain control, the environment push, and index increment. -/
private def diagEnvFoldCostBound
    (worldCount thingCount visitBound : Nat) : List DiagVar → Nat
  | [] => visitBound + 4
  | List.cons var rest =>
      6 + var.domainSize worldCount thingCount *
        (diagEnvFoldCostBound worldCount thingCount visitBound rest + 5)

private theorem foldDiagVarsCosted_cost_le
    (worldCount thingCount : Nat) (vars : List DiagVar)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ)
    (visitBound : Nat)
    (hVisit : ∀ state env, (visit state env).cost ≤ visitBound) :
    (foldDiagVarsCosted worldCount thingCount vars env state stop visit).cost ≤
      diagEnvFoldCostBound worldCount thingCount visitBound vars := by
  induction vars generalizing env state with
  | nil =>
      rw [foldDiagVarsCosted]
      split
      · simp [diagEnvFoldCostBound]
      · simp only [Complexity.Costed.charge_cost, diagEnvFoldCostBound]
        have h := hVisit state env
        omega
  | cons var rest ih =>
      rw [foldDiagVarsCosted]
      split
      · simp only [diagEnvFoldCostBound]
        omega
      · simp only [Complexity.Costed.charge_cost, diagEnvFoldCostBound]
        have hdomain := foldDiagDomainCosted_cost_le
          0 (var.domainSize worldCount thingCount) state stop
          (fun state i => Complexity.Costed.charge 2 <|
            foldDiagVarsCosted worldCount thingCount rest
              (env.push (var.name, i)) state stop visit)
          (diagEnvFoldCostBound worldCount thingCount visitBound rest + 2) (by
            intro state' i hlo hhi
            simpa [Nat.add_comm] using Nat.add_le_add_left (ih (env.push (var.name, i)) state') 2)
        simpa [DiagVar.domainSize, Nat.add_assoc] using Nat.add_le_add_left hdomain 6

private theorem foldDiagEnvsUntilCosted_cost_le
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ)
    (visitBound : Nat)
    (hVisit : ∀ state env, (visit state env).cost ≤ visitBound) :
    (foldDiagEnvsUntilCosted worldCount thingCount vars index env state stop visit).cost ≤
      diagEnvFoldCostBound worldCount thingCount visitBound
        (vars.toList.drop index) := by
  rw [foldDiagEnvsUntilCosted_eq_list]
  exact foldDiagVarsCosted_cost_le worldCount thingCount
    (vars.toList.drop index) env state stop visit visitBound hVisit

/-- Environment-sensitive counterpart of `diagEnvFoldCostBound`. Each quantified
variable extends the environment by one binding, so the visitor bound uses the
environment size at its concrete depth in the search. -/
private def diagEnvDependentFoldCostBound
    (worldCount thingCount : Nat) (visitBound : Nat → Nat) :
    Nat → List DiagVar → Nat
  | envSize, [] => visitBound envSize + 4
  | envSize, List.cons var rest =>
      6 + var.domainSize worldCount thingCount *
        (diagEnvDependentFoldCostBound worldCount thingCount visitBound (envSize + 1) rest + 5)

private theorem foldDiagVarsCosted_dependent_cost_le
    (worldCount thingCount : Nat) (vars : List DiagVar)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ)
    (visitBound : Nat → Nat)
    (hVisit : ∀ state env, (visit state env).cost ≤ visitBound env.size) :
    (foldDiagVarsCosted worldCount thingCount vars env state stop visit).cost ≤
      diagEnvDependentFoldCostBound worldCount thingCount visitBound env.size vars := by
  induction vars generalizing env state with
  | nil =>
      rw [foldDiagVarsCosted]
      split
      · simp [diagEnvDependentFoldCostBound]
      · simp only [Complexity.Costed.charge_cost, diagEnvDependentFoldCostBound]
        have h := hVisit state env
        omega
  | cons var rest ih =>
      rw [foldDiagVarsCosted]
      split
      · simp only [diagEnvDependentFoldCostBound]
        omega
      · simp only [Complexity.Costed.charge_cost, diagEnvDependentFoldCostBound]
        have hdomain := foldDiagDomainCosted_cost_le
          0 (var.domainSize worldCount thingCount) state stop
          (fun state i => Complexity.Costed.charge 2 <|
            foldDiagVarsCosted worldCount thingCount rest
              (env.push (var.name, i)) state stop visit)
          (diagEnvDependentFoldCostBound worldCount thingCount visitBound (env.size + 1) rest + 2)
          (by
            intro state' i hlo hhi
            simpa [Nat.add_comm] using Nat.add_le_add_left (ih (env.push (var.name, i)) state') 2)
        simpa [DiagVar.domainSize, Nat.add_assoc] using Nat.add_le_add_left hdomain 6

private theorem foldDiagEnvsUntilCosted_dependent_cost_le
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ)
    (visitBound : Nat → Nat)
    (hVisit : ∀ state env, (visit state env).cost ≤ visitBound env.size) :
    (foldDiagEnvsUntilCosted worldCount thingCount vars index env state stop visit).cost ≤
      diagEnvDependentFoldCostBound worldCount thingCount visitBound env.size
        (vars.toList.drop index) := by
  rw [foldDiagEnvsUntilCosted_eq_list]
  exact foldDiagVarsCosted_dependent_cost_le worldCount thingCount
    (vars.toList.drop index) env state stop visit visitBound hVisit

private def unaryFieldDslLabel : UnaryField → String
  | .concreteIndividual => "ConcreteIndividual"
  | .abstractIndividual => "AbstractIndividual"
  | .endurant => "Endurant"
  | .perdurant => "Perdurant"
  | .endurantType => "EndurantType"
  | .perdurantType => "PerdurantType"
  | .rigid => "Rigid"
  | .antiRigid => "AntiRigid"
  | .semiRigid => "SemiRigid"
  | .kind => "Kind"
  | .sortal => "Sortal"
  | .nonSortal => "NonSortal"
  | .subKind => "SubKind"
  | .phase => "Phase"
  | .role => "Role"
  | .semiRigidSortal => "SemiRigidSortal"
  | .category => "Category"
  | .mixin => "Mixin"
  | .phaseMixin => "PhaseMixin"
  | .roleMixin => "RoleMixin"
  | .substantial => "Substantial"
  | .moment => "Moment"
  | .object => "Object"
  | .collective => "Collective"
  | .quantity => "Quantity"
  | .relator => "Relator"
  | .intrinsicMoment => "IntrinsicMoment"
  | .mode => "Mode"
  | .qualityKind => "QualityKind"
  | .substantialType => "SubstantialType"
  | .momentType => "MomentType"
  | .objectType => "ObjectType"
  | .collectiveType => "CollectiveType"
  | .quantityType => "QuantityType"
  | .relatorType => "RelatorType"
  | .modeType => "ModeType"
  | .qualityType => "QualityType"
  | .objectKind => "ObjectKind"
  | .collectiveKind => "CollectiveKind"
  | .quantityKind => "QuantityKind"
  | .relatorKind => "RelatorKind"
  | .modeKind => "ModeKind"
  | .ex => "Ex"
  | .quale => "Quale"
  | .set_ => "Set"
  | .qualityDomain => "QualityDomain"
  | .qualityDimension => "QualityDimension"
  | .intrinsicMomentType => "IntrinsicMomentType"
  | .distanceZero => "DistanceZero"

private def binaryFieldDslLabel : BinaryField → String
  | .inst => "::"
  | .sub => "⊑"
  | .part => "Part"
  | .overlap => "Overlap"
  | .properPart => "ProperPart"
  | .functionsAs => "FunctionsAs"
  | .constitutedBy => "ConstitutedBy"
  | .inheresIn => "InheresIn"
  | .foundedBy => "FoundedBy"
  | .quaIndividualOf => "QuaIndividualOf"
  | .mediates => "Mediates"
  | .characterization => "Characterization"
  | .associatedWith => "AssociatedWith"
  | .hasValue => "HasValue"
  | .memberOf => "MemberOf"
  | .manifests => "Manifests"
  | .lifeOf => "LifeOf"
  | .meet => "Meet"
  | .distanceGreaterEq => "DistanceGreaterEq"

private def ternaryFieldDslLabel : TernaryField → String
  | .distance => "Distance"
  | .distanceSum => "DistanceSum"

/-- Resolve a variable with last-binding lookup, then render its source name.
Missing bindings select zero, and out-of-range names retain the #n fallback. -/
private def renderDiagVariableCosted (names : Array Name) (env : Array (String × Nat))
    (name : String) : Complexity.Costed String := do
  let idx ← lookupVarCosted env name
  indexedNameCosted names idx

private theorem renderDiagVariableCosted_value (names : Array Name) (env : Array (String × Nat))
    (name : String) :
    (renderDiagVariableCosted names env name).value = indexedName names (lookupVar env name) := by
  simp only [renderDiagVariableCosted, Bind.bind, Complexity.Costed.bind_value,
    indexedNameCosted_value, lookupVar]

private theorem renderDiagVariableCosted_cost (names : Array Name) (env : Array (String × Nat))
    (name : String) :
    (renderDiagVariableCosted names env name).cost = 4 * env.size + 5 := by
  simp only [renderDiagVariableCosted, Bind.bind, Complexity.Costed.bind_cost,
    lookupVarCosted_cost, indexedNameCosted_cost]

/-- The string specification fixes labels, punctuation, and infix notation.
It is used by the value proofs, not by production rendering. -/
private def renderDiagAtomSpec
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) : DiagAtom → String
  | .typeSem thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] Type({indexedName thingNames (lookupVar env thing)})"
  | .individualSem thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] Individual({indexedName thingNames (lookupVar env thing)})"
  | .unary field thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {unaryFieldDslLabel field}({indexedName thingNames (lookupVar env thing)})"
  | .derivedUnary field thing world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {field}({indexedName thingNames (lookupVar env thing)})"
  | .binary .inst left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {indexedName thingNames (lookupVar env left)} :: {indexedName thingNames (lookupVar env right)}"
  | .binary .sub left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {indexedName thingNames (lookupVar env left)} ⊑ {indexedName thingNames (lookupVar env right)}"
  | .binary field left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {binaryFieldDslLabel field}({indexedName thingNames (lookupVar env left)}, {indexedName thingNames (lookupVar env right)})"
  | .ternary field first second third world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {ternaryFieldDslLabel field}({indexedName thingNames (lookupVar env first)}, {indexedName thingNames (lookupVar env second)}, {indexedName thingNames (lookupVar env third)})"
  | .derivedBinary field left right world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {field}({indexedName thingNames (lookupVar env left)}, {indexedName thingNames (lookupVar env right)})"
  | .quaternary field first second third fourth world =>
      s!"[{indexedName worldNames (lookupVar env world)}] {field}({indexedName thingNames (lookupVar env first)}, {indexedName thingNames (lookupVar env second)}, {indexedName thingNames (lookupVar env third)}, {indexedName thingNames (lookupVar env fourth)})"

/-- Each recursive call uses a proper subformula. The explicit node-count
measure proves termination and keeps the value equations compact enough for
kernel checking under the default heartbeat limit. -/
private def renderDiagFormulaSpec
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) : DiagFormula → String
  | .atom atom => renderDiagAtomSpec worldNames thingNames env atom
  | .eqThing left right =>
      s!"{indexedName thingNames (lookupVar env left)} = {indexedName thingNames (lookupVar env right)}"
  | .eqWorld left right =>
      s!"{indexedName worldNames (lookupVar env left)} = {indexedName worldNames (lookupVar env right)}"
  | .not p => s!"not ({renderDiagFormulaSpec worldNames thingNames env p})"
  | .and p q => s!"({renderDiagFormulaSpec worldNames thingNames env p}) and ({renderDiagFormulaSpec worldNames thingNames env q})"
  | .or p q => s!"({renderDiagFormulaSpec worldNames thingNames env p}) or ({renderDiagFormulaSpec worldNames thingNames env q})"
  | .imp p q => s!"({renderDiagFormulaSpec worldNames thingNames env p}) implies ({renderDiagFormulaSpec worldNames thingNames env q})"
  | .iff p q => s!"({renderDiagFormulaSpec worldNames thingNames env p}) iff ({renderDiagFormulaSpec worldNames thingNames env q})"
  | .forallThing name body => s!"for every thing {name}, {renderDiagFormulaSpec worldNames thingNames env body}"
  | .forallWorld name body => s!"for every world {name}, {renderDiagFormulaSpec worldNames thingNames env body}"
  | .existsThing name body => s!"there exists thing {name}, {renderDiagFormulaSpec worldNames thingNames env body}"
  | .existsWorld name body => s!"there exists world {name}, {renderDiagFormulaSpec worldNames thingNames env body}"
  | .box currentWorld witnessWorld body =>
      s!"from world {indexedName worldNames (lookupVar env currentWorld)}, in every accessible world {witnessWorld}, {renderDiagFormulaSpec worldNames thingNames env body}"
  | .dia currentWorld witnessWorld body =>
      s!"from world {indexedName worldNames (lookupVar env currentWorld)}, in some accessible world {witnessWorld}, {renderDiagFormulaSpec worldNames thingNames env body}"
termination_by formula => formula.nodeCount
decreasing_by all_goals simp_all [DiagFormula.nodeCount] <;> omega

/-- Count atom selection and every lookup used in its text. Binary atoms also
select a field constructor to distinguish infix notation. Each fixed format
charges its literal concatenations. Character traversal is outside this model.
The value/cost separation follows Niu et al. (POPL 2022, doi:10.1145/3498670). -/
private def renderDiagAtomCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) :
    DiagAtom → Complexity.Costed String
  | .typeSem thing world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] Type(")
      let text := text.appendString (renderDiagVariableCosted thingNames env thing)
      text.appendString (Complexity.Costed.pure ")")
  | .individualSem thing world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] Individual(")
      let text := text.appendString (renderDiagVariableCosted thingNames env thing)
      text.appendString (Complexity.Costed.pure ")")
  | .unary field thing world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (Complexity.Costed.tick (unaryFieldDslLabel field) 1)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString (renderDiagVariableCosted thingNames env thing)
      text.appendString (Complexity.Costed.pure ")")
  | .derivedUnary field thing world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (Complexity.Costed.pure field)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString (renderDiagVariableCosted thingNames env thing)
      text.appendString (Complexity.Costed.pure ")")
  | .binary .inst left right world => Complexity.Costed.charge 2 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (renderDiagVariableCosted thingNames env left)
      let text := text.appendString (Complexity.Costed.pure " :: ")
      text.appendString (renderDiagVariableCosted thingNames env right)
  | .binary .sub left right world => Complexity.Costed.charge 2 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (renderDiagVariableCosted thingNames env left)
      let text := text.appendString (Complexity.Costed.pure " ⊑ ")
      text.appendString (renderDiagVariableCosted thingNames env right)
  | .binary field left right world => Complexity.Costed.charge 2 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (Complexity.Costed.tick (binaryFieldDslLabel field) 1)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString (renderDiagVariableCosted thingNames env left)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env right)
      text.appendString (Complexity.Costed.pure ")")
  | .ternary field first second third world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (Complexity.Costed.tick (ternaryFieldDslLabel field) 1)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString (renderDiagVariableCosted thingNames env first)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env second)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env third)
      text.appendString (Complexity.Costed.pure ")")
  | .derivedBinary field left right world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (Complexity.Costed.pure field)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString (renderDiagVariableCosted thingNames env left)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env right)
      text.appendString (Complexity.Costed.pure ")")
  | .quaternary field first second third fourth world => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "[") (renderDiagVariableCosted worldNames env world)
      let text := text.appendString (Complexity.Costed.pure "] ")
      let text := text.appendString (Complexity.Costed.pure field)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString (renderDiagVariableCosted thingNames env first)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env second)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env third)
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString (renderDiagVariableCosted thingNames env fourth)
      text.appendString (Complexity.Costed.pure ")")

private theorem renderDiagAtomCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (atom : DiagAtom) :
    (renderDiagAtomCosted worldNames thingNames env atom).value =
      renderDiagAtomSpec worldNames thingNames env atom := by
  cases atom with
  | binary field left right world =>
      cases field <;>
        simp only [renderDiagAtomCosted, renderDiagAtomSpec, Complexity.Costed.charge_value,
          Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
          Complexity.Costed.tick_value,
          renderDiagVariableCosted_value] <;> rfl
  | _ =>
      simp only [renderDiagAtomCosted, renderDiagAtomSpec, Complexity.Costed.charge_value,
        Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
          Complexity.Costed.tick_value,
        renderDiagVariableCosted_value]
      rfl

private theorem renderDiagAtomCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (atom : DiagAtom) :
    (renderDiagAtomCosted worldNames thingNames env atom).cost ≤ 20 * env.size + 38 := by
  cases atom with
  | binary field left right world =>
      cases field <;>
        simp only [renderDiagAtomCosted, Complexity.Costed.charge_cost,
          Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, renderDiagVariableCosted_cost] <;>
        omega
  | _ =>
      simp only [renderDiagAtomCosted, Complexity.Costed.charge_cost,
        Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, renderDiagVariableCosted_cost]
      omega

/-- Render the formula tree without enumerating its quantifier domains.
Each node charges its constructor selection and text concatenations. Bound
variable names remain literal text. The same decreasing node count as in the
specification keeps both definitions total without an alternate native path. -/
private def renderDiagFormulaCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) :
    DiagFormula → Complexity.Costed String
  | .atom atom => Complexity.Costed.charge 1 (renderDiagAtomCosted worldNames thingNames env atom)
  | .eqThing left right => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (renderDiagVariableCosted thingNames env left) (Complexity.Costed.pure " = ")
      text.appendString (renderDiagVariableCosted thingNames env right)
  | .eqWorld left right => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (renderDiagVariableCosted worldNames env left) (Complexity.Costed.pure " = ")
      text.appendString (renderDiagVariableCosted worldNames env right)
  | .not p => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "not (") (renderDiagFormulaCosted worldNames thingNames env p)
      text.appendString (Complexity.Costed.pure ")")
  | .and p q => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "(") (renderDiagFormulaCosted worldNames thingNames env p)
      let text := text.appendString (Complexity.Costed.pure ") and (")
      let text := text.appendString (renderDiagFormulaCosted worldNames thingNames env q)
      text.appendString (Complexity.Costed.pure ")")
  | .or p q => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "(") (renderDiagFormulaCosted worldNames thingNames env p)
      let text := text.appendString (Complexity.Costed.pure ") or (")
      let text := text.appendString (renderDiagFormulaCosted worldNames thingNames env q)
      text.appendString (Complexity.Costed.pure ")")
  | .imp p q => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "(") (renderDiagFormulaCosted worldNames thingNames env p)
      let text := text.appendString (Complexity.Costed.pure ") implies (")
      let text := text.appendString (renderDiagFormulaCosted worldNames thingNames env q)
      text.appendString (Complexity.Costed.pure ")")
  | .iff p q => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "(") (renderDiagFormulaCosted worldNames thingNames env p)
      let text := text.appendString (Complexity.Costed.pure ") iff (")
      let text := text.appendString (renderDiagFormulaCosted worldNames thingNames env q)
      text.appendString (Complexity.Costed.pure ")")
  | .forallThing name body => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "for every thing ") (Complexity.Costed.pure name)
      let text := text.appendString (Complexity.Costed.pure ", ")
      text.appendString (renderDiagFormulaCosted worldNames thingNames env body)
  | .forallWorld name body => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "for every world ") (Complexity.Costed.pure name)
      let text := text.appendString (Complexity.Costed.pure ", ")
      text.appendString (renderDiagFormulaCosted worldNames thingNames env body)
  | .existsThing name body => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "there exists thing ") (Complexity.Costed.pure name)
      let text := text.appendString (Complexity.Costed.pure ", ")
      text.appendString (renderDiagFormulaCosted worldNames thingNames env body)
  | .existsWorld name body => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "there exists world ") (Complexity.Costed.pure name)
      let text := text.appendString (Complexity.Costed.pure ", ")
      text.appendString (renderDiagFormulaCosted worldNames thingNames env body)
  | .box currentWorld witnessWorld body => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "from world ") (renderDiagVariableCosted worldNames env currentWorld)
      let text := text.appendString (Complexity.Costed.pure ", in every accessible world ")
      let text := text.appendString (Complexity.Costed.pure witnessWorld)
      let text := text.appendString (Complexity.Costed.pure ", ")
      text.appendString (renderDiagFormulaCosted worldNames thingNames env body)
  | .dia currentWorld witnessWorld body => Complexity.Costed.charge 1 <|
      let text := Complexity.Costed.appendString (Complexity.Costed.pure "from world ") (renderDiagVariableCosted worldNames env currentWorld)
      let text := text.appendString (Complexity.Costed.pure ", in some accessible world ")
      let text := text.appendString (Complexity.Costed.pure witnessWorld)
      let text := text.appendString (Complexity.Costed.pure ", ")
      text.appendString (renderDiagFormulaCosted worldNames thingNames env body)
termination_by formula => formula.nodeCount
decreasing_by all_goals simp_all [DiagFormula.nodeCount] <;> omega

private theorem renderDiagFormulaCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagFormulaCosted worldNames thingNames env formula).value =
      renderDiagFormulaSpec worldNames thingNames env formula := by
  induction formula <;> rw [renderDiagFormulaCosted, renderDiagFormulaSpec]
  all_goals
    simp only [Complexity.Costed.charge_value, Complexity.Costed.appendString_value,
      Complexity.Costed.pure_value, renderDiagAtomCosted_value, renderDiagVariableCosted_value, *] <;> rfl

/-- For F formula nodes and E environment bindings, rendering costs at most
F(20E+39) primitive calls. The atom bound includes up to five name resolutions.
This is not a bound on characters copied or on native stack and allocator work. -/
private theorem renderDiagFormulaCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagFormulaCosted worldNames thingNames env formula).cost ≤
      formula.nodeCount * (20 * env.size + 39) := by
  induction formula with
  | atom atom =>
      have h := renderDiagAtomCosted_cost_le worldNames thingNames env atom
      simp only [renderDiagFormulaCosted, Complexity.Costed.charge_cost, DiagFormula.nodeCount,
        Nat.one_mul]
      omega
  | _ =>
      simp_all only [renderDiagFormulaCosted, Complexity.Costed.charge_cost,
        Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
        renderDiagVariableCosted_cost, DiagFormula.nodeCount, Nat.add_mul, Nat.one_mul]
      omega

private theorem renderDiagFormulaCostBound_mono
    {F F' E E' : Nat} (hF : F ≤ F') (hE : E ≤ E') :
    F * (20 * E + 39) ≤ F' * (20 * E' + 39) :=
  Nat.mul_le_mul hF (Nat.add_le_add_right (Nat.mul_le_mul_left 20 hE) 39)

/-- The connective expanded into separate rows: conjunction (`and`) or
disjunction (`or`). Other formula constructors remain whole row entries. -/
private inductive DiagJunction where
  | conjunction | disjunction

private def flattenDiagJunctionSpec (junction : DiagJunction) : DiagFormula → List DiagFormula
  | .and p q => match junction with
      | .conjunction => flattenDiagJunctionSpec junction p ++ flattenDiagJunctionSpec junction q
      | .disjunction => [.and p q]
  | .or p q => match junction with
      | .disjunction => flattenDiagJunctionSpec junction p ++ flattenDiagJunctionSpec junction q
      | .conjunction => [.or p q]
  | formula => [formula]

/-- Two constructor selections identify the requested connective and the
formula. Leaves add one array write. The accumulator retains left-to-right
order without concatenating intermediate arrays. -/
private def flattenDiagJunctionIntoCosted (junction : DiagJunction)
    (out : Array DiagFormula) (formula : DiagFormula) : Complexity.Costed (Array DiagFormula) :=
  Complexity.Costed.charge 2 <| match junction, formula with
  | .conjunction, .and p q | .disjunction, .or p q => do
      let out ← flattenDiagJunctionIntoCosted junction out p
      flattenDiagJunctionIntoCosted junction out q
  | _, formula => Complexity.Costed.tick (out.push formula) 1
termination_by formula.nodeCount
decreasing_by all_goals (simp_all [DiagFormula.nodeCount]; omega)

private theorem flattenDiagJunctionIntoCosted_value (junction : DiagJunction)
    (out : Array DiagFormula) (formula : DiagFormula) :
    (flattenDiagJunctionIntoCosted junction out formula).value =
      out ++ (flattenDiagJunctionSpec junction formula).toArray := by
  induction formula generalizing out <;> cases junction <;>
    simp_all [flattenDiagJunctionIntoCosted, flattenDiagJunctionSpec, Bind.bind,
      Array.append_assoc]

private theorem flattenDiagJunctionIntoCosted_cost_le (junction : DiagJunction)
    (out : Array DiagFormula) (formula : DiagFormula) :
    (flattenDiagJunctionIntoCosted junction out formula).cost ≤ 3 * formula.nodeCount := by
  induction formula generalizing out <;> cases junction <;>
    simp_all [flattenDiagJunctionIntoCosted, Bind.bind, DiagFormula.nodeCount] <;> grind

private theorem flattenDiagJunctionSpec_metrics (junction : DiagJunction) (formula : DiagFormula) :
    (flattenDiagJunctionSpec junction formula).length ≤ formula.nodeCount ∧
    ((flattenDiagJunctionSpec junction formula).map DiagFormula.nodeCount).sum ≤ formula.nodeCount := by
  induction formula <;> cases junction <;>
    simp_all [flattenDiagJunctionSpec, DiagFormula.nodeCount, List.map_append, List.sum_append] <;> omega

private def flattenDiagJunctionCosted (junction : DiagJunction) (formula : DiagFormula) :
    Complexity.Costed (Array DiagFormula) :=
  Complexity.Costed.charge 1 (flattenDiagJunctionIntoCosted junction #[] formula)

private theorem flattenDiagJunctionCosted_value (junction : DiagJunction) (formula : DiagFormula) :
    (flattenDiagJunctionCosted junction formula).value = (flattenDiagJunctionSpec junction formula).toArray := by
  simp [flattenDiagJunctionCosted, flattenDiagJunctionIntoCosted_value]

private theorem flattenDiagJunctionCosted_cost_le (junction : DiagJunction) (formula : DiagFormula) :
    (flattenDiagJunctionCosted junction formula).cost ≤ 3 * formula.nodeCount + 1 := by
  have h := flattenDiagJunctionIntoCosted_cost_le junction #[] formula
  simpa [flattenDiagJunctionCosted, Nat.add_comm] using Nat.add_le_add_right h 1

private def formulaHasDistinctnessRequirement : DiagFormula → Bool
  | .not (.eqThing _ _) => true
  | .not (.eqWorld _ _) => true
  | _ => false

private def diagnosticConditionLabelSpec (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ => "Need one of"
  | .not _ => "Forbidden condition"
  | .atom _ => "Required but missing"
  | .eqThing _ _ => "Required but missing"
  | .eqWorld _ _ => "Required but missing"
  | .and _ _ =>
      if (flattenDiagJunctionSpec .conjunction formula).any formulaHasDistinctnessRequirement then
        "Missing witness requirements"
      else
        "Required together"
  | .existsThing _ _ => "Missing witness requirements"
  | .existsWorld _ _ => "Missing witness requirements"
  | _ => "Failed condition"

private def renderDiagnosticConditionSpec
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ =>
      String.intercalate "\n" <|
        (flattenDiagJunctionSpec .disjunction formula).map fun option =>
          s!"- {renderDiagFormulaSpec worldNames thingNames env option}"
  | .and _ _ =>
      String.intercalate "\n" <|
        (flattenDiagJunctionSpec .conjunction formula).map fun requirement =>
          s!"- {renderDiagFormulaSpec worldNames thingNames env requirement}"
  | _ => renderDiagFormulaSpec worldNames thingNames env formula

/-- Render each row once and join it directly into the output string. The
cost bound sums row sizes, so a large row does not inflate every other row's
charge. String-character copying remains outside this primitive-call model. -/
private def renderDiagnosticRowsCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (rows : Array DiagFormula) : Complexity.Costed String := do
  let joined ← Complexity.Costed.foldArray rows (none : Option String) fun out formula => do
    let row ← Complexity.Costed.appendString (.pure "- ")
      (renderDiagFormulaCosted worldNames thingNames env formula)
    Complexity.Costed.charge 1 <| match out with
    | none => Complexity.Costed.pure (some row)
    | some text => do
        let text ← Complexity.Costed.appendString (.pure text) (.pure "\n")
        let text ← Complexity.Costed.appendString (.pure text) (.pure row)
        Complexity.Costed.pure (some text)
  Complexity.Costed.tick (joined.getD "") 1

private theorem renderDiagnosticRowsCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (rows : Array DiagFormula) :
    (renderDiagnosticRowsCosted worldNames thingNames env rows).value =
      String.intercalate "\n" (rows.toList.map fun formula =>
        s!"- {renderDiagFormulaSpec worldNames thingNames env formula}") := by
  have fold (xs before : List String) :
      (xs.foldl (fun out row => match out with
        | none => some row
        | some text => some (text ++ "\n" ++ row))
        (if before = [] then none else some (String.intercalate "\n" before))).getD "" =
        String.intercalate "\n" (before ++ xs) := by
    induction xs generalizing before with
    | nil => cases before <;> simp
    | cons row xs ih =>
        rw [List.append_cons, ← ih, List.foldl_cons]
        congr
        cases before with
        | nil => simp
        | cons first rest =>
            simp only [List.cons_ne_nil, ↓reduceIte, List.cons_append, Option.some.injEq]
            rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
              String.intercalate_singleton]
  have h := fold (rows.toList.map fun formula =>
    s!"- {renderDiagFormulaSpec worldNames thingNames env formula}") []
  simp only [List.nil_append, ↓reduceIte, List.foldl_map] at h
  simp only [renderDiagnosticRowsCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArray_value, ← Array.foldl_toList,
    Complexity.Costed.charge_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, renderDiagFormulaCosted_value]
  convert h using 1
  congr 2
  funext out formula
  cases out <;> rfl

private theorem renderDiagnosticRowsCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (rows : Array DiagFormula) :
    (renderDiagnosticRowsCosted worldNames thingNames env rows).cost ≤
      (rows.toList.map DiagFormula.nodeCount).sum * (20 * env.size + 39) + 6 * rows.size + 1 := by
  have h := Complexity.Costed.foldArray_cost_le_sum rows (none : Option String)
    (fun out formula => do
      let row ← Complexity.Costed.appendString (.pure "- ")
        (renderDiagFormulaCosted worldNames thingNames env formula)
      Complexity.Costed.charge 1 <| match out with
      | none => Complexity.Costed.pure (some row)
      | some text => do
          let text ← Complexity.Costed.appendString (.pure text) (.pure "\n")
          let text ← Complexity.Costed.appendString (.pure text) (.pure row)
          Complexity.Costed.pure (some text))
    (fun formula => formula.nodeCount * (20 * env.size + 39) + 4) (by
      intro out formula hformula
      have h := renderDiagFormulaCosted_cost_le worldNames thingNames env formula
      cases out <;> simp [Bind.bind] <;> omega)
  have sum (xs : List DiagFormula) :
      (xs.map (fun formula => formula.nodeCount * (20 * env.size + 39) + 4 + 2)).sum =
      (xs.map DiagFormula.nodeCount).sum * (20 * env.size + 39) + 6 * xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih, Nat.add_mul]
        omega
  rw [sum, Array.length_toList] at h
  simpa only [renderDiagnosticRowsCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost] using Nat.add_le_add_right h 1

private def renderDiagnosticConditionCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (formula : DiagFormula) : Complexity.Costed String :=
  Complexity.Costed.charge 1 <| match formula with
  | .or _ _ => do
      let rows ← flattenDiagJunctionCosted .disjunction formula
      renderDiagnosticRowsCosted worldNames thingNames env rows
  | .and _ _ => do
      let rows ← flattenDiagJunctionCosted .conjunction formula
      renderDiagnosticRowsCosted worldNames thingNames env rows
  | _ => renderDiagFormulaCosted worldNames thingNames env formula

private theorem renderDiagnosticConditionCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagnosticConditionCosted worldNames thingNames env formula).value =
      renderDiagnosticConditionSpec worldNames thingNames env formula := by
  cases formula <;>
    simp [renderDiagnosticConditionCosted, renderDiagnosticConditionSpec, Bind.bind,
      flattenDiagJunctionCosted_value, renderDiagnosticRowsCosted_value, renderDiagFormulaCosted_value]

private theorem renderDiagnosticConditionCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagnosticConditionCosted worldNames thingNames env formula).cost ≤
      formula.nodeCount * (20 * env.size + 48) + 3 := by
  have flat (junction : DiagJunction) :
      (do
        let rows ← flattenDiagJunctionCosted junction formula
        renderDiagnosticRowsCosted worldNames thingNames env rows).cost ≤
        formula.nodeCount * (20 * env.size + 48) + 2 := by
    have hf := flattenDiagJunctionCosted_cost_le junction formula
    have hr := renderDiagnosticRowsCosted_cost_le worldNames thingNames env
      (flattenDiagJunctionCosted junction formula).value
    rw [flattenDiagJunctionCosted_value] at hr
    simp only [List.size_toArray] at hr
    have hm := flattenDiagJunctionSpec_metrics junction formula
    have hs := Nat.mul_le_mul_right (20 * env.size + 39) hm.2
    have hn := Nat.mul_le_mul_left 6 hm.1
    simp only [Bind.bind, Complexity.Costed.bind_cost, flattenDiagJunctionCosted_value]
    have heq : formula.nodeCount * (20 * env.size + 48) =
        formula.nodeCount * (20 * env.size + 39) + 9 * formula.nodeCount := by
      rw [show 20 * env.size + 48 = (20 * env.size + 39) + 9 by omega, Nat.mul_add, Nat.mul_comm _ 9]
    rw [heq]
    omega
  have ha := flat .conjunction
  have ho := flat .disjunction
  have hp := renderDiagFormulaCosted_cost_le worldNames thingNames env formula
  have hw := Nat.mul_le_mul_left formula.nodeCount
    (show 20 * env.size + 39 ≤ 20 * env.size + 48 by omega)
  cases formula <;> simp only [renderDiagnosticConditionCosted, Complexity.Costed.charge_cost] <;> omega

private def formulaHasDistinctnessRequirementCosted (formula : DiagFormula) : Complexity.Costed Bool :=
  Complexity.Costed.charge 1 <| match formula with
  | .not body => Complexity.Costed.tick (match body with
      | .eqThing _ _ | .eqWorld _ _ => true
      | _ => false) 1
  | _ => Complexity.Costed.pure false

private theorem formulaHasDistinctnessRequirementCosted_value (formula : DiagFormula) :
    (formulaHasDistinctnessRequirementCosted formula).value = formulaHasDistinctnessRequirement formula := by
  cases formula <;> simp [formulaHasDistinctnessRequirementCosted, formulaHasDistinctnessRequirement]
  rename_i body
  cases body <;> rfl

private theorem formulaHasDistinctnessRequirementCosted_cost_le (formula : DiagFormula) :
    (formulaHasDistinctnessRequirementCosted formula).cost ≤ 2 := by
  cases formula <;> simp [formulaHasDistinctnessRequirementCosted]

/-- The label search stops at the first negated equality in a conjunction.
Its preceding flattening pass still runs in full and contributes its cost. -/
private def diagnosticConditionLabelCosted (formula : DiagFormula) : Complexity.Costed String :=
  Complexity.Costed.charge 1 <| match formula with
  | .or _ _ => .pure "Need one of"
  | .not _ => .pure "Forbidden condition"
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => .pure "Required but missing"
  | .and _ _ => do
      let rows ← flattenDiagJunctionCosted .conjunction formula
      let distinct ← Complexity.anyArrayCosted rows formulaHasDistinctnessRequirementCosted
      Complexity.Costed.charge 1 <| if distinct then .pure "Missing witness requirements"
        else .pure "Required together"
  | .existsThing _ _ | .existsWorld _ _ => .pure "Missing witness requirements"
  | _ => .pure "Failed condition"

private theorem diagnosticConditionLabelCosted_value (formula : DiagFormula) :
    (diagnosticConditionLabelCosted formula).value = diagnosticConditionLabelSpec formula := by
  cases formula <;>
    simp [diagnosticConditionLabelCosted, diagnosticConditionLabelSpec, Bind.bind,
      flattenDiagJunctionCosted_value, Complexity.anyArrayCosted_eq_list,
      Complexity.anyListCosted_value, formulaHasDistinctnessRequirementCosted_value]
  split <;> simp_all

private theorem diagnosticConditionLabelCosted_cost_le (formula : DiagFormula) :
    (diagnosticConditionLabelCosted formula).cost ≤ 8 * formula.nodeCount + 3 := by
  cases formula with
  | and p q =>
      have hf := flattenDiagJunctionCosted_cost_le .conjunction (.and p q)
      have ha := Complexity.anyArrayCosted_cost_le
        (flattenDiagJunctionCosted .conjunction (.and p q)).value
        formulaHasDistinctnessRequirementCosted 2
        (fun f _ => formulaHasDistinctnessRequirementCosted_cost_le f)
      have hm := (flattenDiagJunctionSpec_metrics .conjunction (.and p q)).1
      rw [flattenDiagJunctionCosted_value] at ha
      simp only [List.size_toArray] at ha
      simp only [diagnosticConditionLabelCosted, Complexity.Costed.charge_cost,
        Bind.bind, Complexity.Costed.bind_cost, flattenDiagJunctionCosted_value]
      split <;> simp only [Complexity.Costed.pure_cost] <;> omega
  | _ => simp [diagnosticConditionLabelCosted]

private def renderDiagnosticConditionLineSpec
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) : String :=
  let rendered := renderDiagnosticConditionSpec worldNames thingNames env formula
  if rendered.contains '\n' then
    s!"{diagnosticConditionLabelSpec formula}:\n{rendered}"
  else s!"{diagnosticConditionLabelSpec formula}: {rendered}."

/-- The newline test includes newlines in source names or labels, not only
separators inserted by the layout. It counts one string-search call; character
inspection remains outside the unit-cost model. -/
private def renderDiagnosticConditionLineCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    Complexity.Costed String := do
  let rendered ← renderDiagnosticConditionCosted worldNames thingNames env formula
  let label ← diagnosticConditionLabelCosted formula
  let multiline ← Complexity.Costed.tick (rendered.contains '\n') 1
  Complexity.Costed.charge 1 <| if multiline then
    let text := Complexity.Costed.appendString (.pure label) (.pure ":\n")
    text.appendString (.pure rendered)
  else
    let text := Complexity.Costed.appendString (.pure label) (.pure ": ")
    let text := text.appendString (.pure rendered)
    text.appendString (.pure ".")

private theorem renderDiagnosticConditionLineCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagnosticConditionLineCosted worldNames thingNames env formula).value =
      renderDiagnosticConditionLineSpec worldNames thingNames env formula := by
  simp only [renderDiagnosticConditionLineCosted, renderDiagnosticConditionLineSpec,
    Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
    Complexity.Costed.charge_value, renderDiagnosticConditionCosted_value, diagnosticConditionLabelCosted_value]
  split <;> simp_all only [↓reduceIte] <;> rfl

private theorem renderDiagnosticConditionLineCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (formula : DiagFormula) :
    (renderDiagnosticConditionLineCosted worldNames thingNames env formula).cost ≤
      formula.nodeCount * (20 * env.size + 56) + 11 := by
  have hr := renderDiagnosticConditionCosted_cost_le worldNames thingNames env formula
  have hl := diagnosticConditionLabelCosted_cost_le formula
  have heq : formula.nodeCount * (20 * env.size + 56) =
      formula.nodeCount * (20 * env.size + 48) + 8 * formula.nodeCount := by
    rw [show 20 * env.size + 56 = (20 * env.size + 48) + 8 by omega, Nat.mul_add, Nat.mul_comm _ 8]
  rw [heq]
  simp only [renderDiagnosticConditionLineCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost, Complexity.Costed.charge_cost]
  split <;> simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost] <;> omega

private theorem renderDiagnosticConditionLineCostBound_mono {F F' E E' : Nat}
    (hF : F ≤ F') (hE : E ≤ E') :
    F * (20 * E + 56) + 11 ≤ F' * (20 * E' + 56) + 11 :=
  Nat.add_le_add_right
    (Nat.mul_le_mul hF (Nat.add_le_add_right (Nat.mul_le_mul_left 20 hE) 56)) 11

private def envSummarySpec
    (worldNames thingNames : Array Name) (vars : Array DiagVar) (env : Array (String × Nat)) :
    String :=
  String.intercalate ", " <| vars.toList.map fun var =>
    let idx := lookupVar env var.name
    match var.kind with
    | .thing => s!"{var.name} = {indexedName thingNames idx}"
    | .world => s!"{var.name} = {indexedName worldNames idx}"

/-- A variable's declared kind selects the name array. The environment lookup
still uses the last binding, including when the displayed variables repeat. -/
private def renderDiagAssignmentCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (var : DiagVar) : Complexity.Costed String :=
  Complexity.Costed.charge 1 <|
    let names := match var.kind with
      | .thing => thingNames
      | .world => worldNames
    let text := Complexity.Costed.appendString (.pure var.name) (.pure " = ")
    text.appendString (renderDiagVariableCosted names env var.name)

private theorem renderDiagAssignmentCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (var : DiagVar) :
    (renderDiagAssignmentCosted worldNames thingNames env var).value =
      (match var.kind with
       | .thing => s!"{var.name} = {indexedName thingNames (lookupVar env var.name)}"
       | .world => s!"{var.name} = {indexedName worldNames (lookupVar env var.name)}") := by
  cases var with
  | mk name kind => cases kind <;>
      simp only [renderDiagAssignmentCosted, Complexity.Costed.charge_value,
        Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
        renderDiagVariableCosted_value] <;> rfl

private theorem renderDiagAssignmentCosted_cost
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) (var : DiagVar) :
    (renderDiagAssignmentCosted worldNames thingNames env var).cost = 4 * env.size + 8 := by
  simp [renderDiagAssignmentCosted, renderDiagVariableCosted_cost]
  omega

/-- The forward fold joins assignments without an intermediate list. Each
entry pays for its lookup and text, even if a later output cap discards it. -/
private def envSummaryCosted
    (worldNames thingNames : Array Name) (vars : Array DiagVar)
    (env : Array (String × Nat)) : Complexity.Costed String := do
  let joined ← Complexity.Costed.foldArray vars (none : Option String) fun out var => do
    let assignment ← renderDiagAssignmentCosted worldNames thingNames env var
    Complexity.Costed.charge 1 <| match out with
    | none => Complexity.Costed.pure (some assignment)
    | some text => do
        let text ← Complexity.Costed.appendString (.pure text) (.pure ", ")
        let text ← Complexity.Costed.appendString (.pure text) (.pure assignment)
        Complexity.Costed.pure (some text)
  Complexity.Costed.tick (joined.getD "") 1

private theorem envSummaryCosted_value
    (worldNames thingNames : Array Name) (vars : Array DiagVar) (env : Array (String × Nat)) :
    (envSummaryCosted worldNames thingNames vars env).value =
      envSummarySpec worldNames thingNames vars env := by
  have fold (xs before : List String) :
      (xs.foldl (fun out name => match out with
        | none => some name
        | some text => some (text ++ ", " ++ name))
        (if before = [] then none else some (String.intercalate ", " before))).getD "" =
        String.intercalate ", " (before ++ xs) := by
    induction xs generalizing before with
    | nil => cases before <;> simp
    | cons name xs ih =>
        rw [List.append_cons, ← ih, List.foldl_cons]
        congr
        cases before with
        | nil => simp
        | cons first rest =>
            simp only [List.cons_ne_nil, ↓reduceIte, List.cons_append, Option.some.injEq]
            rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
              String.intercalate_singleton]
  have h := fold (vars.toList.map fun var =>
    (renderDiagAssignmentCosted worldNames thingNames env var).value) []
  simp only [List.nil_append, ↓reduceIte, List.foldl_map] at h
  simp only [envSummaryCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArray_value, ← Array.foldl_toList,
    Complexity.Costed.charge_value]
  have hspec : (String.intercalate ", " (vars.toList.map fun var =>
      (renderDiagAssignmentCosted worldNames thingNames env var).value)) =
      envSummarySpec worldNames thingNames vars env := by
    simp only [renderDiagAssignmentCosted_value, envSummarySpec]
  rw [← hspec]
  convert h using 1
  congr 2
  funext out var
  cases out <;> rfl

private theorem envSummaryCosted_cost_le
    (worldNames thingNames : Array Name) (vars : Array DiagVar) (env : Array (String × Nat)) :
    (envSummaryCosted worldNames thingNames vars env).cost ≤
      vars.size * (4 * env.size + 13) + 1 := by
  have h := Complexity.Costed.foldArray_cost_le vars (none : Option String)
    (fun out var => do
      let assignment ← renderDiagAssignmentCosted worldNames thingNames env var
      Complexity.Costed.charge 1 <| match out with
      | none => Complexity.Costed.pure (some assignment)
      | some text => do
          let text ← Complexity.Costed.appendString (.pure text) (.pure ", ")
          let text ← Complexity.Costed.appendString (.pure text) (.pure assignment)
          Complexity.Costed.pure (some text))
    (4 * env.size + 11) (by
      intro out var hvar
      cases out <;> simp [Bind.bind, renderDiagAssignmentCosted_cost])
  have heq : 4 * env.size + 11 + 2 = 4 * env.size + 13 := by omega
  rw [heq] at h
  simpa only [envSummaryCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost] using Nat.add_le_add_right h 1

private theorem envSummaryCostBound_mono {V V' E E' : Nat} (hV : V ≤ V') (hE : E ≤ E') :
    V * (4 * E + 13) + 1 ≤ V' * (4 * E' + 13) + 1 :=
  Nat.add_le_add_right
    (Nat.mul_le_mul hV (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hE) 13)) 1

private def envVarKind? (outerVars : Array DiagVar) (name : String) : Option DiagVarKind :=
  outerVars.findSome? fun var =>
    if var.name == name then some var.kind else none

/-- Search candidates in declaration order. The numeric loop stops after the
first match. Each visited candidate pays for the bounds guard, array read,
name comparison, and result branch, in addition to the shared loop cost. -/
private def envVarKindCosted (candidates : Array DiagVar) (name : String) :
    Complexity.Costed (Option DiagVarKind) :=
  foldDiagDomainCosted 0 candidates.size none Option.isSome fun _ i =>
    Complexity.Costed.charge 2 <| if hi : i < candidates.size then do
      let var ← Complexity.Costed.tick candidates[i] 1
      Complexity.Costed.tick (if var.name == name then some var.kind else none) 2
    else Complexity.Costed.pure none

private theorem envVarKindCosted_cost_le (candidates : Array DiagVar) (name : String) :
    (envVarKindCosted candidates name).cost ≤ 8 * candidates.size := by
  have h := foldDiagDomainCosted_cost_le 0 candidates.size (none : Option DiagVarKind) Option.isSome
    (fun _ i => Complexity.Costed.charge 2 <| if hi : i < candidates.size then do
      let var ← Complexity.Costed.tick candidates[i] 1
      Complexity.Costed.tick (if var.name == name then some var.kind else none) 2
    else Complexity.Costed.pure none) 5 (by
      intro state i hlo hhi
      have hi : i < candidates.size := by omega
      simp [hi, Bind.bind])
  simpa only [envVarKindCosted, Nat.mul_comm] using h

private theorem envVarKindCosted_value (candidates : Array DiagVar) (name : String) :
    (envVarKindCosted candidates name).value = envVarKind? candidates name := by
  have congrFind (xs : List Nat) (f g : Nat → Option DiagVarKind)
      (h : ∀ i ∈ xs, f i = g i) : xs.findSome? f = xs.findSome? g := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
        have hi := h i (by simp)
        have ht := ih (fun j hj => h j (by simp [hj]))
        simp only [List.findSome?_cons, hi, ht]
  have indexed (xs : Array DiagVar) :
      (List.range xs.size).findSome? (fun i => if hi : i < xs.size then
        if xs[i].name == name then some xs[i].kind else none
        else none) = envVarKind? xs name := by
    induction xs using (measure (fun xs : Array DiagVar => xs.size)).wf.induction with
    | h xs ih =>
      by_cases hempty : xs = #[]
      · subst xs
        simp [envVarKind?]
      · obtain ⟨xs, x, rfl⟩ := Array.exists_push_of_ne_empty hempty
        have ih := ih xs (show xs.size < (xs.push x).size by simp)
        simp only [Array.size_push, List.range_succ, List.findSome?_append, List.findSome?_singleton]
        have hfirst := congrFind (List.range xs.size)
          (fun i => if hi : i < xs.size + 1 then
            if ((xs.push x)[i]'(by simpa using hi)).name == name then
              some ((xs.push x)[i]'(by simpa using hi)).kind else none else none)
          (fun i => if hi : i < xs.size then
            if xs[i].name == name then some xs[i].kind else none else none) (by
              intro i hi
              have hlt := List.mem_range.mp hi
              simp [hlt, show i < xs.size + 1 by omega, Array.getElem_push_lt])
        rw [hfirst, ih]
        simp [envVarKind?, Array.findSome?_push]
  unfold envVarKindCosted
  rw [foldDiagDomainCosted_firstSome_value candidates.size _
    (fun i => if hi : i < candidates.size then
      if candidates[i].name == name then some candidates[i].kind else none else none)
    (by intro i hi; simp [hi, Bind.bind]; rfl)]
  exact indexed candidates

private def formulaBoundVarKindsSpec (formula : DiagFormula) : List DiagVar :=
  match formula with
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => []
  | .not p => formulaBoundVarKindsSpec p
  | .and p q | .or p q | .imp p q | .iff p q =>
      formulaBoundVarKindsSpec p ++ formulaBoundVarKindsSpec q
  | .forallThing name body | .existsThing name body =>
      ⟨name, .thing⟩ :: formulaBoundVarKindsSpec body
  | .forallWorld name body | .existsWorld name body =>
      ⟨name, .world⟩ :: formulaBoundVarKindsSpec body
  | .box _ witnessWorld body | .dia _ witnessWorld body =>
      ⟨witnessWorld, .world⟩ :: formulaBoundVarKindsSpec body

/-- Append binders in preorder: a binder precedes its body, and a left
subformula precedes its right sibling. Starting from the outer candidates
avoids a second array and a later concatenation. Each node costs one selection;
each binder adds one write. -/
private def formulaBoundVarKindsIntoCosted
    (out : Array DiagVar) (formula : DiagFormula) : Complexity.Costed (Array DiagVar) :=
  Complexity.Costed.charge 1 <| match formula with
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => .pure out
  | .not p => formulaBoundVarKindsIntoCosted out p
  | .and p q | .or p q | .imp p q | .iff p q => do
      let out ← formulaBoundVarKindsIntoCosted out p
      formulaBoundVarKindsIntoCosted out q
  | .forallThing name body | .existsThing name body => do
      let out ← Complexity.Costed.tick (out.push ⟨name, .thing⟩) 1
      formulaBoundVarKindsIntoCosted out body
  | .forallWorld name body | .existsWorld name body => do
      let out ← Complexity.Costed.tick (out.push ⟨name, .world⟩) 1
      formulaBoundVarKindsIntoCosted out body
  | .box _ witnessWorld body | .dia _ witnessWorld body => do
      let out ← Complexity.Costed.tick (out.push ⟨witnessWorld, .world⟩) 1
      formulaBoundVarKindsIntoCosted out body
termination_by formula.nodeCount
decreasing_by all_goals simp_all [DiagFormula.nodeCount] <;> omega

private theorem formulaBoundVarKindsIntoCosted_value
    (out : Array DiagVar) (formula : DiagFormula) :
    (formulaBoundVarKindsIntoCosted out formula).value =
      out ++ (formulaBoundVarKindsSpec formula).toArray := by
  induction formula generalizing out <;>
    simp_all [formulaBoundVarKindsIntoCosted, formulaBoundVarKindsSpec, Bind.bind,
      Array.append_assoc, ← Array.append_singleton]

private theorem formulaBoundVarKindsSpec_length_le (formula : DiagFormula) :
    (formulaBoundVarKindsSpec formula).length ≤ formula.nodeCount := by
  induction formula <;> simp_all [formulaBoundVarKindsSpec, DiagFormula.nodeCount] <;> omega

private theorem formulaBoundVarKindsIntoCosted_cost_le
    (out : Array DiagVar) (formula : DiagFormula) :
    (formulaBoundVarKindsIntoCosted out formula).cost ≤ 2 * formula.nodeCount := by
  induction formula generalizing out <;>
    simp_all [formulaBoundVarKindsIntoCosted, Bind.bind, DiagFormula.nodeCount] <;> grind

private theorem formulaBoundVarKindsIntoCosted_size_le
    (out : Array DiagVar) (formula : DiagFormula) :
    (formulaBoundVarKindsIntoCosted out formula).value.size ≤ out.size + formula.nodeCount := by
  rw [formulaBoundVarKindsIntoCosted_value]
  simpa using Nat.add_le_add_left (formulaBoundVarKindsSpec_length_le formula) out.size

private def diagnosticEnvVarsIntoSpec
    (candidates : Array DiagVar) (seen : Std.HashSet String)
    (out : Array DiagVar) (entries : List (String × Nat)) : Array DiagVar :=
  match entries with
  | List.nil => out
  | List.cons entry rest =>
      let name := entry.1
      if seen.contains name then
        diagnosticEnvVarsIntoSpec candidates seen out rest
      else
        match envVarKind? candidates name with
        | some kind =>
            diagnosticEnvVarsIntoSpec candidates (seen.insert name) (out.push ⟨name, kind⟩) rest
        | none => diagnosticEnvVarsIntoSpec candidates seen out rest

/-- The output itself records the names already selected. This avoids a
second mutable set and makes every duplicate check a counted array scan. -/
private def discoverDiagVarCosted (candidates out : Array DiagVar) (entry : String × Nat) :
    Complexity.Costed (Array DiagVar) := do
  let seen ← Complexity.anyArrayCosted out fun var => Complexity.Costed.tick (var.name == entry.1) 1
  Complexity.Costed.charge 1 <| if seen then .pure out else do
    let kind ← envVarKindCosted candidates entry.1
    Complexity.Costed.charge 1 <| match kind with
    | none => .pure out
    | some kind => Complexity.Costed.tick (out.push ⟨entry.1, kind⟩) 1

private theorem discoverDiagVarCosted_value (candidates out : Array DiagVar) (entry : String × Nat) :
    (discoverDiagVarCosted candidates out entry).value =
      if out.any (fun var => var.name == entry.1) then out
      else match envVarKind? candidates entry.1 with
      | none => out
      | some kind => out.push ⟨entry.1, kind⟩ := by
  simp only [discoverDiagVarCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, Complexity.anyArrayCosted_eq_list,
    Complexity.anyListCosted_value, Complexity.Costed.tick_value, Array.any_toList]
  split
  · rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value,
      envVarKindCosted_value]
    split <;> rfl

private theorem discoverDiagVarCosted_size_le (candidates out : Array DiagVar) (entry : String × Nat) :
    (discoverDiagVarCosted candidates out entry).value.size ≤ out.size + 1 := by
  rw [discoverDiagVarCosted_value]
  split
  · omega
  · split <;> simp

private theorem discoverDiagVarCosted_cost_le (candidates out : Array DiagVar) (entry : String × Nat) :
    (discoverDiagVarCosted candidates out entry).cost ≤ 4 * out.size + (8 * candidates.size + 3) := by
  have hs := Complexity.anyArrayCosted_cost_le out
    (fun var => Complexity.Costed.tick (var.name == entry.1) 1) 1 (by intros; rfl)
  have hk := envVarKindCosted_cost_le candidates entry.1
  simp only [discoverDiagVarCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.pure_cost]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.tick_cost] <;> omega

private def diagnosticEnvVarsCosted (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) : Complexity.Costed (Array DiagVar) := do
  let candidates ← formulaBoundVarKindsIntoCosted outerVars formula
  Complexity.Costed.charge 1 <| Complexity.Costed.foldArray env #[] (discoverDiagVarCosted candidates)

/-- The set is a proof specification only. Its membership agrees with names
in the growing output. This invariant proves the counted scan preserves the
first recognized environment occurrence and the candidate-kind priority. -/
private theorem diagnosticEnvVarsCosted_value (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) :
    (diagnosticEnvVarsCosted outerVars formula env).value =
      diagnosticEnvVarsIntoSpec (outerVars ++ (formulaBoundVarKindsSpec formula).toArray) {} #[] env.toList := by
  have loop (candidates : Array DiagVar) (entries : List (String × Nat))
      (seen : Std.HashSet String) (out : Array DiagVar)
      (agree : ∀ name, seen.contains name = out.any (fun var => var.name == name)) :
      entries.foldl (fun out entry => (discoverDiagVarCosted candidates out entry).value) out =
        diagnosticEnvVarsIntoSpec candidates seen out entries := by
    induction entries generalizing seen out with
    | nil => rfl
    | cons entry entries ih =>
        rw [List.foldl_cons, discoverDiagVarCosted_value candidates out entry, diagnosticEnvVarsIntoSpec]
        by_cases hseen : out.any (fun var => var.name == entry.1) = true
        · simp only [agree entry.1, hseen, ↓reduceIte]
          exact ih seen out agree
        · simp only [agree entry.1, hseen]
          cases hkind : envVarKind? candidates entry.1 with
          | none => exact ih seen out agree
          | some kind =>
            apply ih
            intro name
            simp [Std.HashSet.contains_insert, agree, Bool.or_comm]
  simp only [diagnosticEnvVarsCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, Complexity.Costed.foldArray_value, ← Array.foldl_toList,
    formulaBoundVarKindsIntoCosted_value]
  exact loop _ _ {} #[] (by intro name; simp)

private def diagnosticEnvVarsCostBound (F V E : Nat) : Nat :=
  2 * F + 1 + E * (4 * E + 8 * (V + F) + 5)

private theorem diagnosticEnvVarsCosted_cost_le (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) :
    (diagnosticEnvVarsCosted outerVars formula env).cost ≤
      diagnosticEnvVarsCostBound formula.nodeCount outerVars.size env.size := by
  have hc := formulaBoundVarKindsIntoCosted_cost_le outerVars formula
  have hn := formulaBoundVarKindsIntoCosted_size_le outerVars formula
  have hf := Complexity.Costed.foldArray_cost_le_growth env (#[] : Array DiagVar)
    (discoverDiagVarCosted (formulaBoundVarKindsIntoCosted outerVars formula).value)
    Array.size 4 (8 * (formulaBoundVarKindsIntoCosted outerVars formula).value.size + 3)
    (by intro out entry hentry; exact discoverDiagVarCosted_cost_le _ out entry)
    (by intro out entry hentry; exact discoverDiagVarCosted_size_le _ out entry)
  have hscale := Nat.mul_le_mul_left env.size (show
      4 * (0 + env.size) + (8 * (formulaBoundVarKindsIntoCosted outerVars formula).value.size + 3) + 2 ≤
      4 * env.size + 8 * (outerVars.size + formula.nodeCount) + 5 by omega)
  simp only [diagnosticEnvVarsCosted, diagnosticEnvVarsCostBound, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  simp only [Array.size_empty] at hf
  omega

private theorem diagnosticEnvVarsCostBound_mono {F F' V V' E E' : Nat}
    (hF : F ≤ F') (hV : V ≤ V') (hE : E ≤ E') :
    diagnosticEnvVarsCostBound F V E ≤ diagnosticEnvVarsCostBound F' V' E' := by
  unfold diagnosticEnvVarsCostBound
  apply Nat.add_le_add
  · omega
  · apply Nat.mul_le_mul hE
    omega

private theorem diagnosticEnvVarsIntoSpec_size_le
    (candidates : Array DiagVar) (seen : Std.HashSet String)
    (out : Array DiagVar) (entries : List (String × Nat)) :
    (diagnosticEnvVarsIntoSpec candidates seen out entries).size ≤ out.size + entries.length := by
  induction entries generalizing seen out with
  | nil => simp [diagnosticEnvVarsIntoSpec]
  | cons entry rest ih =>
      simp only [diagnosticEnvVarsIntoSpec, List.length_cons]
      split
      · have h := ih seen out
        omega
      · split
        · rename_i kind hkind
          have h := ih (seen.insert entry.1) (out.push ⟨entry.1, kind⟩)
          simp only [Array.size_push] at h
          omega
        · have h := ih seen out
          omega

private theorem diagnosticEnvVarsCosted_size_le
    (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) :
    (diagnosticEnvVarsCosted outerVars formula env).value.size ≤ env.size := by
  rw [diagnosticEnvVarsCosted_value]
  simpa using diagnosticEnvVarsIntoSpec_size_le
    (outerVars ++ (formulaBoundVarKindsSpec formula).toArray) {} (#[] : Array DiagVar) env.toList

/-- Search coordinates in ascending order and retain the first matching assignment.
The numeric loop allocates no domain list. Each visit adds an environment write,
a Boolean comparison, and its branch to the evaluation cost. The shared loop
charges three control operations per visit and for a stop before remaining work. -/
private def firstMatchingEnvCosted (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (name : String) (body : DiagFormula)
    (wanted : Bool) (count : Nat) : Complexity.Costed (Option (Array (String × Nat))) :=
  foldDiagDomainCosted 0 count none Option.isSome fun _ i =>
    let env' := env.push (name, i)
    let checked := evalDiagFormulaCosted worldCount thingCount tables env' body
    ⟨if checked.value == wanted then some env' else none, checked.cost + 3⟩

private theorem firstMatchingEnvCosted_value (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (name : String) (body : DiagFormula)
    (wanted : Bool) (count : Nat) :
    (firstMatchingEnvCosted worldCount thingCount tables env name body wanted count).value =
      (List.range count).findSome? (fun i =>
        let env' := env.push (name, i)
        if evalDiagFormula worldCount thingCount tables env' body == wanted then some env' else none) := by
  apply foldDiagDomainCosted_firstSome_value
  intro i hi
  rfl

private theorem firstMatchingEnvCosted_cost_le (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (name : String) (body : DiagFormula)
    (wanted : Bool) (count : Nat) :
    (firstMatchingEnvCosted worldCount thingCount tables env name body wanted count).cost ≤
      count * (DiagFormula.evalCostBound worldCount thingCount (diagAtomCostBound worldCount thingCount tables)
        (env.size + 1) body + 6) := by
  unfold firstMatchingEnvCosted
  apply foldDiagDomainCosted_cost_le
  intro state i hlo hhi
  have h := evalDiagFormulaCosted_concrete_cost_le worldCount thingCount tables (env.push (name, i)) body
  simp only [Array.size_push] at h
  dsimp only
  omega

private theorem firstMatchingEnvCosted_some_size (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (name : String) (body : DiagFormula)
    (wanted : Bool) (count : Nat) (env' : Array (String × Nat))
    (hs : (firstMatchingEnvCosted worldCount thingCount tables env name body wanted count).value = some env') :
    env'.size = env.size + 1 := by
  have h := foldDiagDomainCosted_preserves 0 count
    (none : Option (Array (String × Nat))) Option.isSome
    (fun _ i =>
      let extended := env.push (name, i)
      let checked := evalDiagFormulaCosted worldCount thingCount tables extended body
      (⟨if checked.value == wanted then some extended else none, checked.cost + 3⟩ :
        Complexity.Costed (Option (Array (String × Nat)))))
    (fun result => ∀ e, result = some e → e.size = env.size + 1)
    (by simp) (by
      intro state i hstate hstop e he
      dsimp only at he
      split at he
      · cases he
        simp
      · contradiction)
  exact h env' hs

private def DiagVarKind.domainSize
    (worldCount thingCount : Nat) : DiagVarKind → Nat
  | .thing => thingCount
  | .world => worldCount

private def firstFailureEnvCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) : Complexity.Costed (Option (Array (String × Nat))) :=
  let bound := match kind with | .thing => thingCount | .world => worldCount
  Complexity.Costed.charge 1 <|
    firstMatchingEnvCosted worldCount thingCount tables env name body false bound

private def firstFailureEnv
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) : Option (Array (String × Nat)) :=
  (firstFailureEnvCosted worldCount thingCount tables env kind name body).value

private def firstSuccessEnvCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) : Complexity.Costed (Option (Array (String × Nat))) :=
  let bound := match kind with | .thing => thingCount | .world => worldCount
  Complexity.Costed.charge 1 <|
    firstMatchingEnvCosted worldCount thingCount tables env name body true bound

private theorem firstFailureEnvCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 6) + 1 := by
  unfold firstFailureEnvCosted
  simp only [Complexity.Costed.charge_cost]
  have h := firstMatchingEnvCosted_cost_le worldCount thingCount tables env
    name body false (kind.domainSize worldCount thingCount)
  cases kind <;>
    simp only [DiagVarKind.domainSize] at h ⊢ <;>
    omega

private theorem firstSuccessEnvCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) :
    (firstSuccessEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 6) + 1 := by
  unfold firstSuccessEnvCosted
  simp only [Complexity.Costed.charge_cost]
  have h := firstMatchingEnvCosted_cost_le worldCount thingCount tables env
    name body true (kind.domainSize worldCount thingCount)
  cases kind <;>
    simp only [DiagVarKind.domainSize] at h ⊢ <;>
    omega

private theorem firstFailureEnvCosted_cost_le_of_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (result : Option (Array (String × Nat)))
    (_hValue : firstFailureEnv worldCount thingCount tables env kind name body = result) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 6) + 1 :=
  firstFailureEnvCosted_cost_le worldCount thingCount tables env kind name body

@[simp] private theorem firstSuccessEnvCosted_some_size
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (env' : Array (String × Nat))
    (hSome : (firstSuccessEnvCosted worldCount thingCount tables env kind name body).value =
      some env') :
    env'.size = env.size + 1 := by
  unfold firstSuccessEnvCosted at hSome
  simp only [Complexity.Costed.charge_value] at hSome
  apply firstMatchingEnvCosted_some_size worldCount thingCount tables env name body
    true _ env' hSome

@[simp] private theorem firstFailureEnvCosted_some_size
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (env' : Array (String × Nat))
    (hSome : (firstFailureEnvCosted worldCount thingCount tables env kind name body).value =
      some env') :
    env'.size = env.size + 1 := by
  unfold firstFailureEnvCosted at hSome
  simp only [Complexity.Costed.charge_value] at hSome
  apply firstMatchingEnvCosted_some_size worldCount thingCount tables env name body
    false _ env' hSome

private def firstSuccessEnv
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) : Option (Array (String × Nat)) :=
  (firstSuccessEnvCosted worldCount thingCount tables env kind name body).value

@[simp] private theorem firstFailureEnvCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).value =
      firstFailureEnv worldCount thingCount tables env kind name body := rfl

@[simp] private theorem firstSuccessEnvCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) :
    (firstSuccessEnvCosted worldCount thingCount tables env kind name body).value =
      firstSuccessEnv worldCount thingCount tables env kind name body := rfl

private theorem firstSuccessEnvCosted_cost_le_of_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (result : Option (Array (String × Nat)))
    (_hValue : firstSuccessEnv worldCount thingCount tables env kind name body = result) :
    (firstSuccessEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 6) + 1 :=
  firstSuccessEnvCosted_cost_le worldCount thingCount tables env kind name body

@[simp] private theorem firstFailureEnv_some_size
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (env' : Array (String × Nat))
    (hSome : firstFailureEnv worldCount thingCount tables env kind name body = some env') :
    env'.size = env.size + 1 := by
  exact firstFailureEnvCosted_some_size worldCount thingCount tables env kind name body env' hSome

@[simp] private theorem firstSuccessEnv_some_size
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (env' : Array (String × Nat))
    (hSome : firstSuccessEnv worldCount thingCount tables env kind name body = some env') :
    env'.size = env.size + 1 := by
  exact firstSuccessEnvCosted_some_size worldCount thingCount tables env kind name body env' hSome

private structure DiagTrace where
  formula : DiagFormula
  env : Array (String × Nat)
  deriving Inhabited

private structure MinimizedFailure where
  formula : DiagFormula
  env : Array (String × Nat)
  context : Array DiagTrace
  deriving Inhabited

private def failedHere (formula : DiagFormula) (env : Array (String × Nat)) :
    MinimizedFailure :=
  { formula, env, context := #[] }

private def withContext (context : Array DiagTrace) (failure : MinimizedFailure) :
    MinimizedFailure :=
  { failure with context := context ++ failure.context }

/-- Prepend successful traces without reversing their explanatory order.
Lean's append traverses the right array, so the cost depends on the failure's
existing context, not on the successful traces that precede it. -/
private def withContextCosted (context : Array DiagTrace) (failure : MinimizedFailure) :
    Complexity.Costed MinimizedFailure :=
  let copied := Complexity.Costed.appendArray context failure.context
  ⟨{ failure with context := copied.value }, copied.cost⟩

@[simp] private theorem withContextCosted_value
    (context : Array DiagTrace) (failure : MinimizedFailure) :
    (withContextCosted context failure).value = withContext context failure := by
  simp [withContextCosted, withContext]

@[simp] private theorem withContextCosted_cost
    (context : Array DiagTrace) (failure : MinimizedFailure) :
    (withContextCosted context failure).cost = 3 * failure.context.size := by
  simp [withContextCosted]

/--
Collect subformulas that succeeded on the current path to a failure.

The rendered diagnostic reports what is missing and why the missing obligation
applied. These traces become the evidence section of the widget. They are
explanatory data, not trusted proof data.
-/
private def successTracesIntoSpec
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace) (formula : DiagFormula) : Array DiagTrace :=
  if !(evalDiagFormula worldCount thingCount tables env formula) then out else
    match formula with
    | .atom _ | .eqThing _ _ | .eqWorld _ _ | .not _ | .iff _ _ |
        .forallThing _ _ | .forallWorld _ _ | .box _ _ _ =>
        out.push ⟨formula, env⟩
    | .and p q =>
        let left := successTracesIntoSpec worldCount thingCount tables env out p
        successTracesIntoSpec worldCount thingCount tables env left q
    | .or p q =>
        if evalDiagFormula worldCount thingCount tables env p then
          successTracesIntoSpec worldCount thingCount tables env out p
        else successTracesIntoSpec worldCount thingCount tables env out q
    | .imp p q =>
        if evalDiagFormula worldCount thingCount tables env p then
          successTracesIntoSpec worldCount thingCount tables env out q
        else out.push ⟨formula, env⟩
    | .existsThing name body =>
        match firstSuccessEnv worldCount thingCount tables env .thing name body with
        | some env' => successTracesIntoSpec worldCount thingCount tables env' out body
        | none => out.push ⟨formula, env⟩
    | .existsWorld name body =>
        match firstSuccessEnv worldCount thingCount tables env .world name body with
        | some env' => successTracesIntoSpec worldCount thingCount tables env' out body
        | none => out.push ⟨formula, env⟩
    | .dia _ name body =>
        match firstSuccessEnv worldCount thingCount tables env .world name body with
        | some env' => successTracesIntoSpec worldCount thingCount tables env' out body
        | none => out.push ⟨formula, env⟩

/-- Append successful context in evaluation order. Each call adds two operations
for the initial negation and branch. A successful result adds one constructor
test, and each retained trace adds one array write. Further Boolean branches
and witness-result tests each add one operation. Child costs enter the total
only on the selected path. These internal traces are not emitted text items.
`successTracesCosted` also charges the empty accumulator. -/
private def successTracesIntoCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace)
    (formula : DiagFormula) : Complexity.Costed (Array DiagTrace) :=
  let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
  if !checked.value then
    ⟨out, checked.cost + 2⟩
  else
    match formula with
    | .atom _ | .eqThing _ _ | .eqWorld _ _ | .not _ =>
        ⟨out.push ⟨formula, env⟩, checked.cost + 4⟩
    | .and p q =>
        let left := successTracesIntoCosted worldCount thingCount tables env out p
        let right := successTracesIntoCosted worldCount thingCount tables env left.value q
        ⟨right.value, checked.cost + left.cost + right.cost + 3⟩
    | .or p q =>
        let leftChecked := evalDiagFormulaCosted worldCount thingCount tables env p
        if leftChecked.value then
          let traces := successTracesIntoCosted worldCount thingCount tables env out p
          ⟨traces.value, checked.cost + leftChecked.cost + traces.cost + 4⟩
        else
          let traces := successTracesIntoCosted worldCount thingCount tables env out q
          ⟨traces.value, checked.cost + leftChecked.cost + traces.cost + 4⟩
    | .imp p q =>
        let antecedent := evalDiagFormulaCosted worldCount thingCount tables env p
        if antecedent.value then
          let traces := successTracesIntoCosted worldCount thingCount tables env out q
          ⟨traces.value, checked.cost + antecedent.cost + traces.cost + 4⟩
        else
          ⟨out.push ⟨formula, env⟩, checked.cost + antecedent.cost + 5⟩
    | .iff _ _ | .forallThing _ _ | .forallWorld _ _ =>
        ⟨out.push ⟨formula, env⟩, checked.cost + 4⟩
    | .existsThing name body =>
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .thing name body
        match witness.value with
        | some env' =>
            let traces := successTracesIntoCosted worldCount thingCount tables env' out body
            ⟨traces.value, checked.cost + witness.cost + traces.cost + 4⟩
        | none => ⟨out.push ⟨formula, env⟩, checked.cost + witness.cost + 5⟩
    | .existsWorld name body =>
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world name body
        match witness.value with
        | some env' =>
            let traces := successTracesIntoCosted worldCount thingCount tables env' out body
            ⟨traces.value, checked.cost + witness.cost + traces.cost + 4⟩
        | none => ⟨out.push ⟨formula, env⟩, checked.cost + witness.cost + 5⟩
    | .box _ _ _ => ⟨out.push ⟨formula, env⟩, checked.cost + 4⟩
    | .dia _ witnessWorld body =>
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world witnessWorld body
        match witness.value with
        | some env' =>
            let traces := successTracesIntoCosted worldCount thingCount tables env' out body
            ⟨traces.value, checked.cost + witness.cost + traces.cost + 4⟩
        | none => ⟨out.push ⟨formula, env⟩, checked.cost + witness.cost + 5⟩

private theorem successTracesIntoCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace) (formula : DiagFormula) :
    (successTracesIntoCosted worldCount thingCount tables env out formula).value =
      successTracesIntoSpec worldCount thingCount tables env out formula := by
  fun_induction successTracesIntoCosted
  all_goals rw [successTracesIntoSpec.eq_def]
  all_goals
    simp_all (config := { zetaDelta := true })
      [evalDiagFormulaCosted_value, firstSuccessEnvCosted_value]

private def successTracesSpec
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Array DiagTrace :=
  successTracesIntoSpec worldCount thingCount tables env #[] formula

private def successTracesCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    Complexity.Costed (Array DiagTrace) :=
  Complexity.Costed.charge 1 (successTracesIntoCosted worldCount thingCount tables env #[] formula)

@[simp] private theorem successTracesCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesCosted worldCount thingCount tables env formula).value =
      successTracesSpec worldCount thingCount tables env formula := by
  exact successTracesIntoCosted_value _ _ _ _ _ _

private def firstMatchCostBound
    (worldCount thingCount : Nat) (tables : FactTables)
    (kind : DiagVarKind) (envSize : Nat) (body : DiagFormula) : Nat :=
  kind.domainSize worldCount thingCount *
      (body.evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) (envSize + 1) + 6) + 1

/-- Structural cost of collecting successful context. The recurrence follows
the executable branch selection: disjunction includes either recursive branch,
while existential and diamond cases include their concrete witness scan. -/
private def DiagFormula.successTraceCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (envSize : Nat) :
    DiagFormula → Nat
  | formula@(.atom _) | formula@(.eqThing _ _) | formula@(.eqWorld _ _) |
      formula@(.not _) | formula@(.iff _ _) | formula@(.forallThing _ _) |
      formula@(.forallWorld _ _) | formula@(.box _ _ _) =>
      formula.evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) envSize + 4
  | formula@(.and p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.successTraceCostBound worldCount thingCount tables envSize + 3
  | formula@(.or p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.successTraceCostBound worldCount thingCount tables envSize + 4
  | formula@(.imp p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        q.successTraceCostBound worldCount thingCount tables envSize + 5
  | formula@(.existsThing _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .thing envSize body +
        body.successTraceCostBound worldCount thingCount tables (envSize + 1) + 5
  | formula@(.existsWorld _ body) | formula@(.dia _ _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .world envSize body +
        body.successTraceCostBound worldCount thingCount tables (envSize + 1) + 5

private theorem successTracesIntoCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace) (formula : DiagFormula) :
    (successTracesIntoCosted worldCount thingCount tables env out formula).cost ≤
      formula.successTraceCostBound worldCount thingCount tables env.size := by
  induction formula generalizing env out with
  | atom atom =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.atom atom) <;>
        omega
  | eqThing left right =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.eqThing left right) <;>
        omega
  | eqWorld left right =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.eqWorld left right) <;>
        omega
  | not p ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.not p) <;>
        omega
  | iff p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.iff p q) <;>
        omega
  | forallThing name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.forallThing name body) <;>
        omega
  | forallWorld name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.forallWorld name body) <;>
        omega
  | box currentWorld witnessWorld body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split <;> dsimp only <;>
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.box currentWorld witnessWorld body) <;>
        omega
  | and p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split
      · dsimp only
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.and p q)
        omega
      · change (evalDiagFormulaCosted worldCount thingCount tables env (.and p q)).cost +
            (successTracesIntoCosted worldCount thingCount tables env out p).cost +
            (successTracesIntoCosted worldCount thingCount tables env
              (successTracesIntoCosted worldCount thingCount tables env out p).value q).cost + 3 ≤ _
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.and p q)
        have hp := ihp env out
        have hq := ihq env
          (successTracesIntoCosted worldCount thingCount tables env out p).value
        omega
  | or p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split
      · dsimp only
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.or p q)
        omega
      · split
        · dsimp only
          have hchecked := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env (.or p q)
          have hleft := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env p
          have htrace := ihp env out
          omega
        · dsimp only
          have hchecked := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env (.or p q)
          have hleft := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env p
          have htrace := ihq env out
          omega
  | imp p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split
      · dsimp only
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.imp p q)
        omega
      · split
        · dsimp only
          have hchecked := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env (.imp p q)
          have hp := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env p
          have hq := ihq env out
          omega
        · dsimp only
          have hchecked := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env (.imp p q)
          have hp := evalDiagFormulaCosted_concrete_cost_le
            worldCount thingCount tables env p
          omega
  | existsThing name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split
      · dsimp only
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.existsThing name body)
        omega
      · cases hw : (firstSuccessEnvCosted worldCount thingCount tables env
            .thing name body).value with
        | none =>
            dsimp only
            have hchecked := evalDiagFormulaCosted_concrete_cost_le
              worldCount thingCount tables env (.existsThing name body)
            have hwitness := firstSuccessEnvCosted_cost_le
              worldCount thingCount tables env .thing name body
            unfold firstMatchCostBound
            omega
        | some env' =>
            dsimp only
            have hchecked := evalDiagFormulaCosted_concrete_cost_le
              worldCount thingCount tables env (.existsThing name body)
            have hwitness := firstSuccessEnvCosted_cost_le
              worldCount thingCount tables env .thing name body
            have hsize := firstSuccessEnvCosted_some_size
              worldCount thingCount tables env .thing name body env' hw
            have htrace := ih env' out
            rw [hsize] at htrace
            unfold firstMatchCostBound
            omega
  | existsWorld name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split
      · dsimp only
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.existsWorld name body)
        omega
      · cases hw : (firstSuccessEnvCosted worldCount thingCount tables env
            .world name body).value with
        | none =>
            dsimp only
            have hchecked := evalDiagFormulaCosted_concrete_cost_le
              worldCount thingCount tables env (.existsWorld name body)
            have hwitness := firstSuccessEnvCosted_cost_le
              worldCount thingCount tables env .world name body
            unfold firstMatchCostBound
            omega
        | some env' =>
            dsimp only
            have hchecked := evalDiagFormulaCosted_concrete_cost_le
              worldCount thingCount tables env (.existsWorld name body)
            have hwitness := firstSuccessEnvCosted_cost_le
              worldCount thingCount tables env .world name body
            have hsize := firstSuccessEnvCosted_some_size
              worldCount thingCount tables env .world name body env' hw
            have htrace := ih env' out
            rw [hsize] at htrace
            unfold firstMatchCostBound
            omega
  | dia currentWorld name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.successTraceCostBound]
      split
      · dsimp only
        have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables env (.dia currentWorld name body)
        omega
      · cases hw : (firstSuccessEnvCosted worldCount thingCount tables env
            .world name body).value with
        | none =>
            dsimp only
            have hchecked := evalDiagFormulaCosted_concrete_cost_le
              worldCount thingCount tables env (.dia currentWorld name body)
            have hwitness := firstSuccessEnvCosted_cost_le
              worldCount thingCount tables env .world name body
            unfold firstMatchCostBound
            omega
        | some env' =>
            dsimp only
            have hchecked := evalDiagFormulaCosted_concrete_cost_le
              worldCount thingCount tables env (.dia currentWorld name body)
            have hwitness := firstSuccessEnvCosted_cost_le
              worldCount thingCount tables env .world name body
            have hsize := firstSuccessEnvCosted_some_size
              worldCount thingCount tables env .world name body env' hw
            have htrace := ih env' out
            rw [hsize] at htrace
            unfold firstMatchCostBound
            omega

private theorem successTracesIntoCosted_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace) (formula : DiagFormula) :
    (successTracesIntoCosted worldCount thingCount tables env out formula).value.size ≤
      out.size + formula.nodeCount := by
  induction formula generalizing env out with
  | atom atom =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | eqThing left right =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | eqWorld left right =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | not p ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | iff p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | forallThing name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | forallWorld name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | box currentWorld witnessWorld body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split <;> dsimp only <;> simp
  | and p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split
      · dsimp only
        omega
      · dsimp only
        have hp := ihp env out
        have hq := ihq env
          (successTracesIntoCosted worldCount thingCount tables env out p).value
        omega
  | or p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split
      · dsimp only
        omega
      · split
        · dsimp only
          have hp := ihp env out
          omega
        · dsimp only
          have hq := ihq env out
          omega
  | imp p q ihp ihq =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split
      · dsimp only
        omega
      · split
        · dsimp only
          have hq := ihq env out
          omega
        · dsimp only
          simp
  | existsThing name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split
      · dsimp only
        omega
      · cases hw : (firstSuccessEnvCosted worldCount thingCount tables env
            .thing name body).value with
        | none =>
            dsimp only
            simp
        | some env' =>
            dsimp only
            have h := ih env' out
            omega
  | existsWorld name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split
      · dsimp only
        omega
      · cases hw : (firstSuccessEnvCosted worldCount thingCount tables env
            .world name body).value with
        | none =>
            dsimp only
            simp
        | some env' =>
            dsimp only
            have h := ih env' out
            omega
  | dia currentWorld name body ih =>
      rw [successTracesIntoCosted]
      simp only [DiagFormula.nodeCount]
      split
      · dsimp only
        omega
      · cases hw : (firstSuccessEnvCosted worldCount thingCount tables env
            .world name body).value with
        | none =>
            dsimp only
            simp
        | some env' =>
            dsimp only
            have h := ih env' out
            omega

/-- Cost-free specification of failure selection and explanatory context.
Conjunctions select the first failed side. Disjunctions retain both failures.
Successful antecedents precede the failed consequent's context. Quantifiers
retain the first selected witness in domain order. This specifies deterministic
selection, not a globally smallest equivalent counterexample. -/
private def minimizeFailureSpec
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → MinimizedFailure
  | formula@(.atom _) => failedHere formula env
  | formula@(.eqThing _ _) => failedHere formula env
  | formula@(.eqWorld _ _) => failedHere formula env
  | formula@(.not p) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        failedHere formula env
      else
        match p with
        | .not q =>
            minimizeFailureSpec worldCount thingCount tables env q
        | .forallThing name body =>
            let witness := firstFailureEnv worldCount thingCount tables env .thing name body
            match witness with
            | some env' => minimizeFailureSpec worldCount thingCount tables env' body
            | none => failedHere formula env
        | .forallWorld name body =>
            let witness := firstFailureEnv worldCount thingCount tables env .world name body
            match witness with
            | some env' => minimizeFailureSpec worldCount thingCount tables env' body
            | none => failedHere formula env
        | .existsThing name body =>
            let witness := firstSuccessEnv worldCount thingCount tables env .thing name body
            match witness with
            | some env' => minimizeFailureSpec worldCount thingCount tables env' body
            | none => failedHere formula env
        | .existsWorld name body =>
            let witness := firstSuccessEnv worldCount thingCount tables env .world name body
            match witness with
            | some env' => minimizeFailureSpec worldCount thingCount tables env' body
            | none => failedHere formula env
        | .box _ witnessWorld body =>
            let witness := firstFailureEnv worldCount thingCount tables env .world witnessWorld body
            match witness with
            | some env' => minimizeFailureSpec worldCount thingCount tables env' body
            | none => failedHere formula env
        | .dia _ witnessWorld body =>
            let witness := firstSuccessEnv worldCount thingCount tables env .world witnessWorld body
            match witness with
            | some env' => minimizeFailureSpec worldCount thingCount tables env' body
            | none => failedHere formula env
        | _ => failedHere formula env
  | formula@(.and p q) =>
      let leftChecked := evalDiagFormula worldCount thingCount tables env p
      if !leftChecked then
        minimizeFailureSpec worldCount thingCount tables env p
      else
        let rightChecked := evalDiagFormula worldCount thingCount tables env q
        if !rightChecked then
          let traces := successTracesSpec worldCount thingCount tables env p
          let failure := minimizeFailureSpec worldCount thingCount tables env q
          withContext traces failure
        else
          failedHere formula env
  | formula@(.or p q) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        failedHere formula env
      else
        let pFailure := minimizeFailureSpec worldCount thingCount tables env p
        let qFailure := minimizeFailureSpec worldCount thingCount tables env q
        {
          formula := .or pFailure.formula qFailure.formula,
          env := pFailure.env ++ qFailure.env,
          context := pFailure.context ++ qFailure.context
        }
  | formula@(.imp p q) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        failedHere formula env
      else
        let traces := successTracesSpec worldCount thingCount tables env p
        let failure := minimizeFailureSpec worldCount thingCount tables env q
        withContext traces failure
  | formula@(.iff p q) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        failedHere formula env
      else
        let leftChecked := evalDiagFormula worldCount thingCount tables env p
        if leftChecked then
          let traces := successTracesSpec worldCount thingCount tables env p
          let failure := minimizeFailureSpec worldCount thingCount tables env q
          withContext traces failure
        else
          let rightChecked := evalDiagFormula worldCount thingCount tables env q
          if rightChecked then
            let traces := successTracesSpec worldCount thingCount tables env q
            let failure := minimizeFailureSpec worldCount thingCount tables env p
            withContext traces failure
          else
            failedHere formula env
  | formula@(.forallThing name body) =>
      let witness := firstFailureEnv worldCount thingCount tables env .thing name body
      match witness with
      | some env' => minimizeFailureSpec worldCount thingCount tables env' body
      | none => failedHere formula env
  | formula@(.forallWorld name body) =>
      let witness := firstFailureEnv worldCount thingCount tables env .world name body
      match witness with
      | some env' => minimizeFailureSpec worldCount thingCount tables env' body
      | none => failedHere formula env
  | formula@(.existsThing name body) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        let witness := firstSuccessEnv worldCount thingCount tables env .thing name body
        match witness with
        | some env' => minimizeFailureSpec worldCount thingCount tables env' body
        | none => failedHere formula env
      else
        failedHere formula env
  | formula@(.existsWorld name body) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        let witness := firstSuccessEnv worldCount thingCount tables env .world name body
        match witness with
        | some env' => minimizeFailureSpec worldCount thingCount tables env' body
        | none => failedHere formula env
      else
        failedHere formula env
  | formula@(.box _ witnessWorld body) =>
      let witness := firstFailureEnv worldCount thingCount tables env .world witnessWorld body
      match witness with
      | some env' => minimizeFailureSpec worldCount thingCount tables env' body
      | none => failedHere formula env
  | formula@(.dia _ witnessWorld body) =>
      let checked := evalDiagFormula worldCount thingCount tables env formula
      if checked then
        let witness := firstSuccessEnv worldCount thingCount tables env .world witnessWorld body
        match witness with
        | some env' => minimizeFailureSpec worldCount thingCount tables env' body
        | none => failedHere formula env
      else
        failedHere formula env

/--
Select a failed subformula and its explanatory context.

For implications and biconditionals this keeps the successful antecedent/context
beside the failing consequent. For quantifiers and modal boxes it also records
the witness assignment that makes the failure concrete in DSL names.

Each visited formula costs one constructor test. Branch conditions, nested
constructor tests, and the conjunction's Boolean negations each cost one.
A terminal result also initializes its empty context array. Array joins use
counted append, which charges each entry of the right operand.
-/
private def minimizeFailureCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → Complexity.Costed MinimizedFailure
  | formula@(.atom _) => ⟨failedHere formula env, 2⟩
  | formula@(.eqThing _ _) => ⟨failedHere formula env, 2⟩
  | formula@(.eqWorld _ _) => ⟨failedHere formula env, 2⟩
  | formula@(.not p) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 3⟩
      else
        match p with
        | .not q =>
            Complexity.Costed.charge (checked.cost + 3) <|
              minimizeFailureCosted worldCount thingCount tables env q
        | .forallThing name body =>
            let witness := firstFailureEnvCosted worldCount thingCount tables env .thing name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 4) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 5⟩
        | .forallWorld name body =>
            let witness := firstFailureEnvCosted worldCount thingCount tables env .world name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 4) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 5⟩
        | .existsThing name body =>
            let witness := firstSuccessEnvCosted worldCount thingCount tables env .thing name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 4) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 5⟩
        | .existsWorld name body =>
            let witness := firstSuccessEnvCosted worldCount thingCount tables env .world name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 4) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 5⟩
        | .box _ witnessWorld body =>
            let witness := firstFailureEnvCosted worldCount thingCount tables env .world witnessWorld body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 4) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 5⟩
        | .dia _ witnessWorld body =>
            let witness := firstSuccessEnvCosted worldCount thingCount tables env .world witnessWorld body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 4) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 5⟩
        | _ => ⟨failedHere formula env, checked.cost + 4⟩
  | formula@(.and p q) =>
      let leftChecked := evalDiagFormulaCosted worldCount thingCount tables env p
      if !leftChecked.value then
        Complexity.Costed.charge (leftChecked.cost + 3) <|
          minimizeFailureCosted worldCount thingCount tables env p
      else
        let rightChecked := evalDiagFormulaCosted worldCount thingCount tables env q
        if !rightChecked.value then
          let traces := successTracesCosted worldCount thingCount tables env p
          let failure := minimizeFailureCosted worldCount thingCount tables env q
          Complexity.Costed.charge
            (leftChecked.cost + rightChecked.cost + traces.cost + failure.cost + 5) <|
              withContextCosted traces.value failure.value
        else
          ⟨failedHere formula env, leftChecked.cost + rightChecked.cost + 6⟩
  | formula@(.or p q) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 3⟩
      else
        let pFailure := minimizeFailureCosted worldCount thingCount tables env p
        let qFailure := minimizeFailureCosted worldCount thingCount tables env q
        let mergedEnv := Complexity.Costed.appendArray pFailure.value.env qFailure.value.env
        let mergedContext := Complexity.Costed.appendArray
          pFailure.value.context qFailure.value.context
        ⟨{
          formula := .or pFailure.value.formula qFailure.value.formula,
          env := mergedEnv.value,
          context := mergedContext.value
        }, checked.cost + pFailure.cost + qFailure.cost +
          mergedEnv.cost + mergedContext.cost + 2⟩
  | formula@(.imp p q) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 3⟩
      else
        let traces := successTracesCosted worldCount thingCount tables env p
        let failure := minimizeFailureCosted worldCount thingCount tables env q
        Complexity.Costed.charge (checked.cost + traces.cost + failure.cost + 2) <|
          withContextCosted traces.value failure.value
  | formula@(.iff p q) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 3⟩
      else
        let leftChecked := evalDiagFormulaCosted worldCount thingCount tables env p
        if leftChecked.value then
          let traces := successTracesCosted worldCount thingCount tables env p
          let failure := minimizeFailureCosted worldCount thingCount tables env q
          Complexity.Costed.charge
            (checked.cost + leftChecked.cost + traces.cost + failure.cost + 3) <|
              withContextCosted traces.value failure.value
        else
          let rightChecked := evalDiagFormulaCosted worldCount thingCount tables env q
          if rightChecked.value then
            let traces := successTracesCosted worldCount thingCount tables env q
            let failure := minimizeFailureCosted worldCount thingCount tables env p
            Complexity.Costed.charge
              (checked.cost + leftChecked.cost + rightChecked.cost + traces.cost + failure.cost + 4) <|
                withContextCosted traces.value failure.value
          else
            ⟨failedHere formula env, checked.cost + leftChecked.cost + rightChecked.cost + 5⟩
  | formula@(.forallThing name body) =>
      let witness := firstFailureEnvCosted worldCount thingCount tables env .thing name body
      match witness.value with
      | some env' => Complexity.Costed.charge (witness.cost + 2) <|
          minimizeFailureCosted worldCount thingCount tables env' body
      | none => ⟨failedHere formula env, witness.cost + 3⟩
  | formula@(.forallWorld name body) =>
      let witness := firstFailureEnvCosted worldCount thingCount tables env .world name body
      match witness.value with
      | some env' => Complexity.Costed.charge (witness.cost + 2) <|
          minimizeFailureCosted worldCount thingCount tables env' body
      | none => ⟨failedHere formula env, witness.cost + 3⟩
  | formula@(.existsThing name body) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .thing name body
        match witness.value with
        | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 3) <|
            minimizeFailureCosted worldCount thingCount tables env' body
        | none => ⟨failedHere formula env, checked.cost + witness.cost + 4⟩
      else
        ⟨failedHere formula env, checked.cost + 3⟩
  | formula@(.existsWorld name body) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world name body
        match witness.value with
        | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 3) <|
            minimizeFailureCosted worldCount thingCount tables env' body
        | none => ⟨failedHere formula env, checked.cost + witness.cost + 4⟩
      else
        ⟨failedHere formula env, checked.cost + 3⟩
  | formula@(.box _ witnessWorld body) =>
      let witness := firstFailureEnvCosted worldCount thingCount tables env .world witnessWorld body
      match witness.value with
      | some env' => Complexity.Costed.charge (witness.cost + 2) <|
          minimizeFailureCosted worldCount thingCount tables env' body
      | none => ⟨failedHere formula env, witness.cost + 3⟩
  | formula@(.dia _ witnessWorld body) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world witnessWorld body
        match witness.value with
        | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 3) <|
            minimizeFailureCosted worldCount thingCount tables env' body
        | none => ⟨failedHere formula env, checked.cost + witness.cost + 4⟩
      else
        ⟨failedHere formula env, checked.cost + 3⟩

private theorem minimizeFailureCosted_spec
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).value =
      minimizeFailureSpec worldCount thingCount tables env formula := by
  fun_induction minimizeFailureCosted
  all_goals rw [minimizeFailureSpec.eq_def]
  all_goals
    simp_all (config := { zetaDelta := true }) [Complexity.Costed.charge_value]

/-- Structural bound on the environment stored in a minimized failure. The
disjunction case adds both recursively produced environments because that is
the only executable branch that concatenates them. -/
private def DiagFormula.failureEnvSizeBound (envSize : Nat) : DiagFormula → Nat
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => envSize
  | .not p => envSize + p.failureEnvSizeBound envSize
  | .and p q | .iff p q =>
      envSize + p.failureEnvSizeBound envSize + q.failureEnvSizeBound envSize
  | .or p q =>
      envSize + p.failureEnvSizeBound envSize + q.failureEnvSizeBound envSize
  | .imp _ q => envSize + q.failureEnvSizeBound envSize
  | .forallThing _ body | .forallWorld _ body | .existsThing _ body |
      .existsWorld _ body | .box _ _ body | .dia _ _ body =>
      envSize + body.failureEnvSizeBound (envSize + 1)

private theorem DiagFormula.le_failureEnvSizeBound
    (formula : DiagFormula) (envSize : Nat) :
    envSize ≤ formula.failureEnvSizeBound envSize := by
  induction formula generalizing envSize with
  | atom | eqThing | eqWorld => simp [failureEnvSizeBound]
  | not p ih => simp [failureEnvSizeBound]
  | and p q ihp ihq | or p q ihp ihq | iff p q ihp ihq =>
      simp [failureEnvSizeBound]
      omega
  | imp p q ihp ihq => simp [failureEnvSizeBound]
  | forallThing name body ih => simp [failureEnvSizeBound]
  | forallWorld name body ih => simp [failureEnvSizeBound]
  | existsThing name body ih => simp [failureEnvSizeBound]
  | existsWorld name body ih => simp [failureEnvSizeBound]
  | box currentWorld witnessWorld body ih => simp [failureEnvSizeBound]
  | dia currentWorld witnessWorld body ih => simp [failureEnvSizeBound]

private theorem DiagFormula.failureEnvSizeBound_mono
    (formula : DiagFormula) {smaller larger : Nat} (h : smaller ≤ larger) :
    formula.failureEnvSizeBound smaller ≤ formula.failureEnvSizeBound larger := by
  induction formula generalizing smaller larger with
  | atom | eqThing | eqWorld => simpa [failureEnvSizeBound]
  | not p ih =>
      simp only [failureEnvSizeBound]
      have hp := ih h
      omega
  | and p q ihp ihq | or p q ihp ihq | iff p q ihp ihq =>
      simp only [failureEnvSizeBound]
      have hp := ihp h
      have hq := ihq h
      omega
  | imp p q ihp ihq =>
      simp only [failureEnvSizeBound]
      have hq := ihq h
      omega
  | forallThing name body ih =>
      simp only [failureEnvSizeBound]
      have hbody := ih (Nat.add_le_add_right h 1)
      omega
  | forallWorld name body ih =>
      simp only [failureEnvSizeBound]
      have hbody := ih (Nat.add_le_add_right h 1)
      omega
  | existsThing name body ih =>
      simp only [failureEnvSizeBound]
      have hbody := ih (Nat.add_le_add_right h 1)
      omega
  | existsWorld name body ih =>
      simp only [failureEnvSizeBound]
      have hbody := ih (Nat.add_le_add_right h 1)
      omega
  | box currentWorld witnessWorld body ih =>
      simp only [failureEnvSizeBound]
      have hbody := ih (Nat.add_le_add_right h 1)
      omega
  | dia currentWorld witnessWorld body ih =>
      simp only [failureEnvSizeBound]
      have hbody := ih (Nat.add_le_add_right h 1)
      omega

private theorem minimizeFailureCosted_env_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).value.env.size ≤
      formula.failureEnvSizeBound env.size := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.failureEnvSizeBound, failedHere, withContext,
      Complexity.Costed.charge_value, Array.size_append]
  all_goals try
    have hsize := firstFailureEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
    omega
  all_goals try
    have hsize := firstSuccessEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
    omega
  all_goals try omega

private theorem minimizeFailureCosted_formula_nodeCount_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).value.formula.nodeCount ≤
      formula.nodeCount := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.nodeCount, failedHere, withContext, Complexity.Costed.charge_value]
  all_goals try omega

private theorem successTracesCosted_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesCosted worldCount thingCount tables env formula).value.size ≤
      formula.nodeCount := by
  unfold successTracesCosted
  simpa using successTracesIntoCosted_size_le
    worldCount thingCount tables env (#[] : Array DiagTrace) formula

private theorem successTracesCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesCosted worldCount thingCount tables env formula).cost ≤
      formula.successTraceCostBound worldCount thingCount tables env.size + 1 := by
  unfold successTracesCosted
  have h := successTracesIntoCosted_cost_le
    worldCount thingCount tables env (#[] : Array DiagTrace) formula
  simp only [Complexity.Costed.charge_cost]
  omega

private theorem successTracesSpec_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesSpec worldCount thingCount tables env formula).size ≤ formula.nodeCount := by
  rw [← successTracesCosted_value]
  exact successTracesCosted_size_le worldCount thingCount tables env formula

/-- Newly collected traces refer to subformulas and add only the quantified
variables on their paths. Existing entries retain their assumed size bounds.
Fixed limits let the second child of a conjunction reuse the first child's
accumulator without enlarging either limit. -/
private theorem successTracesIntoCosted_trace_bounds
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace) (formula : DiagFormula)
    (nodeLimit envLimit : Nat)
    (hNodes : formula.nodeCount ≤ nodeLimit)
    (hEnv : env.size + formula.nodeCount ≤ envLimit)
    (hOut : ∀ trace ∈ out,
      trace.formula.nodeCount ≤ nodeLimit ∧ trace.env.size ≤ envLimit) :
    ∀ trace ∈ (successTracesIntoCosted worldCount thingCount tables env out formula).value,
      trace.formula.nodeCount ≤ nodeLimit ∧ trace.env.size ≤ envLimit := by
  fun_induction successTracesIntoCosted generalizing nodeLimit envLimit
  all_goals
    simp_all (config := { zetaDelta := true }) [DiagFormula.nodeCount, Array.mem_push]
  all_goals try
    have hsize := firstSuccessEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
    grind [DiagFormula.nodeCount]
  all_goals try grind [DiagFormula.nodeCount]
  case case6 h ih2 ih1 =>
    exact ih1 nodeLimit envLimit (by omega) (by omega)
      (ih2 nodeLimit envLimit (by omega) (by omega) hOut)
  case case7 hLeft hChecked ih1 =>
    exact ih1 nodeLimit envLimit (by omega) (by omega) hOut
  case case8 hLeft hChecked ih1 =>
    exact ih1 nodeLimit envLimit (by omega) (by omega) hOut
  case case9 hAntecedent hChecked ih1 =>
    exact ih1 nodeLimit envLimit (by omega) (by omega) hOut

private theorem successTracesCosted_trace_bounds
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    ∀ trace ∈ (successTracesCosted worldCount thingCount tables env formula).value,
      trace.formula.nodeCount ≤ formula.nodeCount ∧
        trace.env.size ≤ env.size + formula.nodeCount := by
  exact successTracesIntoCosted_trace_bounds worldCount thingCount tables env #[] formula
    formula.nodeCount (env.size + formula.nodeCount) (by rfl) (by rfl) (by simp)

/-- Context concatenation joins trace arrays, not the environments inside
their entries. Each trace therefore keeps the original formula's node limit
and the initial environment size plus at most one binding per formula node. -/
private theorem minimizeFailureCosted_trace_bounds
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    ∀ trace ∈ MinimizedFailure.context (minimizeFailureCosted worldCount thingCount tables env formula).value,
      DiagFormula.nodeCount (DiagTrace.formula trace) ≤ DiagFormula.nodeCount formula ∧
        (DiagTrace.env trace).size ≤ env.size + DiagFormula.nodeCount formula := by
  have hs (env : Array (String × Nat)) (formula : DiagFormula) :
      ∀ trace ∈ successTracesSpec worldCount thingCount tables env formula,
        DiagFormula.nodeCount (DiagTrace.formula trace) ≤ DiagFormula.nodeCount formula ∧
          (DiagTrace.env trace).size ≤ env.size + DiagFormula.nodeCount formula := by
    rw [← successTracesCosted_value]
    exact successTracesCosted_trace_bounds _ _ _ _ _
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.nodeCount, failedHere, withContext, Complexity.Costed.charge_value, Array.mem_append]
  all_goals try
    have hsize := firstFailureEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
    grind [DiagFormula.nodeCount]
  all_goals try
    have hsize := firstSuccessEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
    grind [DiagFormula.nodeCount]
  all_goals grind [DiagFormula.nodeCount]

/-- Structural bound on explanatory traces retained by failure minimization.
The additive `nodeCount` terms correspond to successful subformulas that the
executable appends before the recursively minimized failure. -/
private def DiagFormula.failureContextSizeBound : DiagFormula → Nat
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => 0
  | .not p => p.failureContextSizeBound
  | .and p q => p.failureContextSizeBound + q.failureContextSizeBound + p.nodeCount
  | .or p q => p.failureContextSizeBound + q.failureContextSizeBound
  | .imp p q => q.failureContextSizeBound + p.nodeCount
  | .iff p q =>
      p.failureContextSizeBound + q.failureContextSizeBound + p.nodeCount + q.nodeCount
  | .forallThing _ body | .forallWorld _ body | .existsThing _ body |
      .existsWorld _ body | .box _ _ body | .dia _ _ body =>
      body.failureContextSizeBound

private theorem minimizeFailureCosted_context_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).value.context.size ≤
      formula.failureContextSizeBound := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.failureContextSizeBound, failedHere, withContext,
        Complexity.Costed.charge_value, Array.size_append]
  all_goals try omega
  case case20 hleft hright ih =>
    rename_i leftChecked rightChecked traces failure
    have htrace : traces.value.size ≤ _ :=
      successTracesCosted_size_le worldCount thingCount tables _ _
    rw [successTracesCosted_value] at htrace
    omega
  case case25 failure hchecked ih =>
    rename_i q checked traces
    have htrace : traces.value.size ≤ _ :=
      successTracesCosted_size_le worldCount thingCount tables _ _
    rw [successTracesCosted_value] at htrace
    omega
  case case27 hchecked hleft ih =>
    rename_i checked leftChecked traces failure
    have htrace : traces.value.size ≤ _ :=
      successTracesCosted_size_le worldCount thingCount tables _ _
    rw [successTracesCosted_value] at htrace
    omega
  case case28 hleft hright ih =>
    rename_i traces failure hchecked
    have htrace : traces.value.size ≤ _ :=
      successTracesCosted_size_le worldCount thingCount tables _ _
    rw [successTracesCosted_value] at htrace
    omega

/-- A compositional upper bound for the executable failure minimizer. Each
clause follows the corresponding branch of `minimizeFailureCosted`; it includes
formula evaluation, witness search, successful-context collection, recursive
minimization, and the charged array copies. -/
private def DiagFormula.failureMinimizeCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (envSize : Nat) :
    DiagFormula → Nat
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => 2
  | formula@(.not p) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        (match p with
        | .not q => q.failureMinimizeCostBound worldCount thingCount tables envSize
        | .forallThing _ body | .existsThing _ body =>
            firstMatchCostBound worldCount thingCount tables .thing envSize body +
              body.failureMinimizeCostBound worldCount thingCount tables (envSize + 1)
        | .forallWorld _ body | .existsWorld _ body | .box _ _ body | .dia _ _ body =>
            firstMatchCostBound worldCount thingCount tables .world envSize body +
              body.failureMinimizeCostBound worldCount thingCount tables (envSize + 1)
        | _ => 0) + 5
  | .and p q =>
      p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        q.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        p.failureMinimizeCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        3 * q.failureContextSizeBound + 6
  | formula@(.or p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.failureMinimizeCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        3 * q.failureEnvSizeBound envSize + 3 * q.failureContextSizeBound + 3
  | formula@(.imp p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        3 * q.failureContextSizeBound + 3
  | formula@(.iff p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        q.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.successTraceCostBound worldCount thingCount tables envSize +
        p.failureMinimizeCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        3 * p.failureContextSizeBound + 3 * q.failureContextSizeBound + 5
  | formula@(.forallThing _ body) | formula@(.existsThing _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .thing envSize body +
        body.failureMinimizeCostBound worldCount thingCount tables (envSize + 1) + 4
  | formula@(.forallWorld _ body) | formula@(.existsWorld _ body) |
      formula@(.box _ _ body) | formula@(.dia _ _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .world envSize body +
        body.failureMinimizeCostBound worldCount thingCount tables (envSize + 1) + 4

private theorem DiagFormula.not_evalCostBound_add_three_le_failureMinimizeCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (envSize : Nat)
    (p : DiagFormula) :
    (DiagFormula.not p).evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) envSize + 3 ≤
      (DiagFormula.not p).failureMinimizeCostBound worldCount thingCount tables envSize := by
  cases p <;> simp [failureMinimizeCostBound] <;> omega

private theorem evalDiagFormulaCosted_not_cost_add_three_le_failureMinimizeCostBound
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (p : DiagFormula) :
    (evalDiagFormulaCosted worldCount thingCount tables env (.not p)).cost + 3 ≤
      (DiagFormula.not p).failureMinimizeCostBound
        worldCount thingCount tables env.size := by
  have heval := evalDiagFormulaCosted_concrete_cost_le
    worldCount thingCount tables env (.not p)
  have hstruct := DiagFormula.not_evalCostBound_add_three_le_failureMinimizeCostBound
    worldCount thingCount tables env.size p
  omega

private theorem eval_firstFailure_rec_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env env' : Array (String × Nat)) (formula body : DiagFormula)
    (kind : DiagVarKind) (name : String) (evalResult : Bool)
    (_hEval : evalDiagFormula worldCount thingCount tables env formula = evalResult)
    (_ : firstFailureEnv worldCount thingCount tables env kind name body = some env')
    (hRec : (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1)) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost +
          (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost + 4 +
        (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) env.size +
        firstMatchCostBound worldCount thingCount tables kind env.size body +
        body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1) + 4 := by
  have heval := evalDiagFormulaCosted_concrete_cost_le worldCount thingCount tables env formula
  have hwitness := firstFailureEnvCosted_cost_le worldCount thingCount tables env kind name body
  unfold firstMatchCostBound
  omega

private theorem eval_firstSuccess_rec_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env env' : Array (String × Nat)) (formula body : DiagFormula)
    (kind : DiagVarKind) (name : String) (evalResult : Bool)
    (_hEval : evalDiagFormula worldCount thingCount tables env formula = evalResult)
    (_ : firstSuccessEnv worldCount thingCount tables env kind name body = some env')
    (hRec : (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1)) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost +
          (firstSuccessEnvCosted worldCount thingCount tables env kind name body).cost + 4 +
        (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) env.size +
        firstMatchCostBound worldCount thingCount tables kind env.size body +
        body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1) + 4 := by
  have heval := evalDiagFormulaCosted_concrete_cost_le worldCount thingCount tables env formula
  have hwitness := firstSuccessEnvCosted_cost_le worldCount thingCount tables env kind name body
  unfold firstMatchCostBound
  omega

private theorem firstFailure_rec_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env env' : Array (String × Nat)) (body : DiagFormula)
    (kind : DiagVarKind) (name : String)
    (_ : firstFailureEnv worldCount thingCount tables env kind name body = some env')
    (hRec : (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1)) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost + 2 +
        (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      firstMatchCostBound worldCount thingCount tables kind env.size body +
        body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1) + 2 := by
  have hwitness := firstFailureEnvCosted_cost_le worldCount thingCount tables env kind name body
  unfold firstMatchCostBound
  omega

private theorem eval_firstFailure_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula body : DiagFormula)
    (kind : DiagVarKind) (name : String) (evalResult : Bool)
    (result : Option (Array (String × Nat)))
    (_hEval : evalDiagFormula worldCount thingCount tables env formula = evalResult)
    (_hValue : firstFailureEnv worldCount thingCount tables env kind name body = result) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost +
        (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost ≤
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) env.size +
        firstMatchCostBound worldCount thingCount tables kind env.size body := by
  have heval := evalDiagFormulaCosted_concrete_cost_le worldCount thingCount tables env formula
  have hwitness := firstFailureEnvCosted_cost_le worldCount thingCount tables env kind name body
  unfold firstMatchCostBound
  omega

private theorem eval_firstSuccess_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula body : DiagFormula)
    (kind : DiagVarKind) (name : String) (evalResult : Bool)
    (result : Option (Array (String × Nat)))
    (_hEval : evalDiagFormula worldCount thingCount tables env formula = evalResult)
    (_hValue : firstSuccessEnv worldCount thingCount tables env kind name body = result) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost +
        (firstSuccessEnvCosted worldCount thingCount tables env kind name body).cost ≤
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) env.size +
        firstMatchCostBound worldCount thingCount tables kind env.size body := by
  have heval := evalDiagFormulaCosted_concrete_cost_le worldCount thingCount tables env formula
  have hwitness := firstSuccessEnvCosted_cost_le worldCount thingCount tables env kind name body
  unfold firstMatchCostBound
  omega

private theorem firstFailure_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (body : DiagFormula)
    (kind : DiagVarKind) (name : String) (result : Option (Array (String × Nat)))
    (_hValue : firstFailureEnv worldCount thingCount tables env kind name body = result) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost ≤
      firstMatchCostBound worldCount thingCount tables kind env.size body := by
  have hwitness := firstFailureEnvCosted_cost_le worldCount thingCount tables env kind name body
  unfold firstMatchCostBound
  omega
private theorem minimizeFailureCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).cost ≤
      formula.failureMinimizeCostBound worldCount thingCount tables env.size := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.failureMinimizeCostBound, Complexity.Costed.charge_cost]
  all_goals try
    grind [evalDiagFormulaCosted_concrete_cost_le,
      firstFailureEnvCosted_cost_le, firstSuccessEnvCosted_cost_le,
      successTracesCosted_cost_le, successTracesCosted_size_le,
      minimizeFailureCosted_env_size_le, minimizeFailureCosted_context_size_le,
      firstFailureEnv_some_size, firstSuccessEnv_some_size]
  all_goals try
    have hsize := firstFailureEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
  all_goals try
    have hsize := firstSuccessEnv_some_size _ _ _ _ _ _ _ _ (by assumption)
    simp_all
  all_goals try
    have hbound := firstFailure_rec_cost_le _ _ _ _ _ _ _ _
      (by assumption) (by assumption)
    omega
  case case6 hSome hchecked ih =>
    have hbound := eval_firstFailure_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case7 hNone hchecked =>
    have hbound := eval_firstFailure_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case8 hSome hchecked ih =>
    have hbound := eval_firstFailure_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case9 hNone hchecked =>
    have hbound := eval_firstFailure_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case10 hSome hchecked ih =>
    have hbound := eval_firstSuccess_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case11 hNone hchecked =>
    have hbound := eval_firstSuccess_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case12 hSome hchecked ih =>
    have hbound := eval_firstSuccess_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case13 hNone hchecked =>
    have hbound := eval_firstSuccess_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case14 hSome hchecked ih =>
    have hbound := eval_firstFailure_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case15 hNone hchecked =>
    have hbound := eval_firstFailure_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case16 hSome hchecked ih =>
    have hbound := eval_firstSuccess_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case17 hNone hchecked =>
    have hbound := eval_firstSuccess_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case4 hchecked =>
    exact evalDiagFormulaCosted_not_cost_add_three_le_failureMinimizeCostBound _ _ _ _ _
  case case31 hNone =>
    have hbound := firstFailure_cost_le _ _ _ _ _ _ _ _ hNone
    omega
  case case33 hNone =>
    have hbound := firstFailure_cost_le _ _ _ _ _ _ _ _ hNone
    omega
  case case34 hchecked hSome ih =>
    have hbound := eval_firstSuccess_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case35 hchecked hNone =>
    have hbound := eval_firstSuccess_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case37 hchecked hSome ih =>
    have hbound := eval_firstSuccess_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case38 hchecked hNone =>
    have hbound := eval_firstSuccess_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
  case case41 hNone =>
    have hbound := firstFailure_cost_le _ _ _ _ _ _ _ _ hNone
    omega
  case case42 hchecked hSome ih =>
    have hbound := eval_firstSuccess_rec_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hSome ih
    omega
  case case43 hchecked hNone =>
    have hbound := eval_firstSuccess_cost_le _ _ _ _ _ _ _ _ _ _ hchecked hNone
    omega
private def minimizeFailure
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : MinimizedFailure :=
  (minimizeFailureCosted worldCount thingCount tables env formula).value

@[simp] private theorem minimizeFailureCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).value =
      minimizeFailure worldCount thingCount tables env formula := rfl

/-!
## Source facts as diagnostic evidence

An atom supplies the relation and variable names to explain. Variable lookup
resolves the names once, then the source scan retains matching fact summaries
in order. Primitive and derived assertions have separate matching rules. Type
evidence uses instantiation targets; unary evidence also follows the taxonomy.
Value proofs preserve the selected rows. Cost proofs include matching and text,
while the enclosing report remains responsible for charging its calls here.
-/

private def scopeCoversWorldCosted
    (worldNames : Array Name) (scope : NamedFactScope) (worldIdx : Nat) :
    Complexity.Costed Bool := Complexity.Costed.charge 1 <|
  match scope with
  | .everywhere => .pure true
  | .at world => do
      let name ← indexedNameCosted worldNames worldIdx
      .tick (world == name) 1

@[simp] private theorem scopeCoversWorldCosted_value
    (worldNames : Array Name) (scope : NamedFactScope) (worldIdx : Nat) :
    (scopeCoversWorldCosted worldNames scope worldIdx).value =
      match scope with
      | .everywhere => true
      | .at world => world == indexedName worldNames worldIdx := by
  cases scope <;> simp [scopeCoversWorldCosted, Bind.bind, Complexity.Costed.bind_value]

private theorem scopeCoversWorldCosted_cost
    (worldNames : Array Name) (scope : NamedFactScope) (worldIdx : Nat) :
    (scopeCoversWorldCosted worldNames scope worldIdx).cost =
      match scope with
      | .everywhere => 1
      | .at _ => 6 := by
  cases scope <;> simp [scopeCoversWorldCosted, Bind.bind, Complexity.Costed.bind_cost]

private def scopeCoversWorld (worldNames : Array Name) (scope : NamedFactScope)
    (worldIdx : Nat) : Bool :=
  (scopeCoversWorldCosted worldNames scope worldIdx).value

/-- Search the fixed taxonomy's ordered ancestor fields directly. The search
stops at the first match, but ancestor construction runs in full and is charged.
No temporary compiled facts are needed for this membership question. -/
private def unaryFactImpliesCosted (source target : UnaryField) : Complexity.Costed Bool := do
  let fields ← Complexity.Taxonomy.ancestorsCosted source
  Complexity.anyArrayCosted fields fun field => .tick (field == target) 1

private theorem unaryFactImpliesCosted_value (source target : UnaryField) :
    (unaryFactImpliesCosted source target).value =
      (expandUnaryTaxonomyFact source 0 0).any (fun
        | .unary field _ _ => field == target
        | _ => false) := by
  rw [expandUnaryTaxonomyFact_eq_map, Array.any_map]
  simp [unaryFactImpliesCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.anyArrayCosted_eq_list, Complexity.anyListCosted_value,
    expandUnaryTaxonomyFields]

private theorem unaryFactImpliesCosted_cost_le (source target : UnaryField) :
    (unaryFactImpliesCosted source target).cost ≤ 234 := by
  have ancestors := Complexity.Taxonomy.ancestorsCosted_cost_le source
  have size := Complexity.Taxonomy.ancestors_size_le source
  have scan := Complexity.anyArrayCosted_cost_le
    (Complexity.Taxonomy.ancestors source) (fun field => .tick (field == target) 1)
    1 (by intros; rfl)
  simp only [unaryFactImpliesCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Taxonomy.ancestorsCosted_value]
  omega

private def unaryFactImplies (source target : UnaryField) : Bool :=
  (unaryFactImpliesCosted source target).value

-- Each fact is examined once, in source order. The callback charges matching
-- and text construction. The scan charges initialization, iteration, reads,
-- the Option test, and a write for each retained row. Duplicate rows remain.
private def collectNamedFactEvidenceCosted
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Complexity.Costed (Option String)) :
    Complexity.Costed (Array String) := Complexity.Costed.charge 1 <|
  Complexity.Costed.foldArray namedFacts #[] fun out fact => do
    let row ← render? fact
    Complexity.Costed.charge 1 <| match row with
    | none => .pure out
    | some text => .tick (out.push text) 1

private theorem collectNamedFactEvidenceCosted_value
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Complexity.Costed (Option String)) :
    (collectNamedFactEvidenceCosted namedFacts render?).value =
      (namedFacts.toList.filterMap fun fact => (render? fact).value).toArray := by
  have aux (facts : List NamedScopedFact) (out : Array String) :
      facts.foldl (fun out fact => match (render? fact).value with
        | none => out
        | some text => out.push text) out =
      out ++ (facts.filterMap fun fact => (render? fact).value).toArray := by
    induction facts generalizing out with
    | nil => simp
    | cons fact facts ih =>
        simp only [List.foldl_cons, List.filterMap_cons]
        cases (render? fact).value <;> rw [ih]
        simp
  have step (out : Array String) (fact : NamedScopedFact) :
      (do
        let row ← render? fact
        Complexity.Costed.charge 1 <| match row with
        | none => .pure out
        | some text => .tick (out.push text) 1).value =
      match (render? fact).value with
      | none => out
      | some text => out.push text := by
    cases h : (render? fact).value <;>
      simp [Bind.bind, Complexity.Costed.bind_value, h]
  simpa only [collectNamedFactEvidenceCosted, Complexity.Costed.charge_value,
    Complexity.Costed.foldArray_value, step, Array.foldl_toList,
    Array.empty_append] using aux namedFacts.toList #[]

private theorem collectNamedFactEvidenceCosted_cost
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Complexity.Costed (Option String)) :
    (collectNamedFactEvidenceCosted namedFacts render?).cost =
      1 + (namedFacts.toList.map fun fact =>
        (render? fact).cost + 3 + (if (render? fact).value.isSome then 1 else 0)).sum := by
  unfold collectNamedFactEvidenceCosted
  rw [Complexity.Costed.charge_cost,
    Complexity.Costed.foldArray_cost_eq_sum _ _ _
      (fun fact => (render? fact).cost + 1 +
        (if (render? fact).value.isSome then 1 else 0)) (by
          intro out fact
          cases h : (render? fact).value <;>
            simp [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
              h])]
  have arithmetic (c n : Nat) : c + 1 + n + 2 = c + 3 + n := by omega
  simp only [arithmetic]

private theorem collectNamedFactEvidenceCosted_cost_le
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Complexity.Costed (Option String))
    (perFact : Nat) (h : ∀ fact ∈ namedFacts, (render? fact).cost ≤ perFact) :
    (collectNamedFactEvidenceCosted namedFacts render?).cost ≤
      1 + namedFacts.size * (perFact + 4) := by
  have scan := Complexity.Costed.foldArray_cost_le namedFacts (#[] : Array String)
    (fun out fact => do
      let row ← render? fact
      Complexity.Costed.charge 1 <| match row with
      | none => .pure out
      | some text => .tick (out.push text) 1) (perFact + 2) (by
        intro out fact hf
        have hh := h fact hf
        cases hr : (render? fact).value <;>
          simp [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
            hr] <;> omega)
  simpa [collectNamedFactEvidenceCosted, Complexity.Costed.charge_cost,
    Nat.add_assoc] using Nat.add_le_add_left scan 1

-- The list collector is a proof specification. Production uses the counted
-- array scan, so correspondence proofs do not require a runtime list copy.
private def collectNamedFactEvidenceSpec
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Option String) : Array String :=
  (namedFacts.toList.filterMap render?).toArray

private theorem collectNamedFactEvidenceSpec_size_le
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Option String) :
    (collectNamedFactEvidenceSpec namedFacts render?).size ≤ namedFacts.size := by
  unfold collectNamedFactEvidenceSpec
  simpa using List.length_filterMap_le render? namedFacts.toList

private def unaryEvidenceSpec
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) : Array String :=
  let thing := indexedName thingNames thingIdx
  collectNamedFactEvidenceSpec namedFacts fun fact =>
    match fact with
    | .unary sourceField sourceThing scope =>
        if sourceThing == thing && scopeCoversWorld worldNames scope worldIdx &&
            unaryFactImplies sourceField field then
          let suffix :=
            if sourceField == field then ""
            else s!" (taxonomy expansion implies {field.toTableField})"
          some s!"{namedFactSummary fact}{suffix}"
        else none
    | _ => none

/-- Match one unary source fact in name, scope, then taxonomy order. Each false
test skips the remaining tests and all formatting. A matching fact retains its
surface name and gains a suffix only when taxonomy expansion supplies the goal. -/
private def unarySourceEvidenceCosted (worldNames : Array Name) (thing : String)
    (worldIdx : Nat) (field : UnaryField) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .unary sourceField sourceThing scope =>
      let matched := (Complexity.Costed.tick (sourceThing == thing) 1).andThen fun _ =>
        (scopeCoversWorldCosted worldNames scope worldIdx).andThen fun _ =>
          unaryFactImpliesCosted sourceField field
      Complexity.Costed.branch matched (fun _ => do
        let suffix := Complexity.Costed.charge 2 <|
          if sourceField == field then .pure ""
          else
            let text := Complexity.Costed.appendString (.pure " (taxonomy expansion implies ")
              (.tick field.toTableField 1)
            text.appendString (.pure ")")
        let text ← (namedFactSummaryCosted fact).appendString suffix
        Complexity.Costed.pure (some text)) (fun _ => .pure none)
  | _ => .pure none

private theorem unarySourceEvidenceCosted_value (worldNames : Array Name) (thing : String)
    (worldIdx : Nat) (field : UnaryField) (fact : NamedScopedFact) :
    (unarySourceEvidenceCosted worldNames thing worldIdx field fact).value =
      match fact with
      | .unary sourceField sourceThing scope =>
          if sourceThing == thing && scopeCoversWorld worldNames scope worldIdx &&
              unaryFactImplies sourceField field then
            let suffix := if sourceField == field then ""
              else s!" (taxonomy expansion implies {field.toTableField})"
            some s!"{namedFactSummary fact}{suffix}"
          else none
      | _ => none := by
  cases fact with
  | unary sourceField sourceThing scope =>
      by_cases h : sourceField == field
      all_goals
        simp [unarySourceEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
          scopeCoversWorld, unaryFactImplies, namedFactSummary, Bool.and_assoc, h]
        simp [toString]
  | _ => rfl

private theorem unarySourceEvidenceCosted_cost_le (worldNames : Array Name) (thing : String)
    (worldIdx : Nat) (field : UnaryField) (fact : NamedScopedFact) :
    (unarySourceEvidenceCosted worldNames thing worldIdx field fact).cost ≤ 266 := by
  cases fact with
  | unary sourceField sourceThing scope =>
      have hScope : (scopeCoversWorldCosted worldNames scope worldIdx).cost ≤ 6 := by
        rw [scopeCoversWorldCosted_cost]
        cases scope <;> simp
      have hMatches : ((Complexity.Costed.tick (sourceThing == thing) 1).andThen fun _ =>
          (scopeCoversWorldCosted worldNames scope worldIdx).andThen fun _ =>
            unaryFactImpliesCosted sourceField field).cost ≤ 243 := by
        apply Complexity.Costed.andThen_cost_le _ _ 1 241 (by rfl)
        exact Complexity.Costed.andThen_cost_le _ _ 6 234 hScope
          (unaryFactImpliesCosted_cost_le sourceField field)
      have hText := namedFactSummaryCosted_cost_le
        (NamedScopedFact.unary sourceField sourceThing scope)
      unfold unarySourceEvidenceCosted
      simp only [Complexity.Costed.charge_cost]
      change 1 + _ ≤ 1 + 265
      apply Nat.add_le_add_left
      refine Complexity.Costed.branch_cost_le _ _ _ 243 21 hMatches ?_ (by simp)
      simp only [Bind.bind, Complexity.Costed.bind_cost,
        Complexity.Costed.appendString_cost, Complexity.Costed.charge_cost,
        Complexity.Costed.pure_cost]
      split <;> simp <;> omega
  | _ => simp [unarySourceEvidenceCosted]

private def unaryEvidenceCosted
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) : Complexity.Costed (Array String) := do
  let thing ← indexedNameCosted thingNames thingIdx
  collectNamedFactEvidenceCosted namedFacts
    (unarySourceEvidenceCosted worldNames thing worldIdx field)

private theorem unaryEvidenceCosted_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) :
    (unaryEvidenceCosted worldNames thingNames namedFacts thingIdx worldIdx field).value =
      unaryEvidenceSpec worldNames thingNames namedFacts thingIdx worldIdx field := by
  simp [unaryEvidenceCosted, unaryEvidenceSpec, Bind.bind, Complexity.Costed.bind_value,
    collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    unarySourceEvidenceCosted_value]

private theorem unaryEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) :
    (unaryEvidenceCosted worldNames thingNames namedFacts thingIdx worldIdx field).cost ≤
      5 + 270 * namedFacts.size := by
  have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
    (unarySourceEvidenceCosted worldNames (indexedName thingNames thingIdx) worldIdx field)
    266 (by intro fact _; exact unarySourceEvidenceCosted_cost_le _ _ _ _ fact)
  simp only [unaryEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    indexedNameCosted_cost, indexedNameCosted_value]
  omega

private def atomEvidenceSpec
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) : DiagAtom → Array String
  | .unary field thing world =>
      unaryEvidenceSpec worldNames thingNames namedFacts
        (lookupVar env thing) (lookupVar env world) field
  | .derivedUnary field thing world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      let worldIdx := lookupVar env world
      collectNamedFactEvidenceSpec namedFacts fun fact => match fact with
        | .derived (.unary sourceField sourceThing) scope =>
            if sourceField == field && sourceThing == thingName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | .typeSem thing world =>
      let thingIdx := lookupVar env thing
      let worldIdx := lookupVar env world
      collectNamedFactEvidenceSpec namedFacts fun fact => match fact with
        | .binary .inst _ target scope =>
            if target == indexedName thingNames thingIdx && scopeCoversWorld worldNames scope worldIdx then
              some s!"{namedFactSummary fact} (makes {indexedName thingNames thingIdx} a possible type)"
            else none
        | _ => none
  | .binary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldIdx := lookupVar env world
      collectNamedFactEvidenceSpec namedFacts fun fact => match fact with
        | .binary sourceField sourceLeft sourceRight scope =>
            if sourceField == field && sourceLeft == leftName && sourceRight == rightName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | .derivedBinary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldIdx := lookupVar env world
      collectNamedFactEvidenceSpec namedFacts fun fact => match fact with
        | .derived (.binary sourceField sourceLeft sourceRight) scope =>
            if sourceField == field && sourceLeft == leftName && sourceRight == rightName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | .ternary field first second third world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let worldIdx := lookupVar env world
      collectNamedFactEvidenceSpec namedFacts fun fact => match fact with
        | .ternary sourceField sourceFirst sourceSecond sourceThird scope =>
            if sourceField == field && sourceFirst == firstName && sourceSecond == secondName &&
                sourceThird == thirdName && scopeCoversWorld worldNames scope worldIdx then
              some (namedFactSummary fact) else none
        | _ => none
  | .quaternary field first second third fourth world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let fourthName := indexedName thingNames (lookupVar env fourth)
      let worldIdx := lookupVar env world
      collectNamedFactEvidenceSpec namedFacts fun fact => match fact with
        | .derived (.quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth) scope =>
            if sourceField == field && sourceFirst == firstName && sourceSecond == secondName &&
                sourceThird == thirdName && sourceFourth == fourthName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | _ => #[]

private theorem atomEvidenceSpec_size_le_namedFacts
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (atomEvidenceSpec worldNames thingNames namedFacts env atom).size ≤ namedFacts.size := by
  cases atom <;> simp [atomEvidenceSpec,
    unaryEvidenceSpec, collectNamedFactEvidenceSpec_size_le]

/-- A source fact becomes an evidence row only after its counted condition
succeeds. Keeping rendering in the selected branch avoids text work on misses. -/
private def matchingSourceEvidenceCosted (condition : Complexity.Costed Bool)
    (fact : NamedScopedFact) : Complexity.Costed (Option String) :=
  Complexity.Costed.branch condition (fun _ => do
    let text ← namedFactSummaryCosted fact
    Complexity.Costed.pure (some text)) (fun _ => .pure none)

private theorem matchingSourceEvidenceCosted_value (condition : Complexity.Costed Bool)
    (fact : NamedScopedFact) :
    (matchingSourceEvidenceCosted condition fact).value =
      if condition.value then some (namedFactSummary fact) else none := by
  simp [matchingSourceEvidenceCosted, Bind.bind, Complexity.Costed.bind_value, namedFactSummary]

private theorem matchingSourceEvidenceCosted_cost_le (condition : Complexity.Costed Bool)
    (fact : NamedScopedFact) :
    (matchingSourceEvidenceCosted condition fact).cost ≤ condition.cost + 16 := by
  exact Complexity.Costed.branch_cost_le _ _ _ condition.cost 15 (by rfl)
    (by simpa [Bind.bind, Complexity.Costed.bind_cost] using namedFactSummaryCosted_cost_le fact)
    (by simp)

private def derivedUnarySourceEvidenceCosted (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (thingName : String) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .derived inner scope => Complexity.Costed.charge 1 <|
      match inner with
      | .unary sourceField sourceThing =>
          let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceThing == thingName) 1).andThen fun _ =>
              scopeCoversWorldCosted worldNames scope worldIdx
          matchingSourceEvidenceCosted condition fact
      | _ => .pure none
  | _ => .pure none

private theorem derivedUnarySourceEvidenceCosted_value (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (thingName : String) (fact : NamedScopedFact) :
    (derivedUnarySourceEvidenceCosted worldNames worldIdx field thingName fact).value =
      match fact with
      | .derived (.unary sourceField sourceThing) scope =>
          if sourceField == field && sourceThing == thingName && scopeCoversWorld worldNames scope worldIdx then
            some (namedFactSummary fact)
          else none
      | _ => none := by
  cases fact with
  | derived inner scope => cases inner <;> simp [derivedUnarySourceEvidenceCosted, matchingSourceEvidenceCosted_value,
      scopeCoversWorld, Bool.and_assoc]
  | _ => rfl

private def binarySourceEvidenceCosted (worldNames : Array Name) (worldIdx : Nat)
    (field : BinaryField) (leftName rightName : String) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .binary sourceField sourceLeft sourceRight scope =>
      let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
        (Complexity.Costed.tick (sourceLeft == leftName) 1).andThen fun _ =>
          (Complexity.Costed.tick (sourceRight == rightName) 1).andThen fun _ =>
            scopeCoversWorldCosted worldNames scope worldIdx
      matchingSourceEvidenceCosted condition fact
  | _ => .pure none

private theorem binarySourceEvidenceCosted_value (worldNames : Array Name) (worldIdx : Nat)
    (field : BinaryField) (leftName rightName : String) (fact : NamedScopedFact) :
    (binarySourceEvidenceCosted worldNames worldIdx field leftName rightName fact).value =
      match fact with
      | .binary sourceField sourceLeft sourceRight scope =>
          if sourceField == field && sourceLeft == leftName && sourceRight == rightName && scopeCoversWorld worldNames scope worldIdx then
            some (namedFactSummary fact)
          else none
      | _ => none := by
  cases fact with
  | binary sourceField sourceLeft sourceRight scope => simp [binarySourceEvidenceCosted, matchingSourceEvidenceCosted_value,
      scopeCoversWorld, Bool.and_assoc]
  | _ => rfl

private def derivedBinarySourceEvidenceCosted (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (leftName rightName : String) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .derived inner scope => Complexity.Costed.charge 1 <|
      match inner with
      | .binary sourceField sourceLeft sourceRight =>
          let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceLeft == leftName) 1).andThen fun _ =>
              (Complexity.Costed.tick (sourceRight == rightName) 1).andThen fun _ =>
                scopeCoversWorldCosted worldNames scope worldIdx
          matchingSourceEvidenceCosted condition fact
      | _ => .pure none
  | _ => .pure none

private theorem derivedBinarySourceEvidenceCosted_value (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (leftName rightName : String) (fact : NamedScopedFact) :
    (derivedBinarySourceEvidenceCosted worldNames worldIdx field leftName rightName fact).value =
      match fact with
      | .derived (.binary sourceField sourceLeft sourceRight) scope =>
          if sourceField == field && sourceLeft == leftName && sourceRight == rightName && scopeCoversWorld worldNames scope worldIdx then
            some (namedFactSummary fact)
          else none
      | _ => none := by
  cases fact with
  | derived inner scope => cases inner <;> simp [derivedBinarySourceEvidenceCosted, matchingSourceEvidenceCosted_value,
      scopeCoversWorld, Bool.and_assoc]
  | _ => rfl

private def ternarySourceEvidenceCosted (worldNames : Array Name) (worldIdx : Nat)
    (field : TernaryField) (firstName secondName thirdName : String) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .ternary sourceField sourceFirst sourceSecond sourceThird scope =>
      let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
        (Complexity.Costed.tick (sourceFirst == firstName) 1).andThen fun _ =>
          (Complexity.Costed.tick (sourceSecond == secondName) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceThird == thirdName) 1).andThen fun _ =>
              scopeCoversWorldCosted worldNames scope worldIdx
      matchingSourceEvidenceCosted condition fact
  | _ => .pure none

private theorem ternarySourceEvidenceCosted_value (worldNames : Array Name) (worldIdx : Nat)
    (field : TernaryField) (firstName secondName thirdName : String) (fact : NamedScopedFact) :
    (ternarySourceEvidenceCosted worldNames worldIdx field firstName secondName thirdName fact).value =
      match fact with
      | .ternary sourceField sourceFirst sourceSecond sourceThird scope =>
          if sourceField == field && sourceFirst == firstName && sourceSecond == secondName && sourceThird == thirdName && scopeCoversWorld worldNames scope worldIdx then
            some (namedFactSummary fact)
          else none
      | _ => none := by
  cases fact with
  | ternary sourceField sourceFirst sourceSecond sourceThird scope => simp [ternarySourceEvidenceCosted, matchingSourceEvidenceCosted_value,
      scopeCoversWorld, Bool.and_assoc]
  | _ => rfl

private def quaternarySourceEvidenceCosted (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (firstName secondName thirdName fourthName : String) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .derived inner scope => Complexity.Costed.charge 1 <|
      match inner with
      | .quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth =>
          let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceFirst == firstName) 1).andThen fun _ =>
              (Complexity.Costed.tick (sourceSecond == secondName) 1).andThen fun _ =>
                (Complexity.Costed.tick (sourceThird == thirdName) 1).andThen fun _ =>
                  (Complexity.Costed.tick (sourceFourth == fourthName) 1).andThen fun _ =>
                    scopeCoversWorldCosted worldNames scope worldIdx
          matchingSourceEvidenceCosted condition fact
      | _ => .pure none
  | _ => .pure none

private theorem quaternarySourceEvidenceCosted_value (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (firstName secondName thirdName fourthName : String) (fact : NamedScopedFact) :
    (quaternarySourceEvidenceCosted worldNames worldIdx field firstName secondName thirdName fourthName fact).value =
      match fact with
      | .derived (.quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth) scope =>
          if sourceField == field && sourceFirst == firstName && sourceSecond == secondName && sourceThird == thirdName && sourceFourth == fourthName && scopeCoversWorld worldNames scope worldIdx then
            some (namedFactSummary fact)
          else none
      | _ => none := by
  cases fact with
  | derived inner scope => cases inner <;> simp [quaternarySourceEvidenceCosted, matchingSourceEvidenceCosted_value,
      scopeCoversWorld, Bool.and_assoc]
  | _ => rfl

private def typeSemSourceEvidenceCosted (worldNames : Array Name) (worldIdx : Nat)
    (thingName : String) (fact : NamedScopedFact) :
    Complexity.Costed (Option String) := Complexity.Costed.charge 1 <|
  match fact with
  | .binary sourceField _ target scope => Complexity.Costed.charge 1 <|
      match sourceField with
      | .inst =>
          let condition := (Complexity.Costed.tick (target == thingName) 1).andThen fun _ =>
            scopeCoversWorldCosted worldNames scope worldIdx
          Complexity.Costed.branch condition (fun _ => do
            let text := (namedFactSummaryCosted fact).appendString (.pure " (makes ")
            let text := text.appendString (.pure thingName)
            let text ← text.appendString (.pure " a possible type)")
            Complexity.Costed.pure (some text)) (fun _ => .pure none)
      | _ => .pure none
  | _ => .pure none

private theorem typeSemSourceEvidenceCosted_value (worldNames : Array Name) (worldIdx : Nat)
    (thingName : String) (fact : NamedScopedFact) :
    (typeSemSourceEvidenceCosted worldNames worldIdx thingName fact).value =
      match fact with
      | .binary .inst _ target scope =>
          if target == thingName && scopeCoversWorld worldNames scope worldIdx then
            some s!"{namedFactSummary fact} (makes {thingName} a possible type)"
          else none
      | _ => none := by
  cases fact with
  | binary field left right scope => cases field <;> simp [typeSemSourceEvidenceCosted, Bind.bind,
          Complexity.Costed.bind_value, scopeCoversWorld, namedFactSummary, toString]
  | _ => rfl

-- The largest non-unary matcher has five comparisons and five Boolean tests,
-- a scope check costing six, two constructor tests, and row rendering costing
-- at most sixteen including its branch. The common bound is therefore 34.
private theorem derivedUnarySourceEvidenceCosted_cost_le (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (thingName : String) (fact : NamedScopedFact) :
    (derivedUnarySourceEvidenceCosted worldNames worldIdx field thingName fact).cost ≤ 34 := by
  cases fact with
  | derived inner scope =>
      cases inner with
      | unary sourceField sourceThing =>
          let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceThing == thingName) 1).andThen fun _ =>
              scopeCoversWorldCosted worldNames scope worldIdx
          have hCondition : condition.cost ≤ 10 := by
            dsimp only [condition]
            apply Complexity.Costed.andThen_cost_le _ _ 1 8 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 6 (by rfl)
            rw [scopeCoversWorldCosted_cost]
            cases scope <;> simp
          have row := matchingSourceEvidenceCosted_cost_le condition (NamedScopedFact.derived (.unary sourceField sourceThing) scope)
          change 1 + (1 + (matchingSourceEvidenceCosted condition (NamedScopedFact.derived (.unary sourceField sourceThing) scope)).cost) ≤ 34
          omega
      | _ => simp [derivedUnarySourceEvidenceCosted]
  | _ => simp [derivedUnarySourceEvidenceCosted]

private theorem binarySourceEvidenceCosted_cost_le (worldNames : Array Name) (worldIdx : Nat)
    (field : BinaryField) (leftName rightName : String) (fact : NamedScopedFact) :
    (binarySourceEvidenceCosted worldNames worldIdx field leftName rightName fact).cost ≤ 34 := by
  cases fact with
  | binary sourceField sourceLeft sourceRight scope =>
      let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
        (Complexity.Costed.tick (sourceLeft == leftName) 1).andThen fun _ =>
          (Complexity.Costed.tick (sourceRight == rightName) 1).andThen fun _ =>
            scopeCoversWorldCosted worldNames scope worldIdx
      have hCondition : condition.cost ≤ 12 := by
        dsimp only [condition]
        apply Complexity.Costed.andThen_cost_le _ _ 1 10 (by rfl)
        apply Complexity.Costed.andThen_cost_le _ _ 1 8 (by rfl)
        apply Complexity.Costed.andThen_cost_le _ _ 1 6 (by rfl)
        rw [scopeCoversWorldCosted_cost]
        cases scope <;> simp
      have row := matchingSourceEvidenceCosted_cost_le condition (NamedScopedFact.binary sourceField sourceLeft sourceRight scope)
      change 1 + (matchingSourceEvidenceCosted condition (NamedScopedFact.binary sourceField sourceLeft sourceRight scope)).cost ≤ 34
      omega
  | _ => simp [binarySourceEvidenceCosted]

private theorem derivedBinarySourceEvidenceCosted_cost_le (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (leftName rightName : String) (fact : NamedScopedFact) :
    (derivedBinarySourceEvidenceCosted worldNames worldIdx field leftName rightName fact).cost ≤ 34 := by
  cases fact with
  | derived inner scope =>
      cases inner with
      | binary sourceField sourceLeft sourceRight =>
          let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceLeft == leftName) 1).andThen fun _ =>
              (Complexity.Costed.tick (sourceRight == rightName) 1).andThen fun _ =>
                scopeCoversWorldCosted worldNames scope worldIdx
          have hCondition : condition.cost ≤ 12 := by
            dsimp only [condition]
            apply Complexity.Costed.andThen_cost_le _ _ 1 10 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 8 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 6 (by rfl)
            rw [scopeCoversWorldCosted_cost]
            cases scope <;> simp
          have row := matchingSourceEvidenceCosted_cost_le condition (NamedScopedFact.derived (.binary sourceField sourceLeft sourceRight) scope)
          change 1 + (1 + (matchingSourceEvidenceCosted condition (NamedScopedFact.derived (.binary sourceField sourceLeft sourceRight) scope)).cost) ≤ 34
          omega
      | _ => simp [derivedBinarySourceEvidenceCosted]
  | _ => simp [derivedBinarySourceEvidenceCosted]

private theorem ternarySourceEvidenceCosted_cost_le (worldNames : Array Name) (worldIdx : Nat)
    (field : TernaryField) (firstName secondName thirdName : String) (fact : NamedScopedFact) :
    (ternarySourceEvidenceCosted worldNames worldIdx field firstName secondName thirdName fact).cost ≤ 34 := by
  cases fact with
  | ternary sourceField sourceFirst sourceSecond sourceThird scope =>
      let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
        (Complexity.Costed.tick (sourceFirst == firstName) 1).andThen fun _ =>
          (Complexity.Costed.tick (sourceSecond == secondName) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceThird == thirdName) 1).andThen fun _ =>
              scopeCoversWorldCosted worldNames scope worldIdx
      have hCondition : condition.cost ≤ 14 := by
        dsimp only [condition]
        apply Complexity.Costed.andThen_cost_le _ _ 1 12 (by rfl)
        apply Complexity.Costed.andThen_cost_le _ _ 1 10 (by rfl)
        apply Complexity.Costed.andThen_cost_le _ _ 1 8 (by rfl)
        apply Complexity.Costed.andThen_cost_le _ _ 1 6 (by rfl)
        rw [scopeCoversWorldCosted_cost]
        cases scope <;> simp
      have row := matchingSourceEvidenceCosted_cost_le condition (NamedScopedFact.ternary sourceField sourceFirst sourceSecond sourceThird scope)
      change 1 + (matchingSourceEvidenceCosted condition (NamedScopedFact.ternary sourceField sourceFirst sourceSecond sourceThird scope)).cost ≤ 34
      omega
  | _ => simp [ternarySourceEvidenceCosted]

private theorem quaternarySourceEvidenceCosted_cost_le (worldNames : Array Name) (worldIdx : Nat)
    (field : String) (firstName secondName thirdName fourthName : String) (fact : NamedScopedFact) :
    (quaternarySourceEvidenceCosted worldNames worldIdx field firstName secondName thirdName fourthName fact).cost ≤ 34 := by
  cases fact with
  | derived inner scope =>
      cases inner with
      | quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth =>
          let condition := (Complexity.Costed.tick (sourceField == field) 1).andThen fun _ =>
            (Complexity.Costed.tick (sourceFirst == firstName) 1).andThen fun _ =>
              (Complexity.Costed.tick (sourceSecond == secondName) 1).andThen fun _ =>
                (Complexity.Costed.tick (sourceThird == thirdName) 1).andThen fun _ =>
                  (Complexity.Costed.tick (sourceFourth == fourthName) 1).andThen fun _ =>
                    scopeCoversWorldCosted worldNames scope worldIdx
          have hCondition : condition.cost ≤ 16 := by
            dsimp only [condition]
            apply Complexity.Costed.andThen_cost_le _ _ 1 14 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 12 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 10 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 8 (by rfl)
            apply Complexity.Costed.andThen_cost_le _ _ 1 6 (by rfl)
            rw [scopeCoversWorldCosted_cost]
            cases scope <;> simp
          have row := matchingSourceEvidenceCosted_cost_le condition (NamedScopedFact.derived (.quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth) scope)
          change 1 + (1 + (matchingSourceEvidenceCosted condition (NamedScopedFact.derived (.quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth) scope)).cost) ≤ 34
          omega
      | _ => simp [quaternarySourceEvidenceCosted]
  | _ => simp [quaternarySourceEvidenceCosted]

private theorem typeSemSourceEvidenceCosted_cost_le (worldNames : Array Name) (worldIdx : Nat)
    (thingName : String) (fact : NamedScopedFact) :
    (typeSemSourceEvidenceCosted worldNames worldIdx thingName fact).cost ≤ 34 := by
  cases fact with
  | binary sourceField left target scope =>
      cases sourceField with
      | inst =>
          let condition := (Complexity.Costed.tick (target == thingName) 1).andThen fun _ =>
            scopeCoversWorldCosted worldNames scope worldIdx
          have hCondition : condition.cost ≤ 8 := by
            dsimp only [condition]
            apply Complexity.Costed.andThen_cost_le _ _ 1 6 (by rfl)
            rw [scopeCoversWorldCosted_cost]
            cases scope <;> simp
          let render : Unit → Complexity.Costed (Option String) := (fun _ => do
            let text := (namedFactSummaryCosted (NamedScopedFact.binary .inst left target scope)).appendString (.pure " (makes ")
            let text := text.appendString (.pure thingName)
            let text ← text.appendString (.pure " a possible type)")
            Complexity.Costed.pure (some text))
          have hText := namedFactSummaryCosted_cost_le (NamedScopedFact.binary .inst left target scope)
          have row := Complexity.Costed.branch_cost_le condition render (fun _ => .pure none)
            8 18 hCondition (by
              simp only [render, Bind.bind, Complexity.Costed.bind_cost,
                Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
              omega) (by simp)
          change 1 + (1 + (Complexity.Costed.branch condition render (fun _ => .pure none)).cost) ≤ 34
          omega
      | _ => simp [typeSemSourceEvidenceCosted]
  | _ => simp [typeSemSourceEvidenceCosted]

/-- Resolve variables once, before the source scan. Each local result carries
its value and cost; the returned record adds those costs and the atom test. -/
private def atomEvidenceCosted
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) : DiagAtom → Complexity.Costed (Array String)
  | .unary field thing world =>
      let thingIdx := lookupVarCosted env thing
      let worldIdx := lookupVarCosted env world
      let rows := unaryEvidenceCosted worldNames thingNames namedFacts thingIdx.value worldIdx.value field
      ⟨rows.value, 1 + thingIdx.cost + worldIdx.cost + rows.cost⟩
  | .derivedUnary field thing world =>
      let thingName := renderDiagVariableCosted thingNames env thing
      let worldIdx := lookupVarCosted env world
      let rows := collectNamedFactEvidenceCosted namedFacts
        (derivedUnarySourceEvidenceCosted worldNames worldIdx.value field thingName.value)
      ⟨rows.value, 1 + thingName.cost + worldIdx.cost + rows.cost⟩
  | .binary field left right world =>
      let leftName := renderDiagVariableCosted thingNames env left
      let rightName := renderDiagVariableCosted thingNames env right
      let worldIdx := lookupVarCosted env world
      let rows := collectNamedFactEvidenceCosted namedFacts
        (binarySourceEvidenceCosted worldNames worldIdx.value field leftName.value rightName.value)
      ⟨rows.value, 1 + leftName.cost + rightName.cost + worldIdx.cost + rows.cost⟩
  | .derivedBinary field left right world =>
      let leftName := renderDiagVariableCosted thingNames env left
      let rightName := renderDiagVariableCosted thingNames env right
      let worldIdx := lookupVarCosted env world
      let rows := collectNamedFactEvidenceCosted namedFacts
        (derivedBinarySourceEvidenceCosted worldNames worldIdx.value field leftName.value rightName.value)
      ⟨rows.value, 1 + leftName.cost + rightName.cost + worldIdx.cost + rows.cost⟩
  | .ternary field first second third world =>
      let firstName := renderDiagVariableCosted thingNames env first
      let secondName := renderDiagVariableCosted thingNames env second
      let thirdName := renderDiagVariableCosted thingNames env third
      let worldIdx := lookupVarCosted env world
      let rows := collectNamedFactEvidenceCosted namedFacts
        (ternarySourceEvidenceCosted worldNames worldIdx.value field firstName.value secondName.value thirdName.value)
      ⟨rows.value, 1 + firstName.cost + secondName.cost + thirdName.cost + worldIdx.cost + rows.cost⟩
  | .quaternary field first second third fourth world =>
      let firstName := renderDiagVariableCosted thingNames env first
      let secondName := renderDiagVariableCosted thingNames env second
      let thirdName := renderDiagVariableCosted thingNames env third
      let fourthName := renderDiagVariableCosted thingNames env fourth
      let worldIdx := lookupVarCosted env world
      let rows := collectNamedFactEvidenceCosted namedFacts
        (quaternarySourceEvidenceCosted worldNames worldIdx.value field firstName.value secondName.value thirdName.value fourthName.value)
      ⟨rows.value, 1 + firstName.cost + secondName.cost + thirdName.cost + fourthName.cost + worldIdx.cost + rows.cost⟩
  | .typeSem thing world =>
      let thingName := renderDiagVariableCosted thingNames env thing
      let worldIdx := lookupVarCosted env world
      let rows := collectNamedFactEvidenceCosted namedFacts
        (typeSemSourceEvidenceCosted worldNames worldIdx.value thingName.value)
      ⟨rows.value, 1 + thingName.cost + worldIdx.cost + rows.cost⟩
  | .individualSem _ _ => .tick #[] 2

private theorem atomEvidenceCosted_unary_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (field : UnaryField) (thing world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.unary field thing world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.unary field thing world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, unaryEvidenceCosted_value, lookupVar]

private theorem atomEvidenceCosted_derivedUnary_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (field : String) (thing world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.derivedUnary field thing world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.derivedUnary field thing world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, renderDiagVariableCosted_value,
    lookupVar, collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    derivedUnarySourceEvidenceCosted_value]
  rfl

private theorem atomEvidenceCosted_binary_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (field : BinaryField) (left right world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.binary field left right world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.binary field left right world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, renderDiagVariableCosted_value,
    lookupVar, collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    binarySourceEvidenceCosted_value]
  rfl

private theorem atomEvidenceCosted_derivedBinary_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (field : String) (left right world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.derivedBinary field left right world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.derivedBinary field left right world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, renderDiagVariableCosted_value,
    lookupVar, collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    derivedBinarySourceEvidenceCosted_value]
  rfl

private theorem atomEvidenceCosted_ternary_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (field : TernaryField) (first second third world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.ternary field first second third world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.ternary field first second third world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, renderDiagVariableCosted_value,
    lookupVar, collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    ternarySourceEvidenceCosted_value]
  rfl

private theorem atomEvidenceCosted_quaternary_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (field : String) (first second third fourth world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.quaternary field first second third fourth world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.quaternary field first second third fourth world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, renderDiagVariableCosted_value,
    lookupVar, collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    quaternarySourceEvidenceCosted_value]
  rfl

private theorem atomEvidenceCosted_typeSem_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (thing world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.typeSem thing world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.typeSem thing world) := by
  simp only [atomEvidenceCosted, atomEvidenceSpec, renderDiagVariableCosted_value,
    lookupVar, collectNamedFactEvidenceSpec, collectNamedFactEvidenceCosted_value,
    typeSemSourceEvidenceCosted_value]
  rfl

private theorem atomEvidenceCosted_individualSem_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (thing world : String) :
    (atomEvidenceCosted worldNames thingNames namedFacts env (.individualSem thing world)).value =
      atomEvidenceSpec worldNames thingNames namedFacts env (.individualSem thing world) := by
  rfl

private theorem atomEvidenceCosted_value
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (atomEvidenceCosted worldNames thingNames namedFacts env atom).value =
      atomEvidenceSpec worldNames thingNames namedFacts env atom := by
  cases atom <;> simp only [atomEvidenceCosted_unary_value,
    atomEvidenceCosted_derivedUnary_value,
    atomEvidenceCosted_binary_value,
    atomEvidenceCosted_derivedBinary_value,
    atomEvidenceCosted_ternary_value,
    atomEvidenceCosted_quaternary_value,
    atomEvidenceCosted_typeSem_value,
    atomEvidenceCosted_individualSem_value]

/-- Uniform source-evidence bound. Environment lookup is paid once per
variable reference; source-fact matching contributes the linear fact term. -/
private def atomEvidenceCostBound (envSize factCount : Nat) : Nat :=
  20 * envSize + 23 + 270 * factCount

private theorem atomEvidenceCostBound_mono {e e' n n' : Nat} (he : e ≤ e') (hn : n ≤ n') :
    atomEvidenceCostBound e n ≤ atomEvidenceCostBound e' n' := by
  unfold atomEvidenceCostBound
  omega

private theorem atomEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (atomEvidenceCosted worldNames thingNames namedFacts env atom).cost ≤
      atomEvidenceCostBound env.size namedFacts.size := by
  unfold atomEvidenceCostBound
  cases atom with
  | unary field thing world =>
      have scan := unaryEvidenceCosted_cost_le worldNames thingNames namedFacts
        (lookupVarCosted env thing).value (lookupVarCosted env world).value field
      simp only [atomEvidenceCosted, lookupVarCosted_cost]
      omega
  | derivedUnary field thing world =>
      have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
        (derivedUnarySourceEvidenceCosted worldNames (lookupVarCosted env world).value
          field (renderDiagVariableCosted thingNames env thing).value) 34
        (by intro fact _; exact derivedUnarySourceEvidenceCosted_cost_le _ _ _ _ fact)
      simp only [atomEvidenceCosted, renderDiagVariableCosted_cost, lookupVarCosted_cost]
      omega
  | binary field left right world =>
      have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
        (binarySourceEvidenceCosted worldNames (lookupVarCosted env world).value
          field (renderDiagVariableCosted thingNames env left).value (renderDiagVariableCosted thingNames env right).value) 34
        (by intro fact _; exact binarySourceEvidenceCosted_cost_le _ _ _ _ _ fact)
      simp only [atomEvidenceCosted, renderDiagVariableCosted_cost, lookupVarCosted_cost]
      omega
  | derivedBinary field left right world =>
      have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
        (derivedBinarySourceEvidenceCosted worldNames (lookupVarCosted env world).value
          field (renderDiagVariableCosted thingNames env left).value (renderDiagVariableCosted thingNames env right).value) 34
        (by intro fact _; exact derivedBinarySourceEvidenceCosted_cost_le _ _ _ _ _ fact)
      simp only [atomEvidenceCosted, renderDiagVariableCosted_cost, lookupVarCosted_cost]
      omega
  | ternary field first second third world =>
      have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
        (ternarySourceEvidenceCosted worldNames (lookupVarCosted env world).value
          field (renderDiagVariableCosted thingNames env first).value (renderDiagVariableCosted thingNames env second).value (renderDiagVariableCosted thingNames env third).value) 34
        (by intro fact _; exact ternarySourceEvidenceCosted_cost_le _ _ _ _ _ _ fact)
      simp only [atomEvidenceCosted, renderDiagVariableCosted_cost, lookupVarCosted_cost]
      omega
  | quaternary field first second third fourth world =>
      have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
        (quaternarySourceEvidenceCosted worldNames (lookupVarCosted env world).value
          field (renderDiagVariableCosted thingNames env first).value (renderDiagVariableCosted thingNames env second).value (renderDiagVariableCosted thingNames env third).value (renderDiagVariableCosted thingNames env fourth).value) 34
        (by intro fact _; exact quaternarySourceEvidenceCosted_cost_le _ _ _ _ _ _ _ fact)
      simp only [atomEvidenceCosted, renderDiagVariableCosted_cost, lookupVarCosted_cost]
      omega
  | typeSem thing world =>
      have scan := collectNamedFactEvidenceCosted_cost_le namedFacts
        (typeSemSourceEvidenceCosted worldNames (lookupVarCosted env world).value
          (renderDiagVariableCosted thingNames env thing).value) 34
        (by intro fact _; exact typeSemSourceEvidenceCosted_cost_le _ _ _ fact)
      simp only [atomEvidenceCosted, renderDiagVariableCosted_cost, lookupVarCosted_cost]
      omega
  | individualSem => simp [atomEvidenceCosted]; omega

private def collectAtomsIntoSpec
    (out : Array DiagAtom) : DiagFormula → Array DiagAtom
  | .atom atom => out.push atom
  | .eqThing _ _ | .eqWorld _ _ => out
  | .not p => collectAtomsIntoSpec out p
  | .and p q | .or p q | .imp p q | .iff p q =>
      collectAtomsIntoSpec (collectAtomsIntoSpec out p) q
  | .forallThing _ body | .forallWorld _ body |
      .existsThing _ body | .existsWorld _ body |
      .box _ _ body | .dia _ _ body => collectAtomsIntoSpec out body

private theorem collectAtomsIntoSpec_size_le
    (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoSpec out formula).size ≤ out.size + formula.nodeCount := by
  induction formula generalizing out with
  | atom atom => simp [collectAtomsIntoSpec, DiagFormula.nodeCount]
  | eqThing | eqWorld => simp [collectAtomsIntoSpec, DiagFormula.nodeCount]
  | not p ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega
  | and p q ihp ihq | or p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have hp := ihp out
      have hq := ihq (collectAtomsIntoSpec out p)
      omega
  | forallThing name body ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega
  | forallWorld name body ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega
  | existsThing name body ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega
  | existsWorld name body ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega
  | box currentWorld witnessWorld body ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega
  | dia currentWorld witnessWorld body ih =>
      simp only [collectAtomsIntoSpec, DiagFormula.nodeCount]
      have h := ih out
      omega

/-- Collect the atoms written in the formula, retaining order and duplicates.
Quantifiers contribute their body once, not once per model element. One
operation selects each node, and each atom adds one output-array write. -/
private def collectAtomsIntoCosted (out : Array DiagAtom) (formula : DiagFormula) :
    Complexity.Costed (Array DiagAtom) :=
  Complexity.Costed.charge 1 <| match formula with
  | .atom atom => Complexity.Costed.tick (out.push atom) 1
  | .eqThing _ _ | .eqWorld _ _ => .pure out
  | .not p => collectAtomsIntoCosted out p
  | .and p q | .or p q | .imp p q | .iff p q => do
      let out ← collectAtomsIntoCosted out p
      collectAtomsIntoCosted out q
  | .forallThing _ body | .forallWorld _ body |
      .existsThing _ body | .existsWorld _ body |
      .box _ _ body | .dia _ _ body => collectAtomsIntoCosted out body
termination_by formula.nodeCount
decreasing_by all_goals simp_all [DiagFormula.nodeCount] <;> omega

private theorem collectAtomsIntoCosted_value (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoCosted out formula).value = collectAtomsIntoSpec out formula := by
  induction formula generalizing out <;>
    simp_all only [collectAtomsIntoCosted, collectAtomsIntoSpec,
      Complexity.Costed.charge_value, Complexity.Costed.tick_value,
      Complexity.Costed.pure_value, Bind.bind, Complexity.Costed.bind_value]

private theorem collectAtomsIntoCosted_cost_le (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoCosted out formula).cost ≤ 2 * formula.nodeCount := by
  induction formula generalizing out <;>
    simp_all only [collectAtomsIntoCosted, Complexity.Costed.charge_cost,
      Complexity.Costed.tick_cost, Complexity.Costed.pure_cost,
      Bind.bind, Complexity.Costed.bind_cost, DiagFormula.nodeCount] <;> grind

/-- The count consists exactly of visited nodes and newly appended atoms.
Keeping the initial size on the left avoids truncated natural subtraction. -/
private theorem collectAtomsIntoCosted_cost_eq_nodes_and_writes
    (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoCosted out formula).cost + out.size =
      formula.nodeCount + (collectAtomsIntoCosted out formula).value.size := by
  induction formula generalizing out <;>
    simp_all only [collectAtomsIntoCosted, Complexity.Costed.charge_cost,
      Complexity.Costed.charge_value, Complexity.Costed.tick_cost,
      Complexity.Costed.tick_value, Complexity.Costed.pure_cost,
      Complexity.Costed.pure_value, Bind.bind, Complexity.Costed.bind_cost,
      Complexity.Costed.bind_value, DiagFormula.nodeCount, Array.size_push] <;> grind

private theorem collectAtomsIntoCosted_size_le (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsIntoCosted out formula).value.size ≤ out.size + formula.nodeCount := by
  simpa only [collectAtomsIntoCosted_value] using
    collectAtomsIntoSpec_size_le out formula

private def collectAtomsCosted (formula : DiagFormula) : Complexity.Costed (Array DiagAtom) :=
  Complexity.Costed.charge 1 (collectAtomsIntoCosted #[] formula)

private theorem collectAtomsCosted_cost_le (formula : DiagFormula) :
    (collectAtomsCosted formula).cost ≤ 2 * formula.nodeCount + 1 := by
  have h := collectAtomsIntoCosted_cost_le #[] formula
  simp only [collectAtomsCosted, Complexity.Costed.charge_cost]
  omega

private theorem collectAtomsCosted_size_le (formula : DiagFormula) :
    (collectAtomsCosted formula).value.size ≤ formula.nodeCount := by
  simpa only [collectAtomsCosted, Complexity.Costed.charge_value,
    collectAtomsIntoCosted_value, Array.size_empty, Nat.zero_add] using
    collectAtomsIntoSpec_size_le (#[] : Array DiagAtom) formula

private def failingAtomsIntoSpec
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) :
    DiagFormula → Array DiagAtom
  | .atom atom =>
      if evalDiagAtom worldCount thingCount tables env atom then out else out.push atom
  | .eqThing _ _ | .eqWorld _ _ => out
  | .not p =>
      if evalDiagFormula worldCount thingCount tables env (.not p) then out else
        match p with
        | .atom atom => out.push atom
        | _ => out
  | .and p q =>
      failingAtomsIntoSpec worldCount thingCount tables env
        (failingAtomsIntoSpec worldCount thingCount tables env out p) q
  | .or p q =>
      if evalDiagFormula worldCount thingCount tables env (.or p q) then out else
        failingAtomsIntoSpec worldCount thingCount tables env
          (failingAtomsIntoSpec worldCount thingCount tables env out p) q
  | .imp p q =>
      if evalDiagFormula worldCount thingCount tables env (.imp p q) then out else
        failingAtomsIntoSpec worldCount thingCount tables env (collectAtomsIntoSpec out p) q
  | .iff p q =>
      if evalDiagFormula worldCount thingCount tables env (.iff p q) then out else
        failingAtomsIntoSpec worldCount thingCount tables env
          (failingAtomsIntoSpec worldCount thingCount tables env out p) q
  | .forallThing name body =>
      Id.run do
        let mut out := out
        for x in [:thingCount] do
          out := failingAtomsIntoSpec worldCount thingCount tables
            (env.push (name, x)) out body
        return out
  | .forallWorld name body =>
      Id.run do
        let mut out := out
        for w in [:worldCount] do
          out := failingAtomsIntoSpec worldCount thingCount tables
            (env.push (name, w)) out body
        return out
  | .existsThing name body =>
      if evalDiagFormula worldCount thingCount tables env (.existsThing name body) then out else
        Id.run do
          let mut out := out
          for x in [:thingCount] do
            out := failingAtomsIntoSpec worldCount thingCount tables
              (env.push (name, x)) out body
          return out
  | .existsWorld name body =>
      if evalDiagFormula worldCount thingCount tables env (.existsWorld name body) then out else
        Id.run do
          let mut out := out
          for w in [:worldCount] do
            out := failingAtomsIntoSpec worldCount thingCount tables
              (env.push (name, w)) out body
          return out
  | .box _currentWorld witnessWorld body =>
      (List.range worldCount).foldl (fun out w =>
        let env' := env.push (witnessWorld, w)
        if !evalDiagFormula worldCount thingCount tables env' body then
          failingAtomsIntoSpec worldCount thingCount tables env' out body
        else out) out
  | .dia currentWorld witnessWorld body =>
      if evalDiagFormula worldCount thingCount tables env (.dia currentWorld witnessWorld body) then out else
        Id.run do
          let mut out := out
          for w in [:worldCount] do
            out := failingAtomsIntoSpec worldCount thingCount tables
              (env.push (witnessWorld, w)) out body
          return out
termination_by formula => formula.nodeCount
decreasing_by
  all_goals simp only [DiagFormula.nodeCount]
  all_goals omega

private def failingAtomsSpec
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Array DiagAtom :=
  failingAtomsIntoSpec worldCount thingCount tables env #[] formula

private def DiagFormula.failingAtomCountBound
    (worldCount thingCount : Nat) : DiagFormula → Nat
  | .atom _ => 1
  | .eqThing _ _ | .eqWorld _ _ => 0
  | .not _ => 1
  | .and p q | .or p q | .iff p q =>
      p.failingAtomCountBound worldCount thingCount +
        q.failingAtomCountBound worldCount thingCount
  | .imp p q => p.nodeCount + q.failingAtomCountBound worldCount thingCount
  | .forallThing _ body | .existsThing _ body =>
      thingCount * body.failingAtomCountBound worldCount thingCount
  | .forallWorld _ body | .existsWorld _ body | .box _ _ body | .dia _ _ body =>
      worldCount * body.failingAtomCountBound worldCount thingCount

private def DiagFormula.failureAtomEnumerationBound
    (worldCount thingCount : Nat) : DiagFormula → Nat
  | formula@(.atom _) | formula@(.eqThing _ _) | formula@(.eqWorld _ _) =>
      formula.failingAtomCountBound worldCount thingCount
  | formula@(.not p) =>
      formula.failingAtomCountBound worldCount thingCount +
        p.failureAtomEnumerationBound worldCount thingCount
  | formula@(.and p q) | formula@(.or p q) | formula@(.imp p q) | formula@(.iff p q) =>
      formula.failingAtomCountBound worldCount thingCount +
        p.failureAtomEnumerationBound worldCount thingCount +
        q.failureAtomEnumerationBound worldCount thingCount
  | formula@(.forallThing _ body) | formula@(.forallWorld _ body) |
      formula@(.existsThing _ body) | formula@(.existsWorld _ body) |
      formula@(.box _ _ body) | formula@(.dia _ _ body) =>
      formula.failingAtomCountBound worldCount thingCount +
        body.failureAtomEnumerationBound worldCount thingCount

private theorem minimizeFailureCosted_failingAtomCountBound_le_failureEnumeration
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (minimizeFailureCosted worldCount thingCount tables env formula).value.formula.failingAtomCountBound
        worldCount thingCount ≤ formula.failureAtomEnumerationBound worldCount thingCount := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.failureAtomEnumerationBound, DiagFormula.failingAtomCountBound, failedHere, withContext,
      Complexity.Costed.charge_value]
  all_goals try omega

private theorem foldlArraySize_le
    {α β : Type} (items : List α) (out : Array β)
    (step : Array β → α → Array β) (increment : Nat)
    (hstep : ∀ item acc, (step acc item).size ≤ acc.size + increment) :
    (items.foldl step out).size ≤ out.size + items.length * increment := by
  induction items generalizing out with
  | nil => simp
  | cons item items ih =>
      simp only [List.foldl, List.length_cons]
      have hhead := hstep item out
      have htail := ih (step out item)
      rw [Nat.add_mul]
      simp only [Nat.one_mul]
      omega

private theorem foldlRangeFromZeroSize_le
    {β : Type} (count : Nat) (out : Array β)
    (step : Array β → Nat → Array β) (increment : Nat)
    (hstep : ∀ item acc, (step acc item).size ≤ acc.size + increment) :
    ((List.range' 0 count).foldl step out).size ≤ out.size + count * increment := by
  simpa using foldlArraySize_le (List.range' 0 count) out step increment hstep

private theorem foldlRangeSize_le
    {β : Type} (count : Nat) (out : Array β)
    (step : Array β → Nat → Array β) (increment : Nat)
    (hstep : ∀ item acc, (step acc item).size ≤ acc.size + increment) :
    ((List.range count).foldl step out).size ≤ out.size + count * increment := by
  simpa using foldlArraySize_le (List.range count) out step increment hstep

private theorem failingAfterCollectSpec_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (p q : DiagFormula)
    (hrec : (failingAtomsIntoSpec worldCount thingCount tables env
      (collectAtomsIntoSpec out p) q).size ≤
        (collectAtomsIntoSpec out p).size + q.failingAtomCountBound worldCount thingCount) :
    (failingAtomsIntoSpec worldCount thingCount tables env
      (collectAtomsIntoSpec out p) q).size ≤
        out.size + (p.nodeCount + q.failingAtomCountBound worldCount thingCount) := by
  have hcollect := collectAtomsIntoSpec_size_le out p
  omega

private theorem failingAtomsIntoSpec_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoSpec worldCount thingCount tables env out formula).size ≤
      out.size + formula.failingAtomCountBound worldCount thingCount := by
  fun_induction failingAtomsIntoSpec
  all_goals simp_all [DiagFormula.failingAtomCountBound]
  all_goals try omega
  case case12 =>
    apply failingAfterCollectSpec_size_le
    assumption
  case case15 | case16 | case18 | case20 | case23 =>
    apply foldlRangeFromZeroSize_le
    intro item acc
    apply_assumption
  case case21 =>
    apply foldlRangeSize_le
    intro item acc
    split <;> simp_all

private theorem failingAtomsSpec_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsSpec worldCount thingCount tables env formula).size ≤
      formula.failingAtomCountBound worldCount thingCount := by
  unfold failingAtomsSpec
  simpa using failingAtomsIntoSpec_size_le worldCount thingCount tables env #[] formula

/-- Discover failing atoms in formula and ascending domain order. The numeric
fold avoids an allocated domain list. Evaluation stays short-circuiting: a
successful existential or disjunction skips its failing-atom traversal.
The cost includes evaluations even when they produce no evidence. -/
private def failingAtomsIntoCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    Complexity.Costed (Array DiagAtom) :=
  Complexity.Costed.charge 1 <| match formula with
  | .atom atom => do
      let checked ← evalDiagAtomCosted worldCount thingCount tables env atom
      Complexity.Costed.charge 1 <| if checked then .pure out else .tick (out.push atom) 1
  | .eqThing _ _ | .eqWorld _ _ => .pure out
  | .not p => do
      let checked ← evalDiagFormulaCosted worldCount thingCount tables env (.not p)
      Complexity.Costed.charge 1 <| if checked then .pure out else
        Complexity.Costed.charge 1 <| match p with
        | .atom atom => .tick (out.push atom) 1
        | _ => .pure out
  | .and p q => do
      let out ← failingAtomsIntoCosted worldCount thingCount tables env out p
      failingAtomsIntoCosted worldCount thingCount tables env out q
  | .or p q | .iff p q => do
      let checked ← evalDiagFormulaCosted worldCount thingCount tables env formula
      Complexity.Costed.charge 1 <| if checked then .pure out else do
        let out ← failingAtomsIntoCosted worldCount thingCount tables env out p
        failingAtomsIntoCosted worldCount thingCount tables env out q
  | .imp p q => do
      let checked ← evalDiagFormulaCosted worldCount thingCount tables env formula
      Complexity.Costed.charge 1 <| if checked then .pure out else do
        let out ← collectAtomsIntoCosted out p
        failingAtomsIntoCosted worldCount thingCount tables env out q
  | .forallThing name body =>
      foldDiagDomainCosted 0 thingCount out (fun _ => false) fun out x =>
        Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, x)) out body
  | .forallWorld name body =>
      foldDiagDomainCosted 0 worldCount out (fun _ => false) fun out w =>
        Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, w)) out body
  | .existsThing name body => do
      let checked ← evalDiagFormulaCosted worldCount thingCount tables env formula
      Complexity.Costed.charge 1 <| if checked then .pure out else
        foldDiagDomainCosted 0 thingCount out (fun _ => false) fun out x =>
          Complexity.Costed.charge 1 <|
            failingAtomsIntoCosted worldCount thingCount tables (env.push (name, x)) out body
  | .existsWorld name body | .dia _ name body => do
      let checked ← evalDiagFormulaCosted worldCount thingCount tables env formula
      Complexity.Costed.charge 1 <| if checked then .pure out else
        foldDiagDomainCosted 0 worldCount out (fun _ => false) fun out w =>
          Complexity.Costed.charge 1 <|
            failingAtomsIntoCosted worldCount thingCount tables (env.push (name, w)) out body
  | .box _ name body =>
      foldDiagDomainCosted 0 worldCount out (fun _ => false) fun out w => do
        let nextEnv ← Complexity.Costed.tick (env.push (name, w)) 1
        let checked ← evalDiagFormulaCosted worldCount thingCount tables nextEnv body
        Complexity.Costed.charge 2 <| if !checked then
          failingAtomsIntoCosted worldCount thingCount tables nextEnv out body
        else .pure out
termination_by formula.nodeCount
decreasing_by all_goals simp_all [DiagFormula.nodeCount] <;> omega

private theorem failingAtomsIntoCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoCosted worldCount thingCount tables env out formula).value =
      failingAtomsIntoSpec worldCount thingCount tables env out formula := by
  induction formula generalizing env out with
  | not p _ =>
      cases p <;>
        simp only [failingAtomsIntoCosted, failingAtomsIntoSpec, Bind.bind,
          Complexity.Costed.bind_value, Complexity.Costed.charge_value,
          evalDiagFormulaCosted_value]
      all_goals split <;> simp_all
  | box currentWorld name body ih =>
      simp only [failingAtomsIntoCosted, failingAtomsIntoSpec,
        Complexity.Costed.charge_value, foldDiagDomainCosted_value,
        Bool.false_eq_true, ↓reduceIte, Bind.bind, Complexity.Costed.bind_value,
        Complexity.Costed.tick_value, evalDiagFormulaCosted_value,
        ← List.range_eq_range']
      congr 1
      funext state i
      split <;> simp_all
  | _ =>
      (try simp_all [failingAtomsIntoCosted, failingAtomsIntoSpec, foldDiagDomainCosted_value,
        Bind.bind, Complexity.Costed.bind_value, ← List.range_eq_range']) <;>
      first
      | rfl
      | split <;> simp_all [foldDiagDomainCosted_value,
          Complexity.Costed.bind_value, collectAtomsIntoCosted_value,
          ← List.range_eq_range'] <;> rfl

/-- Bound failing-atom discovery by formula structure and model dimensions.
Each evaluation has its own structural bound. A quantifier multiplies its
body cost by its domain size, at an environment size increased by one.
This is not a uniform polynomial in unrestricted formula size. -/
private def DiagFormula.failingAtomsCostBound
    (worldCount thingCount : Nat) (atomBound : Nat → Nat) (envSize : Nat) :
    DiagFormula → Nat
  | .atom _ => atomBound envSize + 3
  | .eqThing _ _ | .eqWorld _ _ => 1
  | formula@(.not _) => formula.evalCostBound worldCount thingCount atomBound envSize + 4
  | .and p q =>
      p.failingAtomsCostBound worldCount thingCount atomBound envSize +
        q.failingAtomsCostBound worldCount thingCount atomBound envSize + 1
  | formula@(.or p q) | formula@(.iff p q) =>
      formula.evalCostBound worldCount thingCount atomBound envSize +
        p.failingAtomsCostBound worldCount thingCount atomBound envSize +
        q.failingAtomsCostBound worldCount thingCount atomBound envSize + 2
  | formula@(.imp p q) =>
      formula.evalCostBound worldCount thingCount atomBound envSize + 2 * p.nodeCount +
        q.failingAtomsCostBound worldCount thingCount atomBound envSize + 2
  | .forallThing _ body =>
      thingCount * (body.failingAtomsCostBound worldCount thingCount atomBound (envSize + 1) + 4) + 1
  | .forallWorld _ body =>
      worldCount * (body.failingAtomsCostBound worldCount thingCount atomBound (envSize + 1) + 4) + 1
  | formula@(.existsThing _ body) =>
      formula.evalCostBound worldCount thingCount atomBound envSize +
        thingCount * (body.failingAtomsCostBound worldCount thingCount atomBound (envSize + 1) + 4) + 2
  | formula@(.existsWorld _ body) | formula@(.dia _ _ body) =>
      formula.evalCostBound worldCount thingCount atomBound envSize +
        worldCount * (body.failingAtomsCostBound worldCount thingCount atomBound (envSize + 1) + 4) + 2
  | .box _ _ body =>
      worldCount * (body.evalCostBound worldCount thingCount atomBound (envSize + 1) +
        body.failingAtomsCostBound worldCount thingCount atomBound (envSize + 1) + 6) + 1

private theorem failingAtomsIntoCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoCosted worldCount thingCount tables env out formula).cost ≤
      formula.failingAtomsCostBound worldCount thingCount atomBound env.size := by
  have heval := evalDiagFormulaCosted_cost_le worldCount thingCount tables atomBound hAtom
  induction formula generalizing env out with
  | atom atom =>
      have h := hAtom env atom
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.tick_cost] <;> omega
  | eqThing | eqWorld => simp [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound]
  | not p _ =>
      have h := heval env (.not p)
      cases p <;>
        simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
          Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost] <;>
        split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.charge_cost,
          Complexity.Costed.tick_cost] <;> omega
  | and p q ihp ihq =>
      have hp := ihp env out
      have hq := ihq env (failingAtomsIntoCosted worldCount thingCount tables env out p).value
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      omega
  | or p q ihp ihq =>
      have h := heval env (.or p q)
      have hp := ihp env out
      have hq := ihq env (failingAtomsIntoCosted worldCount thingCount tables env out p).value
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.bind_cost] <;> omega
  | iff p q ihp ihq =>
      have h := heval env (.iff p q)
      have hp := ihp env out
      have hq := ihq env (failingAtomsIntoCosted worldCount thingCount tables env out p).value
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.bind_cost] <;> omega
  | imp p q _ ihq =>
      have h := heval env (.imp p q)
      have hp := collectAtomsIntoCosted_cost_le out p
      have hq := ihq env (collectAtomsIntoCosted out p).value
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.bind_cost] <;> omega
  | forallThing name body ih =>
      have scan := foldDiagDomainCosted_cost_le 0 thingCount out (fun _ => false)
        (fun out i => Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, i)) out body)
        (body.failingAtomsCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro out i _ _
          have h := ih (env.push (name, i)) out
          simp only [Array.size_push] at h
          simp only [Complexity.Costed.charge_cost]
          omega)
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost]
      simp only [Nat.add_assoc, Nat.reduceAdd] at scan ⊢
      omega
  | forallWorld name body ih =>
      have scan := foldDiagDomainCosted_cost_le 0 worldCount out (fun _ => false)
        (fun out i => Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, i)) out body)
        (body.failingAtomsCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro out i _ _
          have h := ih (env.push (name, i)) out
          simp only [Array.size_push] at h
          simp only [Complexity.Costed.charge_cost]
          omega)
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost]
      simp only [Nat.add_assoc, Nat.reduceAdd] at scan ⊢
      omega
  | existsThing name body ih =>
      have h := heval env (.existsThing name body)
      have scan := foldDiagDomainCosted_cost_le 0 thingCount out (fun _ => false)
        (fun out i => Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, i)) out body)
        (body.failingAtomsCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro out i _ _
          have hb := ih (env.push (name, i)) out
          simp only [Array.size_push] at hb
          simp only [Complexity.Costed.charge_cost]
          omega)
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      simp only [Nat.add_assoc, Nat.reduceAdd] at scan ⊢
      split <;> (try simp only [Complexity.Costed.pure_cost]) <;> omega
  | existsWorld name body ih =>
      have h := heval env (.existsWorld name body)
      have scan := foldDiagDomainCosted_cost_le 0 worldCount out (fun _ => false)
        (fun out i => Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, i)) out body)
        (body.failingAtomsCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro out i _ _
          have hb := ih (env.push (name, i)) out
          simp only [Array.size_push] at hb
          simp only [Complexity.Costed.charge_cost]
          omega)
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      simp only [Nat.add_assoc, Nat.reduceAdd] at scan ⊢
      split <;> (try simp only [Complexity.Costed.pure_cost]) <;> omega
  | dia currentWorld name body ih =>
      have h := heval env (.dia currentWorld name body)
      have scan := foldDiagDomainCosted_cost_le 0 worldCount out (fun _ => false)
        (fun out i => Complexity.Costed.charge 1 <|
          failingAtomsIntoCosted worldCount thingCount tables (env.push (name, i)) out body)
        (body.failingAtomsCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro out i _ _
          have hb := ih (env.push (name, i)) out
          simp only [Array.size_push] at hb
          simp only [Complexity.Costed.charge_cost]
          omega)
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
      simp only [Nat.add_assoc, Nat.reduceAdd] at scan ⊢
      split <;> (try simp only [Complexity.Costed.pure_cost]) <;> omega
  | box currentWorld name body ih =>
      have scan := foldDiagDomainCosted_cost_le 0 worldCount out (fun _ => false)
        (fun out i => do
          let nextEnv ← Complexity.Costed.tick (env.push (name, i)) 1
          let checked ← evalDiagFormulaCosted worldCount thingCount tables nextEnv body
          Complexity.Costed.charge 2 <| if !checked then
            failingAtomsIntoCosted worldCount thingCount tables nextEnv out body
          else .pure out)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) +
          body.failingAtomsCostBound worldCount thingCount atomBound (env.size + 1) + 3) (by
          intro out i _ _
          have hb := ih (env.push (name, i)) out
          have he := heval (env.push (name, i)) body
          simp only [Array.size_push] at hb he
          simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost,
            Complexity.Costed.tick_value, Complexity.Costed.charge_cost]
          split <;> (try simp only [Complexity.Costed.pure_cost]) <;> omega)
      simp only [failingAtomsIntoCosted, DiagFormula.failingAtomsCostBound,
        Complexity.Costed.charge_cost]
      simp only [Nat.add_assoc, Nat.reduceAdd] at scan ⊢
      omega

private theorem failingAtomsIntoCosted_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsIntoCosted worldCount thingCount tables env out formula).value.size ≤
      out.size + formula.failingAtomCountBound worldCount thingCount := by
  simpa only [failingAtomsIntoCosted_value] using
    failingAtomsIntoSpec_size_le worldCount thingCount tables env out formula

private def failingAtomsCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Complexity.Costed (Array DiagAtom) :=
  Complexity.Costed.charge 1 <|
    failingAtomsIntoCosted worldCount thingCount tables env #[] formula

private theorem failingAtomsCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsCosted worldCount thingCount tables env formula).value =
      failingAtomsSpec worldCount thingCount tables env formula := by
  simp only [failingAtomsCosted, failingAtomsSpec, Complexity.Costed.charge_value,
    failingAtomsIntoCosted_value]

private theorem failingAtomsCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsCosted worldCount thingCount tables env formula).cost ≤
      formula.failingAtomsCostBound worldCount thingCount atomBound env.size + 1 := by
  have h := failingAtomsIntoCosted_cost_le worldCount thingCount tables atomBound hAtom env #[] formula
  simp only [failingAtomsCosted, Complexity.Costed.charge_cost]
  omega

private theorem failingAtomsCosted_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtomsCosted worldCount thingCount tables env formula).value.size ≤
      formula.failingAtomCountBound worldCount thingCount := by
  simpa only [failingAtomsCosted, Complexity.Costed.charge_value,
    failingAtomsIntoCosted_value, failingAtomsSpec] using
    failingAtomsSpec_size_le worldCount thingCount tables env formula

private def pushDiagnosticIfRoom
    (budget : Nat) (out : Array String) (line : String) : Array String :=
  if out.size < budget then out.push line else out

private theorem pushDiagnosticIfRoom_size_le
    (budget : Nat) (out : Array String) (line : String)
    (hout : out.size ≤ budget) :
    (pushDiagnosticIfRoom budget out line).size ≤ budget := by
  simp only [pushDiagnosticIfRoom]
  split
  · simp only [Array.size_push]
    omega
  · exact hout

private theorem foldl_preserves_array_size_le
    {α β : Type} (items : List α) (out : Array β) (budget : Nat)
    (step : Array β → α → Array β)
    (hout : out.size ≤ budget)
    (hstep : ∀ acc item, acc.size ≤ budget → (step acc item).size ≤ budget) :
    (items.foldl step out).size ≤ budget := by
  induction items generalizing out with
  | nil => simpa using hout
  | cons item rest ih =>
      simp only [List.foldl]
      exact ih (step out item) (hstep out item hout)

/-- Append only the evidence rows that fit. Numeric traversal reads the
retained prefix directly, without copying the source array or scanning its
discarded suffix. Each retained item costs a loop step, a read, a text join,
a write, and an emission. Capacity subtraction and minimum selection cost three. -/
private def appendEvidenceLinesCosted
    (budget : Nat) (out items : Array String) : Complexity.Costed (Array String) :=
  Complexity.Costed.charge 3 <|
    Complexity.Costed.foldFin (min (budget - out.size) items.size) out fun result i => do
      let item ← Complexity.Costed.tick
        (items[i.val]'(Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right _ _))) 1
      let line ← Complexity.Costed.tick ("  - " ++ item) 1
      Complexity.Costed.tick (result.push line) 2

private theorem appendEvidenceLinesCosted_value
    (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).value =
      out ++ (items.extract 0 (budget - out.size)).map ("  - " ++ ·) := by
  have fold {n : Nat} (f : Fin n → String) (initial : Array String) :
      Fin.foldl n (fun acc i => acc.push (f i)) initial = initial ++ Array.ofFn f := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Fin.foldl_succ_last, ih, Array.ofFn_succ]
        simp [Fin.last]
  simp only [appendEvidenceLinesCosted, Complexity.Costed.charge_value,
    Complexity.Costed.foldFin_value, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value]
  rw [fold]
  congr 1
  apply Array.ext
  · simp
  · intro i hi hj
    simp

private theorem appendEvidenceLinesCosted_size
    (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).value.size =
      out.size + min (budget - out.size) items.size := by
  rw [appendEvidenceLinesCosted_value]
  simp

private theorem appendEvidenceLinesCosted_size_le
    (budget : Nat) (out items : Array String) (hout : out.size ≤ budget) :
    (appendEvidenceLinesCosted budget out items).value.size ≤ budget := by
  rw [appendEvidenceLinesCosted_size]
  have h := Nat.min_le_left (budget - out.size) items.size
  omega

private theorem appendEvidenceLinesCosted_cost
    (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).cost =
      5 * min (budget - out.size) items.size + 3 := by
  unfold appendEvidenceLinesCosted
  rw [Complexity.Costed.charge_cost, Complexity.Costed.foldFin_cost_eq _ _ _ 4 (by intros; rfl)]
  omega

private theorem appendEvidenceLinesCosted_cost_le
    (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).cost ≤ 5 * items.size + 3 := by
  rw [appendEvidenceLinesCosted_cost]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 (Nat.min_le_right _ _)) 3

private theorem appendEvidenceLinesCosted_cost_eq_emitted
    (budget : Nat) (out items : Array String) :
    (appendEvidenceLinesCosted budget out items).cost =
      5 * ((appendEvidenceLinesCosted budget out items).value.size - out.size) + 3 := by
  rw [appendEvidenceLinesCosted_cost, appendEvidenceLinesCosted_size]
  simp

/-- A capacity check costs a comparison and a branch. A retained row adds
one array write and one emission. The caller pays for text already produced. -/
private def pushDiagnosticIfRoomCosted
    (budget : Nat) (out : Array String) (line : String) : Complexity.Costed (Array String) :=
  Complexity.Costed.charge 2 <| if out.size < budget then
    Complexity.Costed.tick (out.push line) 2
  else Complexity.Costed.pure out

private theorem pushDiagnosticIfRoomCosted_value
    (budget : Nat) (out : Array String) (line : String) :
    (pushDiagnosticIfRoomCosted budget out line).value = pushDiagnosticIfRoom budget out line := by
  unfold pushDiagnosticIfRoomCosted pushDiagnosticIfRoom
  split <;> rfl

private theorem pushDiagnosticIfRoomCosted_cost_le
    (budget : Nat) (out : Array String) (line : String) :
    (pushDiagnosticIfRoomCosted budget out line).cost ≤ 4 := by
  unfold pushDiagnosticIfRoomCosted
  split <;> simp

private theorem pushDiagnosticIfRoomCosted_accounting
    (budget : Nat) (out : Array String) (line : String) :
    out.size ≤ (pushDiagnosticIfRoomCosted budget out line).value.size ∧
    (pushDiagnosticIfRoomCosted budget out line).cost + 2 * out.size =
      2 * (pushDiagnosticIfRoomCosted budget out line).value.size + 2 := by
  unfold pushDiagnosticIfRoomCosted
  split <;> simp <;> omega

/-- Source rows take priority over generated-model evidence. When no source
row matches, evaluate the atom and emit the fallback only if it is true.
The enclosing array loop guarantees room for one row before this step. -/
private def appendContextAtomCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) :
    Complexity.Costed (Array String) :=
  let evidence := atomEvidenceCosted worldNames thingNames namedFacts env atom
  if evidence.value.isEmpty then
    let checked := evalDiagAtomCosted worldCount thingCount tables env atom
    if checked.value then
      let text := (Complexity.Costed.appendString (.pure "  - ")
        (renderDiagAtomCosted worldNames thingNames env atom)).appendString
          (.pure " (present in generated finite model)")
      ⟨out.push text.value, evidence.cost + 2 + checked.cost + 1 + text.cost + 2⟩
    else ⟨out, evidence.cost + 2 + checked.cost + 1⟩
  else
    let lines := appendEvidenceLinesCosted budget out evidence.value
    ⟨lines.value, evidence.cost + 2 + lines.cost⟩

private def appendContextAtomSpec
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) : Array String :=
  let evidence := atomEvidenceSpec worldNames thingNames namedFacts env atom
  if evidence.isEmpty then
    if evalDiagAtom worldCount thingCount tables env atom then
      out.push ("  - " ++ renderDiagAtomSpec worldNames thingNames env atom ++
        " (present in generated finite model)")
    else out
  else out ++ (evidence.extract 0 (budget - out.size)).map ("  - " ++ ·)

private theorem appendContextAtomCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) :
    (appendContextAtomCosted budget worldNames thingNames namedFacts worldCount thingCount
      tables env out atom).value =
      appendContextAtomSpec budget worldNames thingNames namedFacts worldCount thingCount tables env out atom := by
  simp only [appendContextAtomCosted, appendContextAtomSpec, atomEvidenceCosted_value,
    evalDiagAtomCosted_value, Complexity.Costed.appendString_value,
    Complexity.Costed.pure_value, renderDiagAtomCosted_value]
  split
  · split <;> rfl
  · exact appendEvidenceLinesCosted_value _ _ _

private theorem appendContextAtomCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom)
    (hout : out.size < budget) :
    (appendContextAtomCosted budget worldNames thingNames namedFacts worldCount thingCount
      tables env out atom).value.size ≤ budget := by
  simp only [appendContextAtomCosted]
  split
  · split <;> simp only [Array.size_push] <;> omega
  · apply appendEvidenceLinesCosted_size_le
    omega

private theorem appendContextAtomCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) :
    (appendContextAtomCosted budget worldNames thingNames namedFacts worldCount thingCount
      tables env out atom).cost ≤
      diagAtomCostBound worldCount thingCount tables env.size +
        40 * env.size + 68 + 275 * namedFacts.size := by
  have hs := atomEvidenceCosted_cost_le worldNames thingNames namedFacts env atom
  have hq := evalDiagAtomCosted_cost_le worldCount thingCount tables env atom
  have hr := renderDiagAtomCosted_cost_le worldNames thingNames env atom
  have hn : (atomEvidenceCosted worldNames thingNames namedFacts env atom).value.size ≤
      namedFacts.size := by
    rw [atomEvidenceCosted_value]
    exact atomEvidenceSpec_size_le_namedFacts _ _ _ _ _
  have hl := appendEvidenceLinesCosted_cost_le budget out
    (atomEvidenceCosted worldNames thingNames namedFacts env atom).value
  unfold atomEvidenceCostBound at hs
  simp only [appendContextAtomCosted]
  split
  · split <;> simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost] <;> omega
  · dsimp only
    omega

/-- Render a successful context trace, whose truth the caller established.
Render its formula once and reuse its label in the fallback row.
Atom collection remains eager and counted. The subsequent indexed scan stops
when the output budget is full. The specification fixes text and row order. -/
private def appendEvidenceForFormulaCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    Complexity.Costed (Array String) :=
  let label := renderDiagFormulaCosted worldNames thingNames env formula
  let headerText := (Complexity.Costed.appendString (.pure "Evidence for ") label).appendString (.pure ":")
  let header := pushDiagnosticIfRoomCosted budget out headerText.value
  let atoms := collectAtomsCosted formula
  let rows := foldDiagArrayCosted atoms.value header.value (fun out => budget ≤ out.size)
    (appendContextAtomCosted budget worldNames thingNames namedFacts worldCount thingCount tables env)
  if rows.value.size == header.value.size then
    let text := (Complexity.Costed.appendString (.pure "  - ") (.pure label.value)).appendString
      (.pure " (true in generated finite model)")
    let result := pushDiagnosticIfRoomCosted budget rows.value text.value
    ⟨result.value, headerText.cost + header.cost + atoms.cost + rows.cost + 2 + text.cost + result.cost⟩
  else ⟨rows.value, headerText.cost + header.cost + atoms.cost + rows.cost + 2⟩

private def appendEvidenceForFormulaSpec
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) : Array String :=
  let label := renderDiagFormulaSpec worldNames thingNames env formula
  let header := pushDiagnosticIfRoom budget out ("Evidence for " ++ label ++ ":")
  let rows := (collectAtomsIntoSpec #[] formula).toList.foldl (fun out atom =>
    if out.size < budget then
      appendContextAtomSpec budget worldNames thingNames namedFacts worldCount thingCount tables env out atom
    else out) header
  if rows.size == header.size then
    pushDiagnosticIfRoom budget rows ("  - " ++ label ++ " (true in generated finite model)")
  else rows

private theorem appendEvidenceForFormulaCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    (appendEvidenceForFormulaCosted budget worldNames thingNames namedFacts worldCount thingCount
      tables out env formula).value =
      appendEvidenceForFormulaSpec budget worldNames thingNames namedFacts worldCount thingCount
        tables out env formula := by
  have visit : (fun (out : Array String) atom =>
      if (decide (budget ≤ out.size)) then out else
        (appendContextAtomCosted budget worldNames thingNames namedFacts worldCount thingCount
          tables env out atom).value) =
      (fun out atom => if out.size < budget then
        appendContextAtomSpec budget worldNames thingNames namedFacts worldCount thingCount tables env out atom
        else out) := by
    funext out atom
    rw [appendContextAtomCosted_value]
    split <;> simp_all
  simp only [appendEvidenceForFormulaCosted, appendEvidenceForFormulaSpec,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value,
    renderDiagFormulaCosted_value, pushDiagnosticIfRoomCosted_value,
    collectAtomsCosted, Complexity.Costed.charge_value, collectAtomsIntoCosted_value,
    foldDiagArrayCosted_value, visit]
  split <;> rfl

private theorem appendEvidenceForFormulaCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula)
    (hout : out.size ≤ budget) :
    (appendEvidenceForFormulaCosted budget worldNames thingNames namedFacts worldCount thingCount
      tables out env formula).value.size ≤ budget := by
  have hp := pushDiagnosticIfRoom_size_le budget out
    ("Evidence for " ++ renderDiagFormulaSpec worldNames thingNames env formula ++ ":") hout
  have hv (out : Array String) (atom : DiagAtom) (h : out.size ≤ budget) :
      (if out.size < budget then
        appendContextAtomSpec budget worldNames thingNames namedFacts worldCount thingCount tables env out atom
        else out).size ≤ budget := by
    split
    · rw [← appendContextAtomCosted_value]
      apply appendContextAtomCosted_size_le
      assumption
    · exact h
  rw [appendEvidenceForFormulaCosted_value]
  unfold appendEvidenceForFormulaSpec
  dsimp only
  split
  · apply pushDiagnosticIfRoom_size_le
    exact foldl_preserves_array_size_le _ _ _ _ hp hv
  · exact foldl_preserves_array_size_le _ _ _ _ hp hv

private theorem appendEvidenceForFormulaCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    (appendEvidenceForFormulaCosted budget worldNames thingNames namedFacts worldCount thingCount
      tables out env formula).cost ≤
      formula.nodeCount * (diagAtomCostBound worldCount thingCount tables env.size +
        60 * env.size + 115 + 275 * namedFacts.size) + 15 := by
  have hr := renderDiagFormulaCosted_cost_le worldNames thingNames env formula
  have hc := collectAtomsCosted_cost_le formula
  have hn := collectAtomsCosted_size_le formula
  have hf (initial : Array String) := foldDiagArrayCosted_cost_le
    (collectAtomsCosted formula).value initial (fun out => budget ≤ out.size)
    (appendContextAtomCosted budget worldNames thingNames namedFacts worldCount thingCount tables env)
    (diagAtomCostBound worldCount thingCount tables env.size + 40 * env.size + 68 + 275 * namedFacts.size)
    (by intros; apply appendContextAtomCosted_cost_le)
  have hs := Nat.mul_le_mul_right
    (diagAtomCostBound worldCount thingCount tables env.size + 40 * env.size + 68 + 275 * namedFacts.size + 6) hn
  simp only [appendEvidenceForFormulaCosted]
  split <;> simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost] <;>
    grind [pushDiagnosticIfRoomCosted_cost_le]

private theorem appendEvidenceForFormulaCostBound_mono
    {f f' e e' n n' q q' : Nat}
    (hf : f ≤ f') (he : e ≤ e') (hn : n ≤ n') (hq : q ≤ q') :
    f * (q + 60 * e + 115 + 275 * n) + 15 ≤
      f' * (q' + 60 * e' + 115 + 275 * n') + 15 :=
  Nat.add_le_add_right (Nat.mul_le_mul hf (by omega)) 15


private def suggestionForAtomSpec
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) : String :=
  let addOrRemove :=
    if wanted then
      "Add the missing DSL fact"
    else
      "Remove or reclassify the DSL fact"
  let tail :=
    if wanted then
      "or remove/relax the facts shown in this counterexample that make this obligation apply."
    else
      "or remove/relax the facts shown in this counterexample that make this combination forbidden."
  match atom with
  | .unary field thing world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{unaryFieldDslLabel field}({thingName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .binary .inst left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{leftName} :: {rightName}` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .binary .sub left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{leftName} ⊑ {rightName}` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .binary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{binaryFieldDslLabel field}({leftName}, {rightName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .ternary field first second third world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{ternaryFieldDslLabel field}({firstName}, {secondName}, {thirdName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .derivedUnary field thing world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{field}({thingName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .derivedBinary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{field}({leftName}, {rightName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .quaternary field first second third fourth world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let fourthName := indexedName thingNames (lookupVar env fourth)
      let worldName := indexedName worldNames (lookupVar env world)
      s!"{addOrRemove} `{field}({firstName}, {secondName}, {thirdName}, {fourthName})` at `{worldName}` (or in an appropriate broader scope), {tail}"
  | .typeSem thing _world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      if wanted then
        s!"Make `{thingName}` behave as a type by adding at least one compatible instantiation, or remove/relax the facts shown in this counterexample that require it to be a type."
      else
        s!"Remove the instantiations that make `{thingName}` behave as a type, or remove/relax the facts shown in this counterexample that require it to be an individual."
  | .individualSem thing _world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      if wanted then
        s!"Make `{thingName}` behave as an individual by removing its compatible instantiations as a type, or remove/relax the facts shown in this counterexample that require it to be an individual."
      else
        s!"Add a compatible instantiation for `{thingName}` if it should be a type, or remove/relax the facts shown in this counterexample that forbid it from being an individual."

/-- Count the operations that construct an atom suggestion. Each string join
uses the shared counted primitive, and each name lookup scans the environment.
The value proof preserves the text independently of these costs, following the
cost/value separation of Niu et al. (POPL 2022, doi:10.1145/3498670).
String-character traversal remains outside the unit-cost model. -/
private def suggestionForAtomCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) : Complexity.Costed String := do
  let addOrRemove ← Complexity.Costed.tick
    (if wanted then "Add the missing DSL fact" else "Remove or reclassify the DSL fact") 1
  let tail ← Complexity.Costed.tick
    (if wanted then "or remove/relax the facts shown in this counterexample that make this obligation apply."
     else "or remove/relax the facts shown in this counterexample that make this combination forbidden.") 1
  (match atom with
  | .unary field thing world => Complexity.Costed.charge 1 <|
      let thingName := renderDiagVariableCosted thingNames env thing
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString (Complexity.Costed.tick (unaryFieldDslLabel field) 1)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString thingName
      let text := text.appendString (Complexity.Costed.pure ")` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .binary .inst left right world => Complexity.Costed.charge 2 <|
      let leftName := renderDiagVariableCosted thingNames env left
      let rightName := renderDiagVariableCosted thingNames env right
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString leftName
      let text := text.appendString (Complexity.Costed.pure " :: ")
      let text := text.appendString rightName
      let text := text.appendString (Complexity.Costed.pure "` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .binary .sub left right world => Complexity.Costed.charge 2 <|
      let leftName := renderDiagVariableCosted thingNames env left
      let rightName := renderDiagVariableCosted thingNames env right
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString leftName
      let text := text.appendString (Complexity.Costed.pure " ⊑ ")
      let text := text.appendString rightName
      let text := text.appendString (Complexity.Costed.pure "` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .binary field left right world => Complexity.Costed.charge 2 <|
      let leftName := renderDiagVariableCosted thingNames env left
      let rightName := renderDiagVariableCosted thingNames env right
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString (Complexity.Costed.tick (binaryFieldDslLabel field) 1)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString leftName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString rightName
      let text := text.appendString (Complexity.Costed.pure ")` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .ternary field first second third world => Complexity.Costed.charge 1 <|
      let firstName := renderDiagVariableCosted thingNames env first
      let secondName := renderDiagVariableCosted thingNames env second
      let thirdName := renderDiagVariableCosted thingNames env third
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString (Complexity.Costed.tick (ternaryFieldDslLabel field) 1)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString firstName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString secondName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString thirdName
      let text := text.appendString (Complexity.Costed.pure ")` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .derivedUnary field thing world => Complexity.Costed.charge 1 <|
      let thingName := renderDiagVariableCosted thingNames env thing
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString (Complexity.Costed.pure field)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString thingName
      let text := text.appendString (Complexity.Costed.pure ")` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .derivedBinary field left right world => Complexity.Costed.charge 1 <|
      let leftName := renderDiagVariableCosted thingNames env left
      let rightName := renderDiagVariableCosted thingNames env right
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString (Complexity.Costed.pure field)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString leftName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString rightName
      let text := text.appendString (Complexity.Costed.pure ")` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .quaternary field first second third fourth world => Complexity.Costed.charge 1 <|
      let firstName := renderDiagVariableCosted thingNames env first
      let secondName := renderDiagVariableCosted thingNames env second
      let thirdName := renderDiagVariableCosted thingNames env third
      let fourthName := renderDiagVariableCosted thingNames env fourth
      let worldName := renderDiagVariableCosted worldNames env world
      let text := Complexity.Costed.appendString (Complexity.Costed.pure addOrRemove) (Complexity.Costed.pure " `")
      let text := text.appendString (Complexity.Costed.pure field)
      let text := text.appendString (Complexity.Costed.pure "(")
      let text := text.appendString firstName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString secondName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString thirdName
      let text := text.appendString (Complexity.Costed.pure ", ")
      let text := text.appendString fourthName
      let text := text.appendString (Complexity.Costed.pure ")` at `")
      let text := text.appendString worldName
      let text := text.appendString (Complexity.Costed.pure "` (or in an appropriate broader scope), ")
      text.appendString (Complexity.Costed.pure tail)
  | .typeSem thing _world => Complexity.Costed.charge 2 <|
      let thingName := renderDiagVariableCosted thingNames env thing
      if wanted then
        let text := Complexity.Costed.appendString (Complexity.Costed.pure "Make `") thingName
        text.appendString (Complexity.Costed.pure "` behave as a type by adding at least one compatible instantiation, or remove/relax the facts shown in this counterexample that require it to be a type.")
      else
        let text := Complexity.Costed.appendString (Complexity.Costed.pure "Remove the instantiations that make `") thingName
        text.appendString (Complexity.Costed.pure "` behave as a type, or remove/relax the facts shown in this counterexample that require it to be an individual.")
  | .individualSem thing _world => Complexity.Costed.charge 2 <|
      let thingName := renderDiagVariableCosted thingNames env thing
      if wanted then
        let text := Complexity.Costed.appendString (Complexity.Costed.pure "Make `") thingName
        text.appendString (Complexity.Costed.pure "` behave as an individual by removing its compatible instantiations as a type, or remove/relax the facts shown in this counterexample that require it to be an individual.")
      else
        let text := Complexity.Costed.appendString (Complexity.Costed.pure "Add a compatible instantiation for `") thingName
        text.appendString (Complexity.Costed.pure "` if it should be a type, or remove/relax the facts shown in this counterexample that forbid it from being an individual."))

private theorem suggestionForAtomCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) :
    (suggestionForAtomCosted worldNames thingNames env atom wanted).value =
      suggestionForAtomSpec worldNames thingNames env atom wanted := by
  cases wanted <;> cases atom with
  | binary field left right world =>
      cases field <;>
        simp only [suggestionForAtomCosted, suggestionForAtomSpec, Bind.bind, Complexity.Costed.bind_value,
          Complexity.Costed.charge_value, Complexity.Costed.appendString_value,
          Complexity.Costed.pure_value, Complexity.Costed.tick_value,
          renderDiagVariableCosted_value, Bool.false_eq_true, ↓reduceIte] <;> rfl
  | _ =>
      simp only [suggestionForAtomCosted, suggestionForAtomSpec, Bind.bind, Complexity.Costed.bind_value,
        Complexity.Costed.charge_value, Complexity.Costed.appendString_value,
        Complexity.Costed.pure_value, Complexity.Costed.tick_value,
        renderDiagVariableCosted_value, Bool.false_eq_true, ↓reduceIte]
      rfl

/-- An atom uses at most five names. Each costs `4E+5` for environment size
`E`. The five-name branch adds fourteen joins, two Boolean selections, and one
atom selection. Other branches have fewer names and fit the same bound. -/
private theorem suggestionForAtomCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atom : DiagAtom) (wanted : Bool) :
    (suggestionForAtomCosted worldNames thingNames env atom wanted).cost ≤
      20 * env.size + 42 := by
  cases wanted <;> cases atom with
  | binary field left right world =>
      cases field <;>
        simp only [suggestionForAtomCosted, Bind.bind, Complexity.Costed.bind_cost,
          Complexity.Costed.tick_value, Complexity.Costed.charge_cost,
          Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
          Complexity.Costed.tick_cost, renderDiagVariableCosted_cost,
          Bool.false_eq_true, ↓reduceIte] <;> omega
  | _ =>
      simp only [suggestionForAtomCosted, Bind.bind, Complexity.Costed.bind_cost,
        Complexity.Costed.tick_value, Complexity.Costed.charge_cost,
        Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
        Complexity.Costed.tick_cost, renderDiagVariableCosted_cost,
        Bool.false_eq_true, ↓reduceIte]
      omega

private def suggestionForFailureSpec
    (worldNames thingNames : Array Name) (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ =>
      "Add at least one of the alternatives listed here, or remove/relax the evidence for this counterexample that makes this alternative obligation apply."
  | .and _ _ =>
      if (flattenDiagJunctionSpec .conjunction formula).toArray.any formulaHasDistinctnessRequirement then
        "Add a witness satisfying all listed requirements, including the distinctness condition, or remove/relax the evidence for this counterexample that makes this witness obligation apply."
      else
        let atoms := failingAtomsSpec worldCount thingCount tables env formula
        match atoms[0]? with
        | some atom =>
            if atoms.size == 1 then
              suggestionForAtomSpec worldNames thingNames env atom true
            else
              "Add all missing facts listed here, or remove/relax the evidence for this counterexample that makes these requirements apply."
        | none =>
            "Use the listed requirements and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."
  | .not (.atom atom) =>
      if evalDiagAtom worldCount thingCount tables env atom then
        suggestionForAtomSpec worldNames thingNames env atom false
      else
        "Inspect the evidence for this counterexample: this forbidden condition holds, but the diagnostic could not reduce it to a single asserted DSL fact."
  | .atom atom =>
      suggestionForAtomSpec worldNames thingNames env atom true
  | _ =>
      let atoms := failingAtomsSpec worldCount thingCount tables env formula
      match atoms[0]? with
      | some atom =>
          if atoms.size == 1 then
            suggestionForAtomSpec worldNames thingNames env atom true
          else
            "Several obligations fail together here. Add the missing facts named in the condition, or remove/relax the evidence for this counterexample that makes all of them required."
      | none =>
          "Use the condition and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."

/-- An empty array selects the no-atom message. A singleton selects its atom's
specific suggestion. Larger arrays select the multiple-atom message. Direct
head access counts its bounds check and reads the array only when nonempty. -/
private def suggestionFromAtomsCosted
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atoms : Array DiagAtom) (many noneText : String) : Complexity.Costed String :=
  Complexity.Costed.charge 2 <| if h : 0 < atoms.size then do
    let atom ← Complexity.Costed.tick atoms[0] 1
    Complexity.Costed.charge 2 <| if atoms.size == 1 then
      suggestionForAtomCosted worldNames thingNames env atom true
    else .pure many
  else .pure noneText

private theorem suggestionFromAtomsCosted_value
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atoms : Array DiagAtom) (many noneText : String) :
    (suggestionFromAtomsCosted worldNames thingNames env atoms many noneText).value =
      match atoms[0]? with
      | some atom => if atoms.size == 1 then suggestionForAtomSpec worldNames thingNames env atom true else many
      | none => noneText := by
  unfold suggestionFromAtomsCosted
  by_cases h : 0 < atoms.size
  · simp only [h, ↓reduceDIte, Complexity.Costed.charge_value, Bind.bind,
      Complexity.Costed.bind_value, Complexity.Costed.tick_value]
    split <;> simp_all [suggestionForAtomCosted_value]
  · simp [h]

private theorem suggestionFromAtomsCosted_cost_le
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (atoms : Array DiagAtom) (many noneText : String) :
    (suggestionFromAtomsCosted worldNames thingNames env atoms many noneText).cost ≤
      20 * env.size + 47 := by
  unfold suggestionFromAtomsCosted
  split
  · have h := suggestionForAtomCosted_cost_le worldNames thingNames env atoms[0] true
    simp only [Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost,
      Complexity.Costed.tick_cost, Complexity.Costed.tick_value]
    split <;> (try simp only [Complexity.Costed.pure_cost]) <;> omega
  · simp [Complexity.Costed.charge_cost]

/-- Suggestion selection includes discovery and evaluation, even if the report
has no room for its text. The conjunction search stops at the first distinctness
requirement, so it skips the remaining predicate tests. -/
private def suggestionForFailureCosted
    (worldNames thingNames : Array Name) (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Complexity.Costed String :=
  let fallback := fun () => do
    let atoms ← failingAtomsCosted worldCount thingCount tables env formula
    suggestionFromAtomsCosted worldNames thingNames env atoms
      "Several obligations fail together here. Add the missing facts named in the condition, or remove/relax the evidence for this counterexample that makes all of them required."
      "Use the condition and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."
  Complexity.Costed.charge 1 <| match formula with
  | .or _ _ => .pure
      "Add at least one of the alternatives listed here, or remove/relax the evidence for this counterexample that makes this alternative obligation apply."
  | .and _ _ => do
      let rows ← flattenDiagJunctionCosted .conjunction formula
      let distinct ← Complexity.anyArrayCosted rows formulaHasDistinctnessRequirementCosted
      Complexity.Costed.charge 1 <| if distinct then .pure
        "Add a witness satisfying all listed requirements, including the distinctness condition, or remove/relax the evidence for this counterexample that makes this witness obligation apply."
      else do
        let atoms ← failingAtomsCosted worldCount thingCount tables env formula
        suggestionFromAtomsCosted worldNames thingNames env atoms
          "Add all missing facts listed here, or remove/relax the evidence for this counterexample that makes these requirements apply."
          "Use the listed requirements and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."
  | .not p => Complexity.Costed.charge 1 <| match p with
      | .atom atom => do
          let checked ← evalDiagAtomCosted worldCount thingCount tables env atom
          Complexity.Costed.charge 1 <| if checked then
            suggestionForAtomCosted worldNames thingNames env atom false
          else .pure
            "Inspect the evidence for this counterexample: this forbidden condition holds, but the diagnostic could not reduce it to a single asserted DSL fact."
      | _ => fallback ()
  | .atom atom => suggestionForAtomCosted worldNames thingNames env atom true
  | _ => fallback ()

private theorem suggestionForFailureCosted_value
    (worldNames thingNames : Array Name) (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (suggestionForFailureCosted worldNames thingNames worldCount thingCount tables env formula).value =
      suggestionForFailureSpec worldNames thingNames worldCount thingCount tables env formula := by
  cases formula with
  | not p =>
      cases p <;>
        simp only [suggestionForFailureCosted, suggestionForFailureSpec,
          Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value,
          failingAtomsCosted_value, suggestionFromAtomsCosted_value, evalDiagAtomCosted_value]
      split <;> simp_all [suggestionForAtomCosted_value]
  | _ =>
      (try simp only [suggestionForFailureCosted, suggestionForFailureSpec,
        Complexity.Costed.charge_value, Complexity.Costed.pure_value,
        Bind.bind, Complexity.Costed.bind_value, failingAtomsCosted_value,
        suggestionFromAtomsCosted_value, suggestionForAtomCosted_value,
        flattenDiagJunctionCosted_value, Complexity.anyArrayCosted_eq_list,
        Complexity.anyListCosted_value,
        formulaHasDistinctnessRequirementCosted_value]) <;>
      first
      | rfl
      | split <;> simp_all [Complexity.Costed.bind_value,
          failingAtomsCosted_value, suggestionFromAtomsCosted_value]

/-- The bound includes discovery, evaluation, at most eight operations per
formula node for conjunction analysis, and the largest atom-specific text.
The atomic evaluator bound remains an explicit premise of the cost theorem. -/
private def DiagFormula.suggestionCostBound
    (worldCount thingCount : Nat) (atomBound : Nat → Nat) (envSize : Nat) (formula : DiagFormula) : Nat :=
  formula.failingAtomsCostBound worldCount thingCount atomBound envSize +
    formula.evalCostBound worldCount thingCount atomBound envSize +
    8 * formula.nodeCount + 20 * envSize + 51

private theorem suggestionForFailureCosted_cost_le
    (worldNames thingNames : Array Name) (worldCount thingCount : Nat) (tables : FactTables)
    (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (suggestionForFailureCosted worldNames thingNames worldCount thingCount tables env formula).cost ≤
      formula.suggestionCostBound worldCount thingCount atomBound env.size := by
  have hd := failingAtomsCosted_cost_le worldCount thingCount tables atomBound hAtom env formula
  have ht := suggestionFromAtomsCosted_cost_le worldNames thingNames env
  have ha := suggestionForAtomCosted_cost_le worldNames thingNames env
  unfold DiagFormula.suggestionCostBound
  cases formula with
  | and p q =>
      have hf := flattenDiagJunctionCosted_cost_le .conjunction (.and p q)
      have hs := Complexity.anyArrayCosted_cost_le
        (flattenDiagJunctionCosted .conjunction (.and p q)).value
        formulaHasDistinctnessRequirementCosted 2
        (fun f _ => formulaHasDistinctnessRequirementCosted_cost_le f)
      have hm := (flattenDiagJunctionSpec_metrics .conjunction (.and p q)).1
      rw [flattenDiagJunctionCosted_value] at hs
      simp only [List.size_toArray] at hs
      simp only [suggestionForFailureCosted, Complexity.Costed.charge_cost,
        Bind.bind, Complexity.Costed.bind_cost, flattenDiagJunctionCosted_value]
      split <;> grind [Complexity.Costed.pure_cost, Complexity.Costed.bind_cost]
  | not p =>
      cases p <;>
        simp only [suggestionForFailureCosted, Complexity.Costed.charge_cost,
          Bind.bind, Complexity.Costed.bind_cost]
      all_goals first
      | grind
      | split <;> grind [Complexity.Costed.pure_cost, DiagFormula.evalCostBound]
  | _ =>
      simp only [suggestionForFailureCosted, Complexity.Costed.charge_cost,
        Bind.bind, Complexity.Costed.bind_cost]
      grind [Complexity.Costed.pure_cost]

private theorem DiagFormula.evalCostBound_mono_env
    (worldCount thingCount : Nat) (atomBound : Nat → Nat) (hAtom : Monotone atomBound)
    (formula : DiagFormula) {e e' : Nat} (h : e ≤ e') :
    formula.evalCostBound worldCount thingCount atomBound e ≤
      formula.evalCostBound worldCount thingCount atomBound e' := by
  induction formula generalizing e e' with
  | atom => exact Nat.add_le_add_right (hAtom h) 1
  | eqThing | eqWorld => simp only [evalCostBound]; omega
  | not p ih => exact Nat.add_le_add_right (ih h) 2
  | and p q ihp ihq | or p q ihp ihq =>
      exact Nat.add_le_add_right (Nat.add_le_add (ihp h) (ihq h)) 2
  | imp p q ihp ihq | iff p q ihp ihq =>
      exact Nat.add_le_add_right (Nat.add_le_add (ihp h) (ihq h)) 3
  | forallThing name body ih | existsThing name body ih =>
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left thingCount (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 3)) 1
  | forallWorld name body ih | existsWorld name body ih =>
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left worldCount (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 3)) 1
  | box currentWorld name body ih | dia currentWorld name body ih =>
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left worldCount (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 3)) 1

private theorem DiagFormula.failingAtomsCostBound_mono_env
    (worldCount thingCount : Nat) (atomBound : Nat → Nat) (hAtom : Monotone atomBound)
    (formula : DiagFormula) {e e' : Nat} (h : e ≤ e') :
    formula.failingAtomsCostBound worldCount thingCount atomBound e ≤
      formula.failingAtomsCostBound worldCount thingCount atomBound e' := by
  have he := DiagFormula.evalCostBound_mono_env worldCount thingCount atomBound hAtom
  induction formula generalizing e e' with
  | atom => exact Nat.add_le_add_right (hAtom h) 3
  | eqThing | eqWorld => exact Nat.le_refl _
  | not p _ => exact Nat.add_le_add_right (he (.not p) h) 4
  | and p q ihp ihq => exact Nat.add_le_add_right (Nat.add_le_add (ihp h) (ihq h)) 1
  | or p q ihp ihq =>
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (he (.or p q) h) (ihp h)) (ihq h)) 2
  | iff p q ihp ihq =>
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (he (.iff p q) h) (ihp h)) (ihq h)) 2
  | imp p q _ ihq =>
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add_right (he (.imp p q) h) _) (ihq h)) 2
  | forallThing name body ih =>
      exact Nat.add_le_add_right (Nat.mul_le_mul_left thingCount
        (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 4)) 1
  | forallWorld name body ih =>
      exact Nat.add_le_add_right (Nat.mul_le_mul_left worldCount
        (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 4)) 1
  | existsThing name body ih =>
      exact Nat.add_le_add_right (Nat.add_le_add (he (.existsThing name body) h)
        (Nat.mul_le_mul_left thingCount (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 4))) 2
  | existsWorld name body ih =>
      exact Nat.add_le_add_right (Nat.add_le_add (he (.existsWorld name body) h)
        (Nat.mul_le_mul_left worldCount (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 4))) 2
  | dia currentWorld name body ih =>
      exact Nat.add_le_add_right (Nat.add_le_add (he (.dia currentWorld name body) h)
        (Nat.mul_le_mul_left worldCount (Nat.add_le_add_right (ih (Nat.add_le_add_right h 1)) 4))) 2
  | box currentWorld name body ih =>
      exact Nat.add_le_add_right (Nat.mul_le_mul_left worldCount
        (Nat.add_le_add_right
          (Nat.add_le_add (he body (Nat.add_le_add_right h 1)) (ih (Nat.add_le_add_right h 1))) 6)) 1

/-- Bound evaluation and atom discovery for any formula produced by failure
minimization. The fixed environment limit also covers merged disjunction
environments. Each pair of child bounds pays for the rebuilt disjunction's
evaluation and discovery. The recurrence uses only the input formula. -/
private def DiagFormula.failureDetailCostBound
    (worldCount thingCount : Nat) (atomBound : Nat → Nat) (envLimit : Nat)
    (formula : DiagFormula) : Nat :=
  formula.evalCostBound worldCount thingCount atomBound envLimit +
    formula.failingAtomsCostBound worldCount thingCount atomBound envLimit +
    match formula with
    | .atom _ | .eqThing _ _ | .eqWorld _ _ => 0
    | .not p => 2 * p.failureDetailCostBound worldCount thingCount atomBound envLimit + 4
    | .and p q | .or p q | .imp p q | .iff p q =>
        2 * p.failureDetailCostBound worldCount thingCount atomBound envLimit +
          2 * q.failureDetailCostBound worldCount thingCount atomBound envLimit + 4
    | .forallThing _ body | .forallWorld _ body | .existsThing _ body | .existsWorld _ body |
        .box _ _ body | .dia _ _ body =>
        2 * body.failureDetailCostBound worldCount thingCount atomBound envLimit + 4

private theorem minimizeFailureCosted_detailCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (atomBound : Nat → Nat) (envLimit : Nat)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    let failed := (minimizeFailureCosted worldCount thingCount tables env formula).value.formula
    failed.evalCostBound worldCount thingCount atomBound envLimit +
      failed.failingAtomsCostBound worldCount thingCount atomBound envLimit ≤
        formula.failureDetailCostBound worldCount thingCount atomBound envLimit := by
  fun_induction minimizeFailureCosted
  all_goals try dsimp only at *
  all_goals
    simp_all (config := { zetaDelta := true })
      [DiagFormula.failureDetailCostBound, DiagFormula.evalCostBound, DiagFormula.failingAtomsCostBound,
        failedHere, withContext, Complexity.Costed.charge_value]
  all_goals omega

private def dType (x w : String) : DiagFormula :=
  .atom (.typeSem x w)

private def dIndividual (x w : String) : DiagFormula :=
  .atom (.individualSem x w)

private def dUnary (field : UnaryField) (x w : String) : DiagFormula :=
  .atom (.unary field x w)

private def dBinary (field : BinaryField) (x y w : String) : DiagFormula :=
  .atom (.binary field x y w)

private def dTernary (field : TernaryField) (x y z w : String) : DiagFormula :=
  .atom (.ternary field x y z w)

private def dInst (x t w : String) : DiagFormula :=
  dBinary .inst x t w

private def dSub (x y w : String) : DiagFormula :=
  dBinary .sub x y w

private def dPart (x y w : String) : DiagFormula :=
  dBinary .part x y w

private def dOverlap (x y w : String) : DiagFormula :=
  dBinary .overlap x y w

private def dProperPart (x y w : String) : DiagFormula :=
  dBinary .properPart x y w

private def dGenericFunctionalDependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "GenericFunctionalDependence" x y w)

private def dIndividualFunctionalDependence
    (x x' y y' w : String) : DiagFormula :=
  .atom (.quaternary "IndividualFunctionalDependence" x x' y y' w)

private def dComponentOf
    (x x' y y' w : String) : DiagFormula :=
  .atom (.quaternary "ComponentOf" x x' y y' w)

private def dGenericConstitutionalDependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "GenericConstitutionalDependence" x y w)

private def dConstitution
    (x x' y y' w : String) : DiagFormula :=
  .atom (.quaternary "Constitution" x x' y y' w)

private def dExistentialDependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "ExistentialDependence" x y w)

private def dExistentialIndependence (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "ExistentialIndependence" x y w)

private def dExternallyDependent (x y w : String) : DiagFormula :=
  .atom (.derivedBinary "ExternallyDependent" x y w)

private def dExternallyDependentMode (x w : String) : DiagFormula :=
  .atom (.derivedUnary "ExternallyDependentMode" x w)

private def dQuaIndividual (x w : String) : DiagFormula :=
  .atom (.derivedUnary "QuaIndividual" x w)

private def dQuaIndividualOf (x y w : String) : DiagFormula :=
  .atom (.binary .quaIndividualOf x y w)

private def dFoundedBy (x y w : String) : DiagFormula :=
  .atom (.binary .foundedBy x y w)

private def dMediates (x y w : String) : DiagFormula :=
  .atom (.binary .mediates x y w)

private def dCharacterization (x y w : String) : DiagFormula :=
  .atom (.binary .characterization x y w)

private def dDistance (x y r w : String) : DiagFormula :=
  dTernary .distance x y r w

private def dDistanceSum (x y z w : String) : DiagFormula :=
  dTernary .distanceSum x y z w

private def dDistanceZero (x w : String) : DiagFormula :=
  dUnary .distanceZero x w

private def dDistanceGreaterEq (x y w : String) : DiagFormula :=
  dBinary .distanceGreaterEq x y w

private def dNeThing (x y : String) : DiagFormula :=
  .not (.eqThing x y)

private def dAndList (xs : List DiagFormula) : DiagFormula :=
  match xs with
  | List.nil => .atom (.typeSem "__invalid" "__invalid")
  | List.cons p ps => ps.foldl (fun acc q => .and acc q) p

private def dOrList (xs : List DiagFormula) : DiagFormula :=
  match xs with
  | List.nil => .not (.atom (.typeSem "__invalid" "__invalid"))
  | List.cons p ps => ps.foldl (fun acc q => .or acc q) p

private def dQuality (x w : String) : DiagFormula :=
  .existsThing "__qualityKind" <| dAndList [
    dUnary .qualityKind "__qualityKind" w,
    dInst x "__qualityKind" w,
    .forallThing "__otherQualityKind" <|
      .imp
        (dAndList [
          dUnary .qualityKind "__otherQualityKind" w,
          dInst x "__otherQualityKind" w
        ])
        (.eqThing "__otherQualityKind" "__qualityKind")
  ]

private def dDerivedUnary (field x w : String) : DiagFormula :=
  .atom (.derivedUnary field x w)

private def dDerivedBinary (field x y w : String) : DiagFormula :=
  .atom (.derivedBinary field x y w)

private def dQualityStructure (x w : String) : DiagFormula :=
  dDerivedUnary "QualityStructure" x w

private def dNonEmptySet (x w : String) : DiagFormula :=
  dDerivedUnary "NonEmptySet" x w

private def dSimpleQuality (x w : String) : DiagFormula :=
  dDerivedUnary "SimpleQuality" x w

private def dComplexQuality (x w : String) : DiagFormula :=
  dDerivedUnary "ComplexQuality" x w

private def dSimpleQualityType (x w : String) : DiagFormula :=
  dDerivedUnary "SimpleQualityType" x w

private def dComplexQualityType (x w : String) : DiagFormula :=
  dDerivedUnary "ComplexQualityType" x w

private def dMemberOf (x y w : String) : DiagFormula :=
  dBinary .memberOf x y w

private def dProperSub (x y w : String) : DiagFormula :=
  dDerivedBinary "ProperSub" x y w

private def dProperSubsetOf (x y w : String) : DiagFormula :=
  dDerivedBinary "ProperSubsetOf" x y w

private def dSpecificEndurantKind (k w : String) : DiagFormula :=
  dOrList [
    dUnary .objectKind k w,
    dUnary .collectiveKind k w,
    dUnary .quantityKind k w,
    dUnary .relatorKind k w,
    dUnary .modeKind k w,
    dUnary .qualityKind k w
  ]

private def renderThingPath (thingNames : Array Name) (path : Array Nat) : String :=
  (joinIndexedNamesCosted thingNames path " InheresIn ").value

private structure UltimateBearerCandidate where
  bearer : Nat
  path : Array Nat
  deriving Inhabited

/-- Render the stored path without searching the closure again. Each name
lookup and concatenation contributes to the count. Character work is outside
the unit-cost model, so this is a bound on primitive calls, not string length. -/
private def renderUltimateBearerCosted (names : Array Name) (c : UltimateBearerCandidate) :
    Complexity.Costed String := do
  let name ← indexedNameCosted names c.bearer
  let path ← joinIndexedNamesCosted names c.path " InheresIn "
  let text ← Complexity.Costed.tick ("`" ++ name) 1
  let text ← Complexity.Costed.tick (text ++ "` via `") 1
  let text ← Complexity.Costed.tick (text ++ path) 1
  Complexity.Costed.tick (text ++ "`") 1

private theorem renderUltimateBearerCosted_value (names : Array Name) (c : UltimateBearerCandidate) :
    (renderUltimateBearerCosted names c).value =
      s!"`{indexedName names c.bearer}` via `{renderThingPath names c.path}`" := by
  simp only [renderUltimateBearerCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, indexedNameCosted_value, renderThingPath]
  rfl

private theorem renderUltimateBearerCosted_cost_le (names : Array Name) (c : UltimateBearerCandidate) :
    (renderUltimateBearerCosted names c).cost ≤ 9 * c.path.size + 9 := by
  have h := joinIndexedNamesCosted_cost_le names c.path " InheresIn "
  simp only [renderUltimateBearerCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost, indexedNameCosted_cost]
  omega

/-- Accumulate the bearer descriptions in candidate order. The option records
whether any item was rendered, including an item whose text is empty. -/
private def renderUltimateBearersCosted (names : Array Name) (candidates : Array UltimateBearerCandidate) :
    Complexity.Costed String := do
  let joined ← Complexity.Costed.foldArray candidates (none : Option String) fun out c => do
    let item ← renderUltimateBearerCosted names c
    Complexity.Costed.charge 1 <| match out with
    | none => Complexity.Costed.pure (some item)
    | some text => do
        let text ← Complexity.Costed.tick (text ++ ", ") 1
        let text ← Complexity.Costed.tick (text ++ item) 1
        Complexity.Costed.pure (some text)
  Complexity.Costed.tick (joined.getD "") 1

private theorem renderUltimateBearersCosted_cost_le
    (names : Array Name) (candidates : Array UltimateBearerCandidate) (T : Nat)
    (paths : ∀ c ∈ candidates, c.path.size ≤ T + 1) :
    (renderUltimateBearersCosted names candidates).cost ≤ candidates.size * (9 * T + 23) + 1 := by
  unfold renderUltimateBearersCosted
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
  apply Nat.add_le_add_right
  apply le_trans (Complexity.Costed.foldArray_cost_le _ _ _ (9 * T + 21) ?_)
  · simp [Nat.add_assoc]
  · intro out c hc
    have h := renderUltimateBearerCosted_cost_le names c
    have hp := paths c hc
    simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    cases out <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.bind_cost,
      Complexity.Costed.tick_cost] <;> omega

private theorem renderUltimateBearersCosted_value
    (names : Array Name) (candidates : Array UltimateBearerCandidate) :
    (renderUltimateBearersCosted names candidates).value =
      String.intercalate ", " (candidates.toList.map fun c =>
        s!"`{indexedName names c.bearer}` via `{renderThingPath names c.path}`") := by
  have fold (xs prefixNames : List String) :
      (xs.foldl (fun out item => match out with
        | none => some item
        | some text => some (text ++ ", " ++ item))
        (if prefixNames = [] then none else some (String.intercalate ", " prefixNames))).getD "" =
        String.intercalate ", " (prefixNames ++ xs) := by
    induction xs generalizing prefixNames with
    | nil => cases prefixNames <;> simp
    | cons item xs ih =>
        rw [List.append_cons, ← ih, List.foldl_cons]
        congr
        cases prefixNames with
        | nil => simp
        | cons first rest =>
            simp only [List.cons_ne_nil, ↓reduceIte, List.cons_append, Option.some.injEq]
            rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
              String.intercalate_singleton]
  have h := fold (candidates.toList.map fun c =>
    s!"`{indexedName names c.bearer}` via `{renderThingPath names c.path}`") []
  simp only [List.nil_append, ↓reduceIte, List.foldl_map] at h
  simp only [renderUltimateBearersCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArray_value, ← Array.foldl_toList,
    renderUltimateBearerCosted_value, Complexity.Costed.charge_value]
  convert h using 1
  congr 2
  funext out c
  cases out <;> rfl

/-- A bearer candidate must be a non-moment with a reconstructed path.
The guarded moment query runs first, so moments never trigger a path search. -/
private def ultimateBearerCandidateCosted
    (W T : Nat) (tables : FactTables) (w m b : Nat) :
    Complexity.Costed (Option UltimateBearerCandidate) := do
  let moment ← Complexity.diagnosticUnaryCosted W T tables .moment b w
  Complexity.Costed.charge 1 <| if moment then Complexity.Costed.pure none else do
    let path ← tables.momentOfPathCosted T w m b
    Complexity.Costed.charge 1 <| match path with
    | none => Complexity.Costed.pure none
    | some path => Complexity.Costed.pure (some ⟨b, path⟩)

private theorem ultimateBearerCandidateCosted_value
    (W T : Nat) (tables : FactTables) (w m b : Nat) :
    (ultimateBearerCandidateCosted W T tables w m b).value =
      if (Complexity.diagnosticUnaryCosted W T tables .moment b w).value then none
      else (tables.momentOfPathCosted T w m b).value.map (fun path => ⟨b, path⟩) := by
  simp only [ultimateBearerCandidateCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases (tables.momentOfPathCosted T w m b).value <;> rfl

private theorem ultimateBearerCandidateCosted_cost_le
    (W T : Nat) (tables : FactTables) (w m b : Nat) :
    (ultimateBearerCandidateCosted W T tables w m b).cost ≤ 11 * T + 21 := by
  have hq := Complexity.diagnosticUnaryCosted_cost_le W T tables .moment b w
  have hp := tables.momentOfPathCosted_cost_le T w m b
  simp only [ultimateBearerCandidateCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.pure_cost]; omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split <;> simp only [Complexity.Costed.pure_cost] <;> omega

/-- Finite coordinates and table agreement recover the sparse moment flag.
Path selection is specified independently by the compiler's next-hop recurrence. -/
private theorem ultimateBearerCandidateCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (w : Fin W) (m : Nat) (b : Fin T) :
    (ultimateBearerCandidateCosted W T tables w.val m b.val).value =
      if tables.unaryLookup "moment" b.val w.val then none
      else (tables.momentOfPath? T w.val m b.val).map (fun path => ⟨b.val, path⟩) := by
  rw [ultimateBearerCandidateCosted_value,
    Complexity.diagnosticUnaryCosted_value W T tables agreement .moment b w]
  rfl

private theorem ultimateBearerCandidateCosted_path_size
    (W T : Nat) (tables : FactTables) (w m b : Nat) (candidate : UltimateBearerCandidate)
    (found : (ultimateBearerCandidateCosted W T tables w m b).value = some candidate) :
    candidate.path.size ≤ T + 1 := by
  rw [ultimateBearerCandidateCosted_value] at found
  split at found
  · cases found
  · cases hp : (tables.momentOfPathCosted T w m b).value with
    | none => simp only [hp, Option.map_none] at found; cases found
    | some path =>
        simp only [hp, Option.map_some, Option.some.injEq] at found
        cases found
        exact FactTables.momentOfPathCosted_some_size tables T w m b path hp

/-- Visit bearer coordinates directly and append each successful candidate once.
The bound includes array initialization and all path-construction work. -/
private def ultimateBearerCandidatesCosted
    (W T : Nat) (tables : FactTables) (w m : Nat) :
    Complexity.Costed (Array UltimateBearerCandidate) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 T #[] (fun _ => false) fun out b => do
      let candidate ← ultimateBearerCandidateCosted W T tables w m b
      Complexity.Costed.charge 1 <| match candidate with
      | none => Complexity.Costed.pure out
      | some candidate => Complexity.Costed.tick (out.push candidate) 1

private theorem ultimateBearerCandidatesCosted_value
    (W T : Nat) (tables : FactTables) (w m : Nat) :
    (ultimateBearerCandidatesCosted W T tables w m).value =
      ((List.range T).filterMap fun b =>
        (ultimateBearerCandidateCosted W T tables w m b).value).toArray := by
  rw [ultimateBearerCandidatesCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  have step (out : Array UltimateBearerCandidate) (b : Nat) :
      (match (ultimateBearerCandidateCosted W T tables w m b).value with
        | none => Complexity.Costed.pure out
        | some c => Complexity.Costed.tick (out.push c) 1).value =
      match (ultimateBearerCandidateCosted W T tables w m b).value with
      | some c => out.push c
      | none => out := by
    cases (ultimateBearerCandidateCosted W T tables w m b).value <;> rfl
  simp only [step]
  calc
    _ = ((List.range T).filterMap fun b =>
        (ultimateBearerCandidateCosted W T tables w m b).value).foldl
        (fun out c => out.push c) (#[] : Array UltimateBearerCandidate) := by
      rw [List.foldl_filterMap]
      apply congrArg (fun visit => (List.range T).foldl visit (#[] : Array UltimateBearerCandidate))
      funext out b
      cases (ultimateBearerCandidateCosted W T tables w m b).value <;> rfl
    _ = _ := by rw [List.foldl_push_eq_append']; simp

private theorem ultimateBearerCandidatesCosted_cost_le
    (W T : Nat) (tables : FactTables) (w m : Nat) :
    (ultimateBearerCandidatesCosted W T tables w m).cost ≤ T * (11 * T + 26) + 1 := by
  unfold ultimateBearerCandidatesCosted
  simp only [Complexity.Costed.charge_cost]
  rw [Nat.add_comm 1]
  apply Nat.add_le_add_right
  refine le_trans (foldDiagDomainCosted_cost_le _ _ _ _ _ (11 * T + 23) ?_) ?_
  · intro out b hlo hhi
    have h := ultimateBearerCandidateCosted_cost_le W T tables w m b
    simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split <;> simp only [Complexity.Costed.pure_cost, Complexity.Costed.tick_cost] <;> omega
  · simp [Nat.add_assoc]

private theorem ultimateBearerCandidatesCosted_size_le
    (W T : Nat) (tables : FactTables) (w m : Nat) :
    (ultimateBearerCandidatesCosted W T tables w m).value.size ≤ T := by
  rw [ultimateBearerCandidatesCosted_value, List.size_toArray]
  exact le_trans (List.length_filterMap_le ..) (by simp)

private theorem ultimateBearerCandidatesCosted_paths_size
    (W T : Nat) (tables : FactTables) (w m : Nat) (candidate : UltimateBearerCandidate)
    (mem : candidate ∈ (ultimateBearerCandidatesCosted W T tables w m).value) :
    candidate.path.size ≤ T + 1 := by
  rw [ultimateBearerCandidatesCosted_value] at mem
  obtain ⟨b, hb, found⟩ := List.mem_filterMap.mp (List.mem_toArray.mp mem)
  exact ultimateBearerCandidateCosted_path_size W T tables w m b candidate found

/-- Inspect one moment for the selected failure category. The category test
is counted too; its callers use only emptiness or a comparison with one. -/
private def firstMomentCandidateCosted
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool) (w m : Nat) :
    Complexity.Costed (Option (Nat × Nat × Array UltimateBearerCandidate)) := do
  let moment ← Complexity.diagnosticUnaryCosted W T tables .moment m w
  Complexity.Costed.charge 1 <| if moment then do
    let candidates ← ultimateBearerCandidatesCosted W T tables w m
    let accepted ← accept candidates
    Complexity.Costed.charge 1 <| if accepted then
      Complexity.Costed.pure (some (w, m, candidates))
    else Complexity.Costed.pure none
  else Complexity.Costed.pure none

private theorem firstMomentCandidateCosted_value
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool) (w m : Nat) :
    (firstMomentCandidateCosted W T tables accept w m).value =
      if (Complexity.diagnosticUnaryCosted W T tables .moment m w).value then
        let candidates := (ultimateBearerCandidatesCosted W T tables w m).value
        if (accept candidates).value then some (w, m, candidates) else none
      else none := by
  simp only [firstMomentCandidateCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    split <;> rfl
  · rfl

private theorem firstMomentCandidateCosted_cost_le
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool)
    (haccept : ∀ cs, (accept cs).cost ≤ 1) (w m : Nat) :
    (firstMomentCandidateCosted W T tables accept w m).cost ≤ T * (11 * T + 26) + 16 := by
  have hq := Complexity.diagnosticUnaryCosted_cost_le W T tables .moment m w
  have hc := ultimateBearerCandidatesCosted_cost_le W T tables w m
  have ha := haccept (ultimateBearerCandidatesCosted W T tables w m).value
  simp only [firstMomentCandidateCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split <;> simp only [Complexity.Costed.pure_cost] <;> omega
  · simp only [Complexity.Costed.pure_cost]; omega

private theorem firstMomentCandidateCosted_candidate_size_le
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool)
    (w m w' m' : Nat) (candidates : Array UltimateBearerCandidate)
    (found : (firstMomentCandidateCosted W T tables accept w m).value = some (w', m', candidates)) :
    candidates.size ≤ T := by
  rw [firstMomentCandidateCosted_value] at found
  split at found
  · dsimp only at found
    split at found
    · simp only [Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.2.2]
      exact ultimateBearerCandidatesCosted_size_le W T tables w m
    · cases found
  · cases found

/-- Worlds precede moments in the search order. Numeric loops stop at the
first accepted assignment and do not construct a world/thing product list. -/
private def firstMomentCandidatesWhereCosted
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool) :
    Complexity.Costed (Option (Nat × Nat × Array UltimateBearerCandidate)) :=
  foldDiagDomainCosted 0 W none Option.isSome fun _ w =>
    foldDiagDomainCosted 0 T none Option.isSome fun _ m =>
      firstMomentCandidateCosted W T tables accept w m

private def ax68SearchCostBound (W T : Nat) : Nat :=
  W * (T * (T * (11 * T + 26) + 19) + 3)

private theorem ax68SearchCostBound_mono {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax68SearchCostBound W T ≤ ax68SearchCostBound W' T' := by
  unfold ax68SearchCostBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

private theorem firstMomentCandidatesWhereCosted_value
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool) :
    (firstMomentCandidatesWhereCosted W T tables accept).value =
      (List.range W).findSome? (fun w =>
        (List.range T).findSome? (fun m =>
          (firstMomentCandidateCosted W T tables accept w m).value)) := by
  unfold firstMomentCandidatesWhereCosted
  apply foldDiagDomainCosted_firstSome_value
  intro w hw
  apply foldDiagDomainCosted_firstSome_value
  intro m hm
  rfl

private theorem firstMomentCandidatesWhereCosted_cost_le
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool)
    (haccept : ∀ cs, (accept cs).cost ≤ 1) :
    (firstMomentCandidatesWhereCosted W T tables accept).cost ≤ ax68SearchCostBound W T := by
  unfold firstMomentCandidatesWhereCosted ax68SearchCostBound
  apply foldDiagDomainCosted_cost_le
  intro state w hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state m hlo hhi
  exact firstMomentCandidateCosted_cost_le W T tables accept haccept w m

private theorem firstMomentCandidatesWhereCosted_candidate_size_le
    (W T : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Complexity.Costed Bool)
    (w m : Nat) (candidates : Array UltimateBearerCandidate)
    (found : (firstMomentCandidatesWhereCosted W T tables accept).value = some (w, m, candidates)) :
    candidates.size ≤ T := by
  rw [firstMomentCandidatesWhereCosted_value] at found
  obtain ⟨w', hw', found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨m', hm', found⟩ := List.exists_of_findSome?_eq_some found
  exact firstMomentCandidateCosted_candidate_size_le W T tables accept w' m' w m candidates found

private def firstMomentWithoutUltimateBearerCosted
    (W T : Nat) (tables : FactTables) : Complexity.Costed (Option (Nat × Nat)) :=
  Complexity.Costed.charge 1 <| Complexity.Costed.map
    (Option.map fun result => (result.1, result.2.1))
    (firstMomentCandidatesWhereCosted W T tables fun cs => Complexity.Costed.tick cs.isEmpty 1)

private def firstMomentWithoutUltimateBearer
    (W T : Nat) (tables : FactTables) : Option (Nat × Nat) :=
  (firstMomentWithoutUltimateBearerCosted W T tables).value

private def firstMomentWithMultipleUltimateBearersCosted
    (W T : Nat) (tables : FactTables) :
    Complexity.Costed (Option (Nat × Nat × Array UltimateBearerCandidate)) :=
  firstMomentCandidatesWhereCosted W T tables fun cs => Complexity.Costed.tick (cs.size > 1) 1

private theorem firstMomentWithoutUltimateBearerCosted_cost_le
    (W T : Nat) (tables : FactTables) :
    (firstMomentWithoutUltimateBearerCosted W T tables).cost ≤ ax68SearchCostBound W T + 1 := by
  have h := firstMomentCandidatesWhereCosted_cost_le W T tables
    (fun cs => Complexity.Costed.tick cs.isEmpty 1) (by intro; rfl)
  simp only [firstMomentWithoutUltimateBearerCosted, Complexity.Costed.charge_cost,
    Complexity.Costed.map_cost]
  omega

private theorem firstMomentWithMultipleUltimateBearersCosted_cost_le
    (W T : Nat) (tables : FactTables) :
    (firstMomentWithMultipleUltimateBearersCosted W T tables).cost ≤ ax68SearchCostBound W T :=
  firstMomentCandidatesWhereCosted_cost_le W T tables
    (fun cs => Complexity.Costed.tick (cs.size > 1) 1) (by intro; rfl)

private theorem firstMomentWithMultipleUltimateBearersCosted_candidate_size_le
    (W T : Nat) (tables : FactTables) (w m : Nat) (candidates : Array UltimateBearerCandidate)
    (found : (firstMomentWithMultipleUltimateBearersCosted W T tables).value = some (w, m, candidates)) :
    candidates.size ≤ T :=
  firstMomentCandidatesWhereCosted_candidate_size_le W T tables _ w m candidates found

private def firstMomentWithMultipleUltimateBearers
    (W T : Nat) (tables : FactTables) : Option (Nat × Nat × Array UltimateBearerCandidate) :=
  (firstMomentWithMultipleUltimateBearersCosted W T tables).value

private theorem firstMomentWithMultipleUltimateBearersCosted_paths_size
    (W T : Nat) (tables : FactTables) (w m : Nat) (candidates : Array UltimateBearerCandidate)
    (found : (firstMomentWithMultipleUltimateBearersCosted W T tables).value = some (w, m, candidates)) :
    ∀ c ∈ candidates, c.path.size ≤ T + 1 := by
  unfold firstMomentWithMultipleUltimateBearersCosted at found
  rw [firstMomentCandidatesWhereCosted_value] at found
  obtain ⟨w', hw', found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨m', hm', found⟩ := List.exists_of_findSome?_eq_some found
  rw [firstMomentCandidateCosted_value] at found
  split at found
  · dsimp only at found
    split at found
    · simp only [Option.some.injEq, Prod.mk.injEq] at found
      rw [← found.2.2]
      exact ultimateBearerCandidatesCosted_paths_size W T tables w' m'
    · cases found
  · cases found

/-- Build the missing-bearer report when no bearer text is supplied, or the
multiple-bearer report otherwise. Names and path text are already resolved.
Each row costs a write and an emission, in addition to its concatenations. -/
private def ax68FailureRowsCosted (mn wn : String) (bearers : Option String) :
    Complexity.Costed (Array String) := Complexity.Costed.charge 1 <| match bearers with
  | none => do
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      let line ← Complexity.Costed.tick ("Closure check for ax68: `" ++ mn) 1
      let line ← Complexity.Costed.tick (line ++ "` is a moment at `") 1
      let line ← Complexity.Costed.tick (line ++ wn) 1
      let line ← Complexity.Costed.tick (line ++ "`, but no non-moment ultimate bearer is reachable through `InheresIn`.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      let line ← Complexity.Costed.tick ("Suggestion: add an inherence chain from `" ++ mn) 1
      let line ← Complexity.Costed.tick (line ++ "` to a concrete non-moment bearer, or reclassify the endpoint so it is not a moment.") 1
      Complexity.Costed.tick (out.push line) 2
  | some text => do
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      let line ← Complexity.Costed.tick ("Closure check for ax68: `" ++ mn) 1
      let line ← Complexity.Costed.tick (line ++ "` has multiple reachable non-moment bearers at `") 1
      let line ← Complexity.Costed.tick (line ++ wn) 1
      let line ← Complexity.Costed.tick (line ++ "`.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      let line ← Complexity.Costed.tick ("Reachable bearers: " ++ text) 1
      let line ← Complexity.Costed.tick (line ++ ".") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      Complexity.Costed.tick (out.push "Suggestion: remove the competing inherence branch, or reclassify the unintended endpoint so it is not an ultimate bearer.") 2

private theorem ax68FailureRowsCosted_value (mn wn : String) (bearers : Option String) :
    (ax68FailureRowsCosted mn wn bearers).value = match bearers with
    | none => #[
        s!"Closure check for ax68: `{mn}` is a moment at `{wn}`, but no non-moment ultimate bearer is reachable through `InheresIn`.",
        s!"Suggestion: add an inherence chain from `{mn}` to a concrete non-moment bearer, or reclassify the endpoint so it is not a moment."]
    | some text => #[
        s!"Closure check for ax68: `{mn}` has multiple reachable non-moment bearers at `{wn}`.",
        s!"Reachable bearers: {text}.",
        "Suggestion: remove the competing inherence branch, or reclassify the unintended endpoint so it is not an ultimate bearer."] := by
  cases bearers <;> rfl

private theorem ax68FailureRowsCosted_cost (mn wn : String) (bearers : Option String) :
    (ax68FailureRowsCosted mn wn bearers).cost = if bearers.isSome then 14 else 12 := by
  cases bearers <;> rfl

private theorem ax68FailureRowsCosted_size_le (mn wn : String) (bearers : Option String) :
    (ax68FailureRowsCosted mn wn bearers).value.size ≤ 3 := by
  rw [ax68FailureRowsCosted_value]
  cases bearers <;> simp

/-- Search missing bearers before multiple bearers. Each search stops at its
first result. The report reuses its stored paths and resolved names. Cost
composition follows Niu et al. (POPL 2022, doi:10.1145/3498670): a bind adds
the costs of the operations that execute and preserves their ordinary value. -/
def ax68ClosureAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let missing ← firstMomentWithoutUltimateBearerCosted worldNames.size thingNames.size tables
  Complexity.Costed.charge 1 <| match missing with
  | some (w, m) => do
      let mn ← indexedNameCosted thingNames m
      let wn ← indexedNameCosted worldNames w
      ax68FailureRowsCosted mn wn none
  | none => do
      let multiple ← firstMomentWithMultipleUltimateBearersCosted worldNames.size thingNames.size tables
      Complexity.Costed.charge 1 <| match multiple with
      | some (w, m, candidates) => do
          let mn ← indexedNameCosted thingNames m
          let wn ← indexedNameCosted worldNames w
          let rendered ← renderUltimateBearersCosted thingNames candidates
          ax68FailureRowsCosted mn wn (some rendered)
      | none => do
          let out ← Complexity.Costed.tick (#[] : Array String) 1
          let out ← Complexity.Costed.tick (out.push
            "Closure check for ax68: every moment in the diagnostic tables has exactly one non-moment endpoint in the stored next-hop paths.") 2
          Complexity.Costed.tick (out.push
            "If certification still reports ax68, inspect the correspondence between these paths, the compiled closure, and MomentOf.") 2

/-- Two search bounds cover category priority. At most T paths, each of length
at most T+1, give the rendering term. The remaining 26 calls cover names,
branch tests, report construction, and the final string default. -/
private def ax68ClosureAnalysisCostBound (W T : Nat) : Nat :=
  2 * ax68SearchCostBound W T + T * (9 * T + 23) + 26

private theorem ax68ClosureAnalysisCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax68ClosureAnalysisCostBound W T ≤ ax68ClosureAnalysisCostBound W' T' := by
  unfold ax68ClosureAnalysisCostBound
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul_left 2 (ax68SearchCostBound_mono hW hT))
    (Nat.mul_le_mul hT (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hT) 23))) 26

private theorem ax68ClosureAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).cost ≤
      ax68ClosureAnalysisCostBound worldNames.size thingNames.size := by
  have hmissing := firstMomentWithoutUltimateBearerCosted_cost_le
    worldNames.size thingNames.size tables
  have hmultiple := firstMomentWithMultipleUltimateBearersCosted_cost_le
    worldNames.size thingNames.size tables
  unfold ax68ClosureAnalysisCostBound
  simp only [ax68ClosureAnalysisCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, indexedNameCosted_cost, ax68FailureRowsCosted_cost,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split
    · rename_i w m candidates found
      have hc := firstMomentWithMultipleUltimateBearersCosted_candidate_size_le
        worldNames.size thingNames.size tables w m candidates found
      have hp := firstMomentWithMultipleUltimateBearersCosted_paths_size
        worldNames.size thingNames.size tables w m candidates found
      have hr := le_trans (renderUltimateBearersCosted_cost_le thingNames candidates
        thingNames.size hp) (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 1)
      simp only [Complexity.Costed.bind_cost, indexedNameCosted_cost, ax68FailureRowsCosted_cost,
        Option.isSome_some, ↓reduceIte]
      omega
    · simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
      omega

/-- This specification retains category priority and report text. It describes
the supplied diagnostic tables, without assuming that their paths are valid
inherence evidence. That separate correspondence requires compiled tables. -/
private theorem ax68ClosureAnalysisCosted_value_cases
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).value =
      match (firstMomentWithoutUltimateBearerCosted worldNames.size thingNames.size tables).value with
      | some (w, m) => #[
          s!"Closure check for ax68: `{indexedName thingNames m}` is a moment at `{indexedName worldNames w}`, but no non-moment ultimate bearer is reachable through `InheresIn`.",
          s!"Suggestion: add an inherence chain from `{indexedName thingNames m}` to a concrete non-moment bearer, or reclassify the endpoint so it is not a moment."]
      | none => match (firstMomentWithMultipleUltimateBearersCosted worldNames.size thingNames.size tables).value with
        | some (w, m, candidates) => #[
            s!"Closure check for ax68: `{indexedName thingNames m}` has multiple reachable non-moment bearers at `{indexedName worldNames w}`.",
            "Reachable bearers: " ++ String.intercalate ", " (candidates.toList.map fun c =>
              s!"`{indexedName thingNames c.bearer}` via `{renderThingPath thingNames c.path}`") ++ ".",
            "Suggestion: remove the competing inherence branch, or reclassify the unintended endpoint so it is not an ultimate bearer."]
        | none => #[
            "Closure check for ax68: every moment in the diagnostic tables has exactly one non-moment endpoint in the stored next-hop paths.",
            "If certification still reports ax68, inspect the correspondence between these paths, the compiled closure, and MomentOf."] := by
  simp only [ax68ClosureAnalysisCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.bind_value, indexedNameCosted_value,
      ax68FailureRowsCosted_value]
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    split
    · simp only [Complexity.Costed.bind_value, indexedNameCosted_value,
        renderUltimateBearersCosted_value, ax68FailureRowsCosted_value]
      rfl
    · rfl

private theorem ax68ClosureAnalysisCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).value.size ≤ 3 := by
  simp only [ax68ClosureAnalysisCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.bind_value]
    exact ax68FailureRowsCosted_size_le _ _ _
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    split
    · simp only [Complexity.Costed.bind_value]
      exact ax68FailureRowsCosted_size_le _ _ _
    · decide

def ax68ClosureAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax68ClosureAnalysisCosted worldNames thingNames tables).value

@[simp] theorem ax68ClosureAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).value =
      ax68ClosureAnalysis worldNames thingNames tables := rfl

/-- The elaborator runs this precheck before attempting the axiom-68 proof.
A missing bearer skips the multiple-bearer search: this is short-circuit
execution. Each searched result adds one option test, and the disjunction adds
one branch test. Report construction, if requested later, is a separate call. -/
def hasAx68ClosureFailureCosted (W T : Nat) (tables : FactTables) : Complexity.Costed Bool :=
  (Complexity.Costed.charge 1 <| Complexity.Costed.map Option.isSome
    (firstMomentWithoutUltimateBearerCosted W T tables)).orElse fun _ =>
      Complexity.Costed.charge 1 <| Complexity.Costed.map Option.isSome
        (firstMomentWithMultipleUltimateBearersCosted W T tables)

def hasAx68ClosureFailure (worldCount thingCount : Nat) (tables : FactTables) : Bool :=
  (hasAx68ClosureFailureCosted worldCount thingCount tables).value

theorem hasAx68ClosureFailureCosted_value (W T : Nat) (tables : FactTables) :
    (hasAx68ClosureFailureCosted W T tables).value =
      ((firstMomentWithoutUltimateBearer W T tables).isSome ||
        (firstMomentWithMultipleUltimateBearers W T tables).isSome) := by
  simp [hasAx68ClosureFailureCosted, firstMomentWithoutUltimateBearer,
    firstMomentWithMultipleUltimateBearers]

/-- Both searches have the same size bound. The missing-bearer search also
projects its result once. Two option tests and the disjunction give the other
three fixed operations. This bound includes no report rendering. -/
theorem hasAx68ClosureFailureCosted_cost_le (W T : Nat) (tables : FactTables) :
    (hasAx68ClosureFailureCosted W T tables).cost ≤
      2 * (W * (T * (T * (11 * T + 26) + 19) + 3)) + 4 := by
  have hleft := firstMomentWithoutUltimateBearerCosted_cost_le W T tables
  have hright := firstMomentWithMultipleUltimateBearersCosted_cost_le W T tables
  have h := Complexity.Costed.orElse_cost_le
    (Complexity.Costed.charge 1 <| Complexity.Costed.map Option.isSome
      (firstMomentWithoutUltimateBearerCosted W T tables))
    (fun _ => Complexity.Costed.charge 1 <| Complexity.Costed.map Option.isSome
      (firstMomentWithMultipleUltimateBearersCosted W T tables))
    (ax68SearchCostBound W T + 2) (ax68SearchCostBound W T + 1)
    (by simp only [Complexity.Costed.charge_cost, Complexity.Costed.map_cost]; omega)
    (by simp only [Complexity.Costed.charge_cost, Complexity.Costed.map_cost]; omega)
  unfold hasAx68ClosureFailureCosted
  unfold ax68SearchCostBound at h
  omega

private def partLookup (tables : FactTables) (x y w : Nat) : Bool :=
  x == y || tables.binaryLookup "part" x y w

/-- Reflexivity determines the answer before any coordinate guard or table
read. A non-reflexive pair uses the same guarded part query as formula atoms. -/
private def partLookupCosted (W T : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed Bool :=
  (Complexity.Costed.tick (x == y) 1).orElse
    (fun _ => Complexity.diagnosticBinaryCosted W T tables .part x y w)

private theorem partLookupCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (partLookupCosted W T tables x.val y.val w.val).value =
      partLookup tables x.val y.val w.val := by
  simp only [partLookupCosted, Complexity.Costed.orElse_value, Complexity.Costed.tick_value,
    Complexity.diagnosticBinaryCosted_value W T tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField, partLookup]

private theorem partLookupCosted_cost_le
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (partLookupCosted W T tables x y w).cost ≤ 19 := by
  exact Complexity.Costed.orElse_cost_le _ _ 1 17 (by rfl)
    (Complexity.diagnosticBinaryCosted_cost_le W T tables .part x y w)

/-- Collect FoundedBy targets once, in ascending coordinate order. Guarded
queries count coordinate checks and dense access. Numeric traversal prevents
duplicate facts from duplicating a candidate and needs no intermediate list.
The bound is 22T+1: initialization, then at most 17 query operations, a branch,
a push, and three loop operations for each of T things. -/
private def foundationCandidatesCosted
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 T #[] (fun _ => false) fun out y => do
      let founded ← Complexity.diagnosticBinaryCosted W T tables .foundedBy x y w
      if founded then Complexity.Costed.tick (out.push y) 2
      else Complexity.Costed.tick out 1

private theorem foundationCandidatesCosted_filter_value
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted W T tables x w).value =
      ((List.range T).filter (fun y =>
        (Complexity.diagnosticBinaryCosted W T tables .foundedBy x y w).value)).toArray := by
  rw [foundationCandidatesCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Complexity.Costed.bind_value]
  have h : (List.range T).foldl (fun out y =>
      (if (Complexity.diagnosticBinaryCosted W T tables .foundedBy x y w).value then
        Complexity.Costed.tick (out.push y) 2 else Complexity.Costed.tick out 1).value) #[] =
      (List.range T).foldl (fun out y =>
        if (Complexity.diagnosticBinaryCosted W T tables .foundedBy x y w).value then
          out.push y else out) #[] := by
    congr 1
    funext out y
    split <;> rfl
  rw [h, ← List.foldl_filter, List.foldl_push_eq_append']
  simp

private theorem foundationCandidatesCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (foundationCandidatesCosted W T tables x.val w.val).value =
      ((List.range T).filter (fun y => tables.binaryLookup "foundedBy" x.val y w.val)).toArray := by
  rw [foundationCandidatesCosted_filter_value]
  congr 1
  apply List.filter_congr
  intro y hy
  exact Complexity.diagnosticBinaryCosted_value W T tables agreement .foundedBy
    x ⟨y, List.mem_range.mp hy⟩ w

private theorem foundationCandidatesCosted_cost_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted W T tables x w).cost ≤ 22 * T + 1 := by
  have h := foldDiagDomainCosted_cost_le 0 T (#[] : Array Nat) (fun _ => false)
    (fun out y => Complexity.diagnosticBinaryCosted W T tables .foundedBy x y w >>= fun founded =>
      if founded then Complexity.Costed.tick (out.push y) 2 else Complexity.Costed.tick out 1)
    19 (by
      intro out y hlo hhi
      have hquery := Complexity.diagnosticBinaryCosted_cost_le W T tables .foundedBy x y w
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.tick_cost] <;> omega)
  simpa [foundationCandidatesCosted, Complexity.Costed.charge_cost,
    Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_right h 1

private theorem foundationCandidatesCosted_size_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted W T tables x w).value.size ≤ T := by
  rw [foundationCandidatesCosted_filter_value, List.size_toArray]
  exact le_trans (List.length_filter_le _ _) (by simp)

private theorem foundationCandidatesCosted_nodup
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted W T tables x w).value.toList.Nodup := by
  rw [foundationCandidatesCosted_filter_value]
  exact (List.nodup_range (n := T)).filter _

/-- A unique foundation is the only collected target. The size test proves
the direct array read safe; no second optional lookup repeats that check. -/
private def uniqueFoundationCosted (W T : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Option Nat) := do
  let candidates ← foundationCandidatesCosted W T tables x w
  Complexity.Costed.charge 2 <| if h : candidates.size = 1 then
    Complexity.Costed.tick (some candidates[0]) 1
  else Complexity.Costed.pure none

private theorem uniqueFoundationCosted_value
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (uniqueFoundationCosted W T tables x w).value =
      let candidates := (foundationCandidatesCosted W T tables x w).value
      if candidates.size = 1 then candidates[0]? else none := by
  simp only [uniqueFoundationCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.tick_value]
    exact (Array.getElem?_eq_getElem (by omega)).symm
  · simp_all

/-- Under table agreement, uniqueness means that filtering all finite targets
leaves a singleton. This states both the positive result and rejection of
missing or ambiguous foundations without referring to the counted search. -/
private theorem uniqueFoundationCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (uniqueFoundationCosted W T tables x.val w.val).value =
      match (List.range T).filter (fun y => tables.binaryLookup "foundedBy" x.val y w.val) with
      | [y] => some y
      | _ => none := by
  rw [uniqueFoundationCosted_value, foundationCandidatesCosted_sparse_value W T tables agreement]
  generalize (List.range T).filter
    (fun y => tables.binaryLookup "foundedBy" x.val y w.val) = ys
  cases ys with
  | nil => simp
  | cons y ys => cases ys <;> simp

private theorem uniqueFoundationCosted_cost_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (uniqueFoundationCosted W T tables x w).cost ≤ 22 * T + 4 := by
  have h := foundationCandidatesCosted_cost_le W T tables x w
  simp only [uniqueFoundationCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split <;> simp only [Complexity.Costed.tick_cost, Complexity.Costed.pure_cost] <;> omega

/-- Render the ordered ambiguity list with a string accumulator. Each name
costs four indexed-name operations and two quoting concatenations. A visited
item also charges the array read, loop, option branch, and any separator.
As in Niu et al.'s cost-aware semantics (POPL 2022, doi:10.1145/3498670),
the value proof and cost proof describe the same executable composition.
String-character copying remains outside this unit-cost model. -/
private def renderAmbiguousFoundationsCosted (names : Array Name) (indices : Array Nat) :
    Complexity.Costed String := do
  let joined ← Complexity.Costed.foldArray indices (none : Option String) fun out i => do
    let name ← indexedNameCosted names i
    let quoted ← Complexity.Costed.tick ("`" ++ name) 1
    let quoted ← Complexity.Costed.tick (quoted ++ "`") 1
    Complexity.Costed.charge 1 <| match out with
    | none => Complexity.Costed.pure (some quoted)
    | some text => do
        let text ← Complexity.Costed.tick (text ++ "; ") 1
        let text ← Complexity.Costed.tick (text ++ quoted) 1
        Complexity.Costed.pure (some text)
  let text ← Complexity.Costed.tick (joined.getD "") 1
  Complexity.Costed.tick ("ambiguous foundations " ++ text) 1

private theorem renderAmbiguousFoundationsCosted_cost_le (names : Array Name) (indices : Array Nat) :
    (renderAmbiguousFoundationsCosted names indices).cost ≤ 11 * indices.size + 2 := by
  have h := Complexity.Costed.foldArray_cost_le indices (none : Option String)
    (fun out i => do
      let name ← indexedNameCosted names i
      let quoted ← Complexity.Costed.tick ("`" ++ name) 1
      let quoted ← Complexity.Costed.tick (quoted ++ "`") 1
      Complexity.Costed.charge 1 <| match out with
      | none => Complexity.Costed.pure (some quoted)
      | some text => do
          let text ← Complexity.Costed.tick (text ++ "; ") 1
          let text ← Complexity.Costed.tick (text ++ quoted) 1
          Complexity.Costed.pure (some text))
    9 (by
      intro out i hi
      simp only [Bind.bind, Complexity.Costed.bind_cost, indexedNameCosted_cost,
        Complexity.Costed.tick_cost, Complexity.Costed.charge_cost]
      cases out <;> simp)
  simp only [Bind.bind] at h
  simp only [renderAmbiguousFoundationsCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost]
  omega

private theorem renderAmbiguousFoundationsCosted_value (names : Array Name) (indices : Array Nat) :
    (renderAmbiguousFoundationsCosted names indices).value =
      "ambiguous foundations " ++ String.intercalate "; "
        (indices.toList.map (fun i => "`" ++ indexedName names i ++ "`")) := by
  have fold (xs prefixNames : List String) :
      (xs.foldl (fun out name => match out with
        | none => some name
        | some text => some (text ++ "; " ++ name))
        (if prefixNames = [] then none else some (String.intercalate "; " prefixNames))).getD "" =
        String.intercalate "; " (prefixNames ++ xs) := by
    induction xs generalizing prefixNames with
    | nil => cases prefixNames <;> simp
    | cons name xs ih =>
        rw [List.append_cons, ← ih, List.foldl_cons]
        congr
        cases prefixNames with
        | nil => simp
        | cons first rest =>
            simp only [List.cons_ne_nil, ↓reduceIte, List.cons_append, Option.some.injEq]
            rw [← List.cons_append, String.intercalate_append_of_ne_nil (by simp) (by simp),
              String.intercalate_singleton]
  have h := fold (indices.toList.map (fun i => "`" ++ indexedName names i ++ "`")) []
  simp only [List.nil_append, ↓reduceIte, List.foldl_map] at h
  simp only [renderAmbiguousFoundationsCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArray_value, ← Array.foldl_toList,
    indexedNameCosted_value, Complexity.Costed.charge_value]
  congr 1
  convert h using 1
  congr 2
  funext out i
  cases out <;> rfl

/-- Foundation status retains all candidates so ambiguity can name every
target. It charges each visited size test and constructs only the selected text.
With T thing names, collection and formatting together cost at most 33T+12. -/
private def renderFoundationStatusCosted
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed String := do
  let candidates ← foundationCandidatesCosted worldCount thingNames.size tables x w
  Complexity.Costed.charge 2 <| if candidates.isEmpty then
    Complexity.Costed.pure "no `FoundedBy` fact"
  else Complexity.Costed.charge 2 <| if h : candidates.size = 1 then do
    let candidate ← Complexity.Costed.tick candidates[0] 1
    let name ← indexedNameCosted thingNames candidate
    let text ← Complexity.Costed.tick ("foundation `" ++ name) 1
    Complexity.Costed.tick (text ++ "`") 1
  else renderAmbiguousFoundationsCosted thingNames candidates

private theorem renderFoundationStatusCosted_value
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderFoundationStatusCosted worldCount thingNames tables x w).value =
      let candidates := (foundationCandidatesCosted worldCount thingNames.size tables x w).value
      if candidates.isEmpty then "no `FoundedBy` fact"
      else if candidates.size = 1 then
        "foundation `" ++ indexedName thingNames candidates[0]! ++ "`"
      else "ambiguous foundations " ++ String.intercalate "; "
        (candidates.toList.map (fun y => "`" ++ indexedName thingNames y ++ "`")) := by
  simp only [renderFoundationStatusCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · rfl
  · split
    · rw [getElem!_pos
        (foundationCandidatesCosted worldCount thingNames.size tables x w).value 0 (by omega)]
      simp only [Complexity.Costed.charge_value, Complexity.Costed.bind_value,
        Complexity.Costed.tick_value, indexedNameCosted_value]
    · exact renderAmbiguousFoundationsCosted_value _ _

private theorem renderFoundationStatusCosted_sparse_value
    (W : Nat) (thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups W thingNames.size = tables.denseLookups W thingNames.size)
    (x : Fin thingNames.size) (w : Fin W) :
    (renderFoundationStatusCosted W thingNames tables x.val w.val).value =
      let candidates := ((List.range thingNames.size).filter
        (fun y => tables.binaryLookup "foundedBy" x.val y w.val)).toArray
      if candidates.isEmpty then "no `FoundedBy` fact"
      else if candidates.size = 1 then
        "foundation `" ++ indexedName thingNames candidates[0]! ++ "`"
      else "ambiguous foundations " ++ String.intercalate "; "
        (candidates.toList.map (fun y => "`" ++ indexedName thingNames y ++ "`")) := by
  rw [renderFoundationStatusCosted_value,
    foundationCandidatesCosted_sparse_value W thingNames.size tables agreement]

private theorem renderFoundationStatusCosted_cost_le
    (worldCount : Nat) (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderFoundationStatusCosted worldCount thingNames tables x w).cost ≤
      33 * thingNames.size + 12 := by
  have hcost := foundationCandidatesCosted_cost_le worldCount thingNames.size tables x w
  have hsize := foundationCandidatesCosted_size_le worldCount thingNames.size tables x w
  have hrender := renderAmbiguousFoundationsCosted_cost_le thingNames
    (foundationCandidatesCosted worldCount thingNames.size tables x w).value
  simp only [renderFoundationStatusCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.pure_cost]
    omega
  · simp only [Complexity.Costed.charge_cost]
    split
    · simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost, indexedNameCosted_cost]
      omega
    · omega

/-- Both unique-foundation searches run before comparing their results.
The optional result distinguishes an unequal pair from missing or ambiguous
foundations. Each visited option branch and the final equality are charged. -/
private def foundationEqCosted
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Option Bool) := do
  let left ← uniqueFoundationCosted W T tables x w
  let right ← uniqueFoundationCosted W T tables y w
  Complexity.Costed.charge 1 <| match left with
  | none => Complexity.Costed.pure none
  | some fx => Complexity.Costed.charge 1 <| match right with
    | none => Complexity.Costed.pure none
    | some fy => Complexity.Costed.tick (some (fx == fy)) 1

private theorem foundationEqCosted_value
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (foundationEqCosted W T tables x y w).value =
      match (uniqueFoundationCosted W T tables x w).value,
        (uniqueFoundationCosted W T tables y w).value with
      | some fx, some fy => some (fx == fy)
      | _, _ => none := by
  simp only [foundationEqCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  cases (uniqueFoundationCosted W T tables x w).value <;>
    cases (uniqueFoundationCosted W T tables y w).value <;> rfl

private theorem foundationEqCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (foundationEqCosted W T tables x.val y.val w.val).value =
      match (List.range T).filter (fun f => tables.binaryLookup "foundedBy" x.val f w.val),
        (List.range T).filter (fun f => tables.binaryLookup "foundedBy" y.val f w.val) with
      | [fx], [fy] => some (fx == fy)
      | _, _ => none := by
  rw [foundationEqCosted_value,
    uniqueFoundationCosted_sparse_value W T tables agreement,
    uniqueFoundationCosted_sparse_value W T tables agreement]
  generalize (List.range T).filter
    (fun f => tables.binaryLookup "foundedBy" x.val f w.val) = xs
  generalize (List.range T).filter
    (fun f => tables.binaryLookup "foundedBy" y.val f w.val) = ys
  cases xs with
  | nil => cases ys <;> rfl
  | cons fx xs =>
      cases xs with
      | nil => cases ys with
        | nil => rfl
        | cons fy ys => cases ys <;> rfl
      | cons next rest => cases ys <;> rfl

private theorem foundationEqCosted_cost_le
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (foundationEqCosted W T tables x y w).cost ≤ 44 * T + 11 := by
  have hleft := uniqueFoundationCosted_cost_le W T tables x w
  have hright := uniqueFoundationCosted_cost_le W T tables y w
  simp only [foundationEqCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  cases (uniqueFoundationCosted W T tables x w).value <;>
    cases (uniqueFoundationCosted W T tables y w).value <;>
    simp only [Complexity.Costed.charge_cost, Complexity.Costed.tick_cost,
      Complexity.Costed.pure_cost] <;> omega

/-- Sharing a foundation means having at least one common FoundedBy target.
It does not require either thing to have a unique foundation. The finite loop
visits targets in coordinate order, skips the second query when the first is
false, and stops at the first common target. No target list is allocated. -/
private def sameFoundationLookupCosted
    (W T : Nat) (tables : FactTables) (x y w : Nat) : Complexity.Costed Bool :=
  Complexity.anyFinCosted T fun foundation =>
    (Complexity.diagnosticBinaryCosted W T tables .foundedBy x foundation.val w).andThen
      (fun _ => Complexity.diagnosticBinaryCosted W T tables .foundedBy y foundation.val w)

private theorem sameFoundationLookupCosted_cost_le
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (sameFoundationLookupCosted W T tables x y w).cost ≤ 37 * T := by
  unfold sameFoundationLookupCosted
  rw [Complexity.anyFinCosted_eq_list]
  have h := Complexity.anyListCosted_cost_le (List.finRange T)
    (fun foundation =>
      (Complexity.diagnosticBinaryCosted W T tables .foundedBy x foundation.val w).andThen
        (fun _ => Complexity.diagnosticBinaryCosted W T tables .foundedBy y foundation.val w))
    35 (by
      intro foundation hfoundation
      exact Complexity.Costed.andThen_cost_le _ _ 17 17
        (Complexity.diagnosticBinaryCosted_cost_le W T tables .foundedBy x foundation.val w)
        (Complexity.diagnosticBinaryCosted_cost_le W T tables .foundedBy y foundation.val w))
  simpa [Nat.mul_comm] using h

private theorem sameFoundationLookupCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (sameFoundationLookupCosted W T tables x.val y.val w.val).value =
      (List.finRange T).any (fun foundation =>
        tables.binaryLookup "foundedBy" x.val foundation.val w.val &&
          tables.binaryLookup "foundedBy" y.val foundation.val w.val) := by
  simp only [sameFoundationLookupCosted, Complexity.anyFinCosted_eq_list,
    Complexity.anyListCosted_value, Complexity.Costed.andThen_value,
    Complexity.diagnosticBinaryCosted_value W T tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem sameFoundationLookupCosted_iff
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (sameFoundationLookupCosted W T tables x.val y.val w.val).value = true ↔
      ∃ foundation : Fin T,
        tables.binaryLookup "foundedBy" x.val foundation.val w.val = true ∧
          tables.binaryLookup "foundedBy" y.val foundation.val w.val = true := by
  rw [sameFoundationLookupCosted_sparse_value W T tables agreement x y w]
  simp

/-- Axiom 73's right-hand predicate checks computed mode, then inherence,
then a common foundation. Each later operand is delayed until all preceding
ones are true. The fixed mode predicate needs no string-name dispatch.
This follows the compositional cost semantics of Niu et al. (POPL 2022):
the value and the visited-work count come from one executable definition. -/
private def ax73CharacterizedCosted
    (W T : Nat) (tables : FactTables) (z x y w : Nat) : Complexity.Costed Bool :=
  (externallyDependentModeLookupCosted W T tables z w).andThen (fun _ =>
    (Complexity.diagnosticBinaryCosted W T tables .inheresIn z y w).andThen (fun _ =>
      sameFoundationLookupCosted W T tables z x w))

private def ax73CharacterizedCostBound (W T : Nat) : Nat :=
  T * (28 * W + T * (56 * W + 22) + 3) + 13 + 37 * T + 19

private theorem ax73CharacterizedCosted_cost_le
    (W T : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73CharacterizedCosted W T tables z x y w).cost ≤ ax73CharacterizedCostBound W T := by
  unfold ax73CharacterizedCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _
      (T * (28 * W + T * (56 * W + 22) + 3) + 13) (17 + 1 + 37 * T)
      (externallyDependentModeLookupCosted_cost_le W T tables z w) ?_) ?_
  · exact Complexity.Costed.andThen_cost_le _ _ 17 (37 * T)
      (Complexity.diagnosticBinaryCosted_cost_le W T tables .inheresIn z y w)
      (sameFoundationLookupCosted_cost_le W T tables z x w)
  · unfold ax73CharacterizedCostBound
    omega

/-- Under table agreement, the predicate has its sparse relational meaning.
The computed-mode correspondence theorem supplies its modal interpretation.
The foundation test is existential, including when several targets are shared. -/
private theorem ax73CharacterizedCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (z x y : Fin T) (w : Fin W) :
    (ax73CharacterizedCosted W T tables z.val x.val y.val w.val).value =
      ((externallyDependentModeLookupCosted W T tables z.val w.val).value &&
        (tables.binaryLookup "inheresIn" z.val y.val w.val &&
          (List.finRange T).any (fun foundation =>
            tables.binaryLookup "foundedBy" z.val foundation.val w.val &&
              tables.binaryLookup "foundedBy" x.val foundation.val w.val))) := by
  simp only [ax73CharacterizedCosted, Complexity.Costed.andThen_value,
    Complexity.diagnosticBinaryCosted_value W T tables agreement,
    sameFoundationLookupCosted_sparse_value W T tables agreement,
    FactTables.binaryTypedTable, BinaryField.toTableField]

private theorem ax73CharacterizedCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax73CharacterizedCostBound W T ≤ ax73CharacterizedCostBound W' T' := by
  unfold ax73CharacterizedCostBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

/-
Declared product-family validation for ax99.

The axiom quantifies over an existential finite family `ys zs : Fin n → Thing`,
so it does not fit the simple `DiagFormula` language above. The validator in
`Complexity.Diagnostics.ProductFamily` checks the supplied arrays. These
helpers locate the first failing association and explain its requirements.
-/
/-- Collect characterization targets once, in ascending coordinate order.
The guarded table query prevents invalid coordinates from aliasing a cell.
The collector charges initialization, every query, and every appended target. -/
private def characterizationTargetsCosted
    (W T : Nat) (tables : FactTables) (t w : Nat) :
    Complexity.Costed (Array Nat) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 T #[] (fun _ => false) fun out z => do
      let characterizes ← Complexity.diagnosticBinaryCosted W T tables .characterization t z w
      if characterizes then Complexity.Costed.tick (out.push z) 2
      else Complexity.Costed.tick out 1

private theorem characterizationTargetsCosted_filter_value
    (W T : Nat) (tables : FactTables) (t w : Nat) :
    (characterizationTargetsCosted W T tables t w).value =
      ((List.range T).filter (fun z =>
        (Complexity.diagnosticBinaryCosted W T tables .characterization t z w).value)).toArray := by
  rw [characterizationTargetsCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Complexity.Costed.bind_value]
  have h : (List.range T).foldl (fun out z =>
      (if (Complexity.diagnosticBinaryCosted W T tables .characterization t z w).value then
        Complexity.Costed.tick (out.push z) 2 else Complexity.Costed.tick out 1).value) #[] =
      (List.range T).foldl (fun out z =>
        if (Complexity.diagnosticBinaryCosted W T tables .characterization t z w).value then
          out.push z else out) #[] := by
    congr 1
    funext out z
    split <;> rfl
  rw [h, ← List.foldl_filter, List.foldl_push_eq_append']
  simp

private theorem characterizationTargetsCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (t : Fin T) (w : Fin W) :
    (characterizationTargetsCosted W T tables t.val w.val).value =
      ((List.range T).filter (fun z => tables.binaryLookup "characterization" t.val z w.val)).toArray := by
  rw [characterizationTargetsCosted_filter_value]
  congr 1
  apply List.filter_congr
  intro z hz
  exact Complexity.diagnosticBinaryCosted_value W T tables agreement .characterization
    t ⟨z, List.mem_range.mp hz⟩ w

private theorem characterizationTargetsCosted_cost_le
    (W T : Nat) (tables : FactTables) (t w : Nat) :
    (characterizationTargetsCosted W T tables t w).cost ≤ 22 * T + 1 := by
  have h := foldDiagDomainCosted_cost_le 0 T (#[] : Array Nat) (fun _ => false)
    (fun out z => Complexity.diagnosticBinaryCosted W T tables .characterization t z w >>= fun characterizes =>
      if characterizes then Complexity.Costed.tick (out.push z) 2 else Complexity.Costed.tick out 1)
    19 (by
      intro out z hlo hhi
      have hquery := Complexity.diagnosticBinaryCosted_cost_le W T tables .characterization t z w
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.tick_cost] <;> omega)
  simpa [characterizationTargetsCosted, Complexity.Costed.charge_cost,
    Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_right h 1

private theorem characterizationTargetsCosted_size_le
    (W T : Nat) (tables : FactTables) (t w : Nat) :
    (characterizationTargetsCosted W T tables t w).value.size ≤ T := by
  rw [characterizationTargetsCosted_filter_value, List.size_toArray]
  exact le_trans (List.length_filter_le _ _) (by simp)

/-- Check registration in source order without copying the family array.
The type comparison runs only for a matching domain. This checks the key,
not the dimension/type arrays or their relational witness conditions. -/
private def productFamilyEntryPresentCosted
    (tables : FactTables) (x t : Nat) : Complexity.Costed Bool :=
  Complexity.anyArrayCosted tables.productFamilies fun family =>
    (Complexity.Costed.tick (family.domain == x) 1).andThen fun _ =>
      Complexity.Costed.tick (family.qualityType == t) 1

private theorem productFamilyEntryPresentCosted_value
    (tables : FactTables) (x t : Nat) :
    (productFamilyEntryPresentCosted tables x t).value =
      tables.productFamilies.any (fun family => family.domain == x && family.qualityType == t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [productFamilyEntryPresentCosted, Complexity.anyArrayCosted_eq_list,
    Complexity.anyListCosted_eq_true_iff]
  simp [Array.mem_iff_getElem]
  aesop

private theorem productFamilyEntryPresentCosted_cost_le
    (tables : FactTables) (x t : Nat) :
    (productFamilyEntryPresentCosted tables x t).cost ≤
      6 * tables.productFamilies.size := by
  unfold productFamilyEntryPresentCosted
  have h := Complexity.anyArrayCosted_cost_le tables.productFamilies
    (fun family => (Complexity.Costed.tick (family.domain == x) 1).andThen fun _ =>
      Complexity.Costed.tick (family.qualityType == t) 1) 3 (by
        intro family hfamily
        exact Complexity.Costed.andThen_cost_le _ _ 1 1 (Nat.le_refl _) (Nat.le_refl _))
  simpa [Nat.mul_comm] using h

/-- Render the axiom 99 failure category from already resolved names.
Each concatenation costs one; each appended row charges its write and emission. -/
private def ax99FailureRowsCosted (xn tn wn rendered : String) (entryPresent : Bool) :
    Complexity.Costed (Array String) :=
  Complexity.Costed.charge 1 <| if entryPresent then do
    let out ← Complexity.Costed.tick (#[] : Array String) 1
    let line ← Complexity.Costed.tick ("Product-family witness data is present for x = " ++ xn) 1
    let line ← Complexity.Costed.tick (line ++ ", t = ") 1
    let line ← Complexity.Costed.tick (line ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ ", w = ") 1
    let line ← Complexity.Costed.tick (line ++ wn) 1
    let line ← Complexity.Costed.tick (line ++ ", but it does not satisfy ax99.") 1
    let out ← Complexity.Costed.tick (out.push line) 2
    let line ← Complexity.Costed.tick ("The witness must list one quality dimension for each characterization of `" ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ "` and prove that every member of `") 1
    let line ← Complexity.Costed.tick (line ++ xn) 1
    let line ← Complexity.Costed.tick (line ++ "` projects into the corresponding dimension.") 1
    let out ← Complexity.Costed.tick (out.push line) 2
    let out ← Complexity.Costed.tick (out.push "Check the `dimensions` and `types` listed in the `product_family` block, the `Characterization(t, z)` facts, the `AssociatedWith(y, z)` facts for the listed dimensions, and the `TupleProjection(tuple, i, component)` plus `MemberOf(component, y)` facts for every domain member.") 2
    let line ← Complexity.Costed.tick ("Characterization targets found for `" ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ "`: ") 1
    let line ← Complexity.Costed.tick (line ++ rendered) 1
    let line ← Complexity.Costed.tick (line ++ ".") 1
    Complexity.Costed.tick (out.push line) 2
  else do
    let out ← Complexity.Costed.tick (#[] : Array String) 1
    let line ← Complexity.Costed.tick ("Missing product-family witness data for x = " ++ xn) 1
    let line ← Complexity.Costed.tick (line ++ ", t = ") 1
    let line ← Complexity.Costed.tick (line ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ ", w = ") 1
    let line ← Complexity.Costed.tick (line ++ wn) 1
    let line ← Complexity.Costed.tick (line ++ ".") 1
    let out ← Complexity.Costed.tick (out.push line) 2
    let line ← Complexity.Costed.tick ("The model says `" ++ xn) 1
    let line ← Complexity.Costed.tick (line ++ "` is a quality domain associated with `") 1
    let line ← Complexity.Costed.tick (line ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ "`, so ax99 needs an explicit finite product-family witness for that pair.") 1
    let out ← Complexity.Costed.tick (out.push line) 2
    let line ← Complexity.Costed.tick ("Add a block of the form `product_family " ++ xn) 1
    let line ← Complexity.Costed.tick (line ++ " for ") 1
    let line ← Complexity.Costed.tick (line ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ ":` with one `dimensions` entry and one `types` entry for each component quality type characterizing `") 1
    let line ← Complexity.Costed.tick (line ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ "`.") 1
    let out ← Complexity.Costed.tick (out.push line) 2
    let out ← Complexity.Costed.tick (out.push "For each listed dimension/type pair, also provide the ordinary facts that make the witness meaningful: `Characterization(t, z)`, `AssociatedWith(y, z)`, `MemberOf(tuple, x)` for domain members, `TupleProjection(tuple, i, component)`, and `MemberOf(component, y)`.") 2
    let line ← Complexity.Costed.tick ("Characterization targets currently found for `" ++ tn) 1
    let line ← Complexity.Costed.tick (line ++ "`: ") 1
    let line ← Complexity.Costed.tick (line ++ rendered) 1
    let line ← Complexity.Costed.tick (line ++ ".") 1
    Complexity.Costed.tick (out.push line) 2

private theorem ax99FailureRowsCosted_value (xn tn wn rendered : String) (entryPresent : Bool) :
    (ax99FailureRowsCosted xn tn wn rendered entryPresent).value =
      if entryPresent then #[
        s!"Product-family witness data is present for x = {xn}, t = {tn}, w = {wn}, but it does not satisfy ax99.",
        s!"The witness must list one quality dimension for each characterization of `{tn}` and prove that every member of `{xn}` projects into the corresponding dimension.",
        "Check the `dimensions` and `types` listed in the `product_family` block, the `Characterization(t, z)` facts, the `AssociatedWith(y, z)` facts for the listed dimensions, and the `TupleProjection(tuple, i, component)` plus `MemberOf(component, y)` facts for every domain member.",
        s!"Characterization targets found for `{tn}`: {rendered}."]
      else #[
        s!"Missing product-family witness data for x = {xn}, t = {tn}, w = {wn}.",
        s!"The model says `{xn}` is a quality domain associated with `{tn}`, so ax99 needs an explicit finite product-family witness for that pair.",
        s!"Add a block of the form `product_family {xn} for {tn}:` with one `dimensions` entry and one `types` entry for each component quality type characterizing `{tn}`.",
        "For each listed dimension/type pair, also provide the ordinary facts that make the witness meaningful: `Characterization(t, z)`, `AssociatedWith(y, z)`, `MemberOf(tuple, x)` for domain members, `TupleProjection(tuple, i, component)`, and `MemberOf(component, y)`.",
        s!"Characterization targets currently found for `{tn}`: {rendered}."]
    := by cases entryPresent <;> rfl

private theorem ax99FailureRowsCosted_cost (xn tn wn rendered : String) (entryPresent : Bool) :
    (ax99FailureRowsCosted xn tn wn rendered entryPresent).cost =
      if entryPresent then 24 else 32 := by
  cases entryPresent <;>
    simp only [ax99FailureRowsCosted, Complexity.Costed.charge_cost, Bool.false_eq_true,
      ↓reduceIte, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]

private theorem ax99FailureRowsCosted_size_le (xn tn wn rendered : String) (entryPresent : Bool) :
    (ax99FailureRowsCosted xn tn wn rendered entryPresent).value.size ≤ 5 := by
  rw [ax99FailureRowsCosted_value]
  cases entryPresent <;> simp

private def ax99FailureEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x t w : Nat) (entryPresent : Bool) : Complexity.Costed (Array String) := do
  let zs ← characterizationTargetsCosted worldNames.size thingNames.size tables t w
  let rendered ← Complexity.Costed.charge 2 <| if zs.isEmpty then
    Complexity.Costed.pure "none" else joinIndexedNamesCosted thingNames zs
  let xn ← indexedNameCosted thingNames x
  let tn ← indexedNameCosted thingNames t
  let wn ← indexedNameCosted worldNames w
  ax99FailureRowsCosted xn tn wn rendered entryPresent

private theorem ax99FailureEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x t w : Nat) (entryPresent : Bool) :
    (ax99FailureEvidenceCosted worldNames thingNames tables x t w entryPresent).cost ≤
      31 * thingNames.size + 48 := by
  have hcost := characterizationTargetsCosted_cost_le worldNames.size thingNames.size tables t w
  have hsize := characterizationTargetsCosted_size_le worldNames.size thingNames.size tables t w
  have hjoin := joinIndexedNamesCosted_cost_le thingNames
    (characterizationTargetsCosted worldNames.size thingNames.size tables t w).value
  simp only [ax99FailureEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    indexedNameCosted_cost, ax99FailureRowsCosted_cost, Complexity.Costed.charge_cost]
  split <;> cases entryPresent <;> simp only [Complexity.Costed.pure_cost, Bool.false_eq_true,
    ↓reduceIte] <;> omega

private theorem ax99FailureEvidenceCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x t w : Nat) (entryPresent : Bool) :
    (ax99FailureEvidenceCosted worldNames thingNames tables x t w entryPresent).value.size ≤ 5 := by
  simp only [ax99FailureEvidenceCosted, Bind.bind, Complexity.Costed.bind_value]
  exact ax99FailureRowsCosted_size_le ..

/-- Check one association and construct evidence only after a failed registry
check. Missing registration and invalid registered witnesses remain distinct. -/
private def ax99AssociationCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x t w : Nat) :
    Complexity.Costed (Option (Array String)) := do
  let associated ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size
    tables .associatedWith x t w
  Complexity.Costed.charge 1 <| if associated then do
    let entry ← productFamilyEntryPresentCosted tables x t
    Complexity.Costed.charge 1 <| if entry then do
      let valid ← Complexity.productFamiliesDiagnosticCosted
        worldNames.size thingNames.size tables x t w
      Complexity.Costed.charge 1 <| if valid then Complexity.Costed.pure none else do
        let rows ← ax99FailureEvidenceCosted worldNames thingNames tables x t w true
        Complexity.Costed.pure (some rows)
    else do
      let rows ← ax99FailureEvidenceCosted worldNames thingNames tables x t w false
      Complexity.Costed.pure (some rows)
  else Complexity.Costed.pure none

private def ax99AssociationCostBound (T : Nat) (families : Array ProductFamilySpec) : Nat :=
  6 * families.size + Complexity.productFamiliesDiagnosticBound T families + 31 * T + 68

private theorem ax99AssociationCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x t w : Nat) :
    (ax99AssociationCosted worldNames thingNames tables x t w).value =
      if (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size
          tables .associatedWith x t w).value then
        if (productFamilyEntryPresentCosted tables x t).value then
          if (Complexity.productFamiliesDiagnosticCosted worldNames.size thingNames.size tables x t w).value then
            none
          else some (ax99FailureEvidenceCosted worldNames thingNames tables x t w true).value
        else some (ax99FailureEvidenceCosted worldNames thingNames tables x t w false).value
      else none := by
  simp only [ax99AssociationCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    split
    · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
      split <;> simp only [Complexity.Costed.bind_value, Complexity.Costed.pure_value]
    · simp only [Complexity.Costed.bind_value, Complexity.Costed.pure_value]
  · rfl

private theorem ax99AssociationCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x t w : Nat) :
    (ax99AssociationCosted worldNames thingNames tables x t w).cost ≤
      ax99AssociationCostBound thingNames.size tables.productFamilies := by
  have hquery := Complexity.diagnosticBinaryCosted_cost_le worldNames.size thingNames.size
    tables .associatedWith x t w
  have hentry := productFamilyEntryPresentCosted_cost_le tables x t
  have hwitness := Complexity.productFamiliesDiagnosticCosted_cost_le
    worldNames.size thingNames.size tables x t w
  have hregistered := ax99FailureEvidenceCosted_cost_le worldNames thingNames tables x t w true
  have hmissing := ax99FailureEvidenceCosted_cost_le worldNames thingNames tables x t w false
  cases ha : (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .associatedWith x t w).value <;>
    cases he : (productFamilyEntryPresentCosted tables x t).value <;>
    cases hv : (Complexity.productFamiliesDiagnosticCosted worldNames.size thingNames.size tables x t w).value <;>
    simp only [ax99AssociationCosted, Bind.bind, Complexity.Costed.bind_cost,
      Complexity.Costed.charge_cost, ha, he, hv, Bool.false_eq_true, ↓reduceIte,
      Complexity.Costed.pure_cost, ax99AssociationCostBound] <;> omega

private theorem ax99AssociationCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x t w : Nat)
    (rows : Array String) (found : (ax99AssociationCosted worldNames thingNames tables x t w).value = some rows) :
    rows.size ≤ 5 := by
  rw [ax99AssociationCosted_value] at found
  split at found
  · split at found
    · split at found
      · cases found
      · cases Option.some.inj found
        exact ax99FailureEvidenceCosted_size_le ..
    · cases Option.some.inj found
      exact ax99FailureEvidenceCosted_size_le ..
  · cases found

private def ax99QualityDomainCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Option (Array String)) := do
  let domain ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityDomain x w
  Complexity.Costed.charge 1 <| if domain then
    foldDiagDomainCosted 0 thingNames.size none Option.isSome fun _ t =>
      ax99AssociationCosted worldNames thingNames tables x t w
  else Complexity.Costed.pure none

private def ax99QualityDomainCostBound (T : Nat) (families : Array ProductFamilySpec) : Nat :=
  13 + T * (ax99AssociationCostBound T families + 3)

private theorem ax99QualityDomainCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (ax99QualityDomainCosted worldNames thingNames tables x w).value =
      if (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .qualityDomain x w).value then
        (List.range thingNames.size).findSome? (fun t =>
          (ax99AssociationCosted worldNames thingNames tables x t w).value)
      else none := by
  simp only [ax99QualityDomainCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · exact foldDiagDomainCosted_firstSome_value _ _ _ (by intros; rfl)
  · rfl

private theorem ax99QualityDomainCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (ax99QualityDomainCosted worldNames thingNames tables x w).cost ≤
      ax99QualityDomainCostBound thingNames.size tables.productFamilies := by
  have hquery := Complexity.diagnosticUnaryCosted_cost_le worldNames.size thingNames.size tables .qualityDomain x w
  have hscan := foldDiagDomainCosted_cost_le 0 thingNames.size (none : Option (Array String)) Option.isSome
    (fun _ t => ax99AssociationCosted worldNames thingNames tables x t w)
    (ax99AssociationCostBound thingNames.size tables.productFamilies)
    (by intros; exact ax99AssociationCosted_cost_le ..)
  simp only [ax99QualityDomainCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, ax99QualityDomainCostBound]
  split
  · omega
  · simp only [Complexity.Costed.pure_cost]
    omega

private theorem ax99QualityDomainCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (rows : Array String) (found : (ax99QualityDomainCosted worldNames thingNames tables x w).value = some rows) :
    rows.size ≤ 5 := by
  rw [ax99QualityDomainCosted_value] at found
  split at found
  · obtain ⟨t, ht, found⟩ := List.exists_of_findSome?_eq_some found
    exact ax99AssociationCosted_some_size worldNames thingNames tables x t w rows found
  · cases found

/-- Numeric world/thing loops preserve lexicographic first-failure order.
The quality-domain query is shared by all candidate types for that thing. -/
private def ax99AssignmentsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Option (Array String)) :=
  foldDiagDomainCosted 0 worldNames.size none Option.isSome fun _ w =>
    foldDiagDomainCosted 0 thingNames.size none Option.isSome fun _ x =>
      ax99QualityDomainCosted worldNames thingNames tables x w

private theorem ax99AssignmentsCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax99AssignmentsCosted worldNames thingNames tables).value =
      (List.range worldNames.size).findSome? (fun w =>
        (List.range thingNames.size).findSome? (fun x =>
          (ax99QualityDomainCosted worldNames thingNames tables x w).value)) := by
  unfold ax99AssignmentsCosted
  apply foldDiagDomainCosted_firstSome_value
  intro w hw
  apply foldDiagDomainCosted_firstSome_value
  intro x hx
  rfl

private theorem ax99AssignmentsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax99AssignmentsCosted worldNames thingNames tables).cost ≤
      worldNames.size * (thingNames.size *
        (ax99QualityDomainCostBound thingNames.size tables.productFamilies + 3) + 3) := by
  unfold ax99AssignmentsCosted
  apply foldDiagDomainCosted_cost_le
  intro state w hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state x hlo hhi
  exact ax99QualityDomainCosted_cost_le ..

private theorem ax99AssignmentsCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (rows : Array String)
    (found : (ax99AssignmentsCosted worldNames thingNames tables).value = some rows) :
    rows.size ≤ 5 := by
  rw [ax99AssignmentsCosted_value] at found
  obtain ⟨w, hw, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨x, hx, found⟩ := List.exists_of_findSome?_eq_some found
  exact ax99QualityDomainCosted_some_size worldNames thingNames tables x w rows found

private def ax99QualityDomainAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let found ← ax99AssignmentsCosted worldNames thingNames tables
  Complexity.Costed.charge 1 <| match found with
  | some rows => Complexity.Costed.pure rows
  | none => do
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      let out ← Complexity.Costed.tick (out.push
        "Product check for ax99: every asserted quality-domain association has a valid registered product-family witness in the diagnostic tables.") 2
      Complexity.Costed.tick (out.push
        "If certification still reports ax99, inspect the conversion from registered product-family records to finite checker witnesses.") 2

private def ax99QualityDomainAnalysisCostBound (W T : Nat) (families : Array ProductFamilySpec) : Nat :=
  W * (T * (ax99QualityDomainCostBound T families + 3) + 3) + 6

/-- The bound grows with worlds, things, records, and both slot totals.
No ordering or content relation between the two registries is required. -/
private theorem ax99QualityDomainAnalysisCostBound_mono {W W' T T' : Nat}
    {families families' : Array ProductFamilySpec} (hW : W ≤ W') (hT : T ≤ T')
    (hR : families.size ≤ families'.size)
    (hD : (families.toList.map fun f => f.dimensionThings.size).sum ≤
      (families'.toList.map fun f => f.dimensionThings.size).sum)
    (hZ : (families.toList.map fun f => f.typeThings.size).sum ≤
      (families'.toList.map fun f => f.typeThings.size).sum) :
    ax99QualityDomainAnalysisCostBound W T families ≤
      ax99QualityDomainAnalysisCostBound W' T' families' := by
  have hP := Complexity.productFamiliesDiagnosticBound_mono hT hR hD hZ
  unfold ax99QualityDomainAnalysisCostBound ax99QualityDomainCostBound ax99AssociationCostBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

private theorem ax99QualityDomainAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax99QualityDomainAnalysisCosted worldNames thingNames tables).cost ≤
      ax99QualityDomainAnalysisCostBound worldNames.size thingNames.size tables.productFamilies := by
  have h := ax99AssignmentsCosted_cost_le worldNames thingNames tables
  unfold ax99QualityDomainAnalysisCosted ax99QualityDomainAnalysisCostBound
  generalize ax99AssignmentsCosted worldNames thingNames tables = found at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  cases found.value <;> simp <;> omega

private theorem ax99QualityDomainAnalysisCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax99QualityDomainAnalysisCosted worldNames thingNames tables).value.size ≤ 5 := by
  have h := ax99AssignmentsCosted_some_size worldNames thingNames tables
  simp only [ax99QualityDomainAnalysisCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  cases found : (ax99AssignmentsCosted worldNames thingNames tables).value with
  | none => simp
  | some rows => exact h rows found


/-- Find the first world where x exists without y. The conjunction skips
the y query when x does not exist, and the domain loop stops at the first
witness. Both queries include their finite-coordinate guards. -/
private def firstExWithoutCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed (Option Nat) :=
  findDiagDomainCosted worldCount fun w =>
    (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex x w).andThen fun _ =>
      (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex y w).not

private theorem firstExWithoutCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x y : Nat) :
    (firstExWithoutCosted worldCount thingCount tables x y).cost ≤ 30 * worldCount := by
  unfold firstExWithoutCosted
  have h := findDiagDomainCosted_cost_le worldCount
    (fun w => (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex x w).andThen
      fun _ => (Complexity.diagnosticUnaryCosted worldCount thingCount tables .ex y w).not)
    26 (by
      intro w hw
      have hx := Complexity.diagnosticUnaryCosted_cost_le worldCount thingCount tables .ex x w
      have hy := Complexity.diagnosticUnaryCosted_cost_le worldCount thingCount tables .ex y w
      apply Complexity.Costed.andThen_cost_le _ _ 12 13 hx
      simp only [Complexity.Costed.not_cost]
      omega)
  simpa [Nat.mul_comm] using h

private theorem firstExWithoutCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x y : Fin thingCount) :
    (firstExWithoutCosted worldCount thingCount tables x.val y.val).value =
      (List.range worldCount).find? (fun w =>
        tables.unaryLookup "ex" x.val w && !tables.unaryLookup "ex" y.val w) := by
  unfold firstExWithoutCosted
  apply findDiagDomainCosted_value
  intro w hw
  have hx := Complexity.diagnosticUnaryCosted_value worldCount thingCount tables
    agreement .ex x ⟨w, hw⟩
  have hy := Complexity.diagnosticUnaryCosted_value worldCount thingCount tables
    agreement .ex y ⟨w, hw⟩
  simp only [Complexity.Costed.andThen_value, Complexity.Costed.not_value, hx, hy]
  rfl

/-- Both directional searches run because the explanation distinguishes
which witness is absent. Names are rendered only on failure and reused within
the message. Every concatenation below contributes its own primitive cost. -/
private def firstExternalIndependenceFailureCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    Complexity.Costed (Option String) := do
  let yWithoutZ ← firstExWithoutCosted worldNames.size thingNames.size tables y z
  let zWithoutY ← firstExWithoutCosted worldNames.size thingNames.size tables z y
  Complexity.Costed.charge 2 <| match yWithoutZ, zWithoutY with
  | none, none => do
      let yn ← indexedNameCosted thingNames y
      let zn ← indexedNameCosted thingNames z
      let text ← Complexity.Costed.tick ("the assertion needs one witness world where Ex(" ++ yn) 1
      let text ← Complexity.Costed.tick (text ++ ") holds without Ex(") 1
      let text ← Complexity.Costed.tick (text ++ zn) 1
      let text ← Complexity.Costed.tick (text ++ "), and one witness world where Ex(") 1
      let text ← Complexity.Costed.tick (text ++ zn) 1
      let text ← Complexity.Costed.tick (text ++ ") holds without Ex(") 1
      let text ← Complexity.Costed.tick (text ++ yn) 1
      let text ← Complexity.Costed.tick (text ++ "); neither witness exists in the current `Ex` facts") 1
      Complexity.Costed.pure (some text)
  | none, some _ => do
      let yn ← indexedNameCosted thingNames y
      let zn ← indexedNameCosted thingNames z
      let text ← Complexity.Costed.tick ("the assertion needs a witness world where Ex(" ++ yn) 1
      let text ← Complexity.Costed.tick (text ++ ") holds without Ex(") 1
      let text ← Complexity.Costed.tick (text ++ zn) 1
      let text ← Complexity.Costed.tick (text ++ "), but no such world exists in the current `Ex` facts") 1
      Complexity.Costed.pure (some text)
  | some _, none => do
      let yn ← indexedNameCosted thingNames y
      let zn ← indexedNameCosted thingNames z
      let text ← Complexity.Costed.tick ("the assertion needs a witness world where Ex(" ++ zn) 1
      let text ← Complexity.Costed.tick (text ++ ") holds without Ex(") 1
      let text ← Complexity.Costed.tick (text ++ yn) 1
      let text ← Complexity.Costed.tick (text ++ "), but no such world exists in the current `Ex` facts") 1
      Complexity.Costed.pure (some text)
  | some _, some _ => Complexity.Costed.pure none

/-- The counted renderer retains the four existing messages/selections. The
search values already have their sparse-relation correspondence theorem. -/
private theorem firstExternalIndependenceFailureCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    (firstExternalIndependenceFailureCosted worldNames thingNames tables y z).value =
      match (firstExWithoutCosted worldNames.size thingNames.size tables y z).value,
          (firstExWithoutCosted worldNames.size thingNames.size tables z y).value with
      | none, none =>
          some s!"the assertion needs one witness world where Ex({indexedName thingNames y}) holds without Ex({indexedName thingNames z}), and one witness world where Ex({indexedName thingNames z}) holds without Ex({indexedName thingNames y}); neither witness exists in the current `Ex` facts"
      | none, some _ =>
          some s!"the assertion needs a witness world where Ex({indexedName thingNames y}) holds without Ex({indexedName thingNames z}), but no such world exists in the current `Ex` facts"
      | some _, none =>
          some s!"the assertion needs a witness world where Ex({indexedName thingNames z}) holds without Ex({indexedName thingNames y}), but no such world exists in the current `Ex` facts"
      | some _, some _ => none := by
  simp only [firstExternalIndependenceFailureCosted, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  split <;> simp only [Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.pure_value, indexedNameCosted_value]
  all_goals rfl

private def firstExternalIndependenceFailure?
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    Option String :=
  (firstExternalIndependenceFailureCosted worldNames thingNames tables y z).value

private theorem firstExternalIndependenceFailureCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    (firstExternalIndependenceFailureCosted worldNames thingNames tables y z).cost ≤
      60 * worldNames.size + 18 := by
  have hyz := firstExWithoutCosted_cost_le worldNames.size thingNames.size tables y z
  have hzy := firstExWithoutCosted_cost_le worldNames.size thingNames.size tables z y
  simp only [firstExternalIndependenceFailureCosted, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  split <;> simp <;> omega

/-- Return the first failing bearer together with its computed reason.
Only inherence matches run the two directional existence-witness searches.
The optional state retains the reason for the renderer. -/
private def firstExternalBearerWitnessCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Option (Nat × String)) :=
  foldDiagDomainCosted 0 thingNames.size none Option.isSome fun _ z => do
    let inheres ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
      .inheresIn x z w
    if inheres then
      Complexity.Costed.charge 1 do
        let reason ← firstExternalIndependenceFailureCosted worldNames thingNames tables y z
        Complexity.Costed.tick (reason.map (fun reason => (z, reason))) 1
    else Complexity.Costed.tick none 1

private theorem firstExternalBearerWitnessCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (firstExternalBearerWitnessCosted worldNames thingNames tables x y w).cost ≤
      thingNames.size * (60 * worldNames.size + 40) := by
  unfold firstExternalBearerWitnessCosted
  have h := foldDiagDomainCosted_cost_le 0 thingNames.size
    (none : Option (Nat × String)) Option.isSome
    (fun _ z => do
      let inheres ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
        .inheresIn x z w
      if inheres then
        Complexity.Costed.charge 1 do
          let reason ← firstExternalIndependenceFailureCosted worldNames thingNames tables y z
          Complexity.Costed.tick (reason.map (fun reason => (z, reason))) 1
      else Complexity.Costed.tick none 1)
    (60 * worldNames.size + 37) (by
      intro state z hlo hhi
      have hquery := Complexity.diagnosticBinaryCosted_cost_le
        worldNames.size thingNames.size tables .inheresIn x z w
      have hreason := firstExternalIndependenceFailureCosted_cost_le
        worldNames thingNames tables y z
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.charge_cost, Complexity.Costed.bind_cost,
        Complexity.Costed.tick_cost] <;> omega)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h

private theorem firstExternalBearerWitnessCosted_sparse_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (y : Nat) (w : Fin worldNames.size) :
    (firstExternalBearerWitnessCosted worldNames thingNames tables x.val y w.val).value =
      (List.range thingNames.size).findSome? (fun z =>
        if tables.binaryLookup "inheresIn" x.val z w.val then
          (firstExternalIndependenceFailureCosted worldNames thingNames tables y z).value.map
            (fun reason => (z, reason))
        else none) := by
  unfold firstExternalBearerWitnessCosted
  apply foldDiagDomainCosted_firstSome_value
  intro z hz
  have hquery := Complexity.diagnosticBinaryCosted_value
    worldNames.size thingNames.size tables agreement .inheresIn x ⟨z, hz⟩ w
  simp only [Bind.bind, Complexity.Costed.bind_value, hquery,
    FactTables.binaryTypedTable, BinaryField.toTableField]
  split <;> simp

/-- Render the retained witness without repeating the independence searches.
The successful branch adds four name renders and ten concatenations. -/
private def firstExternalBearerFailureCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed String := do
  let found ← firstExternalBearerWitnessCosted worldNames thingNames tables x y w
  match found with
  | none =>
      Complexity.Costed.tick
        "no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence." 1
  | some (z, reason) => Complexity.Costed.charge 1 do
      let xn ← indexedNameCosted thingNames x
      let zn ← indexedNameCosted thingNames z
      let wn ← indexedNameCosted worldNames w
      let yn ← indexedNameCosted thingNames y
      let text ← Complexity.Costed.tick ("`" ++ xn) 1
      let text ← Complexity.Costed.tick (text ++ "` inheres in `") 1
      let text ← Complexity.Costed.tick (text ++ zn) 1
      let text ← Complexity.Costed.tick (text ++ "` at `") 1
      let text ← Complexity.Costed.tick (text ++ wn) 1
      let text ← Complexity.Costed.tick (text ++ "`, but `") 1
      let text ← Complexity.Costed.tick (text ++ yn) 1
      let text ← Complexity.Costed.tick (text ++ "` is not existentially independent from that bearer: ") 1
      let text ← Complexity.Costed.tick (text ++ reason) 1
      Complexity.Costed.tick (text ++ ".") 1

private theorem firstExternalBearerFailureCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (firstExternalBearerFailureCosted worldNames thingNames tables x y w).cost ≤
      thingNames.size * (60 * worldNames.size + 40) + 27 := by
  have hscan := firstExternalBearerWitnessCosted_cost_le worldNames thingNames tables x y w
  simp only [firstExternalBearerFailureCosted, Bind.bind, Complexity.Costed.bind_cost]
  split <;> simp <;> omega

private theorem firstExternalBearerFailureCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (firstExternalBearerFailureCosted worldNames thingNames tables x y w).value =
      match (firstExternalBearerWitnessCosted worldNames thingNames tables x y w).value with
      | none =>
          "no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence."
      | some (z, reason) =>
          s!"`{indexedName thingNames x}` inheres in `{indexedName thingNames z}` at `{indexedName worldNames w}`, but `{indexedName thingNames y}` is not existentially independent from that bearer: {reason}." := by
  cases h : (firstExternalBearerWitnessCosted worldNames thingNames tables x y w).value with
  | none =>
      simp only [firstExternalBearerFailureCosted, Bind.bind, Complexity.Costed.bind_value, h]
      rfl
  | some witness =>
      rcases witness with ⟨z, reason⟩
      simp only [firstExternalBearerFailureCosted, Bind.bind, Complexity.Costed.bind_value, h]
      change s!"`{(indexedNameCosted thingNames x).value}` inheres in `{(indexedNameCosted thingNames z).value}` at `{(indexedNameCosted worldNames w).value}`, but `{(indexedNameCosted thingNames y).value}` is not existentially independent from that bearer: {reason}." = _
      simp only [indexedNameCosted_value]

/-- Explain a failed modal implication before inspecting bearers. The
selected world is reused in the text, and the bearer scan runs only when no
such world exists. -/
private def firstExternallyDependentFailureReasonCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed String := do
  let boxFailure ← firstExWithoutCosted worldNames.size thingNames.size tables x y
  Complexity.Costed.charge 1 <| match boxFailure with
  | some witnessWorld => do
      let xn ← indexedNameCosted thingNames x
      let wn ← indexedNameCosted worldNames witnessWorld
      let yn ← indexedNameCosted thingNames y
      let text ← Complexity.Costed.tick ("`" ++ xn) 1
      let text ← Complexity.Costed.tick (text ++ "` exists at `") 1
      let text ← Complexity.Costed.tick (text ++ wn) 1
      let text ← Complexity.Costed.tick (text ++ "`, but `") 1
      let text ← Complexity.Costed.tick (text ++ yn) 1
      Complexity.Costed.tick (text ++ "` does not; this breaks existential dependence.") 1
  | none => firstExternalBearerFailureCosted worldNames thingNames tables x y w

private theorem firstExternallyDependentFailureReasonCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w).cost ≤
      30 * worldNames.size + thingNames.size * (60 * worldNames.size + 40) + 28 := by
  have hbox := firstExWithoutCosted_cost_le worldNames.size thingNames.size tables x y
  have hbearer := firstExternalBearerFailureCosted_cost_le worldNames thingNames tables x y w
  simp only [firstExternallyDependentFailureReasonCosted, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  split <;> simp <;> omega

private theorem firstExternallyDependentFailureReasonCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w).value =
      match (firstExWithoutCosted worldNames.size thingNames.size tables x y).value with
      | some witnessWorld =>
          s!"`{indexedName thingNames x}` exists at `{indexedName worldNames witnessWorld}`, but `{indexedName thingNames y}` does not; this breaks existential dependence."
      | none => (firstExternalBearerFailureCosted worldNames thingNames tables x y w).value := by
  simp only [firstExternallyDependentFailureReasonCosted, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  split <;> simp
  all_goals rfl

private def firstExternallyDependentFailureReason
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : String :=
  (firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w).value

/-- Collect computed witnesses in ascending thing order. The numeric loop
avoids a candidate-list allocation and accumulates cost before continuing.
The initial empty output array costs one, even when there are no things. -/
private def externallyDependentWitnessesCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 thingNames.size #[] (fun _ => false) fun out y => do
      let dependent ← externallyDependentLookupCosted
        worldNames.size thingNames.size tables x y w
      if dependent then Complexity.Costed.tick (out.push y) 2
      else Complexity.Costed.tick out 1

private theorem externallyDependentWitnessesCosted_ordered_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value =
      (List.range thingNames.size).foldl (fun out y =>
        if externallyDependentLookup worldNames.size thingNames.size tables x y w then
          out.push y else out) #[] := by
  rw [externallyDependentWitnessesCosted, Complexity.Costed.charge_value, foldDiagDomainCosted_value]
  rw [← List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Complexity.Costed.bind_value]
  congr 1
  funext out y
  simp only [externallyDependentLookupCosted_value]
  split <;> simp_all

private theorem externallyDependentWitnessesCosted_filter_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value =
      ((List.range thingNames.size).filter
        (fun y => externallyDependentLookup worldNames.size thingNames.size tables x y w)).toArray := by
  rw [externallyDependentWitnessesCosted_ordered_value, ← List.foldl_filter,
    List.foldl_push_eq_append']
  simp

private theorem externallyDependentWitnessesCosted_nodup
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value.toList.Nodup := by
  rw [externallyDependentWitnessesCosted_filter_value]
  change ((List.range thingNames.size).filter
    (fun y => externallyDependentLookup worldNames.size thingNames.size tables x y w)).Nodup
  exact (List.nodup_range (n := thingNames.size)).filter _

/-- One dependence check, at most one witness push and branch, and three
numeric-loop operations per candidate. The collector emits at most T items. -/
private def externallyDependentWitnessCostBound (worldCount thingCount : Nat) : Nat :=
  28 * worldCount + thingCount * (56 * worldCount + 22) + 6

private theorem externallyDependentWitnessesCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).cost ≤
      thingNames.size *
        externallyDependentWitnessCostBound worldNames.size thingNames.size + 1 := by
  have h := foldDiagDomainCosted_cost_le 0 thingNames.size (#[] : Array Nat)
    (fun _ => false)
    (fun out y => externallyDependentLookupCosted worldNames.size thingNames.size tables x y w
      >>= fun dependent => if dependent then Complexity.Costed.tick (out.push y) 2
        else Complexity.Costed.tick out 1)
    (28 * worldNames.size + thingNames.size * (56 * worldNames.size + 22) + 3) (by
      intro out y hlo hhi
      have hdep := externallyDependentLookupCosted_cost_le
        worldNames.size thingNames.size tables x y w
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.tick_cost] <;> omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  simp only [externallyDependentWitnessesCosted, Complexity.Costed.charge_cost,
    externallyDependentWitnessCostBound, Nat.add_assoc]
  omega

private theorem externallyDependentWitnessesCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value.size ≤
      thingNames.size := by
  rw [externallyDependentWitnessesCosted, Complexity.Costed.charge_value]
  refine le_trans (foldDiagDomainCosted_array_size_le _ _ _ _ _ 1 ?_) (by simp)
  intro out y
  simp only [Bind.bind, Complexity.Costed.bind_value]
  split <;> simp

private def externallyDependentWitnesses
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array Nat :=
  (externallyDependentWitnessesCosted worldNames thingNames tables x w).value

@[simp] private theorem externallyDependentWitnessesCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value =
      externallyDependentWitnesses worldNames thingNames tables x w := rfl

/-- Declared candidates come from stored derived assertions. The compiler has
no primitive `externallyDependent` field; its false lookup need not be scanned.
Computed external dependence remains a separate predicate. The initial array
costs one, independently of the number of declared candidates. -/
private def declaredExternalCandidatesCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 thingCount #[] (fun _ => false) fun out y => do
      let declared ← assertedDerivedBinaryLookupCosted tables "ExternallyDependent" x y w
      if declared then Complexity.Costed.tick (out.push y) 2
      else Complexity.Costed.tick out 1

private theorem declaredExternalCandidatesCosted_filter_value
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (declaredExternalCandidatesCosted thingCount tables x w).value =
      ((List.range thingCount).filter
        (fun y => assertedDerivedBinaryLookup tables "ExternallyDependent" x y w)).toArray := by
  rw [declaredExternalCandidatesCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Complexity.Costed.bind_value]
  have hvisit :
      (fun (out : Array Nat) y => (if (assertedDerivedBinaryLookupCosted tables "ExternallyDependent" x y w).value
          then Complexity.Costed.tick (out.push y) 2 else Complexity.Costed.tick out 1).value) =
      (fun out y => if assertedDerivedBinaryLookup tables "ExternallyDependent" x y w
        then out.push y else out) := by
    funext out y
    unfold assertedDerivedBinaryLookup
    split <;> simp_all
  rw [hvisit, ← List.foldl_filter, List.foldl_push_eq_append']
  simp

/-- The removed primitive branch is false for every explicit compiled model,
so declared candidates preserve the previous union of primitive and asserted
facts without evaluating an unsupported lookup field. -/
private theorem declaredExternalCandidatesCosted_compiled_value
    (ast : ModelAST) (x w : Nat) :
    (declaredExternalCandidatesCosted ast.thingCount (compileExplicitModelAST ast) x w).value =
      ((List.range ast.thingCount).filter (fun y =>
        (compileExplicitModelAST ast).binaryLookup "externallyDependent" x y w ||
        assertedDerivedBinaryLookup (compileExplicitModelAST ast) "ExternallyDependent" x y w)).toArray := by
  have unknown : ∀ field : BinaryField, "externallyDependent" ≠ field.toTableField := by
    intro field
    cases field <;> decide
  rw [declaredExternalCandidatesCosted_filter_value]
  simp only [Complexity.Production.compileExplicitModelAST_binaryLookup_unknown ast
    "externallyDependent" unknown, Bool.false_or]

private theorem declaredExternalCandidatesCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (declaredExternalCandidatesCosted thingCount tables x w).cost ≤
      thingCount * (4 * tables.derivedProps.size + 21) + 1 := by
  have h := foldDiagDomainCosted_cost_le 0 thingCount (#[] : Array Nat)
    (fun _ => false)
    (fun out y => assertedDerivedBinaryLookupCosted tables "ExternallyDependent" x y w
      >>= fun declared => if declared then Complexity.Costed.tick (out.push y) 2
        else Complexity.Costed.tick out 1)
    (4 * tables.derivedProps.size + 18) (by
      intro out y hlo hhi
      have hdeclared := assertedDerivedBinaryLookupCosted_cost_le
        tables "ExternallyDependent" x y w
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.tick_cost] <;> omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  simp only [declaredExternalCandidatesCosted, Complexity.Costed.charge_cost]
  omega

private theorem declaredExternalCandidatesCosted_size_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (declaredExternalCandidatesCosted thingCount tables x w).value.size ≤ thingCount := by
  rw [declaredExternalCandidatesCosted, Complexity.Costed.charge_value]
  refine le_trans (foldDiagDomainCosted_array_size_le _ _ _ _ _ 1 ?_) (by simp)
  intro out y
  simp only [Bind.bind, Complexity.Costed.bind_value]
  split <;> simp

private theorem declaredExternalCandidatesCosted_nodup
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (declaredExternalCandidatesCosted thingCount tables x w).value.toList.Nodup := by
  rw [declaredExternalCandidatesCosted_filter_value]
  change ((List.range thingCount).filter
    (fun y => assertedDerivedBinaryLookup tables "ExternallyDependent" x y w)).Nodup
  exact (List.nodup_range (n := thingCount)).filter _

/-- Prefer the first declared candidate. Otherwise search coordinates in order
and stop after the first inherence match. If no match exists, coordinate zero
still gives the renderer a candidate to explain, unless the domain is empty.
The scan charges each guarded table query and never builds a candidate list. -/
private def firstModeStatusCandidateCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat)
    (declared : Array Nat) : Complexity.Costed (Option Nat) :=
  if h : 0 < declared.size then
    Complexity.Costed.tick (some declared[0]) 3
  else
    Complexity.Costed.charge 2 do
      let found ← findDiagDomainCosted thingCount fun z =>
        Complexity.diagnosticBinaryCosted worldCount thingCount tables .inheresIn x z w
      match found with
      | some z => Complexity.Costed.tick (some z) 1
      | none => Complexity.Costed.tick (if thingCount == 0 then none else some 0) 3

private theorem firstModeStatusCandidateCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) (declared : Array Nat) :
    (firstModeStatusCandidateCosted worldCount thingCount tables x w declared).cost ≤
      21 * thingCount + 5 := by
  have hscan := findDiagDomainCosted_cost_le thingCount
    (fun z => Complexity.diagnosticBinaryCosted worldCount thingCount tables .inheresIn x z w)
    17 (by intro z hz; exact Complexity.diagnosticBinaryCosted_cost_le _ _ _ _ _ _ _)
  simp only [firstModeStatusCandidateCosted]
  split
  · simp only [Complexity.Costed.tick_cost]
    omega
  · simp only [Complexity.Costed.charge_cost, Bind.bind, Complexity.Costed.bind_cost]
    split <;> simp only [Complexity.Costed.tick_cost] <;> omega

/-- Table agreement turns the executable search into the first sparse
inherence witness. The list occurs only in this specification. -/
private theorem firstModeStatusCandidateCosted_sparse_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups worldCount thingCount =
      tables.denseLookups worldCount thingCount)
    (x : Fin thingCount) (w : Fin worldCount) (declared : Array Nat) :
    (firstModeStatusCandidateCosted worldCount thingCount tables x.val w.val declared).value =
      if h : 0 < declared.size then some declared[0] else
        ((List.range thingCount).find? (fun z => tables.binaryLookup "inheresIn" x.val z w.val)).orElse
          (fun _ => if thingCount == 0 then none else some 0) := by
  have hscan := findDiagDomainCosted_value thingCount
    (fun z => Complexity.diagnosticBinaryCosted worldCount thingCount tables .inheresIn x.val z w.val)
    (fun z => tables.binaryLookup "inheresIn" x.val z w.val) (by
      intro z hz
      exact Complexity.diagnosticBinaryCosted_value worldCount thingCount tables
        agreement .inheresIn x ⟨z, hz⟩ w)
  simp only [firstModeStatusCandidateCosted]
  split
  · rfl
  · simp only [Complexity.Costed.charge_value, Bind.bind, Complexity.Costed.bind_value, hscan]
    cases (List.range thingCount).find? (fun z => tables.binaryLookup "inheresIn" x.val z w.val) <;> rfl

/-- Render the two failure rows and, when present, the declared-candidate
note. Keeping row construction separate lets the search retain and reuse its
selected reason. Each row charges its array push and emitted item. -/
private def renderModeFailureRowsCosted
    (thingNames : Array Name) (x : Nat) (firstReason : String) (declared : Array Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let line ← Complexity.Costed.tick ("  - Computed ExternallyDependentMode: false. `" ++ xn) 1
  let line ← Complexity.Costed.tick (line ++ "` is a `Mode`, but no thing witnesses computed `ExternallyDependent(") 1
  let line ← Complexity.Costed.tick (line ++ xn) 1
  let line ← Complexity.Costed.tick (line ++ ", y)`.") 1
  let reasonLine ← Complexity.Costed.tick ("  - First candidate check: " ++ firstReason) 1
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push line) 2
  let out ← Complexity.Costed.tick (out.push reasonLine) 2
  Complexity.Costed.charge 2 <| if declared.isEmpty then Complexity.Costed.pure out else do
    let names ← joinIndexedNamesCosted thingNames declared
    let line ← Complexity.Costed.tick ("  - Note: asserted `ExternallyDependent` facts name candidate(s) " ++ names) 1
    let line ← Complexity.Costed.tick (line ++ ", but certification uses the computed external-dependence semantics.") 1
    Complexity.Costed.tick (out.push line) 2

private theorem renderModeFailureRowsCosted_cost_le
    (thingNames : Array Name) (x : Nat) (firstReason : String) (declared : Array Nat) :
    (renderModeFailureRowsCosted thingNames x firstReason declared).cost ≤
      9 * declared.size + 21 := by
  have hjoin := joinIndexedNamesCosted_cost_le thingNames declared
  simp only [renderModeFailureRowsCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost, indexedNameCosted_cost, Complexity.Costed.tick_cost]
  split <;> simp
  omega

private theorem renderModeFailureRowsCosted_size_le
    (thingNames : Array Name) (x : Nat) (firstReason : String) (declared : Array Nat) :
    (renderModeFailureRowsCosted thingNames x firstReason declared).value.size ≤ 3 := by
  simp only [renderModeFailureRowsCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, Complexity.Costed.tick_value]
  split <;> simp

private theorem renderModeFailureRowsCosted_value
    (thingNames : Array Name) (x : Nat) (firstReason : String) (declared : Array Nat) :
    (renderModeFailureRowsCosted thingNames x firstReason declared).value =
      let out := #[
        s!"  - Computed ExternallyDependentMode: false. `{indexedName thingNames x}` is a `Mode`, but no thing witnesses computed `ExternallyDependent({indexedName thingNames x}, y)`.",
        s!"  - First candidate check: {firstReason}"]
      if declared.isEmpty then out else
        out.push s!"  - Note: asserted `ExternallyDependent` facts name candidate(s) {String.intercalate ", " (declared.toList.map (indexedName thingNames))}, but certification uses the computed external-dependence semantics." := by
  simp only [renderModeFailureRowsCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, Complexity.Costed.tick_value, indexedNameCosted_value]
  split <;> simp only [Complexity.Costed.pure_value, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, joinIndexedNamesCosted_value] <;> rfl

/-- Report computed mode status and its supporting or failing candidates.
The mode guard precedes all witness searches. Rows are appended in display
order, charging array initialization, each push, and each emitted item. -/
private def renderExternallyDependentModeStatusCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) := do
  let mode ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .mode x w
  Complexity.Costed.charge 2 <| if !mode then do
    let xn ← indexedNameCosted thingNames x
    let wn ← indexedNameCosted worldNames w
    let line ← Complexity.Costed.tick ("  - Computed ExternallyDependentMode: false, because `" ++ xn) 1
    let line ← Complexity.Costed.tick (line ++ "` is not a `Mode` at `") 1
    let line ← Complexity.Costed.tick (line ++ wn) 1
    let line ← Complexity.Costed.tick (line ++ "`.") 1
    let out ← Complexity.Costed.tick (#[] : Array String) 1
    Complexity.Costed.tick (out.push line) 2
  else do
    let witnesses ← externallyDependentWitnessesCosted worldNames thingNames tables x w
    Complexity.Costed.charge 2 <| if witnesses.isEmpty then do
      let declared ← declaredExternalCandidatesCosted thingNames.size tables x w
      let candidate ← firstModeStatusCandidateCosted worldNames.size thingNames.size tables x w declared
      let firstReason ← Complexity.Costed.charge 1 <| match candidate with
        | none => Complexity.Costed.pure "there are no candidate things to witness external dependence."
        | some candidate =>
            firstExternallyDependentFailureReasonCosted worldNames thingNames tables x candidate w
      renderModeFailureRowsCosted thingNames x firstReason declared
    else do
      let names ← joinIndexedNamesCosted thingNames witnesses
      let line ← Complexity.Costed.tick ("  - Computed ExternallyDependentMode: true, witnessed by " ++ names) 1
      let line ← Complexity.Costed.tick (line ++ ".") 1
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      Complexity.Costed.tick (out.push line) 2

private def renderExternallyDependentModeStatus
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value

private def externallyDependentModeStatusCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  thingCount * externallyDependentWitnessCostBound worldCount thingCount +
    thingCount * (4 * tables.derivedProps.size + 51) +
    (30 * worldCount + thingCount * (60 * worldCount + 40) + 28) + 45

private theorem renderExternallyDependentModeStatusCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).cost ≤
      externallyDependentModeStatusCostBound worldNames.size thingNames.size tables := by
  have hmode := Complexity.diagnosticUnaryCosted_cost_le
    worldNames.size thingNames.size tables .mode x w
  have hwitnessCost := externallyDependentWitnessesCosted_cost_le worldNames thingNames tables x w
  have hwitnessSize := externallyDependentWitnessesCosted_size_le worldNames thingNames tables x w
  have hdeclaredCost := declaredExternalCandidatesCosted_cost_le thingNames.size tables x w
  have hdeclaredSize := declaredExternalCandidatesCosted_size_le thingNames.size tables x w
  have hcandidate := firstModeStatusCandidateCosted_cost_le worldNames.size thingNames.size tables x w
    (declaredExternalCandidatesCosted thingNames.size tables x w).value
  have hjoinWitness := joinIndexedNamesCosted_cost_le thingNames
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value
  have hreason :
      (match (firstModeStatusCandidateCosted worldNames.size thingNames.size tables x w
          (declaredExternalCandidatesCosted thingNames.size tables x w).value).value with
        | none => Complexity.Costed.pure "there are no candidate things to witness external dependence."
        | some candidate => firstExternallyDependentFailureReasonCosted
            worldNames thingNames tables x candidate w).cost ≤
        30 * worldNames.size + thingNames.size * (60 * worldNames.size + 40) + 28 := by
    split
    · simp
    · exact firstExternallyDependentFailureReasonCosted_cost_le worldNames thingNames tables x _ w
  have hrows := renderModeFailureRowsCosted_cost_le thingNames x
    (match (firstModeStatusCandidateCosted worldNames.size thingNames.size tables x w
        (declaredExternalCandidatesCosted thingNames.size tables x w).value).value with
      | none => Complexity.Costed.pure "there are no candidate things to witness external dependence."
      | some candidate => firstExternallyDependentFailureReasonCosted
          worldNames thingNames tables x candidate w).value
    (declaredExternalCandidatesCosted thingNames.size tables x w).value
  simp only [renderExternallyDependentModeStatusCosted, Bind.bind,
    Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  split
  · simp
    unfold externallyDependentModeStatusCostBound
    omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split
    · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
        Complexity.Costed.charge_value]
      unfold externallyDependentModeStatusCostBound
      simp only [Nat.mul_add] at hdeclaredCost hreason ⊢
      omega
    · simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
      unfold externallyDependentModeStatusCostBound
      simp only [Nat.mul_add]
      omega

private theorem renderExternallyDependentModeStatusCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value.size ≤ 3 := by
  simp only [renderExternallyDependentModeStatusCosted, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  split
  · simp
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    split
    · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
      exact renderModeFailureRowsCosted_size_le _ _ _ _
    · simp

@[simp] private theorem renderExternallyDependentModeStatusCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value =
      renderExternallyDependentModeStatus worldNames thingNames tables x w := rfl

/-- Under table agreement, the counted renderer preserves the displayed
rows, their order, and the optional declared-candidate note. The witness and
candidate arrays are the same compiled-table searches used by production. -/
private theorem renderExternallyDependentModeStatusCosted_sparse_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x.val w.val).value =
      if !tables.unaryLookup "mode" x.val w.val then
        #[s!"  - Computed ExternallyDependentMode: false, because `{indexedName thingNames x.val}` is not a `Mode` at `{indexedName worldNames w.val}`."]
      else
        let witnesses := (externallyDependentWitnessesCosted worldNames thingNames tables x.val w.val).value
        if witnesses.isEmpty then
          let declared := (declaredExternalCandidatesCosted thingNames.size tables x.val w.val).value
          let candidate := (firstModeStatusCandidateCosted worldNames.size thingNames.size tables
            x.val w.val declared).value
          let reason := (match candidate with
            | none => Complexity.Costed.pure "there are no candidate things to witness external dependence."
            | some candidate => firstExternallyDependentFailureReasonCosted
                worldNames thingNames tables x.val candidate w.val).value
          let out := #[
            s!"  - Computed ExternallyDependentMode: false. `{indexedName thingNames x.val}` is a `Mode`, but no thing witnesses computed `ExternallyDependent({indexedName thingNames x.val}, y)`.",
            s!"  - First candidate check: {reason}"]
          if declared.isEmpty then out else
            out.push s!"  - Note: asserted `ExternallyDependent` facts name candidate(s) {String.intercalate ", " (declared.toList.map (indexedName thingNames))}, but certification uses the computed external-dependence semantics."
        else
          #[s!"  - Computed ExternallyDependentMode: true, witnessed by {String.intercalate ", " (witnesses.toList.map (indexedName thingNames))}."] := by
  have hmode := Complexity.diagnosticUnaryCosted_value worldNames.size thingNames.size tables
    agreement .mode x w
  change (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .mode
    x.val w.val).value = tables.unaryLookup "mode" x.val w.val at hmode
  simp only [renderExternallyDependentModeStatusCosted, Bind.bind,
    Complexity.Costed.bind_value, Complexity.Costed.charge_value, hmode]
  split
  · simp
    rfl
  · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    split
    · simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value,
        renderModeFailureRowsCosted_value]
    · simp only [Complexity.Costed.bind_value, Complexity.Costed.tick_value,
        joinIndexedNamesCosted_value]
      rfl



/-- Test one founded pair. The relator query is delayed until computed mode
classification is false. This is short-circuit evaluation: a true left side of
the disjunction determines the answer without evaluating its right side.
The result retains both tests needed by the failure explanation. -/
private def ax71AssignmentCosted
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Option (Bool × Bool)) := do
  let founded ← Complexity.diagnosticBinaryCosted W T tables .foundedBy x y w
  Complexity.Costed.charge 1 <| if founded then do
    let classification ← (externallyDependentModeLookupCosted W T tables x w).orElse
      (fun _ => Complexity.diagnosticUnaryCosted W T tables .relator x w)
    let foundation ← Complexity.diagnosticUnaryCosted W T tables .perdurant y w
    Complexity.Costed.tick
      (if !(classification && foundation) then some (classification, foundation) else none) 3
  else Complexity.Costed.pure none

private def ax71AssignmentCostBound (W T : Nat) : Nat :=
  T * (28 * W + T * (56 * W + 22) + 3) + 13 + 46

private theorem ax71AssignmentCosted_cost_le
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (ax71AssignmentCosted W T tables x y w).cost ≤ ax71AssignmentCostBound W T := by
  have hfounded := Complexity.diagnosticBinaryCosted_cost_le W T tables .foundedBy x y w
  have hfoundation := Complexity.diagnosticUnaryCosted_cost_le W T tables .perdurant y w
  have hclassification := Complexity.Costed.orElse_cost_le
    (externallyDependentModeLookupCosted W T tables x w)
    (fun _ => Complexity.diagnosticUnaryCosted W T tables .relator x w)
    (T * (28 * W + T * (56 * W + 22) + 3) + 13) 12
    (externallyDependentModeLookupCosted_cost_le W T tables x w)
    (Complexity.diagnosticUnaryCosted_cost_le W T tables .relator x w)
  simp only [ax71AssignmentCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.charge_cost]
  split <;> simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost,
    Complexity.Costed.pure_cost]
  all_goals unfold ax71AssignmentCostBound; omega

private theorem ax71AssignmentCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (ax71AssignmentCosted W T tables x.val y.val w.val).value =
      if tables.binaryLookup "foundedBy" x.val y.val w.val then
        let classification := (externallyDependentModeLookupCosted W T tables x.val w.val).value ||
          tables.unaryLookup "relator" x.val w.val
        let foundation := tables.unaryLookup "perdurant" y.val w.val
        if !(classification && foundation) then some (classification, foundation) else none
      else none := by
  have hf := Complexity.diagnosticBinaryCosted_value W T tables agreement .foundedBy x y w
  have hr := Complexity.diagnosticUnaryCosted_value W T tables agreement .relator x w
  have hp := Complexity.diagnosticUnaryCosted_value W T tables agreement .perdurant y w
  simp only [ax71AssignmentCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value, hf, FactTables.binaryTypedTable, BinaryField.toTableField]
  split <;> simp only [Complexity.Costed.bind_value, Complexity.Costed.orElse_value,
    Complexity.Costed.tick_value, Complexity.Costed.pure_value, hr, hp,
    FactTables.unaryTypedTable, UnaryField.toTableField]

/-- Search worlds, left things, then right things in increasing coordinate
order. Each loop retains the first failure and stops before testing another
assignment. Numeric traversal allocates no list of the Cartesian product.
Following the cost-aware semantics of Niu et al. (POPL 2022), each visited
branch contributes its operations to the same computation that returns the
answer. The bound below composes those charges, not native instruction counts. -/
private def ax71AssignmentsCosted
    (W T : Nat) (tables : FactTables) :
    Complexity.Costed (Option (Nat × Nat × Nat × Bool × Bool)) :=
  foldDiagDomainCosted 0 W none Option.isSome fun _ w =>
    foldDiagDomainCosted 0 T none Option.isSome fun _ x =>
      foldDiagDomainCosted 0 T none Option.isSome fun _ y => do
        let failure ← ax71AssignmentCosted W T tables x y w
        Complexity.Costed.tick (failure.map fun (classification, foundation) =>
          (w, x, y, classification, foundation)) 1

private theorem ax71AssignmentsCosted_cost_le (W T : Nat) (tables : FactTables) :
    (ax71AssignmentsCosted W T tables).cost ≤
      W * (T * (T * (ax71AssignmentCostBound W T + 4) + 3) + 3) := by
  unfold ax71AssignmentsCosted
  apply foldDiagDomainCosted_cost_le
  intro state w hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state x hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state y hlo hhi
  have h := ax71AssignmentCosted_cost_le W T tables x y w
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
  omega

/-- The nested list searches specify first-failure order only. Table agreement
connects every visited guarded query to its sparse meaning. The separate
computed-mode value theorem supplies that predicate's modal interpretation. -/
private theorem ax71AssignmentsCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T) :
    (ax71AssignmentsCosted W T tables).value =
      (List.range W).findSome? (fun w =>
        (List.range T).findSome? (fun x =>
          (List.range T).findSome? (fun y =>
            if tables.binaryLookup "foundedBy" x y w then
              let classification := (externallyDependentModeLookupCosted W T tables x w).value ||
                tables.unaryLookup "relator" x w
              let foundation := tables.unaryLookup "perdurant" y w
              if !(classification && foundation) then some (w, x, y, classification, foundation)
              else none
            else none))) := by
  unfold ax71AssignmentsCosted
  apply foldDiagDomainCosted_firstSome_value
  intro w hw
  apply foldDiagDomainCosted_firstSome_value
  intro x hx
  apply foldDiagDomainCosted_firstSome_value
  intro y hy
  have h := ax71AssignmentCosted_sparse_value W T tables agreement ⟨x, hx⟩ ⟨y, hy⟩ ⟨w, hw⟩
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value, h]
  split
  · split <;> rfl
  · rfl

/-- A retained failure has valid coordinates. This connects the search proof
to the guarded queries used later while formatting its explanation. -/
private theorem ax71AssignmentsCosted_some_bounds
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (w x y : Nat) (classification foundation : Bool)
    (found : (ax71AssignmentsCosted W T tables).value =
      some (w, x, y, classification, foundation)) :
    w < W ∧ x < T ∧ y < T := by
  rw [ax71AssignmentsCosted_sparse_value W T tables agreement] at found
  obtain ⟨w', hw', found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨x', hx', found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨y', hy', found⟩ := List.exists_of_findSome?_eq_some found
  split at found
  · dsimp only at found
    split at found
    · simp only [Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl, rfl, _, _⟩
      exact ⟨List.mem_range.mp hw', List.mem_range.mp hx', List.mem_range.mp hy'⟩
    · contradiction
  · contradiction

/-- Format a retained axiom 71 failure. Names are rendered once and reused.
The mode-status rows already count their emission; copying them into the final
array charges only each read, loop iteration, and push. String-character work
is outside the primitive-call cost model. -/
private def ax71FailureRowsCosted
    (worldNames thingNames : Array Name) (w x y : Nat)
    (classification relator foundation : Bool) (modeStatus : Array String) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let wn ← indexedNameCosted worldNames w
  let assignment ← Complexity.Costed.tick ("Counterexample assignment: x = " ++ xn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", y = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ yn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", w = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ wn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ".") 1
  let trigger ← Complexity.Costed.tick ("Triggered by: `FoundedBy(" ++ xn) 1
  let trigger ← Complexity.Costed.tick (trigger ++ ", ") 1
  let trigger ← Complexity.Costed.tick (trigger ++ yn) 1
  let trigger ← Complexity.Costed.tick (trigger ++ ")`.") 1
  let relatorText ← Complexity.Costed.tick (if relator then "true" else "false") 1
  let relatorLine ← Complexity.Costed.tick ("  - Relator(" ++ xn) 1
  let relatorLine ← Complexity.Costed.tick (relatorLine ++ "): ") 1
  let relatorLine ← Complexity.Costed.tick (relatorLine ++ relatorText) 1
  let relatorLine ← Complexity.Costed.tick (relatorLine ++ ".") 1
  let foundationText ← Complexity.Costed.tick (if foundation then "true" else "false") 1
  let foundationLine ← Complexity.Costed.tick ("  - Perdurant(" ++ yn) 1
  let foundationLine ← Complexity.Costed.tick (foundationLine ++ "): ") 1
  let foundationLine ← Complexity.Costed.tick (foundationLine ++ foundationText) 1
  let foundationLine ← Complexity.Costed.tick (foundationLine ++ ".") 1
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assignment) 2
  let out ← Complexity.Costed.tick (out.push trigger) 2
  let out ← Complexity.Costed.tick (out.push
    "Required together: the founded thing must be a computed `ExternallyDependentMode` or a `Relator`, and the foundation must be a `Perdurant`.") 2
  let out ← Complexity.Costed.tick (out.push relatorLine) 2
  let out ← Complexity.Costed.tick (out.push foundationLine) 2
  let out ← Complexity.Costed.foldArray modeStatus out fun out row =>
    Complexity.Costed.tick (out.push row) 1
  let suggestion ← Complexity.Costed.charge 2 <| if !classification then
    Complexity.Costed.pure
      "Suggestion: add the modal `Ex` variation and `InheresIn` facts needed for computed external dependence, or remove/relax the `FoundedBy` fact if this thing is not a relator or externally dependent mode."
    else do
      let text ← Complexity.Costed.tick ("Suggestion: classify `" ++ yn) 1
      Complexity.Costed.tick (text ++ "` as `Perdurant`, or change the `FoundedBy` target to a perdurant foundation.") 1
  Complexity.Costed.tick (out.push suggestion) 2

private theorem ax71FailureRowsCosted_value
    (worldNames thingNames : Array Name) (w x y : Nat)
    (classification relator foundation : Bool) (modeStatus : Array String) :
    (ax71FailureRowsCosted worldNames thingNames w x y classification relator foundation modeStatus).value =
      (#[s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
        s!"Triggered by: `FoundedBy({indexedName thingNames x}, {indexedName thingNames y})`.",
        "Required together: the founded thing must be a computed `ExternallyDependentMode` or a `Relator`, and the foundation must be a `Perdurant`.",
        s!"  - Relator({indexedName thingNames x}): {if relator then "true" else "false"}.",
        s!"  - Perdurant({indexedName thingNames y}): {if foundation then "true" else "false"}."
      ] ++ modeStatus).push
        (if !classification then
          "Suggestion: add the modal `Ex` variation and `InheresIn` facts needed for computed external dependence, or remove/relax the `FoundedBy` fact if this thing is not a relator or externally dependent mode."
        else
          s!"Suggestion: classify `{indexedName thingNames y}` as `Perdurant`, or change the `FoundedBy` target to a perdurant foundation.") := by
  unfold ax71FailureRowsCosted
  rw [← indexedNameCosted_value thingNames x, ← indexedNameCosted_value thingNames y,
    ← indexedNameCosted_value worldNames w]
  generalize indexedNameCosted thingNames x = xn
  generalize indexedNameCosted thingNames y = yn
  generalize indexedNameCosted worldNames w = wn
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
    Complexity.Costed.foldArray_value, Complexity.Costed.charge_value]
  rw [Array.foldl_push_eq_append rfl]
  rw [Array.map_id']
  cases classification <;> rfl

private theorem ax71FailureRowsCosted_cost_le
    (worldNames thingNames : Array Name) (w x y : Nat)
    (classification relator foundation : Bool) (modeStatus : Array String) :
    (ax71FailureRowsCosted worldNames thingNames w x y classification relator foundation modeStatus).cost ≤
      3 * modeStatus.size + 49 := by
  have hcopy (out : Array String) :
      (Complexity.Costed.foldArray modeStatus out
        (fun out row => Complexity.Costed.tick (out.push row) 1)).cost ≤ modeStatus.size * 3 :=
    Complexity.Costed.foldArray_cost_le modeStatus out
      (fun out row => Complexity.Costed.tick (out.push row) 1) 1 (by intros; rfl)
  cases classification <;>
    simp only [ax71FailureRowsCosted, Bind.bind, Complexity.Costed.bind_cost,
      Complexity.Costed.tick_cost, indexedNameCosted_cost, Complexity.Costed.charge_cost,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Complexity.Costed.pure_cost] <;> grind only

private theorem ax71FailureRowsCosted_size
    (worldNames thingNames : Array Name) (w x y : Nat)
    (classification relator foundation : Bool) (modeStatus : Array String) :
    (ax71FailureRowsCosted worldNames thingNames w x y classification relator foundation modeStatus).value.size =
      6 + modeStatus.size := by
  rw [ax71FailureRowsCosted_value]
  simp
  omega

/-- Explain the retained assignment. This boundary keeps the search proof
independent of string construction and lets its caller reuse the explanation's
value, cost, and row-count lemmas without expanding the renderer. -/
private def ax71FailureAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (w x y : Nat)
    (classification foundation : Bool) : Complexity.Costed (Array String) := do
  let modeStatus ← renderExternallyDependentModeStatusCosted worldNames thingNames tables x w
  let relator ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w
  ax71FailureRowsCosted worldNames thingNames w x y classification relator foundation modeStatus

private theorem ax71FailureAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (w x y : Nat)
    (classification foundation : Bool) :
    (ax71FailureAnalysisCosted worldNames thingNames tables w x y classification foundation).value =
      (ax71FailureRowsCosted worldNames thingNames w x y classification
        (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w).value
        foundation (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value).value := by
  -- Compose the two projection lemmas explicitly. Asking the kernel to
  -- normalize both sides expands the long row renderer during this proof.
  exact Eq.trans
    (Complexity.Costed.bind_value
      (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w)
      (fun status => Complexity.Costed.bind
        (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w)
        (fun relator => ax71FailureRowsCosted worldNames thingNames w x y classification
          relator foundation status)))
    (Complexity.Costed.bind_value
      (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w)
      (fun relator => ax71FailureRowsCosted worldNames thingNames w x y classification
        relator foundation
        (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value))

private theorem ax71FailureAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (w x y : Nat)
    (classification foundation : Bool) :
    (ax71FailureAnalysisCosted worldNames thingNames tables w x y classification foundation).cost ≤
      externallyDependentModeStatusCostBound worldNames.size thingNames.size tables + 70 := by
  have hstatus := renderExternallyDependentModeStatusCosted_cost_le worldNames thingNames tables x w
  have hsize := renderExternallyDependentModeStatusCosted_size_le worldNames thingNames tables x w
  have hrelator := Complexity.diagnosticUnaryCosted_cost_le worldNames.size thingNames.size tables .relator x w
  have hrows := ax71FailureRowsCosted_cost_le worldNames thingNames w x y classification
    (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w).value
    foundation (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value
  simp only [ax71FailureAnalysisCosted, Bind.bind, Complexity.Costed.bind_cost]
  omega

private theorem ax71FailureAnalysisCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (w x y : Nat)
    (classification foundation : Bool) :
    (ax71FailureAnalysisCosted worldNames thingNames tables w x y classification foundation).value.size ≤ 9 := by
  rw [ax71FailureAnalysisCosted_value, ax71FailureRowsCosted_size]
  have h := renderExternallyDependentModeStatusCosted_size_le worldNames thingNames tables x w
  omega

private def ax71FoundationAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let found ← ax71AssignmentsCosted worldNames.size thingNames.size tables
  Complexity.Costed.charge 1 <| match found with
  | none => do
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      Complexity.Costed.tick (out.push
        "Foundation check for ax71: every `FoundedBy` fact has a computed externally dependent mode or relator on the left and a perdurant on the right.") 2
  | some (w, x, y, classification, foundation) =>
      ax71FailureAnalysisCosted worldNames thingNames tables w x y classification foundation

private def ax71FoundationAnalysisCostBound
    (W T : Nat) (tables : FactTables) : Nat :=
  W * (T * (T * (ax71AssignmentCostBound W T + 4) + 3) + 3) +
    externallyDependentModeStatusCostBound W T tables + 71

/-- Increasing the world, thing, or assertion count cannot lower this upper
bound. Exact execution counts can fall when added facts cause an earlier exit. -/
private theorem ax71FoundationAnalysisCostBound_mono
    {W W' T T' : Nat} {tables tables' : FactTables}
    (hW : W ≤ W') (hT : T ≤ T')
    (hD : tables.derivedProps.size ≤ tables'.derivedProps.size) :
    ax71FoundationAnalysisCostBound W T tables ≤ ax71FoundationAnalysisCostBound W' T' tables' := by
  unfold ax71FoundationAnalysisCostBound ax71AssignmentCostBound
    externallyDependentModeStatusCostBound externallyDependentWitnessCostBound
  repeat' first
    | assumption
    | exact Nat.le_refl _
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul

/-- Search-result correspondence and row-format correspondence compose here.
The failure's coordinates justify the sparse meaning of the final relator
read. Classification and foundation status come from the retained assignment,
and the row theorem fixes all text and row order. -/
private theorem ax71FoundationAnalysisCosted_result_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size) :
    (ax71FoundationAnalysisCosted worldNames thingNames tables).value =
      match (ax71AssignmentsCosted worldNames.size thingNames.size tables).value with
      | none => #["Foundation check for ax71: every `FoundedBy` fact has a computed externally dependent mode or relator on the left and a perdurant on the right."]
      | some (w, x, y, classification, foundation) =>
          (ax71FailureRowsCosted worldNames thingNames w x y classification
            (tables.unaryLookup "relator" x w) foundation
            (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value).value := by
  simp only [ax71FoundationAnalysisCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · rfl
  · rename_i w x y classification foundation found
    obtain ⟨hw, hx, _⟩ := ax71AssignmentsCosted_some_bounds worldNames.size thingNames.size
      tables agreement w x y classification foundation found
    have hrelator := Complexity.diagnosticUnaryCosted_value worldNames.size thingNames.size
      tables agreement .relator ⟨x, hx⟩ ⟨w, hw⟩
    rw [ax71FailureAnalysisCosted_value]
    exact congrArg (fun relator =>
      (ax71FailureRowsCosted worldNames thingNames w x y classification relator foundation
        (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value).value)
      hrelator

private theorem ax71FoundationAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax71FoundationAnalysisCosted worldNames thingNames tables).cost ≤
      ax71FoundationAnalysisCostBound worldNames.size thingNames.size tables := by
  have hsearch := ax71AssignmentsCosted_cost_le worldNames.size thingNames.size tables
  unfold ax71FoundationAnalysisCosted
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
    unfold ax71FoundationAnalysisCostBound
    omega
  · rename_i w x y classification foundation heq
    have hfailure := ax71FailureAnalysisCosted_cost_le worldNames thingNames tables w x y classification foundation
    unfold ax71FoundationAnalysisCostBound
    omega

private theorem ax71FoundationAnalysisCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax71FoundationAnalysisCosted worldNames thingNames tables).value.size ≤ 9 := by
  simp only [ax71FoundationAnalysisCosted, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.charge_value]
  split
  · simp
  · rename_i w x y classification foundation heq
    exact ax71FailureAnalysisCosted_size_le worldNames thingNames tables w x y classification foundation

/-- The four ways an asserted QuaIndividualOf fact can disagree with its
part characterization. The constructor order is also the diagnostic priority
when a constituent violates more than one requirement. -/
private inductive Ax73ConstituentFailure where
  | missingMode
  | missingInherence
  | missingFoundation
  | missingPart
  deriving DecidableEq, Repr

/-- Select a constituent failure before constructing any diagnostic text.
A candidate QuaIndividualOf fact relates x to bearer y at world w; z is the
constituent being tested.
A part must satisfy mode, inherence, then common foundation. A non-part needs
a report only when all three conditions hold. Later queries run only when
the earlier conditions leave them relevant to that decision. -/
private def ax73ConstituentFailureCosted
    (W T : Nat) (tables : FactTables) (z x y w : Nat) :
    Complexity.Costed (Option Ax73ConstituentFailure) := do
  let isPart ← partLookupCosted W T tables z x w
  Complexity.Costed.charge 1 <| if isPart then do
    let mode ← externallyDependentModeLookupCosted W T tables z w
    Complexity.Costed.charge 1 <| if mode then do
      let inheres ← Complexity.diagnosticBinaryCosted W T tables .inheresIn z y w
      Complexity.Costed.charge 1 <| if inheres then do
        let shared ← sameFoundationLookupCosted W T tables z x w
        Complexity.Costed.charge 1 <| if shared then Complexity.Costed.pure none
          else Complexity.Costed.pure (some .missingFoundation)
      else Complexity.Costed.pure (some .missingInherence)
    else Complexity.Costed.pure (some .missingMode)
  else do
    let characterized ← ax73CharacterizedCosted W T tables z x y w
    Complexity.Costed.charge 1 <| if characterized then Complexity.Costed.pure (some .missingPart)
      else Complexity.Costed.pure none

private def ax73ConstituentCostBound (W T : Nat) : Nat :=
  ax73CharacterizedCostBound W T + 21

/-- The Boolean specification records the report priority independently of
which tests the executable skips. In particular, a missing mode takes priority
over missing inherence on the same constituent. -/
private theorem ax73ConstituentFailureCosted_value
    (W T : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73ConstituentFailureCosted W T tables z x y w).value =
      let isPart := (partLookupCosted W T tables z x w).value
      let mode := (externallyDependentModeLookupCosted W T tables z w).value
      let inheres := (Complexity.diagnosticBinaryCosted W T tables .inheresIn z y w).value
      let shared := (sameFoundationLookupCosted W T tables z x w).value
      if isPart && !mode then some .missingMode
      else if isPart && !inheres then some .missingInherence
      else if isPart && mode && inheres && !shared then some .missingFoundation
      else if !isPart && mode && inheres && shared then some .missingPart
      else none := by
  cases hpart : (partLookupCosted W T tables z x w).value <;>
    cases hmode : (externallyDependentModeLookupCosted W T tables z w).value <;>
    cases hinheres : (Complexity.diagnosticBinaryCosted W T tables .inheresIn z y w).value <;>
    cases hshared : (sameFoundationLookupCosted W T tables z x w).value <;>
    simp_all [ax73ConstituentFailureCosted, ax73CharacterizedCosted, Bind.bind]

private theorem ax73ConstituentFailureCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (z x y : Fin T) (w : Fin W) :
    (ax73ConstituentFailureCosted W T tables z.val x.val y.val w.val).value =
      let isPart := z.val == x.val || tables.binaryLookup "part" z.val x.val w.val
      let mode := (externallyDependentModeLookupCosted W T tables z.val w.val).value
      let inheres := tables.binaryLookup "inheresIn" z.val y.val w.val
      let shared := (List.finRange T).any fun foundation =>
        tables.binaryLookup "foundedBy" z.val foundation.val w.val &&
          tables.binaryLookup "foundedBy" x.val foundation.val w.val
      if isPart && !mode then some .missingMode
      else if isPart && !inheres then some .missingInherence
      else if isPart && mode && inheres && !shared then some .missingFoundation
      else if !isPart && mode && inheres && shared then some .missingPart
      else none := by
  rw [ax73ConstituentFailureCosted_value,
    partLookupCosted_sparse_value W T tables agreement,
    Complexity.diagnosticBinaryCosted_value W T tables agreement,
    sameFoundationLookupCosted_sparse_value W T tables agreement]
  rfl

private theorem ax73ConstituentFailureCosted_isNone
    (W T : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73ConstituentFailureCosted W T tables z x y w).value.isNone =
      ((partLookupCosted W T tables z x w).value ==
        (ax73CharacterizedCosted W T tables z x y w).value) := by
  rw [ax73ConstituentFailureCosted_value]
  simp only [ax73CharacterizedCosted, Complexity.Costed.andThen_value]
  cases (partLookupCosted W T tables z x w).value <;>
    cases (externallyDependentModeLookupCosted W T tables z w).value <;>
    cases (Complexity.diagnosticBinaryCosted W T tables .inheresIn z y w).value <;>
    cases (sameFoundationLookupCosted W T tables z x w).value <;> rfl

private theorem ax73ConstituentFailureCosted_cost_le
    (W T : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73ConstituentFailureCosted W T tables z x y w).cost ≤ ax73ConstituentCostBound W T := by
  have hpart := partLookupCosted_cost_le W T tables z x w
  have hmode := externallyDependentModeLookupCosted_cost_le W T tables z w
  have hinheres := Complexity.diagnosticBinaryCosted_cost_le W T tables .inheresIn z y w
  have hshared := sameFoundationLookupCosted_cost_le W T tables z x w
  have hcharacterized := ax73CharacterizedCosted_cost_le W T tables z x y w
  unfold ax73ConstituentFailureCosted ax73ConstituentCostBound
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  split
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split
    · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
      split
      · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
        split <;> simp only [Complexity.Costed.pure_cost] <;>
          unfold ax73CharacterizedCostBound <;> omega
      · simp only [Complexity.Costed.pure_cost]
        unfold ax73CharacterizedCostBound
        omega
    · simp only [Complexity.Costed.pure_cost]
      unfold ax73CharacterizedCostBound
      omega
  · simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split <;> simp only [Complexity.Costed.pure_cost] <;> omega

private theorem ax73ConstituentCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax73ConstituentCostBound W T ≤ ax73ConstituentCostBound W' T' :=
  Nat.add_le_add_right (ax73CharacterizedCostBound_mono hW hT) 21

/-- Format only the selected constituent failure. Names and the assignment
line are computed once and reused. Foundation details run only for the
foundation failure. Each array push charges both storage and an emitted row;
string operations use the documented unit-cost interface, not character cost. -/
private def ax73PrimaryEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax73ConstituentFailure) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let zn ← indexedNameCosted thingNames z
  let wn ← indexedNameCosted worldNames w
  let assignment ← Complexity.Costed.tick ("Counterexample assignment: x = " ++ xn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", y = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ yn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", z = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ zn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", w = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ wn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ".") 1
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assignment) 2
  Complexity.Costed.charge 1 <| match failure with
  | .missingMode => do
      let line ← Complexity.Costed.tick ("Required but missing: constituent `" ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ "` is a part of qua individual `") 1
      let line ← Complexity.Costed.tick (line ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ "` but is not a computed `ExternallyDependentMode`.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      Complexity.Costed.tick (out.push
        "Suggestion: supply the mode, modal existence, and inherence facts needed for external dependence, or revise the `Part`/`QuaIndividualOf` assertions.") 2
  | .missingInherence => do
      let line ← Complexity.Costed.tick ("Required but missing: constituent `" ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ "` must `InheresIn(") 1
      let line ← Complexity.Costed.tick (line ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ ", ") 1
      let line ← Complexity.Costed.tick (line ++ yn) 1
      let line ← Complexity.Costed.tick (line ++ ")` because it is a part of `QuaIndividualOf(") 1
      let line ← Complexity.Costed.tick (line ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ ", ") 1
      let line ← Complexity.Costed.tick (line ++ yn) 1
      let line ← Complexity.Costed.tick (line ++ ")`.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      Complexity.Costed.tick (out.push
        "Suggestion: add the constituent's inherence in the asserted bearer, or revise the `Part`/`QuaIndividualOf` assertions.") 2
  | .missingFoundation => do
      let equality ← foundationEqCosted worldNames.size thingNames.size tables z x w
      let reason ← Complexity.Costed.charge 1 <| match equality with
        | none => Complexity.Costed.pure "missing or ambiguous foundation data"
        | some equal => Complexity.Costed.tick
            (if equal then "matching foundations" else "different foundations") 1
      let zStatus ← renderFoundationStatusCosted worldNames.size thingNames tables z w
      let xStatus ← renderFoundationStatusCosted worldNames.size thingNames tables x w
      let line ← Complexity.Costed.tick ("Required but missing: constituent `" ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ "` and qua individual `") 1
      let line ← Complexity.Costed.tick (line ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ "` must share `FoundationOf`; the tables show ") 1
      let line ← Complexity.Costed.tick (line ++ reason) 1
      let line ← Complexity.Costed.tick (line ++ ".") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      let zLine ← Complexity.Costed.tick ("  - " ++ zn) 1
      let zLine ← Complexity.Costed.tick (zLine ++ ": ") 1
      let zLine ← Complexity.Costed.tick (zLine ++ zStatus) 1
      let out ← Complexity.Costed.tick (out.push zLine) 2
      let xLine ← Complexity.Costed.tick ("  - " ++ xn) 1
      let xLine ← Complexity.Costed.tick (xLine ++ ": ") 1
      let xLine ← Complexity.Costed.tick (xLine ++ xStatus) 1
      let out ← Complexity.Costed.tick (out.push xLine) 2
      Complexity.Costed.tick (out.push
        "Suggestion: give both constituents exactly one common `FoundedBy` target, or revise the `Part`/`QuaIndividualOf` assertions.") 2
  | .missingPart => do
      let line ← Complexity.Costed.tick ("Required but missing: `Part(" ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ ", ") 1
      let line ← Complexity.Costed.tick (line ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ ")`; the entity is an externally dependent mode that inheres in the asserted bearer and shares the qua individual's foundation.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      Complexity.Costed.tick (out.push
        "Suggestion: add the missing constituent part fact, or revise the facts that satisfy the right-hand characterization.") 2

private theorem ax73PrimaryEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax73ConstituentFailure) :
    (ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w failure).value =
      let assignment :=
        s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}."
      match failure with
      | .missingMode => #[
          assignment,
          s!"Required but missing: constituent `{indexedName thingNames z}` is a part of qua individual `{indexedName thingNames x}` but is not a computed `ExternallyDependentMode`.",
          "Suggestion: supply the mode, modal existence, and inherence facts needed for external dependence, or revise the `Part`/`QuaIndividualOf` assertions."]
      | .missingInherence => #[
          assignment,
          s!"Required but missing: constituent `{indexedName thingNames z}` must `InheresIn({indexedName thingNames z}, {indexedName thingNames y})` because it is a part of `QuaIndividualOf({indexedName thingNames x}, {indexedName thingNames y})`.",
          "Suggestion: add the constituent's inherence in the asserted bearer, or revise the `Part`/`QuaIndividualOf` assertions."]
      | .missingFoundation =>
          let reason := match (foundationEqCosted worldNames.size thingNames.size tables z x w).value with
            | some false => "different foundations"
            | none => "missing or ambiguous foundation data"
            | some true => "matching foundations"
          #[
            assignment,
            s!"Required but missing: constituent `{indexedName thingNames z}` and qua individual `{indexedName thingNames x}` must share `FoundationOf`; the tables show {reason}.",
            s!"  - {indexedName thingNames z}: {(renderFoundationStatusCosted worldNames.size thingNames tables z w).value}",
            s!"  - {indexedName thingNames x}: {(renderFoundationStatusCosted worldNames.size thingNames tables x w).value}",
            "Suggestion: give both constituents exactly one common `FoundedBy` target, or revise the `Part`/`QuaIndividualOf` assertions."]
      | .missingPart => #[
          assignment,
          s!"Required but missing: `Part({indexedName thingNames z}, {indexedName thingNames x})`; the entity is an externally dependent mode that inheres in the asserted bearer and shares the qua individual's foundation.",
          "Suggestion: add the missing constituent part fact, or revise the facts that satisfy the right-hand characterization."] := by
  unfold ax73PrimaryEvidenceCosted
  rw [← indexedNameCosted_value thingNames x, ← indexedNameCosted_value thingNames y,
    ← indexedNameCosted_value thingNames z, ← indexedNameCosted_value worldNames w]
  generalize indexedNameCosted thingNames x = xn
  generalize indexedNameCosted thingNames y = yn
  generalize indexedNameCosted thingNames z = zn
  generalize indexedNameCosted worldNames w = wn
  generalize foundationEqCosted worldNames.size thingNames.size tables z x w = equality
  generalize renderFoundationStatusCosted worldNames.size thingNames tables z w = zStatus
  generalize renderFoundationStatusCosted worldNames.size thingNames tables x w = xStatus
  cases failure <;>
    simp only [Bind.bind, Complexity.Costed.bind_value,
      Complexity.Costed.tick_value, Complexity.Costed.charge_value]
  all_goals try rfl
  cases equality.value with
  | none => rfl
  | some equal => cases equal <;> rfl

private theorem ax73PrimaryEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax73ConstituentFailure) :
    (ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w failure).cost ≤
      110 * thingNames.size + 85 := by
  -- Bound each name computation before introducing its returned string.
  -- This keeps helper implementations out of the remaining arithmetic proof
  -- and avoids repeatedly reducing them during kernel checking.
  have step {α β : Type} (first : Complexity.Costed α) (next : α → Complexity.Costed β)
      (a b : Nat) (hfirst : first.cost ≤ a) (hnext : ∀ value, (next value).cost ≤ b) :
      (first.bind next).cost ≤ a + b :=
    Nat.add_le_add hfirst (hnext first.value)
  unfold ax73PrimaryEvidenceCosted
  simp only [Bind.bind]
  refine le_trans (step _ _ 4 (110 * thingNames.size + 81) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames x)
  intro xn
  refine le_trans (step _ _ 4 (110 * thingNames.size + 77) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames y)
  intro yn
  refine le_trans (step _ _ 4 (110 * thingNames.size + 73) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames z)
  intro zn
  refine le_trans (step _ _ 4 (110 * thingNames.size + 69) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost worldNames w)
  intro wn
  have hequality := foundationEqCosted_cost_le worldNames.size thingNames.size tables z x w
  have hz := renderFoundationStatusCosted_cost_le worldNames.size thingNames tables z w
  have hx := renderFoundationStatusCosted_cost_le worldNames.size thingNames tables x w
  generalize foundationEqCosted worldNames.size thingNames.size tables z x w = equality at *
  generalize renderFoundationStatusCosted worldNames.size thingNames tables z w = zStatus at *
  generalize renderFoundationStatusCosted worldNames.size thingNames tables x w = xStatus at *
  cases failure <;>
    simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost, Complexity.Costed.charge_cost]
  all_goals cases equality.value <;>
    simp_all only [Complexity.Costed.pure_cost, Complexity.Costed.tick_cost, Nat.reduceAdd] <;> omega

private theorem ax73PrimaryEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax73ConstituentFailure) :
    (ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w failure).value.size =
      match failure with
      | .missingFoundation => 5
      | _ => 3 := by
  cases failure <;>
    simp only [ax73PrimaryEvidenceCosted, Bind.bind, Complexity.Costed.bind_value,
      Complexity.Costed.tick_value, Complexity.Costed.charge_value, Array.size_push, Array.size_empty]

/-- Retain the first failing constituent and its reason. The direct numeric
loop stops before another query after finding a result. Each visited thing
adds an option-map branch and the loop operations to its predicate cost. -/
private def ax73PrimaryFailureCosted
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Option (Nat × Ax73ConstituentFailure)) :=
  foldDiagDomainCosted 0 T none Option.isSome fun _ z => do
    let failure ← ax73ConstituentFailureCosted W T tables z x y w
    Complexity.Costed.tick (failure.map fun reason => (z, reason)) 1

private theorem ax73PrimaryFailureCosted_value
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (ax73PrimaryFailureCosted W T tables x y w).value =
      (List.range T).findSome? (fun z =>
        (ax73ConstituentFailureCosted W T tables z x y w).value.map fun reason => (z, reason)) := by
  unfold ax73PrimaryFailureCosted
  apply foldDiagDomainCosted_firstSome_value
  intro z hz
  rfl

private theorem ax73PrimaryFailureCosted_some_bound
    (W T : Nat) (tables : FactTables) (x y w z : Nat) (reason : Ax73ConstituentFailure)
    (found : (ax73PrimaryFailureCosted W T tables x y w).value = some (z, reason)) : z < T := by
  rw [ax73PrimaryFailureCosted_value] at found
  obtain ⟨candidate, hcandidate, found⟩ := List.exists_of_findSome?_eq_some found
  have hbound := List.mem_range.mp hcandidate
  cases h : (ax73ConstituentFailureCosted W T tables candidate x y w).value with
  | none => simp [h] at found
  | some cause =>
      simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
      omega

private theorem ax73PrimaryFailureCosted_cost_le
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (ax73PrimaryFailureCosted W T tables x y w).cost ≤ T * (ax73ConstituentCostBound W T + 4) := by
  unfold ax73PrimaryFailureCosted
  apply foldDiagDomainCosted_cost_le
  intro state z hlo hhi
  have h := ax73ConstituentFailureCosted_cost_le W T tables z x y w
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
  omega

/-- An unasserted QuaIndividualOf fact cannot trigger a constituent report, so
it costs only the entry branch here. For an asserted fact, search first and
render the retained failure once. Niu et al.'s compositional cost semantics
(POPL 2022, doi:10.1145/3498670) motivates keeping both stages in this same
counted executable rather than assigning a separate report counter. -/
private def ax73PrimaryZScanCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) : Complexity.Costed (Option (Array String)) :=
  Complexity.Costed.charge 1 <| if qio then do
    let found ← ax73PrimaryFailureCosted worldNames.size thingNames.size tables x y w
    Complexity.Costed.charge 1 <| match found with
    | none => Complexity.Costed.pure none
    | some (z, reason) => do
        let rows ← ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w reason
        Complexity.Costed.pure (some rows)
  else Complexity.Costed.pure none

private def ax73PrimaryScanCostBound (W T : Nat) : Nat :=
  T * (ax73ConstituentCostBound W T + 4) + 110 * T + 87

private theorem ax73PrimaryZScanCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) :
    (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w).value =
      if qio then
        ((List.range thingNames.size).findSome? (fun z =>
          (ax73ConstituentFailureCosted worldNames.size thingNames.size tables z x y w).value.map
            fun reason => (z, reason))).map fun (z, reason) =>
              (ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w reason).value
      else none := by
  -- Prove erasure for abstract search and rendering computations first.
  -- Instantiation then needs no reduction of either implementation.
  have erase (search : Complexity.Costed (Option (Nat × Ax73ConstituentFailure)))
      (render : Nat → Ax73ConstituentFailure → Complexity.Costed (Array String)) (asserted : Bool) :
      (Complexity.Costed.charge 1 <| if asserted then do
        let found ← search
        Complexity.Costed.charge 1 <| match found with
        | none => Complexity.Costed.pure none
        | some (z, reason) => do
            let rows ← render z reason
            Complexity.Costed.pure (some rows)
      else Complexity.Costed.pure none).value =
        if asserted then search.value.map (fun (z, reason) => (render z reason).value) else none := by
    cases asserted <;> simp only [Complexity.Costed.charge_value, Bool.false_eq_true,
      ↓reduceIte, Bind.bind, Complexity.Costed.bind_value]
    · rfl
    · cases search.value with
      | none => rfl
      | some found => rcases found with ⟨z, reason⟩; rfl
  exact Eq.trans
    (erase (ax73PrimaryFailureCosted worldNames.size thingNames.size tables x y w)
      (fun z reason => ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w reason) qio)
    (congrArg (fun found => if qio then found.map (fun (z, reason) =>
        (ax73PrimaryEvidenceCosted worldNames thingNames tables x y z w reason).value) else none)
      (ax73PrimaryFailureCosted_value worldNames.size thingNames.size tables x y w))

private theorem ax73PrimaryZScanCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) :
    (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w).cost ≤
      ax73PrimaryScanCostBound worldNames.size thingNames.size := by
  have hsearch := ax73PrimaryFailureCosted_cost_le worldNames.size thingNames.size tables x y w
  simp only [ax73PrimaryZScanCosted, Complexity.Costed.charge_cost]
  split
  · simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
    split
    · simp only [Complexity.Costed.pure_cost]
      unfold ax73PrimaryScanCostBound
      omega
    · rename_i z reason hfound
      have hrows := ax73PrimaryEvidenceCosted_cost_le worldNames thingNames tables x y z w reason
      simp only [Complexity.Costed.bind_cost, Complexity.Costed.pure_cost]
      unfold ax73PrimaryScanCostBound
      omega
  · simp only [Complexity.Costed.pure_cost]
    unfold ax73PrimaryScanCostBound
    omega

private theorem ax73PrimaryScanCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax73PrimaryScanCostBound W T ≤ ax73PrimaryScanCostBound W' T' := by
  unfold ax73PrimaryScanCostBound
  exact Nat.add_le_add_right
    (Nat.add_le_add
      (Nat.mul_le_mul hT (Nat.add_le_add_right (ax73ConstituentCostBound_mono hW hT) 4))
      (Nat.mul_le_mul_left 110 hT)) 87

/-- Check both sides of the characterization at each thing. A mismatch ends
the universal scan immediately. The two sides are evaluated before their
Boolean equality test, but later things are not evaluated after a mismatch. -/
private def ax73CharacterizationZScanCosted
    (W T : Nat) (tables : FactTables) (x y w : Nat) : Complexity.Costed Bool :=
  Complexity.allFinCosted T fun z => do
    let isPart ← partLookupCosted W T tables z.val x w
    let characterized ← ax73CharacterizedCosted W T tables z.val x y w
    Complexity.Costed.tick (isPart == characterized) 1

private def ax73CharacterizationZCostBound (W T : Nat) : Nat :=
  ax73CharacterizedCostBound W T + 22

private theorem ax73CharacterizationZScanCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    T * ax73CharacterizationZCostBound W T ≤ T' * ax73CharacterizationZCostBound W' T' :=
  Nat.mul_le_mul hT (Nat.add_le_add_right (ax73CharacterizedCostBound_mono hW hT) 22)

private theorem ax73CharacterizationZScanCosted_cost_le
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (ax73CharacterizationZScanCosted W T tables x y w).cost ≤
      T * ax73CharacterizationZCostBound W T := by
  unfold ax73CharacterizationZScanCosted
  rw [Complexity.allFinCosted_eq_list]
  have h := Complexity.allListCosted_cost_le (List.finRange T)
    (fun z => do
      let isPart ← partLookupCosted W T tables z.val x w
      let characterized ← ax73CharacterizedCosted W T tables z.val x y w
      Complexity.Costed.tick (isPart == characterized) 1)
    (ax73CharacterizedCostBound W T + 20) (by
      intro z hz
      have hpart := partLookupCosted_cost_le W T tables z.val x w
      have hcharacterized := ax73CharacterizedCosted_cost_le W T tables z.val x y w
      simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
      omega)
  simpa [ax73CharacterizationZCostBound, Nat.add_assoc] using h

private theorem ax73CharacterizationZScanCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x y : Fin T) (w : Fin W) :
    (ax73CharacterizationZScanCosted W T tables x.val y.val w.val).value =
      (List.finRange T).all (fun z =>
        ((z.val == x.val || tables.binaryLookup "part" z.val x.val w.val) ==
          ((externallyDependentModeLookupCosted W T tables z.val w.val).value &&
            (tables.binaryLookup "inheresIn" z.val y.val w.val &&
              (List.finRange T).any (fun foundation =>
                tables.binaryLookup "foundedBy" z.val foundation.val w.val &&
                  tables.binaryLookup "foundedBy" x.val foundation.val w.val))))) := by
  simp only [ax73CharacterizationZScanCosted, Complexity.allFinCosted_eq_list,
    Complexity.allListCosted_value, Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, partLookupCosted_sparse_value W T tables agreement,
    ax73CharacterizedCosted_sparse_value W T tables agreement, partLookup]

/-- The first-failure search returns no result exactly when every constituent
matches the Boolean characterization test. This holds for every raw table
because both procedures use the same guarded queries. -/
private theorem ax73PrimaryFailureCosted_isNone
    (W T : Nat) (tables : FactTables) (x y w : Nat) :
    (ax73PrimaryFailureCosted W T tables x y w).value.isNone =
      (ax73CharacterizationZScanCosted W T tables x y w).value := by
  rw [Bool.eq_iff_iff, Option.isNone_iff_eq_none, ax73PrimaryFailureCosted_value,
    List.findSome?_eq_none_iff]
  simp only [Option.map_eq_none_iff, List.mem_range, ax73CharacterizationZScanCosted,
    Complexity.allFinCosted_eq_list, Complexity.allListCosted_value,
    Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value, List.all_eq_true]
  constructor
  · intro h z hz
    have hnone := h z.val z.isLt
    have hvalue := ax73ConstituentFailureCosted_isNone W T tables z.val x y w
    rw [hnone] at hvalue
    exact hvalue.symm
  · intro h z hz
    apply Option.isNone_iff_eq_none.mp
    rw [ax73ConstituentFailureCosted_isNone]
    exact h ⟨z, hz⟩ (List.mem_finRange _)

/-- Formatting preserves whether the constituent search found a mismatch.
An absent QuaIndividualOf assertion skips this direction of the implication. -/
private theorem ax73PrimaryZScanCosted_isNone
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) :
    (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w).value.isNone =
      if qio then
        (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value
      else true := by
  rw [ax73PrimaryZScanCosted_value, ← ax73PrimaryFailureCosted_value]
  split
  · rw [Option.isNone_map, ax73PrimaryFailureCosted_isNone]
  · rfl

/-- A retained constituent report has at most five rows. The search's option
map preserves the selected formatter result without copying or re-emitting it. -/
private theorem ax73PrimaryZScanCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) (rows : Array String)
    (found : (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w).value = some rows) :
    rows.size ≤ 5 := by
  rw [ax73PrimaryZScanCosted_value] at found
  split at found
  · obtain ⟨⟨z, reason⟩, hsearch, hrows⟩ := Option.map_eq_some_iff.mp found
    rw [← hrows, ax73PrimaryEvidenceCosted_size]
    cases reason <;> decide
  · contradiction

/-- Report the reverse implication: the full characterization holds, but the
QuaIndividualOf fact is absent. The three names are rendered once. Six
concatenations construct the assignment and four construct the explanation.
Initialization and the three row pushes/emissions complete the 29 operations. -/
private def ax73ReverseEvidenceCosted
    (worldNames thingNames : Array Name) (x y w : Nat) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let wn ← indexedNameCosted worldNames w
  let assignment ← Complexity.Costed.tick ("Counterexample assignment: x = " ++ xn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", y = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ yn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", w = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ wn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ".") 1
  let line ← Complexity.Costed.tick ("Required but missing: `QuaIndividualOf(" ++ xn) 1
  let line ← Complexity.Costed.tick (line ++ ", ") 1
  let line ← Complexity.Costed.tick (line ++ yn) 1
  let line ← Complexity.Costed.tick (line ++ ")`; its complete part characterization holds.") 1
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assignment) 2
  let out ← Complexity.Costed.tick (out.push line) 2
  Complexity.Costed.tick (out.push
    "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact.") 2

private theorem ax73ReverseEvidenceCosted_value
    (worldNames thingNames : Array Name) (x y w : Nat) :
    (ax73ReverseEvidenceCosted worldNames thingNames x y w).value = #[
      s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
      s!"Required but missing: `QuaIndividualOf({indexedName thingNames x}, {indexedName thingNames y})`; its complete part characterization holds.",
      "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact."] := by
  unfold ax73ReverseEvidenceCosted
  rw [← indexedNameCosted_value thingNames x, ← indexedNameCosted_value thingNames y,
    ← indexedNameCosted_value worldNames w]
  generalize indexedNameCosted thingNames x = xn
  generalize indexedNameCosted thingNames y = yn
  generalize indexedNameCosted worldNames w = wn
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value]
  rfl

private theorem ax73ReverseEvidenceCosted_cost
    (worldNames thingNames : Array Name) (x y w : Nat) :
    (ax73ReverseEvidenceCosted worldNames thingNames x y w).cost = 29 := by
  simp only [ax73ReverseEvidenceCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.tick_cost, indexedNameCosted_cost]

private theorem ax73ReverseEvidenceCosted_size
    (worldNames thingNames : Array Name) (x y w : Nat) :
    (ax73ReverseEvidenceCosted worldNames thingNames x y w).value.size = 3 := by
  rw [ax73ReverseEvidenceCosted_value]
  rfl

/-- Check one assignment in both directions. The guarded table query supplies
the QuaIndividualOf Boolean. A constituent report takes priority. When that
search returns none, only an absent QuaIndividualOf fact needs the reverse
characterization test. Returned rows are already emitted by their formatter. -/
private def ax73AssignmentCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Option (Array String)) := do
  let qio ← Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables .quaIndividualOf x y w
  let primary ← ax73PrimaryZScanCosted worldNames thingNames tables qio x y w
  Complexity.Costed.charge 1 <| match primary with
  | some rows => Complexity.Costed.pure (some rows)
  | none => Complexity.Costed.charge 1 <| if qio then Complexity.Costed.pure none else do
      let characterization ← ax73CharacterizationZScanCosted
        worldNames.size thingNames.size tables x y w
      Complexity.Costed.charge 1 <| if characterization then do
        let rows ← ax73ReverseEvidenceCosted worldNames thingNames x y w
        Complexity.Costed.pure (some rows)
      else Complexity.Costed.pure none

private def ax73AssignmentCostBound (W T : Nat) : Nat :=
  ax73PrimaryScanCostBound W T + T * ax73CharacterizationZCostBound W T + 49

private theorem ax73AssignmentCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (ax73AssignmentCosted worldNames thingNames tables x y w).value =
      let qio := (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
        .quaIndividualOf x y w).value
      match (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w).value with
      | some rows => some rows
      | none => if qio then none
          else if (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value
          then some (ax73ReverseEvidenceCosted worldNames thingNames x y w).value else none := by
  unfold ax73AssignmentCosted
  generalize Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
    .quaIndividualOf x y w = query
  generalize ax73PrimaryZScanCosted worldNames thingNames tables = primary
  generalize ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w = characterization
  generalize ax73ReverseEvidenceCosted worldNames thingNames x y w = reverse
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  cases (primary query.value x y w).value with
  | some rows => rfl
  | none =>
      cases hq : query.value <;> cases hc : characterization.value <;>
        simp_all only [Bool.false_eq_true, ↓reduceIte, Complexity.Costed.charge_value,
          Complexity.Costed.bind_value, Complexity.Costed.pure_value]

/-- An assignment produces no report exactly when its QuaIndividualOf query
agrees with the complete characterization. This is the diagnostic Boolean
biconditional, independent of table agreement or a checker correspondence. -/
private theorem ax73AssignmentCosted_isNone
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (ax73AssignmentCosted worldNames thingNames tables x y w).value.isNone =
      ((Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
        .quaIndividualOf x y w).value ==
        (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value) := by
  have h := ax73PrimaryZScanCosted_isNone worldNames thingNames tables
    (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
      .quaIndividualOf x y w).value x y w
  rw [ax73AssignmentCosted_value]
  dsimp only
  generalize (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
    .quaIndividualOf x y w).value = qio at *
  generalize (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value = characterization at *
  generalize (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w).value = primary at *
  cases qio <;> cases primary <;> cases characterization <;>
    simp_all only [Bool.false_eq_true, ↓reduceIte,
      Option.isNone_none, Option.isNone_some, Bool.false_beq, Bool.true_beq,
      Bool.not_false, Bool.not_true, Bool.true_eq_false]

private theorem ax73AssignmentCosted_sparse_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x y : Fin thingNames.size) (w : Fin worldNames.size) :
    (ax73AssignmentCosted worldNames thingNames tables x.val y.val w.val).value =
      let qio := tables.binaryLookup "quaIndividualOf" x.val y.val w.val
      match (ax73PrimaryZScanCosted worldNames thingNames tables qio x.val y.val w.val).value with
      | some rows => some rows
      | none => if qio then none
          else if (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables
            x.val y.val w.val).value
          then some (ax73ReverseEvidenceCosted worldNames thingNames x.val y.val w.val).value
          else none := by
  rw [ax73AssignmentCosted_value,
    Complexity.diagnosticBinaryCosted_value worldNames.size thingNames.size tables agreement]
  rfl

private theorem ax73AssignmentCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (ax73AssignmentCosted worldNames thingNames tables x y w).cost ≤
      ax73AssignmentCostBound worldNames.size thingNames.size := by
  have hquery := Complexity.diagnosticBinaryCosted_cost_le
    worldNames.size thingNames.size tables .quaIndividualOf x y w
  have hprimary (qio : Bool) := ax73PrimaryZScanCosted_cost_le worldNames thingNames tables qio x y w
  have hcharacterization := ax73CharacterizationZScanCosted_cost_le
    worldNames.size thingNames.size tables x y w
  have hreverse := ax73ReverseEvidenceCosted_cost worldNames thingNames x y w
  unfold ax73AssignmentCosted
  generalize Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
    .quaIndividualOf x y w = query at *
  generalize ax73PrimaryZScanCosted worldNames thingNames tables = primary at *
  generalize ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w = characterization at *
  generalize ax73ReverseEvidenceCosted worldNames thingNames x y w = reverse at *
  have hp := hprimary query.value
  clear hprimary
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  cases (primary query.value x y w).value with
  | some rows =>
      simp only [Complexity.Costed.pure_cost]
      unfold ax73AssignmentCostBound
      omega
  | none =>
      cases hq : query.value <;> cases hc : characterization.value <;>
        simp_all only [Bool.false_eq_true, ↓reduceIte, Complexity.Costed.charge_cost,
          Complexity.Costed.bind_cost, Complexity.Costed.pure_cost] <;>
        unfold ax73AssignmentCostBound <;> omega

private theorem ax73AssignmentCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) (rows : Array String)
    (found : (ax73AssignmentCosted worldNames thingNames tables x y w).value = some rows) :
    rows.size ≤ 5 := by
  rw [ax73AssignmentCosted_value] at found
  dsimp only at found
  split at found
  · exact ax73PrimaryZScanCosted_some_size worldNames thingNames tables _ x y w rows (by
      rename_i result hprimary
      simpa using hprimary.trans found)
  · split at found
    · contradiction
    · split at found
      · injection found with hrows
        rw [← hrows, ax73ReverseEvidenceCosted_size]
        decide
      · contradiction

/-- Visit worlds, qua-individual candidates, and bearer candidates in increasing
coordinate order. Each loop stops as soon as the inner visit returns evidence.
The nested list searches below are proof specifications, not allocated input.
This follows the compositional cost semantics of Niu et al. (POPL 2022):
the counted traversal and its erased result come from this executable core. -/
private def ax73AssignmentsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Option (Array String)) :=
  foldDiagDomainCosted 0 worldNames.size none Option.isSome fun _ w =>
    foldDiagDomainCosted 0 thingNames.size none Option.isSome fun _ x =>
      foldDiagDomainCosted 0 thingNames.size none Option.isSome fun _ y =>
        ax73AssignmentCosted worldNames thingNames tables x y w

private theorem ax73AssignmentsCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73AssignmentsCosted worldNames thingNames tables).value =
      (List.range worldNames.size).findSome? (fun w =>
        (List.range thingNames.size).findSome? (fun x =>
          (List.range thingNames.size).findSome? (fun y =>
            (ax73AssignmentCosted worldNames thingNames tables x y w).value))) := by
  unfold ax73AssignmentsCosted
  apply foldDiagDomainCosted_firstSome_value
  intro w hw
  apply foldDiagDomainCosted_firstSome_value
  intro x hx
  apply foldDiagDomainCosted_firstSome_value
  intro y hy
  rfl

/-- No selected report means the diagnostic biconditional holds at every
bounded assignment. The ordered-search value theorem separately fixes which
assignment is reported when this universal condition fails. -/
private theorem ax73AssignmentsCosted_eq_none_iff
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73AssignmentsCosted worldNames thingNames tables).value = none ↔
      ∀ w < worldNames.size, ∀ x < thingNames.size, ∀ y < thingNames.size,
        (Complexity.diagnosticBinaryCosted worldNames.size thingNames.size tables
          .quaIndividualOf x y w).value =
        (ax73CharacterizationZScanCosted worldNames.size thingNames.size tables x y w).value := by
  rw [ax73AssignmentsCosted_value]
  simp only [List.findSome?_eq_none_iff, List.mem_range]
  simp only [← Option.isNone_iff_eq_none, ax73AssignmentCosted_isNone, beq_iff_eq]

private theorem ax73AssignmentsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73AssignmentsCosted worldNames thingNames tables).cost ≤
      worldNames.size * (thingNames.size *
        (thingNames.size * (ax73AssignmentCostBound worldNames.size thingNames.size + 3) + 3) + 3) := by
  unfold ax73AssignmentsCosted
  apply foldDiagDomainCosted_cost_le
  intro state w hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state x hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state y hlo hhi
  exact ax73AssignmentCosted_cost_le worldNames thingNames tables x y w

private theorem ax73AssignmentsCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (rows : Array String)
    (found : (ax73AssignmentsCosted worldNames thingNames tables).value = some rows) :
    rows.size ≤ 5 := by
  rw [ax73AssignmentsCosted_value] at found
  obtain ⟨w, hw, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨x, hx, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨y, hy, found⟩ := List.exists_of_findSome?_eq_some found
  exact ax73AssignmentCosted_some_size worldNames thingNames tables x y w rows found

private def ax73PartCharacterizationAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let found ← ax73AssignmentsCosted worldNames thingNames tables
  Complexity.Costed.charge 1 <| match found with
  | some rows => Complexity.Costed.pure rows
  | none => do
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      Complexity.Costed.tick (out.push
        "Part-characterization check for ax73 found no direct mismatch in either direction of the biconditional.") 2

private def ax73PartCharacterizationAnalysisCostBound (W T : Nat) : Nat :=
  W * (T * (T * (ax73AssignmentCostBound W T + 3) + 3) + 3) + 4

private theorem ax73PartCharacterizationAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).value =
      ((ax73AssignmentsCosted worldNames thingNames tables).value).getD #[
        "Part-characterization check for ax73 found no direct mismatch in either direction of the biconditional."] := by
  unfold ax73PartCharacterizationAnalysisCosted
  generalize ax73AssignmentsCosted worldNames thingNames tables = search
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  cases search.value <;> rfl

private theorem ax73PartCharacterizationAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).cost ≤
      ax73PartCharacterizationAnalysisCostBound worldNames.size thingNames.size := by
  have h := ax73AssignmentsCosted_cost_le worldNames thingNames tables
  unfold ax73PartCharacterizationAnalysisCosted
  generalize ax73AssignmentsCosted worldNames thingNames tables = search at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  cases search.value <;>
    simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost, Complexity.Costed.pure_cost] <;>
    unfold ax73PartCharacterizationAnalysisCostBound <;> omega

private theorem ax73PartCharacterizationAnalysisCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).value.size ≤ 5 := by
  rw [ax73PartCharacterizationAnalysisCosted_value]
  cases h : (ax73AssignmentsCosted worldNames thingNames tables).value with
  | none => decide
  | some rows => exact ax73AssignmentsCosted_some_size worldNames thingNames tables rows h

private theorem ax73PartCharacterizationAnalysisCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax73PartCharacterizationAnalysisCostBound W T ≤ ax73PartCharacterizationAnalysisCostBound W' T' := by
  have hA : ax73AssignmentCostBound W T ≤ ax73AssignmentCostBound W' T' :=
    Nat.add_le_add_right (Nat.add_le_add (ax73PrimaryScanCostBound_mono hW hT)
      (ax73CharacterizationZScanCostBound_mono hW hT)) 49
  unfold ax73PartCharacterizationAnalysisCostBound
  exact Nat.add_le_add_right (Nat.mul_le_mul hW
    (Nat.add_le_add_right (Nat.mul_le_mul hT
      (Nat.add_le_add_right (Nat.mul_le_mul hT (Nat.add_le_add_right hA 3)) 3)) 3)) 4

/-!
## Relator/part foundation diagnostics

Axiom 78 compares unique foundations for each relator and part. A missing or
ambiguous foundation produces witness requirements; two distinct unique
foundations produce a mismatch. The scan keeps world/relator/part order and
stops between five-row evidence groups when the budget is full.
-/

/-- Append one evidence group. Names and status strings are computed once and
reused across its five rows. The branch selects the mismatch wording or the
missing-witness wording. Following Niu et al. (POPL 2022,
doi:10.1145/3498670), the returned strings and their construction costs belong
to the same executable definition. Character copying remains outside this
unit-cost model. -/
private def ax78EvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (different : Bool) (x y w : Nat) (out : Array String) :
    Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let wn ← indexedNameCosted worldNames w
  let left ← renderFoundationStatusCosted worldNames.size thingNames tables x w
  let right ← renderFoundationStatusCosted worldNames.size thingNames tables y w
  let assignment ← Complexity.Costed.tick ("Counterexample assignment: x = " ++ xn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", y = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ yn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", w = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ wn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ".") 1
  let detail ← Complexity.Costed.charge 1 <| if different then do
      let line ← Complexity.Costed.tick ("Required but missing: Relator `" ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ "` and its part `") 1
      let line ← Complexity.Costed.tick (line ++ yn) 1
      Complexity.Costed.tick (line ++ "` must share the same `FoundationOf`.") 1
    else do
      let line ← Complexity.Costed.tick ("Missing witness requirements: Relator `" ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ "` and its part `") 1
      let line ← Complexity.Costed.tick (line ++ yn) 1
      Complexity.Costed.tick (line ++ "` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.") 1
  let evidence ← Complexity.Costed.tick ("Evidence for FoundationOf(" ++ xn) 1
  let evidence ← Complexity.Costed.tick (evidence ++ ") = FoundationOf(") 1
  let evidence ← Complexity.Costed.tick (evidence ++ yn) 1
  let evidence ← Complexity.Costed.tick (evidence ++ "):") 1
  let leftLine ← Complexity.Costed.tick ("  - " ++ xn) 1
  let leftLine ← Complexity.Costed.tick (leftLine ++ ": ") 1
  let leftLine ← Complexity.Costed.tick (leftLine ++ left) 1
  let rightLine ← Complexity.Costed.tick ("  - " ++ yn) 1
  let rightLine ← Complexity.Costed.tick (rightLine ++ ": ") 1
  let rightLine ← Complexity.Costed.tick (rightLine ++ right) 1
  let out ← Complexity.Costed.tick (out.push assignment) 2
  let out ← Complexity.Costed.tick (out.push detail) 2
  let out ← Complexity.Costed.tick (out.push evidence) 2
  let out ← Complexity.Costed.tick (out.push leftLine) 2
  Complexity.Costed.tick (out.push rightLine) 2

private theorem ax78EvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (different : Bool) (x y w : Nat) (out : Array String) :
    (ax78EvidenceCosted worldNames thingNames tables different x y w out).value =
      (out
        |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
        |>.push (if different then
            s!"Required but missing: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` must share the same `FoundationOf`."
          else
            s!"Missing witness requirements: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations.")
        |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
        |>.push s!"  - {indexedName thingNames x}: {(renderFoundationStatusCosted worldNames.size thingNames tables x w).value}"
        |>.push s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted worldNames.size thingNames tables y w).value}") := by
  unfold ax78EvidenceCosted
  rw [← indexedNameCosted_value thingNames x, ← indexedNameCosted_value thingNames y,
    ← indexedNameCosted_value worldNames w]
  generalize indexedNameCosted thingNames x = xn
  generalize indexedNameCosted thingNames y = yn
  generalize indexedNameCosted worldNames w = wn
  generalize renderFoundationStatusCosted worldNames.size thingNames tables x w = left
  generalize renderFoundationStatusCosted worldNames.size thingNames tables y w = right
  cases different <;>
    simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.tick_value,
      Complexity.Costed.charge_value, Bool.false_eq_true, ↓reduceIte] <;> rfl

private theorem ax78EvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (different : Bool) (x y w : Nat) (out : Array String) :
    (ax78EvidenceCosted worldNames thingNames tables different x y w out).cost ≤
      66 * thingNames.size + 67 := by
  have step {α β : Type} (first : Complexity.Costed α) (next : α → Complexity.Costed β)
      (a b : Nat) (hfirst : first.cost ≤ a) (hnext : ∀ value, (next value).cost ≤ b) :
      (first.bind next).cost ≤ a + b :=
    Nat.add_le_add hfirst (hnext first.value)
  unfold ax78EvidenceCosted
  simp only [Bind.bind]
  refine le_trans (step _ _ 4 (66 * thingNames.size + 63) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames x)
  intro xn
  refine le_trans (step _ _ 4 (66 * thingNames.size + 59) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames y)
  intro yn
  refine le_trans (step _ _ 4 (66 * thingNames.size + 55) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost worldNames w)
  intro wn
  refine le_trans (step _ _ (33 * thingNames.size + 12) (33 * thingNames.size + 43) ?_ ?_) (by omega)
  · exact renderFoundationStatusCosted_cost_le worldNames.size thingNames tables x w
  intro left
  refine le_trans (step _ _ (33 * thingNames.size + 12) 31 ?_ ?_) (by omega)
  · exact renderFoundationStatusCosted_cost_le worldNames.size thingNames tables y w
  intro right
  cases different <;>
    simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost,
      Complexity.Costed.charge_cost, Bool.false_eq_true, ↓reduceIte] <;> decide

private theorem ax78EvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables)
    (different : Bool) (x y w : Nat) (out : Array String) :
    (ax78EvidenceCosted worldNames thingNames tables different x y w out).value.size = out.size + 5 := by
  rw [ax78EvidenceCosted_value]
  simp only [Array.size_push]

/-- Only relator/part pairs need a foundation comparison. Equal unique
foundations emit no rows. Other results share one formatter, with the reason
selected from the comparison result. The surrounding loops enforce the budget. -/
private def ax78FoundationPairCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y w : Nat) (out : Array String) : Complexity.Costed (Array String) := do
  let relator ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w
  Complexity.Costed.charge 1 <| if relator then do
    let part ← partLookupCosted worldNames.size thingNames.size tables y x w
    Complexity.Costed.charge 1 <| if part then do
      let equality ← foundationEqCosted worldNames.size thingNames.size tables x y w
      Complexity.Costed.charge 1 <| match equality with
      | none => ax78EvidenceCosted worldNames thingNames tables false x y w out
      | some equal => Complexity.Costed.charge 1 <| if equal then Complexity.Costed.pure out
          else ax78EvidenceCosted worldNames thingNames tables true x y w out
    else Complexity.Costed.pure out
  else Complexity.Costed.pure out

private theorem ax78FoundationPairCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y w : Nat) (out : Array String) :
    (ax78FoundationPairCosted worldNames thingNames tables x y w out).value =
      if (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w).value &&
          (partLookupCosted worldNames.size thingNames.size tables y x w).value then
        match (foundationEqCosted worldNames.size thingNames.size tables x y w).value with
        | some true => out
        | some false => (ax78EvidenceCosted worldNames thingNames tables true x y w out).value
        | none => (ax78EvidenceCosted worldNames thingNames tables false x y w out).value
      else out := by
  -- Prove the sequencing law on abstract computations before instantiating
  -- the queries. Kernel checking then need not reduce their implementations.
  have erase (relator part : Complexity.Costed Bool)
      (equality : Complexity.Costed (Option Bool))
      (render : Bool → Complexity.Costed (Array String)) (out : Array String) :
      (do
        let isRelator ← relator
        Complexity.Costed.charge 1 <| if isRelator then do
          let isPart ← part
          Complexity.Costed.charge 1 <| if isPart then do
            let equal ← equality
            Complexity.Costed.charge 1 <| match equal with
            | none => render false
            | some same => Complexity.Costed.charge 1 <| if same then Complexity.Costed.pure out
                else render true
          else Complexity.Costed.pure out
        else Complexity.Costed.pure out).value =
        (if relator.value && part.value then
          match equality.value with
          | some true => out
          | some false => (render true).value
          | none => (render false).value
        else out) := by
    cases hr : relator.value <;> cases hp : part.value <;> cases he : equality.value with
    | none => simp_all only [Bind.bind, Complexity.Costed.bind_value,
        Complexity.Costed.charge_value, Complexity.Costed.pure_value,
        Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and]
    | some equal =>
        cases equal <;> simp_all only [Bind.bind, Complexity.Costed.bind_value,
          Complexity.Costed.charge_value, Complexity.Costed.pure_value,
          Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and]
  exact erase
    (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w)
    (partLookupCosted worldNames.size thingNames.size tables y x w)
    (foundationEqCosted worldNames.size thingNames.size tables x y w)
    (fun different => ax78EvidenceCosted worldNames thingNames tables different x y w out) out

private theorem ax78FoundationPairCosted_sparse_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x y : Fin thingNames.size) (w : Fin worldNames.size) (out : Array String) :
    (ax78FoundationPairCosted worldNames thingNames tables x.val y.val w.val out).value =
      if tables.unaryLookup "relator" x.val w.val && partLookup tables y.val x.val w.val then
        match (foundationEqCosted worldNames.size thingNames.size tables x.val y.val w.val).value with
        | some true => out
        | some false => (ax78EvidenceCosted worldNames thingNames tables true x.val y.val w.val out).value
        | none => (ax78EvidenceCosted worldNames thingNames tables false x.val y.val w.val out).value
      else out := by
  rw [ax78FoundationPairCosted_value,
    Complexity.diagnosticUnaryCosted_value worldNames.size thingNames.size tables agreement,
    partLookupCosted_sparse_value worldNames.size thingNames.size tables agreement]
  rfl

private theorem ax78FoundationPairCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y w : Nat) (out : Array String) :
    (ax78FoundationPairCosted worldNames thingNames tables x y w out).cost ≤
      110 * thingNames.size + 113 := by
  have hr := Complexity.diagnosticUnaryCosted_cost_le worldNames.size thingNames.size tables .relator x w
  have hp := partLookupCosted_cost_le worldNames.size thingNames.size tables y x w
  have he := foundationEqCosted_cost_le worldNames.size thingNames.size tables x y w
  have hf := ax78EvidenceCosted_cost_le worldNames thingNames tables false x y w out
  have ht := ax78EvidenceCosted_cost_le worldNames thingNames tables true x y w out
  unfold ax78FoundationPairCosted
  generalize Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w = relator at *
  generalize partLookupCosted worldNames.size thingNames.size tables y x w = part at *
  generalize foundationEqCosted worldNames.size thingNames.size tables x y w = equality at *
  generalize ax78EvidenceCosted worldNames thingNames tables = render at *
  cases hrelator : relator.value <;> cases hpart : part.value <;> cases heq : equality.value with
  | none =>
      simp_all only [Bind.bind, Complexity.Costed.bind_cost,
        Complexity.Costed.charge_cost, Complexity.Costed.pure_cost,
        Bool.false_eq_true, ↓reduceIte]
      omega
  | some equal =>
      cases equal <;> simp_all only [Bind.bind, Complexity.Costed.bind_cost,
        Complexity.Costed.charge_cost, Complexity.Costed.pure_cost,
        Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem ax78FoundationPairCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y w : Nat) (out : Array String) :
    (ax78FoundationPairCosted worldNames thingNames tables x y w out).value.size ≤ out.size + 5 := by
  rw [ax78FoundationPairCosted_value]
  split
  · split
    · omega
    · simp only [ax78EvidenceCosted_size]
      exact le_rfl
    · simp only [ax78EvidenceCosted_size]
      exact le_rfl
  · omega

/-- The loops share the output accumulator and stop between evidence groups.
A final group can cross the budget by at most four rows; the public producer
then takes the deterministic budget-sized prefix. No assignment list is built. -/
private def ax78FoundationScanCosted
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (out : Array String) : Complexity.Costed (Array String) :=
  foldDiagDomainCosted 0 worldNames.size out (fun rows => rows.size >= budget) fun rows w =>
    foldDiagDomainCosted 0 thingNames.size rows (fun rows => rows.size >= budget) fun rows x =>
      foldDiagDomainCosted 0 thingNames.size rows (fun rows => rows.size >= budget) fun rows y =>
        ax78FoundationPairCosted worldNames thingNames tables x y w rows

private theorem ax78FoundationScanCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (out : Array String) :
    (ax78FoundationScanCosted budget worldNames thingNames tables out).value =
      (List.range worldNames.size).foldl (fun rows w => if rows.size >= budget then rows else
        (List.range thingNames.size).foldl (fun rows x => if rows.size >= budget then rows else
          (List.range thingNames.size).foldl (fun rows y => if rows.size >= budget then rows else
            (ax78FoundationPairCosted worldNames thingNames tables x y w rows).value) rows) rows) out := by
  simp only [ax78FoundationScanCosted, foldDiagDomainCosted_value,
    ← List.range_eq_range', decide_eq_true_eq]

private def ax78FoundationAnalysisCostBound (W T : Nat) : Nat :=
  W * (T * (T * (110 * T + 116) + 3) + 3) + 12

private theorem ax78FoundationScanCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (out : Array String) :
    (ax78FoundationScanCosted budget worldNames thingNames tables out).cost ≤
      worldNames.size * (thingNames.size * (thingNames.size * (110 * thingNames.size + 116) + 3) + 3) := by
  unfold ax78FoundationScanCosted
  apply foldDiagDomainCosted_cost_le
  intro rows w hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro rows x hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro rows y hlo hhi
  exact ax78FoundationPairCosted_cost_le worldNames thingNames tables x y w rows

private theorem ax78FoundationScanCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (out : Array String) :
    (ax78FoundationScanCosted budget worldNames thingNames tables out).value.size ≤
      out.size + worldNames.size * (thingNames.size * (thingNames.size * 5)) := by
  unfold ax78FoundationScanCosted
  apply foldDiagDomainCosted_array_size_le
  intro rows w
  apply foldDiagDomainCosted_array_size_le
  intro rows x
  apply foldDiagDomainCosted_array_size_le
  intro rows y
  exact ax78FoundationPairCosted_size_le worldNames thingNames tables x y w rows

private theorem ax78FoundationScanCosted_budget
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (out : Array String) :
    (ax78FoundationScanCosted budget worldNames thingNames tables out).value.size ≤
      max out.size (budget + 4) := by
  unfold ax78FoundationScanCosted
  refine foldDiagDomainCosted_preserves _ _ _ _ _
    (fun (rows : Array String) => rows.size ≤ max out.size (budget + 4)) (le_max_left _ _) ?_
  intro rows w hrows hstop
  refine foldDiagDomainCosted_preserves _ _ _ _ _
    (fun (rows : Array String) => rows.size ≤ max out.size (budget + 4)) hrows ?_
  intro rows x hrows hstop
  refine foldDiagDomainCosted_preserves _ _ _ _ _
    (fun (rows : Array String) => rows.size ≤ max out.size (budget + 4)) hrows ?_
  intro rows y hrows hstop
  have hpair := ax78FoundationPairCosted_size_le worldNames thingNames tables x y w rows
  have hmax := le_max_right out.size (budget + 4)
  have hbefore : ¬ rows.size ≥ budget := of_decide_eq_false hstop
  omega

/-- Append the suggestion only when room remains. With no evidence, construct
only the allowed prefix of the two fallback rows. The initial empty array,
branch tests, and each push/emission are included in the count. -/
private def ax78FoundationAnalysisCosted
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let scanned ← Complexity.Costed.charge 1 (ax78FoundationScanCosted budget worldNames thingNames tables #[])
  Complexity.Costed.charge 2 <| if scanned.isEmpty then do
    let out ← Complexity.Costed.tick (#[] : Array String) 1
    Complexity.Costed.charge 2 <| if budget = 0 then Complexity.Costed.pure out else do
      let out ← Complexity.Costed.tick (out.push
        "Foundation check for ax78: every relator/part pair with unique DSL foundations has matching foundations.") 2
      Complexity.Costed.charge 2 <| if budget = 1 then Complexity.Costed.pure out else
        Complexity.Costed.tick (out.push
          "If Lean still reports ax78, inspect relator parts whose foundations are not explicitly determined by `FoundedBy` facts.") 2
  else Complexity.Costed.charge 2 <| if scanned.size < budget then
    Complexity.Costed.tick (scanned.push
      "Suggestion: align the `FoundedBy` facts for the relator and every relevant part, or remove/relax the `Relator`/`Part` assertions.") 2
  else Complexity.Costed.pure scanned

private theorem ax78FoundationAnalysisCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax78FoundationAnalysisCosted budget worldNames thingNames tables).value =
      let scanned := (ax78FoundationScanCosted budget worldNames thingNames tables #[]).value
      if scanned.isEmpty then
        if budget = 0 then #[]
        else if budget = 1 then #[
          "Foundation check for ax78: every relator/part pair with unique DSL foundations has matching foundations."]
        else #[
          "Foundation check for ax78: every relator/part pair with unique DSL foundations has matching foundations.",
          "If Lean still reports ax78, inspect relator parts whose foundations are not explicitly determined by `FoundedBy` facts."]
      else if scanned.size < budget then scanned.push
        "Suggestion: align the `FoundedBy` facts for the relator and every relevant part, or remove/relax the `Relator`/`Part` assertions."
      else scanned := by
  unfold ax78FoundationAnalysisCosted
  generalize ax78FoundationScanCosted budget worldNames thingNames tables #[] = scanned
  cases hs : scanned.value.isEmpty <;>
    by_cases hz : budget = 0 <;> by_cases ho : budget = 1 <;>
    by_cases hb : scanned.value.size < budget <;>
    simp_all [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value,
      Complexity.Costed.tick_value, Complexity.Costed.pure_value]
  exact apply_ite (fun (result : Complexity.Costed (Array String)) => result.value) _ _ _

private theorem ax78FoundationAnalysisCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax78FoundationAnalysisCosted budget worldNames thingNames tables).cost ≤
      ax78FoundationAnalysisCostBound worldNames.size thingNames.size := by
  have h := ax78FoundationScanCosted_cost_le budget worldNames thingNames tables #[]
  unfold ax78FoundationAnalysisCosted
  generalize ax78FoundationScanCosted budget worldNames thingNames tables #[] = scanned at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  split <;> split <;>
    simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
      Complexity.Costed.tick_cost, Complexity.Costed.pure_cost]
  all_goals try { unfold ax78FoundationAnalysisCostBound; omega }
  split <;> simp only [Complexity.Costed.tick_cost, Complexity.Costed.pure_cost] <;>
    unfold ax78FoundationAnalysisCostBound <;> omega

private theorem ax78FoundationAnalysisCosted_budget
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax78FoundationAnalysisCosted budget worldNames thingNames tables).value.size ≤ budget + 4 := by
  have h := ax78FoundationScanCosted_budget budget worldNames thingNames tables #[]
  simp only [Array.size_empty, Nat.zero_max] at h
  rw [ax78FoundationAnalysisCosted_value]
  generalize (ax78FoundationScanCosted budget worldNames thingNames tables #[]).value = scanned at *
  dsimp only
  cases hs : scanned.isEmpty <;> by_cases hz : budget = 0 <;>
    by_cases ho : budget = 1 <;> by_cases hb : scanned.size < budget <;>
    simp_all only [Bool.false_eq_true, ↓reduceIte, Array.size_push,
      Array.size_empty]
  all_goals try omega
  all_goals simp only [Array.size, List.length_cons, List.length_nil]; omega

private theorem ax78FoundationAnalysisCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax78FoundationAnalysisCostBound W T ≤ ax78FoundationAnalysisCostBound W' T' := by
  unfold ax78FoundationAnalysisCostBound
  exact Nat.add_le_add_right (Nat.mul_le_mul hW
    (Nat.add_le_add_right (Nat.mul_le_mul hT
      (Nat.add_le_add_right (Nat.mul_le_mul hT
        (Nat.add_le_add_right (Nat.mul_le_mul_left 110 hT) 116)) 3)) 3)) 12

/-- Collect proper parts in increasing coordinate order. The query is
ProperPart(candidate, whole), so it must not be reversed like a foundation
target query. Array initialization costs one. Each candidate costs at most
22 operations: the guarded query, branch, optional push, and numeric loop.
Niu et al.'s cost-aware semantics (POPL 2022, doi:10.1145/3498670) motivates
composing these operations in the executable collector itself. -/
private def properPartCandidatesCosted
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  Complexity.Costed.charge 1 <|
    foldDiagDomainCosted 0 T #[] (fun _ => false) fun out y => do
      let isPart ← Complexity.diagnosticBinaryCosted W T tables .properPart y x w
      if isPart then Complexity.Costed.tick (out.push y) 2
      else Complexity.Costed.tick out 1

private theorem properPartCandidatesCosted_filter_value
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted W T tables x w).value =
      ((List.range T).filter (fun y =>
        (Complexity.diagnosticBinaryCosted W T tables .properPart y x w).value)).toArray := by
  rw [properPartCandidatesCosted, Complexity.Costed.charge_value,
    foldDiagDomainCosted_value, ← List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Complexity.Costed.bind_value]
  have h : (List.range T).foldl (fun out y =>
      (if (Complexity.diagnosticBinaryCosted W T tables .properPart y x w).value then
        Complexity.Costed.tick (out.push y) 2 else Complexity.Costed.tick out 1).value) #[] =
      (List.range T).foldl (fun out y =>
        if (Complexity.diagnosticBinaryCosted W T tables .properPart y x w).value then
          out.push y else out) #[] := by
    congr 1
    funext out y
    split <;> rfl
  rw [h, ← List.foldl_filter, List.foldl_push_eq_append']
  simp

private theorem properPartCandidatesCosted_sparse_value
    (W T : Nat) (tables : FactTables)
    (agreement : tables.sparseLookups W T = tables.denseLookups W T)
    (x : Fin T) (w : Fin W) :
    (properPartCandidatesCosted W T tables x.val w.val).value =
      ((List.range T).filter (fun y => tables.binaryLookup "properPart" y x.val w.val)).toArray := by
  rw [properPartCandidatesCosted_filter_value]
  congr 1
  apply List.filter_congr
  intro y hy
  exact Complexity.diagnosticBinaryCosted_value W T tables agreement .properPart
    ⟨y, List.mem_range.mp hy⟩ x w

private theorem properPartCandidatesCosted_cost_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted W T tables x w).cost ≤ 22 * T + 1 := by
  have h := foldDiagDomainCosted_cost_le 0 T (#[] : Array Nat) (fun _ => false)
    (fun out y => Complexity.diagnosticBinaryCosted W T tables .properPart y x w >>= fun isPart =>
      if isPart then Complexity.Costed.tick (out.push y) 2 else Complexity.Costed.tick out 1)
    19 (by
      intro out y hlo hhi
      have hquery := Complexity.diagnosticBinaryCosted_cost_le W T tables .properPart y x w
      simp only [Bind.bind, Complexity.Costed.bind_cost]
      split <;> simp only [Complexity.Costed.tick_cost] <;> omega)
  simpa [properPartCandidatesCosted, Complexity.Costed.charge_cost,
    Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_right h 1

private theorem properPartCandidatesCosted_size_le
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted W T tables x w).value.size ≤ T := by
  rw [properPartCandidatesCosted_filter_value, List.size_toArray]
  exact le_trans (List.length_filter_le _ _) (by simp)

private theorem properPartCandidatesCosted_nodup
    (W T : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted W T tables x w).value.toList.Nodup := by
  rw [properPartCandidatesCosted_filter_value]
  exact (List.nodup_range (n := T)).filter _

/-- Every collected coordinate is in the finite thing domain and satisfies
the guarded proper-part query. This supplies the bounds needed by consumers
without a second search through the source facts. -/
private theorem properPartCandidatesCosted_mem
    (W T : Nat) (tables : FactTables) (x w y : Nat) :
    y ∈ (properPartCandidatesCosted W T tables x w).value.toList ↔
      y < T ∧ (Complexity.diagnosticBinaryCosted W T tables .properPart y x w).value = true := by
  rw [properPartCandidatesCosted_filter_value]
  change y ∈ (List.range T).filter _ ↔ _
  simp only [List.mem_filter, List.mem_range]

/-- The report categories keep the existing priority: qua-individual status,
unique foundations, then the two directions of existential dependence. -/
private inductive Ax79PairFailure where
  | missingQua | differentFoundation | missingFoundation | missingDependence
  deriving DecidableEq, Repr

/-- Classify one pair without rendering evidence. Fixed predicates are called
directly: QuaIndividual is computed from QuaIndividualOf, and existential
dependence from Ex across worlds. Stored derived assertions cannot override
these tests. Each later query runs only while the preceding requirements hold. -/
private def ax79PairFailureCosted (W T : Nat) (tables : FactTables) (y z w : Nat) :
    Complexity.Costed (Option Ax79PairFailure) := do
  let yQua ← quaIndividualLookupCosted W T tables y w
  Complexity.Costed.charge 1 <| if yQua then do
    let zQua ← quaIndividualLookupCosted W T tables z w
    Complexity.Costed.charge 1 <| if zQua then do
      let equality ← foundationEqCosted W T tables y z w
      Complexity.Costed.charge 1 <| match equality with
      | none => Complexity.Costed.pure (some .missingFoundation)
      | some equal => Complexity.Costed.charge 1 <| if equal then do
          let yz ← existentialDependenceLookupCosted W T tables y z
          Complexity.Costed.charge 1 <| if yz then do
            let zy ← existentialDependenceLookupCosted W T tables z y
            Complexity.Costed.tick (if zy then none else some .missingDependence) 1
          else Complexity.Costed.pure (some .missingDependence)
        else Complexity.Costed.pure (some .differentFoundation)
    else Complexity.Costed.pure (some .missingQua)
  else Complexity.Costed.pure (some .missingQua)

private theorem ax79PairFailureCosted_value
    (W T : Nat) (tables : FactTables) (y z w : Nat) :
    (ax79PairFailureCosted W T tables y z w).value =
      if !(quaIndividualLookupCosted W T tables y w).value then some .missingQua
      else if !(quaIndividualLookupCosted W T tables z w).value then some .missingQua
      else match (foundationEqCosted W T tables y z w).value with
        | some false => some .differentFoundation
        | none => some .missingFoundation
        | some true =>
          if !(existentialDependenceLookupCosted W T tables y z).value then some .missingDependence
          else if !(existentialDependenceLookupCosted W T tables z y).value then some .missingDependence
          else none := by
  unfold ax79PairFailureCosted
  generalize quaIndividualLookupCosted W T tables y w = yQua
  generalize quaIndividualLookupCosted W T tables z w = zQua
  generalize foundationEqCosted W T tables y z w = equality
  generalize existentialDependenceLookupCosted W T tables y z = yz
  generalize existentialDependenceLookupCosted W T tables z y = zy
  cases hy : yQua.value <;> cases hz : zQua.value <;>
    cases hyz : yz.value <;> cases hzy : zy.value <;> cases he : equality.value with
  | none => simp_all only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value,
      Complexity.Costed.pure_value, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
  | some same =>
      cases same <;> simp_all only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value,
        Complexity.Costed.tick_value, Complexity.Costed.pure_value, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]

/-- The fixed calls have the same values as the derived-name dispatcher used
by the diagnostic formulas. This theorem does not equate their costs: direct
calls omit string-name comparisons. -/
private theorem ax79PairFailureCosted_registered_value
    (W T : Nat) (tables : FactTables) (y z w : Nat) :
    (ax79PairFailureCosted W T tables y z w).value =
      if !(derivedUnaryLookupCosted W T tables "QuaIndividual" y w).value then some .missingQua
      else if !(derivedUnaryLookupCosted W T tables "QuaIndividual" z w).value then some .missingQua
      else match (foundationEqCosted W T tables y z w).value with
        | some false => some .differentFoundation
        | none => some .missingFoundation
        | some true =>
          if !(derivedBinaryLookupCosted W T tables "ExistentialDependence" y z w).value then some .missingDependence
          else if !(derivedBinaryLookupCosted W T tables "ExistentialDependence" z y w).value then some .missingDependence
          else none := by
  rw [ax79PairFailureCosted_value]
  rfl

private theorem ax79PairFailureCosted_cost_le
    (W T : Nat) (tables : FactTables) (y z w : Nat) :
    (ax79PairFailureCosted W T tables y z w).cost ≤ 82 * T + 56 * W + 17 := by
  have hy := quaIndividualLookupCosted_cost_le W T tables y w
  have hz := quaIndividualLookupCosted_cost_le W T tables z w
  have he := foundationEqCosted_cost_le W T tables y z w
  have hyz := boxExImpLookupCosted_cost_le W T tables y z
  have hzy := boxExImpLookupCosted_cost_le W T tables z y
  unfold ax79PairFailureCosted existentialDependenceLookupCosted
  generalize quaIndividualLookupCosted W T tables y w = yQua at *
  generalize quaIndividualLookupCosted W T tables z w = zQua at *
  generalize foundationEqCosted W T tables y z w = equality at *
  generalize boxExImpLookupCosted W T tables y z = yz at *
  generalize boxExImpLookupCosted W T tables z y = zy at *
  cases hyv : yQua.value <;> cases hzv : zQua.value <;>
    cases hyzv : yz.value <;> cases hzyv : zy.value <;> cases hev : equality.value with
  | none =>
      simp_all only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
        Complexity.Costed.pure_cost, Bool.false_eq_true, ↓reduceIte]
      omega
  | some same =>
      cases same <;> simp_all only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
        Complexity.Costed.tick_cost, Complexity.Costed.pure_cost, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Render only the selected failure. The four names and assignment text are
shared by all rows. Foundation evidence additionally renders two status strings.
As in Niu et al.'s compositional cost semantics (POPL 2022,
doi:10.1145/3498670), formatting and its cost are one executable computation. -/
private def ax79PairEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax79PairFailure) : Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let yn ← indexedNameCosted thingNames y
  let zn ← indexedNameCosted thingNames z
  let wn ← indexedNameCosted worldNames w
  let assignment ← Complexity.Costed.tick ("Counterexample assignment: x = " ++ xn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", y = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ yn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", z = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ zn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", w = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ wn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ".") 1
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assignment) 2
  Complexity.Costed.charge 1 <| match failure with
  | .missingQua => do
      let line ← Complexity.Costed.tick ("Required together: proper parts of relator `" ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ "` must be qua individuals.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      Complexity.Costed.tick (out.push
        "Suggestion: add a `QuaIndividualOf(part, bearer)` fact for each proper part in this world, or revise the `Relator`/`ProperPart` assertions.") 2
  | .missingDependence => do
      let line ← Complexity.Costed.tick ("Required together: proper parts of relator `" ++ xn) 1
      let line ← Complexity.Costed.tick (line ++ "` must be mutually existentially dependent.") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      Complexity.Costed.tick (out.push
        "Suggestion: align the parts' `Ex` facts so each exists in every world where the other exists, or revise the `Relator`/`ProperPart` assertions.") 2
  | .differentFoundation | .missingFoundation => do
      let out ← Complexity.Costed.charge 2 <| if failure = .differentFoundation then do
          let line ← Complexity.Costed.tick ("Required but missing: proper parts of relator `" ++ xn) 1
          let line ← Complexity.Costed.tick (line ++ "` must share a foundation.") 1
          let out ← Complexity.Costed.tick (out.push line) 2
          Complexity.Costed.tick (out.push
            "Suggestion: align the `FoundedBy` facts for the relator's qua-individual parts.") 2
        else do
          let out ← Complexity.Costed.tick (out.push
            "Missing witness requirements: ax79 compares `FoundationOf` for relator parts, but the DSL facts do not determine unique foundations.") 2
          Complexity.Costed.tick (out.push
            "Suggestion: give each qua-individual part exactly one `FoundedBy` target.") 2
      let yStatus ← renderFoundationStatusCosted worldNames.size thingNames tables y w
      let zStatus ← renderFoundationStatusCosted worldNames.size thingNames tables z w
      let line ← Complexity.Costed.tick ("Evidence for FoundationOf(" ++ yn) 1
      let line ← Complexity.Costed.tick (line ++ ") = FoundationOf(") 1
      let line ← Complexity.Costed.tick (line ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ "):") 1
      let out ← Complexity.Costed.tick (out.push line) 2
      let line ← Complexity.Costed.tick ("  - " ++ yn) 1
      let line ← Complexity.Costed.tick (line ++ ": ") 1
      let line ← Complexity.Costed.tick (line ++ yStatus) 1
      let out ← Complexity.Costed.tick (out.push line) 2
      let line ← Complexity.Costed.tick ("  - " ++ zn) 1
      let line ← Complexity.Costed.tick (line ++ ": ") 1
      let line ← Complexity.Costed.tick (line ++ zStatus) 1
      Complexity.Costed.tick (out.push line) 2

private theorem ax79PairEvidenceCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax79PairFailure) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w failure).value =
      let assignment :=
        s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}."
      match failure with
      | .missingQua => #[
          assignment,
          s!"Required together: proper parts of relator `{indexedName thingNames x}` must be qua individuals.",
          "Suggestion: add a `QuaIndividualOf(part, bearer)` fact for each proper part in this world, or revise the `Relator`/`ProperPart` assertions."]
      | .missingDependence => #[
          assignment,
          s!"Required together: proper parts of relator `{indexedName thingNames x}` must be mutually existentially dependent.",
          "Suggestion: align the parts' `Ex` facts so each exists in every world where the other exists, or revise the `Relator`/`ProperPart` assertions."]
      | .differentFoundation => #[
          assignment,
          s!"Required but missing: proper parts of relator `{indexedName thingNames x}` must share a foundation.",
          "Suggestion: align the `FoundedBy` facts for the relator's qua-individual parts.",
          s!"Evidence for FoundationOf({indexedName thingNames y}) = FoundationOf({indexedName thingNames z}):",
          s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted worldNames.size thingNames tables y w).value}",
          s!"  - {indexedName thingNames z}: {(renderFoundationStatusCosted worldNames.size thingNames tables z w).value}"]
      | .missingFoundation => #[
          assignment,
          "Missing witness requirements: ax79 compares `FoundationOf` for relator parts, but the DSL facts do not determine unique foundations.",
          "Suggestion: give each qua-individual part exactly one `FoundedBy` target.",
          s!"Evidence for FoundationOf({indexedName thingNames y}) = FoundationOf({indexedName thingNames z}):",
          s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted worldNames.size thingNames tables y w).value}",
          s!"  - {indexedName thingNames z}: {(renderFoundationStatusCosted worldNames.size thingNames tables z w).value}"] := by
  unfold ax79PairEvidenceCosted
  rw [← indexedNameCosted_value thingNames x, ← indexedNameCosted_value thingNames y,
    ← indexedNameCosted_value thingNames z, ← indexedNameCosted_value worldNames w]
  generalize indexedNameCosted thingNames x = xn
  generalize indexedNameCosted thingNames y = yn
  generalize indexedNameCosted thingNames z = zn
  generalize indexedNameCosted worldNames w = wn
  generalize renderFoundationStatusCosted worldNames.size thingNames tables y w = yStatus
  generalize renderFoundationStatusCosted worldNames.size thingNames tables z w = zStatus
  cases failure <;> simp only [Bind.bind, Complexity.Costed.bind_value,
    Complexity.Costed.tick_value, Complexity.Costed.charge_value, reduceCtorEq, ↓reduceIte] <;> rfl

private theorem ax79PairEvidenceCosted_missingQua_cost
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w .missingQua).cost =
      34 := by
  have hx := indexedNameCosted_cost thingNames x
  have hy := indexedNameCosted_cost thingNames y
  have hz := indexedNameCosted_cost thingNames z
  have hw := indexedNameCosted_cost worldNames w
  unfold ax79PairEvidenceCosted
  generalize indexedNameCosted thingNames x = xn at *
  generalize indexedNameCosted thingNames y = yn at *
  generalize indexedNameCosted thingNames z = zn at *
  generalize indexedNameCosted worldNames w = wn at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost,
    Complexity.Costed.charge_cost, hx, hy, hz, hw]

private theorem ax79PairEvidenceCosted_missingDependence_cost
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w .missingDependence).cost =
      34 := by
  have hx := indexedNameCosted_cost thingNames x
  have hy := indexedNameCosted_cost thingNames y
  have hz := indexedNameCosted_cost thingNames z
  have hw := indexedNameCosted_cost worldNames w
  unfold ax79PairEvidenceCosted
  generalize indexedNameCosted thingNames x = xn at *
  generalize indexedNameCosted thingNames y = yn at *
  generalize indexedNameCosted thingNames z = zn at *
  generalize indexedNameCosted worldNames w = wn at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost,
    Complexity.Costed.charge_cost, hx, hy, hz, hw]

private theorem ax79PairEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax79PairFailure) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w failure).cost ≤
      66 * thingNames.size + 76 := by
  -- Bound each continuation for every returned string or array. This keeps
  -- the arithmetic proof independent of the growing assignment text.
  have step {α β : Type} (first : Complexity.Costed α) (next : α → Complexity.Costed β)
      (a b : Nat) (hfirst : first.cost ≤ a) (hnext : ∀ value, (next value).cost ≤ b) :
      (first.bind next).cost ≤ a + b :=
    Nat.add_le_add hfirst (hnext first.value)
  unfold ax79PairEvidenceCosted
  simp only [Bind.bind]
  refine le_trans (step _ _ 4 (66 * thingNames.size + 72) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames x)
  intro xn
  refine le_trans (step _ _ 4 (66 * thingNames.size + 68) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames y)
  intro yn
  refine le_trans (step _ _ 4 (66 * thingNames.size + 64) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost thingNames z)
  intro zn
  refine le_trans (step _ _ 4 (66 * thingNames.size + 60) ?_ ?_) (by omega)
  · exact le_of_eq (indexedNameCosted_cost worldNames w)
  intro wn
  refine le_trans (step _ _ 1 (66 * thingNames.size + 59) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment0
  refine le_trans (step _ _ 1 (66 * thingNames.size + 58) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment1
  refine le_trans (step _ _ 1 (66 * thingNames.size + 57) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment2
  refine le_trans (step _ _ 1 (66 * thingNames.size + 56) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment3
  refine le_trans (step _ _ 1 (66 * thingNames.size + 55) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment4
  refine le_trans (step _ _ 1 (66 * thingNames.size + 54) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment5
  refine le_trans (step _ _ 1 (66 * thingNames.size + 53) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment6
  refine le_trans (step _ _ 1 (66 * thingNames.size + 52) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro assignment7
  refine le_trans (step _ _ 1 (66 * thingNames.size + 51) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro empty
  refine le_trans (step _ _ 2 (66 * thingNames.size + 49) ?_ ?_) (by omega)
  · exact Nat.le_refl _
  intro out
  have hy := renderFoundationStatusCosted_cost_le worldNames.size thingNames tables y w
  have hz := renderFoundationStatusCosted_cost_le worldNames.size thingNames tables z w
  generalize renderFoundationStatusCosted worldNames.size thingNames tables y w = left at *
  generalize renderFoundationStatusCosted worldNames.size thingNames tables z w = right at *
  cases failure <;> simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost,
    Complexity.Costed.charge_cost, reduceCtorEq, ↓reduceIte] <;> omega

private theorem ax79PairEvidenceCosted_size
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (failure : Ax79PairFailure) :
    (ax79PairEvidenceCosted worldNames thingNames tables x y z w failure).value.size =
      match failure with
      | .differentFoundation | .missingFoundation => 6
      | _ => 3 := by
  rw [ax79PairEvidenceCosted_value]
  cases failure <;> rfl

private def ax79PairAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    Complexity.Costed (Option (Array String)) := do
  let failure ← ax79PairFailureCosted worldNames.size thingNames.size tables y z w
  Complexity.Costed.charge 1 <| match failure with
  | none => Complexity.Costed.pure none
  | some reason => do
      let rows ← ax79PairEvidenceCosted worldNames thingNames tables x y z w reason
      Complexity.Costed.pure (some rows)

private theorem ax79PairAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (ax79PairAnalysisCosted worldNames thingNames tables x y z w).value =
      (ax79PairFailureCosted worldNames.size thingNames.size tables y z w).value.map
        (fun reason => (ax79PairEvidenceCosted worldNames thingNames tables x y z w reason).value) := by
  have erase (failure : Complexity.Costed (Option Ax79PairFailure))
      (render : Ax79PairFailure → Complexity.Costed (Array String)) :
      (failure.bind fun result => Complexity.Costed.charge 1 <| match result with
        | none => Complexity.Costed.pure none
        | some reason => (render reason).bind fun rows => Complexity.Costed.pure (some rows)).value =
      failure.value.map (fun reason => (render reason).value) := by
    simp only [Complexity.Costed.bind_value, Complexity.Costed.charge_value]
    cases failure.value <;> rfl
  exact erase _ _

private theorem ax79PairAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y z w : Nat) :
    (ax79PairAnalysisCosted worldNames thingNames tables x y z w).cost ≤
      148 * thingNames.size + 56 * worldNames.size + 94 := by
  have hfailure := ax79PairFailureCosted_cost_le worldNames.size thingNames.size tables y z w
  have hrender (reason : Ax79PairFailure) :=
    ax79PairEvidenceCosted_cost_le worldNames thingNames tables x y z w reason
  unfold ax79PairAnalysisCosted
  generalize ax79PairFailureCosted worldNames.size thingNames.size tables y z w = failure at *
  generalize ax79PairEvidenceCosted worldNames thingNames tables x y z w = render at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  cases failure.value with
  | none => simp only [Complexity.Costed.pure_cost]; omega
  | some reason =>
      have h := hrender reason
      simp only [Complexity.Costed.bind_cost, Complexity.Costed.pure_cost]
      omega

private theorem ax79PairAnalysisCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y z w : Nat) (rows : Array String)
    (found : (ax79PairAnalysisCosted worldNames thingNames tables x y z w).value = some rows) :
    rows.size ≤ 6 := by
  rw [ax79PairAnalysisCosted_value] at found
  obtain ⟨reason, hreason, hrows⟩ := Option.map_eq_some_iff.mp found
  rw [← hrows, ax79PairEvidenceCosted_size]
  cases reason <;> decide

private theorem ax79PairAnalysisCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    148 * T + 56 * W + 94 ≤ 148 * T' + 56 * W' + 94 := by omega

/-- Visit pairs in array order, retaining the first report. An error in the
array fold carries that report and stops both loops. Each loop charges its
array reads and iterations through `foldArrayExcept`. The visitor charges
the result tests, and each completed fold charges its final result selection.
No pair array or list is constructed. -/
private def ax79PartPairsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (parts : Array Nat) : Complexity.Costed (Option (Array String)) := do
  let result ← Complexity.Costed.charge 1 <|
    Complexity.Costed.foldArrayExcept parts () fun _ y =>
      Complexity.Costed.charge 2 <|
        Complexity.Costed.foldArrayExcept parts () fun _ z => do
          let pair ← ax79PairAnalysisCosted worldNames thingNames tables x y z w
          Complexity.Costed.tick (match pair with
            | none => Except.ok ()
            | some rows => Except.error rows) 2
  Complexity.Costed.tick (match result with
    | .ok _ => none
    | .error rows => some rows) 1

private def ax79PartPairsCostBound (W T P : Nat) : Nat :=
  P * (P * (148 * T + 56 * W + 98) + 4) + 2

private theorem ax79PartPairsCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (parts : Array Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w parts).value =
      parts.toList.findSome? (fun y => parts.toList.findSome? (fun z =>
        (ax79PairAnalysisCosted worldNames thingNames tables x y z w).value)) := by
  have scan (xs : List Nat) (f : Nat → Except (Array String) Unit) :
      xs.foldlM (fun (_ : Unit) i => f i) () =
        match xs.findSome? (fun i => match f i with
          | .ok _ => none | .error rows => some rows) with
        | none => Except.ok () | some rows => Except.error rows := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
        cases h : f i with
        | error rows => simp [List.foldlM_cons, h, Bind.bind, Except.bind]
        | ok state =>
            cases state
            simpa [List.foldlM_cons, List.findSome?_cons, h, Bind.bind, Except.bind] using ih
  have cancel (rows : Option (Array String)) :
      (match (match rows with
        | none => Except.ok () | some rows => Except.error rows) with
        | .ok _ => none | .error rows => some rows) = rows := by
    cases rows <;> rfl
  unfold ax79PartPairsCosted
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value,
    Complexity.Costed.tick_value, Complexity.Costed.foldArrayExcept_value,
    ← Array.foldlM_toList, scan, cancel]

/-- The nested specification agrees with left-to-right search of the
Cartesian product. The product occurs only in this theorem's specification. -/
private theorem ax79PartPairsCosted_product_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (parts : Array Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w parts).value =
      (parts.toList.flatMap fun y => parts.toList.map (y, ·)).findSome?
        (fun pair => (ax79PairAnalysisCosted worldNames thingNames tables x pair.1 pair.2 w).value) := by
  have product (xs ys : List Nat) (f : Nat × Nat → Option (Array String)) :
      (xs.flatMap fun y => ys.map (y, ·)).findSome? f =
        xs.findSome? (fun y => ys.findSome? (fun z => f (y, z))) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [List.findSome?_append, List.findSome?_map, List.findSome?_cons,
          Function.comp_def, ih]
        cases ys.findSome? (fun z => f (x, z)) <;> rfl
  rw [ax79PartPairsCosted_value, product]

private theorem ax79PartPairsCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x w : Nat) (parts : Array Nat) (rows : Array String)
    (found : (ax79PartPairsCosted worldNames thingNames tables x w parts).value = some rows) :
    rows.size ≤ 6 := by
  rw [ax79PartPairsCosted_value] at found
  obtain ⟨y, hy, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨z, hz, found⟩ := List.exists_of_findSome?_eq_some found
  exact ax79PairAnalysisCosted_some_size worldNames thingNames tables x y z w rows found

private theorem ax79PartPairsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (parts : Array Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w parts).cost ≤
      ax79PartPairsCostBound worldNames.size thingNames.size parts.size := by
  let visit := fun y z => do
    let pair ← ax79PairAnalysisCosted worldNames thingNames tables x y z w
    Complexity.Costed.tick (match pair with
      | none => Except.ok () | some rows => Except.error rows) 2
  have hvisit (y z : Nat) :
      (visit y z).cost ≤ 148 * thingNames.size + 56 * worldNames.size + 96 := by
    have h := ax79PairAnalysisCosted_cost_le worldNames thingNames tables x y z w
    simp only [visit, Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
    omega
  have hinner (y : Nat) := Complexity.Costed.foldArrayExcept_cost_le parts ()
    (fun _ z => visit y z) (148 * thingNames.size + 56 * worldNames.size + 96)
    (by intro state z hz; exact hvisit y z)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hinner
  have houter := Complexity.Costed.foldArrayExcept_cost_le parts ()
    (fun _ y => Complexity.Costed.charge 2 <|
      Complexity.Costed.foldArrayExcept parts () (fun _ z => visit y z))
    (parts.size * (148 * thingNames.size + 56 * worldNames.size + 98) + 2)
    (by
      intro state y hy
      simp only [Complexity.Costed.charge_cost, Nat.add_assoc]
      have h := hinner y
      omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at houter
  unfold ax79PartPairsCosted ax79PartPairsCostBound
  change 1 + (Complexity.Costed.foldArrayExcept parts () (fun _ y =>
    Complexity.Costed.charge 2 <|
      Complexity.Costed.foldArrayExcept parts () (fun _ z => visit y z))).cost + 1 ≤ _
  simp only [Nat.add_assoc]
  omega

private theorem ax79PartPairsCostBound_mono
    {W W' T T' P P' : Nat} (hW : W ≤ W') (hT : T ≤ T') (hP : P ≤ P') :
    ax79PartPairsCostBound W T P ≤ ax79PartPairsCostBound W' T' P' := by
  unfold ax79PartPairsCostBound
  have hpair : 148 * T + 56 * W + 98 ≤ 148 * T' + 56 * W' + 98 := by omega
  exact Nat.add_le_add_right
    (Nat.mul_le_mul hP (Nat.add_le_add_right (Nat.mul_le_mul hP hpair) 4)) 2

private theorem ax79ProperPartPairsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w
      (properPartCandidatesCosted worldNames.size thingNames.size tables x w).value).cost ≤
      ax79PartPairsCostBound worldNames.size thingNames.size thingNames.size := by
  exact Nat.le_trans (ax79PartPairsCosted_cost_le worldNames thingNames tables x w _)
    (ax79PartPairsCostBound_mono (Nat.le_refl _) (Nat.le_refl _)
      (properPartCandidatesCosted_size_le worldNames.size thingNames.size tables x w))

/-- A missing-part report reuses the two rendered names. Every concatenation,
array initialization, and emitted row contributes to its exact cost. -/
private def ax79MissingPartsEvidenceCosted
    (worldNames thingNames : Array Name) (x w : Nat) : Complexity.Costed (Array String) := do
  let xn ← indexedNameCosted thingNames x
  let wn ← indexedNameCosted worldNames w
  let assignment ← Complexity.Costed.tick ("Counterexample assignment: x = " ++ xn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ", w = ") 1
  let assignment ← Complexity.Costed.tick (assignment ++ wn) 1
  let assignment ← Complexity.Costed.tick (assignment ++ ".") 1
  let detail ← Complexity.Costed.tick ("Missing witness requirements: Relator `" ++ xn) 1
  let detail ← Complexity.Costed.tick (detail ++ "` must have at least one proper part in the finite DSL model.") 1
  let out ← Complexity.Costed.tick (#[] : Array String) 1
  let out ← Complexity.Costed.tick (out.push assignment) 2
  let out ← Complexity.Costed.tick (out.push detail) 2
  Complexity.Costed.tick (out.push
    "Suggestion: add `ProperPart(part, relator)` facts and the corresponding qua-individual/dependence/foundation facts, or remove/relax the `Relator` assertion.") 2

private theorem ax79MissingPartsEvidenceCosted_value
    (worldNames thingNames : Array Name) (x w : Nat) :
    (ax79MissingPartsEvidenceCosted worldNames thingNames x w).value = #[
      s!"Counterexample assignment: x = {indexedName thingNames x}, w = {indexedName worldNames w}.",
      s!"Missing witness requirements: Relator `{indexedName thingNames x}` must have at least one proper part in the finite DSL model.",
      "Suggestion: add `ProperPart(part, relator)` facts and the corresponding qua-individual/dependence/foundation facts, or remove/relax the `Relator` assertion."] := by
  unfold ax79MissingPartsEvidenceCosted
  rw [← indexedNameCosted_value thingNames x, ← indexedNameCosted_value worldNames w]
  generalize indexedNameCosted thingNames x = xn
  generalize indexedNameCosted worldNames w = wn
  rfl

private theorem ax79MissingPartsEvidenceCosted_cost
    (worldNames thingNames : Array Name) (x w : Nat) :
    (ax79MissingPartsEvidenceCosted worldNames thingNames x w).cost = 21 := by
  have hx := indexedNameCosted_cost thingNames x
  have hw := indexedNameCosted_cost worldNames w
  unfold ax79MissingPartsEvidenceCosted
  generalize indexedNameCosted thingNames x = xn at *
  generalize indexedNameCosted worldNames w = wn at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.tick_cost, hx, hw]

private def ax79RelatorAssignmentCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Option (Array String)) := do
  let relator ← Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w
  Complexity.Costed.charge 1 <| if relator then do
    let parts ← properPartCandidatesCosted worldNames.size thingNames.size tables x w
    Complexity.Costed.charge 2 <| if parts.isEmpty then do
      let rows ← ax79MissingPartsEvidenceCosted worldNames thingNames x w
      Complexity.Costed.pure (some rows)
    else ax79PartPairsCosted worldNames thingNames tables x w parts
  else Complexity.Costed.pure none

private def ax79RelatorCostBound (W T : Nat) : Nat :=
  22 * T + 37 + ax79PartPairsCostBound W T T

private theorem ax79RelatorAssignmentCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (ax79RelatorAssignmentCosted worldNames thingNames tables x w).value =
      if (Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w).value then
        let parts := (properPartCandidatesCosted worldNames.size thingNames.size tables x w).value
        if parts.isEmpty then some (ax79MissingPartsEvidenceCosted worldNames thingNames x w).value
        else (ax79PartPairsCosted worldNames thingNames tables x w parts).value
      else none := by
  unfold ax79RelatorAssignmentCosted
  generalize Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w = relator
  generalize properPartCandidatesCosted worldNames.size thingNames.size tables x w = parts
  generalize ax79MissingPartsEvidenceCosted worldNames thingNames x w = missing
  cases hr : relator.value <;> cases hp : parts.value.isEmpty <;>
    simp_all only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value,
      Complexity.Costed.pure_value, Bool.false_eq_true, ↓reduceIte]

private theorem ax79RelatorAssignmentCosted_sparse_value
    (worldNames thingNames : Array Name) (tables : FactTables)
    (agreement : tables.sparseLookups worldNames.size thingNames.size =
      tables.denseLookups worldNames.size thingNames.size)
    (x : Fin thingNames.size) (w : Fin worldNames.size) :
    (ax79RelatorAssignmentCosted worldNames thingNames tables x.val w.val).value =
      if tables.unaryLookup "relator" x.val w.val then
        let parts := ((List.range thingNames.size).filter
          (fun y => tables.binaryLookup "properPart" y x.val w.val)).toArray
        if parts.isEmpty then some (ax79MissingPartsEvidenceCosted worldNames thingNames x.val w.val).value
        else (ax79PartPairsCosted worldNames thingNames tables x.val w.val parts).value
      else none := by
  rw [ax79RelatorAssignmentCosted_value,
    Complexity.diagnosticUnaryCosted_value worldNames.size thingNames.size tables agreement,
    properPartCandidatesCosted_sparse_value worldNames.size thingNames.size tables agreement]
  rfl

private theorem ax79RelatorAssignmentCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (ax79RelatorAssignmentCosted worldNames thingNames tables x w).cost ≤
      ax79RelatorCostBound worldNames.size thingNames.size := by
  have hrel := Complexity.diagnosticUnaryCosted_cost_le worldNames.size thingNames.size tables .relator x w
  have hparts := properPartCandidatesCosted_cost_le worldNames.size thingNames.size tables x w
  have hpairs := ax79ProperPartPairsCosted_cost_le worldNames thingNames tables x w
  have hmissing := ax79MissingPartsEvidenceCosted_cost worldNames thingNames x w
  unfold ax79RelatorAssignmentCosted ax79RelatorCostBound
  generalize Complexity.diagnosticUnaryCosted worldNames.size thingNames.size tables .relator x w = relator at *
  generalize properPartCandidatesCosted worldNames.size thingNames.size tables x w = parts at *
  generalize ax79MissingPartsEvidenceCosted worldNames thingNames x w = missing at *
  cases hr : relator.value <;> cases hp : parts.value.isEmpty <;>
    simp_all only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
      Complexity.Costed.pure_cost, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem ax79RelatorAssignmentCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) (rows : Array String)
    (found : (ax79RelatorAssignmentCosted worldNames thingNames tables x w).value = some rows) :
    rows.size ≤ 6 := by
  rw [ax79RelatorAssignmentCosted_value] at found
  dsimp only at found
  split at found
  · split at found
    · simp only [Option.some.injEq] at found
      rw [← found, ax79MissingPartsEvidenceCosted_value]
      change 3 ≤ 6
      decide
    · exact ax79PartPairsCosted_some_size worldNames thingNames tables x w _ rows found
  · contradiction

/-- Search worlds first, then things, in ascending coordinate order. A selected
report stops both numeric loops before another assignment is evaluated. -/
private def ax79RelatorsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Option (Array String)) :=
  foldDiagDomainCosted 0 worldNames.size none Option.isSome fun _ w =>
    foldDiagDomainCosted 0 thingNames.size none Option.isSome fun _ x =>
      ax79RelatorAssignmentCosted worldNames thingNames tables x w

private theorem ax79RelatorsCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79RelatorsCosted worldNames thingNames tables).value =
      (List.range worldNames.size).findSome? (fun w =>
        (List.range thingNames.size).findSome? (fun x =>
          (ax79RelatorAssignmentCosted worldNames thingNames tables x w).value)) := by
  unfold ax79RelatorsCosted
  apply foldDiagDomainCosted_firstSome_value
  intro w hw
  apply foldDiagDomainCosted_firstSome_value
  intro x hx
  rfl

private theorem ax79RelatorsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79RelatorsCosted worldNames thingNames tables).cost ≤
      worldNames.size * (thingNames.size * (ax79RelatorCostBound worldNames.size thingNames.size + 3) + 3) := by
  unfold ax79RelatorsCosted
  apply foldDiagDomainCosted_cost_le
  intro state w hlo hhi
  apply foldDiagDomainCosted_cost_le
  intro state x hlo hhi
  exact ax79RelatorAssignmentCosted_cost_le worldNames thingNames tables x w

private theorem ax79RelatorsCosted_some_size
    (worldNames thingNames : Array Name) (tables : FactTables) (rows : Array String)
    (found : (ax79RelatorsCosted worldNames thingNames tables).value = some rows) :
    rows.size ≤ 6 := by
  rw [ax79RelatorsCosted_value] at found
  obtain ⟨w, hw, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨x, hx, found⟩ := List.exists_of_findSome?_eq_some found
  exact ax79RelatorAssignmentCosted_some_size worldNames thingNames tables x w rows found

private def ax79FoundationAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) := do
  let found ← ax79RelatorsCosted worldNames thingNames tables
  Complexity.Costed.charge 1 <| match found with
  | some rows => Complexity.Costed.pure rows
  | none => do
      let out ← Complexity.Costed.tick (#[] : Array String) 1
      let out ← Complexity.Costed.tick (out.push
        "Foundation check for ax79: no obvious DSL-level relator/foundation mismatch was found.") 2
      Complexity.Costed.tick (out.push
        "If Lean still reports ax79, the remaining issue may involve the full closure direction of the relator definition.") 2

private def ax79FoundationAnalysisCostBound (W T : Nat) : Nat :=
  W * (T * (ax79RelatorCostBound W T + 3) + 3) + 6

private theorem ax79FoundationAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79FoundationAnalysisCosted worldNames thingNames tables).value =
      match (ax79RelatorsCosted worldNames thingNames tables).value with
      | some rows => rows
      | none => #[
          "Foundation check for ax79: no obvious DSL-level relator/foundation mismatch was found.",
          "If Lean still reports ax79, the remaining issue may involve the full closure direction of the relator definition."] := by
  unfold ax79FoundationAnalysisCosted
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.charge_value]
  cases (ax79RelatorsCosted worldNames thingNames tables).value <;> rfl

private theorem ax79FoundationAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79FoundationAnalysisCosted worldNames thingNames tables).cost ≤
      ax79FoundationAnalysisCostBound worldNames.size thingNames.size := by
  have h := ax79RelatorsCosted_cost_le worldNames thingNames tables
  unfold ax79FoundationAnalysisCosted ax79FoundationAnalysisCostBound
  generalize ax79RelatorsCosted worldNames thingNames tables = found at *
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.charge_cost]
  cases found.value <;>
    simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost, Complexity.Costed.pure_cost] <;> omega

private theorem ax79FoundationAnalysisCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79FoundationAnalysisCosted worldNames thingNames tables).value.size ≤ 6 := by
  rw [ax79FoundationAnalysisCosted_value]
  cases found : (ax79RelatorsCosted worldNames thingNames tables).value with
  | none => decide
  | some rows => exact ax79RelatorsCosted_some_size worldNames thingNames tables rows found

private theorem ax79FoundationAnalysisCostBound_mono
    {W W' T T' : Nat} (hW : W ≤ W') (hT : T ≤ T') :
    ax79FoundationAnalysisCostBound W T ≤ ax79FoundationAnalysisCostBound W' T' := by
  have hpairs := ax79PartPairsCostBound_mono hW hT hT
  have hrel : ax79RelatorCostBound W T ≤ ax79RelatorCostBound W' T' := by
    unfold ax79RelatorCostBound
    omega
  unfold ax79FoundationAnalysisCostBound
  exact Nat.add_le_add_right (Nat.mul_le_mul hW
    (Nat.add_le_add_right (Nat.mul_le_mul hT (Nat.add_le_add_right hrel 3)) 3)) 6

/--
Structured diagnostic mirrors for selected certificate fields.

These formulas are not the authoritative axiom statements; they are finite-table
explainers used after Lean has already reported that a generated certificate
field failed. Keep them close to source-level vocabulary so the widget can point
modelers to facts they can add, remove, or re-scope. This closed registry is
static program data. Per-call lookup reuses it after module initialization.
-/
private def diagnosticFormulaRegistry : Array (String × DiagFormula) := #[
  ("ax1",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dType "x" "w")
          (.dia "w" "w'" <| .existsThing "y" <| dInst "y" "x" "w'")),
  ("ax2",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dIndividual "x" "w")
          (.box "w" "w'" <| .not <| .existsThing "y" <| dInst "y" "x" "w'")),
  ("ax3",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dInst "x" "y" "w")
          (.or (dType "x" "w") (dIndividual "x" "w"))),
  ("ax4",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| .existsThing "y" <| .existsThing "z" <|
          dAndList [
            dType "x" "w",
            dInst "x" "y" "w",
            dInst "y" "z" "w"
          ]),
  ("ax5",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dSub "x" "y" "w")
          (dAndList [
            dType "x" "w",
            dType "y" "w",
            .box "w" "w'" <| .forallThing "z" <|
              .imp (dInst "z" "x" "w'") (dInst "z" "y" "w'")
          ])),
  ("ax6",
    .forallThing "t1" <| .forallThing "t2" <| .forallThing "x" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dInst "x" "t1" "w",
              dInst "x" "t2" "w",
              .not (dSub "t1" "t2" "w"),
              .not (dSub "t2" "t1" "w")
            ])
            (.or
              (.existsThing "t3" <| dAndList [
                dSub "t1" "t3" "w",
                dSub "t2" "t3" "w",
                dInst "x" "t3" "w"
              ])
              (.existsThing "t3" <| dAndList [
                dSub "t3" "t1" "w",
                dSub "t3" "t2" "w",
                dInst "x" "t3" "w"
              ]))),
  ("ax7",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .concreteIndividual "x" "w") (dIndividual "x" "w")),
  ("ax8",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .abstractIndividual "x" "w") (dIndividual "x" "w")),
  ("ax9",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .concreteIndividual "x" "w")
          (.not (dUnary .abstractIndividual "x" "w"))),
  ("ax10",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dIndividual "x" "w")
          (.or
            (dUnary .concreteIndividual "x" "w")
            (dUnary .abstractIndividual "x" "w"))),
  ("ax11",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .endurant "x" "w") (dUnary .concreteIndividual "x" "w")),
  ("ax12",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .perdurant "x" "w") (dUnary .concreteIndividual "x" "w")),
  ("ax13",
    .forallThing "x" <| .forallWorld "w" <|
          .imp
            (dUnary .endurant "x" "w")
            (.not (dUnary .perdurant "x" "w"))),
  ("ax14",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dUnary .concreteIndividual "x" "w")
          (.or
            (dUnary .endurant "x" "w")
            (dUnary .perdurant "x" "w"))),
  ("ax15",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .endurantType "x" "w") (dType "x" "w")),
  ("ax16",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .perdurantType "x" "w") (dType "x" "w")),
  ("ax17",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurantType "x" "w")
          (.not (dUnary .perdurantType "x" "w"))),
  ("ax18",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .rigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .forallThing "x" <|
              .imp
                (.dia "w" "w'" <| dInst "x" "t" "w'")
                (.box "w" "w'" <| dInst "x" "t" "w'")
          ])),
  ("ax19",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .antiRigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .forallThing "x" <|
              .imp
                (.dia "w" "w'" <| dInst "x" "t" "w'")
                (.dia "w" "w'" <| .not (dInst "x" "t" "w'"))
          ])),
  ("ax20",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .semiRigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .not (dUnary .rigid "t" "w"),
            .not (dUnary .antiRigid "t" "w")
          ])),
  ("ax21",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurant "x" "w")
          (.existsThing "k" <| dAndList [
            dUnary .kind "k" "w",
            .box "w" "w'" <| dInst "x" "k" "w'"
          ])),
  ("ax22",
    .forallThing "k" <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .kind "k" "w",
            dInst "x" "k" "w"
          ])
          (.not <| .dia "w" "w'" <| .existsThing "z" <| dAndList [
            dUnary .kind "z" "w'",
            dInst "x" "z" "w'",
            dNeThing "z" "k"
          ])),
  ("ax23",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .sortal "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .existsThing "k" <| dAndList [
              dUnary .kind "k" "w",
              .box "w" "w'" <| .forallThing "x" <|
                .imp (dInst "x" "t" "w'") (dInst "x" "k" "w'")
            ]
          ])),
  ("ax24",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .nonSortal "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .not (dUnary .sortal "t" "w")
          ])),
  ("ax25",
    .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .kind "t" "w",
          dUnary .subKind "t" "w"
        ]),
  ("ax26",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .kind "t" "w",
            dUnary .subKind "t" "w"
          ])
          (dAndList [
            dUnary .rigid "t" "w",
            dUnary .sortal "t" "w"
          ])),
  ("ax_kindStable",
    .forallThing "k" <| .forallWorld "w" <| .forallWorld "v" <|
        .imp
          (dUnary .kind "k" "w")
          (dUnary .kind "k" "v")),
  ("ax_instEndurant",
    .forallThing "t" <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .endurantType "t" "w",
            dInst "x" "t" "w"
          ])
          (dUnary .endurant "x" "w")),
  ("ax_sub_kind_sortal",
    .forallThing "a" <| .forallThing "k" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dSub "a" "k" "w",
            dUnary .kind "k" "w"
          ])
          (dUnary .sortal "a" "w")),
  ("ax_nonSortal_up",
    .forallThing "a" <| .forallThing "b" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .nonSortal "a" "w",
            dSub "a" "b" "w"
          ])
          (dUnary .nonSortal "b" "w")),
  ("ax27",
    .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .phase "t" "w",
          dUnary .role "t" "w"
        ]),
  ("ax28",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .phase "t" "w",
            dUnary .role "t" "w"
          ])
          (dAndList [
            dUnary .antiRigid "t" "w",
            dUnary .sortal "t" "w"
          ])),
  ("ax29",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .semiRigidSortal "t" "w")
          (dAndList [
            dUnary .semiRigid "t" "w",
            dUnary .sortal "t" "w"
          ])),
  ("ax30",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .category "t" "w")
          (dAndList [
            dUnary .rigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])),
  ("ax31",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .mixin "t" "w")
          (dAndList [
            dUnary .semiRigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])),
  ("ax32",
    .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .phaseMixin "t" "w",
          dUnary .roleMixin "t" "w"
        ]),
  ("ax33",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .phaseMixin "t" "w",
            dUnary .roleMixin "t" "w"
          ])
          (dAndList [
            dUnary .antiRigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])),
  ("ax34",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .substantial "x" "w",
            dUnary .moment "x" "w"
          ])
          (dUnary .endurant "x" "w")),
  ("ax35",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .substantial "x" "w",
          dUnary .moment "x" "w"
        ]),
  ("ax36",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .object "x" "w",
            dUnary .collective "x" "w",
            dUnary .quantity "x" "w"
          ])
          (dUnary .substantial "x" "w")),
  ("ax37",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .object "x" "w",
          dUnary .collective "x" "w"
        ]),
  ("ax38",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .object "x" "w",
          dUnary .quantity "x" "w"
        ]),
  ("ax39",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .collective "x" "w",
          dUnary .quantity "x" "w"
        ]),
  ("ax40",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .relator "x" "w",
            dUnary .intrinsicMoment "x" "w"
          ])
          (dUnary .moment "x" "w")),
  ("ax41",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .relator "x" "w",
          dUnary .intrinsicMoment "x" "w"
        ]),
  ("ax42",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .mode "x" "w",
            dQuality "x" "w"
          ])
          (dUnary .intrinsicMoment "x" "w")),
  ("ax43",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .mode "x" "w",
          dQuality "x" "w"
        ]),
  ("ax44",
    .forallThing "t" <| .forallWorld "w" <| dAndList [
        .iff
          (dUnary .endurantType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .endurant "x" "w'")
          ]),
        .iff
          (dUnary .perdurantType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .perdurant "x" "w'")
          ]),
        .iff
          (dUnary .substantialType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .substantial "x" "w'")
          ]),
        .iff
          (dUnary .momentType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .moment "x" "w'")
          ]),
        .iff
          (dUnary .objectType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .object "x" "w'")
          ]),
        .iff
          (dUnary .collectiveType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .collective "x" "w'")
          ]),
        .iff
          (dUnary .quantityType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .quantity "x" "w'")
          ]),
        .iff
          (dUnary .relatorType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .relator "x" "w'")
          ]),
        .iff
          (dUnary .modeType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dUnary .mode "x" "w'")
          ]),
        .iff
          (dUnary .qualityType "t" "w")
          (dAndList [
            dType "t" "w",
            .box "w" "w'" <| .forallThing "x" <|
              .imp (dInst "x" "t" "w'") (dQuality "x" "w'")
          ])
      ]),
  ("ax45",
    .forallThing "t" <| .forallWorld "w" <| dAndList [
        .iff
          (dUnary .objectKind "t" "w")
          (dAndList [dUnary .objectType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .collectiveKind "t" "w")
          (dAndList [dUnary .collectiveType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .quantityKind "t" "w")
          (dAndList [dUnary .quantityType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .relatorKind "t" "w")
          (dAndList [dUnary .relatorType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .modeKind "t" "w")
          (dAndList [dUnary .modeType "t" "w", dUnary .kind "t" "w"]),
        .iff
          (dUnary .qualityKind "t" "w")
          (dAndList [dUnary .qualityType "t" "w", dUnary .kind "t" "w"])
      ]),
  ("ax46",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurant "x" "w")
          (.dia "w" "w'" <| .existsThing "k" <| dAndList [
            dSpecificEndurantKind "k" "w'",
            dInst "x" "k" "w'"
          ])),
  ("ax47",
    .forallThing "x" <| .forallWorld "w" <|
        dPart "x" "x" "w"),
  ("ax48",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dPart "x" "y" "w",
            dPart "y" "x" "w"
          ])
          (.eqThing "x" "y")),
  ("ax49",
    .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dPart "x" "y" "w",
              dPart "y" "z" "w"
            ])
            (dPart "x" "z" "w")),
  ("ax50",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dOverlap "x" "y" "w")
          (.existsThing "z" <| dAndList [
            dPart "z" "x" "w",
            dPart "z" "y" "w"
          ])),
  ("ax51",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (.not (dPart "y" "x" "w"))
          (.existsThing "z" <| dAndList [
            dPart "z" "y" "w",
            .not (dOverlap "z" "x" "w")
          ])),
  ("ax52",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dProperPart "x" "y" "w")
          (dAndList [
            dPart "x" "y" "w",
            .not (dPart "y" "x" "w")
          ])),
  ("ax53",
    .forallThing "x'" <| .forallThing "y'" <| .forallWorld "w" <|
        .iff
          (dGenericFunctionalDependence "x'" "y'" "w")
          (.forallThing "x" <|
            .imp
              (dAndList [
                dInst "x" "x'" "w",
                dBinary .functionsAs "x" "x'" "w"
              ])
              (.existsThing "y" <| dAndList [
                dNeThing "y" "x",
                dInst "y" "y'" "w",
                dBinary .functionsAs "y" "y'" "w"
              ]))),
  ("ax54",
    .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dIndividualFunctionalDependence "x" "x'" "y" "y'" "w")
            (dAndList [
              dGenericFunctionalDependence "x'" "y'" "w",
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              .imp
                (dBinary .functionsAs "x" "x'" "w")
                (dBinary .functionsAs "y" "y'" "w")
            ])),
  ("ax55",
    .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dComponentOf "x" "x'" "y" "y'" "w")
            (dAndList [
              dProperPart "x" "y" "w",
              dIndividualFunctionalDependence "x" "x'" "y" "y'" "w"
            ])),
  ("ax56",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .constitutedBy "x" "y" "w")
          (dAndList [
            .iff (dUnary .endurant "x" "w") (dUnary .endurant "y" "w"),
            .iff (dUnary .perdurant "x" "w") (dUnary .perdurant "y" "w")
          ])),
  ("ax57",
    .forallThing "x" <| .forallThing "y" <| .forallThing "x'" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .constitutedBy "x" "y" "w",
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              dUnary .kind "x'" "w",
              dUnary .kind "y'" "w"
            ])
            (dNeThing "x'" "y'")),
  ("ax58",
    .forallThing "x'" <| .forallThing "y'" <| .forallWorld "w" <|
        .iff
          (dGenericConstitutionalDependence "x'" "y'" "w")
          (.forallThing "x" <|
            .imp
              (dInst "x" "x'" "w")
              (.existsThing "y" <| dAndList [
                dInst "y" "y'" "w",
                dBinary .constitutedBy "x" "y" "w"
              ]))),
  ("ax59",
    .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dConstitution "x" "x'" "y" "y'" "w")
            (dAndList [
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              dGenericConstitutionalDependence "x'" "y'" "w",
              dBinary .constitutedBy "x" "y" "w"
            ])),
  ("ax60",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .perdurant "x" "w",
            dBinary .constitutedBy "x" "y" "w"
          ])
          (.box "w" "w'" <|
            .imp
              (dUnary .ex "x" "w'")
              (dBinary .constitutedBy "x" "y" "w'"))),
  ("ax61",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .constitutedBy "x" "y" "w")
          (.not (dBinary .constitutedBy "y" "x" "w"))),
  ("ax62",
    .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .ex "x" "w") (.eqThing "x" "x")),
  ("ax63",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExistentialDependence "x" "y" "w")
          (.box "w" "w'" <|
            .imp
              (dUnary .ex "x" "w'")
              (dUnary .ex "y" "w'"))),
  ("ax64",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExistentialIndependence "x" "y" "w")
          (dAndList [
            .not (dExistentialDependence "x" "y" "w"),
            .not (dExistentialDependence "y" "x" "w")
          ])),
  ("ax65",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .inheresIn "x" "y" "w")
          (dExistentialDependence "x" "y" "w")),
  ("ax66",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .inheresIn "x" "y" "w")
          (dAndList [
            dUnary .moment "x" "w",
            .or (dType "y" "w") (dUnary .concreteIndividual "y" "w")
          ])),
  ("ax67",
    .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .inheresIn "x" "y" "w",
              dBinary .inheresIn "x" "z" "w"
            ])
            (.eqThing "y" "z")),
  ("ax69",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExternallyDependent "x" "y" "w")
          (dAndList [
            dExistentialDependence "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dBinary .inheresIn "x" "z" "w")
                (dExistentialIndependence "y" "z" "w")
          ])),
  ("ax70",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dExternallyDependentMode "x" "w")
          (dAndList [
            dUnary .mode "x" "w",
            .existsThing "y" <| dExternallyDependent "x" "y" "w"
          ])),
  ("ax71",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dFoundedBy "x" "y" "w")
          (dAndList [
            .or (dExternallyDependentMode "x" "w") (dUnary .relator "x" "w"),
            dUnary .perdurant "y" "w"
          ])),
  ("ax72",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dExternallyDependentMode "x" "w")
          (.existsThing "y" <| dAndList [
            dFoundedBy "x" "y" "w",
            .forallThing "z" <|
              .imp (dFoundedBy "x" "z" "w") (.eqThing "z" "y")
          ])),
  ("ax74",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dQuaIndividual "x" "w")
          (.existsThing "y" <| dQuaIndividualOf "x" "y" "w")),
  ("ax75",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQuaIndividual "x" "w")
          (dExternallyDependentMode "x" "w")),
  ("ax76",
    .forallThing "x" <| .forallThing "y" <| .forallThing "y'" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dQuaIndividualOf "x" "y" "w",
              dQuaIndividualOf "x" "y'" "w"
            ])
            (.eqThing "y" "y'")),
  ("ax77",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .relator "x" "w")
          (.existsThing "y" <| dAndList [
            dFoundedBy "x" "y" "w",
            .forallThing "z" <|
              .imp (dFoundedBy "x" "z" "w") (.eqThing "z" "y")
          ])),
  ("ax80",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dMediates "x" "y" "w")
          (dAndList [
            dUnary .relator "x" "w",
            dUnary .endurant "y" "w",
            .existsThing "z" <| dAndList [
              dQuaIndividualOf "z" "y" "w",
              dPart "z" "x" "w"
            ]
          ])),
  ("axQuaIndividualOfEndurant",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dQuaIndividualOf "x" "y" "w")
          (dUnary .endurant "y" "w")),
  ("ax81",
    .forallThing "t" <| .forallThing "m" <| .forallWorld "w" <|
        .imp
          (dCharacterization "t" "m" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            dUnary .momentType "m" "w",
            .forallThing "x" <|
              .imp
                (dInst "x" "t" "w")
                (.existsThing "y" <| dAndList [
                  dInst "y" "m" "w",
                  dBinary .inheresIn "y" "x" "w"
                ]),
            .forallThing "z" <|
              .imp
                (dInst "z" "m" "w")
                (.existsThing "bearer" <| dAndList [
                  dInst "bearer" "t" "w",
                  dBinary .inheresIn "z" "bearer" "w",
                  .forallThing "otherBearer" <|
                    .imp
                      (dAndList [
                        dInst "otherBearer" "t" "w",
                        dBinary .inheresIn "z" "otherBearer" "w"
                      ])
                      (.eqThing "otherBearer" "bearer")
                ])
          ])),
  ("ax82",
    .forallThing "t" <| .forallThing "q" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dCharacterization "t" "q" "w",
            dUnary .qualityType "q" "w"
          ])
          (.forallThing "x" <|
            .imp
              (dInst "x" "q" "w")
              (.existsThing "y" <| dAndList [
                dInst "y" "t" "w",
                dBinary .inheresIn "x" "y" "w",
                .forallThing "otherBearer" <|
                  .imp
                    (dAndList [
                      dInst "otherBearer" "t" "w",
                      dBinary .inheresIn "x" "otherBearer" "w"
                    ])
                    (.eqThing "otherBearer" "y")
              ]))),
  ("ax83",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .quale "x" "w")
          (dUnary .abstractIndividual "x" "w")),
  ("ax84",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .set_ "x" "w")
          (dUnary .abstractIndividual "x" "w")),
  ("ax85",
    .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .quale "x" "w",
          dUnary .set_ "x" "w"
        ]),
  ("ax86",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQualityStructure "x" "w")
          (dAndList [
            dUnary .set_ "x" "w",
            dNonEmptySet "x" "w"
          ])),
  ("ax87",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dUnary .quale "x" "w")
          (.existsThing "y" <| dAndList [
            dQualityStructure "y" "w",
            dMemberOf "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dAndList [
                  dQualityStructure "z" "w",
                  dMemberOf "x" "z" "w"
                ])
                (.eqThing "z" "y")
          ])),
  ("ax88",
    .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dQualityStructure "x" "w")
          (.or
            (dUnary .qualityDomain "x" "w")
            (dUnary .qualityDimension "x" "w"))),
  ("ax89",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .qualityDomain "x" "w")
          (.not (dUnary .qualityDimension "x" "w"))),
  ("ax90",
    .forallThing "s" <| .forallThing "t" <| .forallThing "s'" <|
        .forallThing "t'" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .associatedWith "s" "t" "w",
              dBinary .associatedWith "s'" "t'" "w",
              dProperSub "t'" "t" "w"
            ])
            (dProperSubsetOf "s'" "s" "w")),
  ("ax91",
    .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .qualityType "t" "w")
          (dAndList [
            dUnary .intrinsicMomentType "t" "w",
            .existsThing "x" <| dAndList [
              dQualityStructure "x" "w",
              dBinary .associatedWith "x" "t" "w",
              .forallThing "y" <|
                .imp
                  (dAndList [
                    dQualityStructure "y" "w",
                    dBinary .associatedWith "y" "t" "w"
                  ])
                  (.eqThing "y" "x")
            ]
          ])),
  ("ax92",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .hasValue "x" "y" "w")
          (dAndList [
            dQuality "x" "w",
            dUnary .quale "y" "w"
          ])),
  ("ax93",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQuality "x" "w")
          (.existsThing "y" <| dAndList [
            dBinary .hasValue "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dBinary .hasValue "x" "z" "w")
                (.eqThing "z" "y")
          ])),
  ("ax94",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .hasValue "x" "y" "w")
          (.existsThing "t" <| .existsThing "s" <| dAndList [
            dInst "x" "t" "w",
            dBinary .associatedWith "s" "t" "w",
            dMemberOf "y" "s" "w"
          ])),
  ("ax95",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .associatedWith "x" "y" "w")
          (.iff
            (dUnary .qualityDimension "x" "w")
            (dSimpleQualityType "y" "w"))),
  ("ax96",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .associatedWith "x" "y" "w")
          (.iff
            (dUnary .qualityDomain "x" "w")
            (dComplexQualityType "y" "w"))),
  ("ax97",
    .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallThing "Y" <| .forallThing "Z" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dComplexQuality "x" "w",
              dInst "y" "Y" "w",
              dInst "z" "Z" "w",
              dBinary .inheresIn "y" "x" "w",
              dBinary .inheresIn "z" "x" "w",
              .eqThing "Y" "Z"
            ])
            (.eqThing "y" "z")),
  ("ax98",
    .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dComplexQuality "x" "w")
          (.forallThing "y" <|
            .imp
              (dBinary .inheresIn "y" "x" "w")
              (dSimpleQuality "y" "w"))),
  ("ax100",
    .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dDistance "x" "y" "r" "w")
            (dAndList [
              dUnary .quale "x" "w",
              dUnary .quale "y" "w",
              .existsThing "z" <| dAndList [
                dMemberOf "x" "z" "w",
                dMemberOf "y" "z" "w"
              ]
            ])),
  ("ax101",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .quale "x" "w",
            dUnary .quale "y" "w"
          ])
          (.existsThing "r" <| dAndList [
            dDistance "x" "y" "r" "w",
            .forallThing "s" <|
              .imp
                (dDistance "x" "y" "s" "w")
                (.eqThing "s" "r")
          ])),
  ("axDistanceIdentity",
    .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              .eqThing "x" "y",
              dDistance "x" "y" "r" "w"
            ])
            (dDistanceZero "r" "w")),
  ("axDistanceSymmetry",
    .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dDistance "x" "y" "r" "w")
            (dDistance "y" "x" "r" "w")),
  ("axDistanceTriangle",
    .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallThing "r0" <| .forallThing "r1" <| .forallThing "r2" <|
        .forallThing "s" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dDistance "x" "y" "r0" "w",
              dDistance "y" "z" "r1" "w",
              dDistance "x" "z" "r2" "w",
              dDistanceSum "r0" "r1" "s" "w"
            ])
            (dDistanceGreaterEq "s" "r2" "w")),
  ("ax102",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .manifests "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .endurant "y" "w"
          ])),
  ("ax103",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dBinary .lifeOf "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .endurant "y" "w",
            .forallThing "z" <|
              .iff
                (dOverlap "z" "x" "w")
                (dAndList [
                  dUnary .perdurant "z" "w",
                  dBinary .manifests "z" "y" "w"
                ])
          ])),
  ("ax104",
    .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .meet "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .perdurant "y" "w"
          ]))
]

/-- Select the first exact field name from a registry. Each visit costs eight:
three loop controls, a checked array read (three), a string comparison, and a
branch. A match stops before another entry is read. Formula constants belong
to the program and are not rebuilt by this per-call lookup. -/
private def lookupDiagnosticFormulaCosted
    (registry : Array (String × DiagFormula)) (field : String) :
    Complexity.Costed (Option DiagFormula) :=
  foldDiagArrayCosted registry none Option.isSome fun _ entry =>
    .tick (if entry.1 == field then some entry.2 else none) 2

private theorem lookupDiagnosticFormulaCosted_value
    (registry : Array (String × DiagFormula)) (field : String) :
    (lookupDiagnosticFormulaCosted registry field).value =
      registry.toList.foldl (fun selected entry =>
        if selected.isSome then selected
        else if entry.1 == field then some entry.2 else none) none := by
  simp [lookupDiagnosticFormulaCosted, foldDiagArrayCosted_value]

private theorem lookupDiagnosticFormulaCosted_cost_le
    (registry : Array (String × DiagFormula)) (field : String) :
    (lookupDiagnosticFormulaCosted registry field).cost ≤ 8 * registry.size := by
  have h := foldDiagArrayCosted_cost_le registry none Option.isSome
    (fun _ entry =>
      Complexity.Costed.tick (if entry.1 == field then some entry.2 else none) 2)
    2 (by intros; rfl)
  simpa [lookupDiagnosticFormulaCosted, Nat.mul_comm] using h

private def diagnosticFormulaCosted (field : String) : Complexity.Costed (Option DiagFormula) :=
  lookupDiagnosticFormulaCosted diagnosticFormulaRegistry field

private def diagnosticFormula? (field : String) : Option DiagFormula :=
  (diagnosticFormulaCosted field).value

@[simp] private theorem diagnosticFormulaCosted_value (field : String) :
    (diagnosticFormulaCosted field).value = diagnosticFormula? field := rfl

private theorem diagnosticFormulaCosted_cost_le (field : String) :
    (diagnosticFormulaCosted field).cost ≤ 8 * diagnosticFormulaRegistry.size :=
  lookupDiagnosticFormulaCosted_cost_le _ _

/-- Append successful context traces in order, stopping at the output limit.
Each visited trace pays for its formula report and the indexed loop.
The input array is not converted to a list during execution. -/
private def appendContextEvidenceCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : Array DiagTrace) :
    Complexity.Costed (Array String) :=
  foldDiagArrayCosted traces out (fun out => budget ≤ out.size) fun out trace =>
    appendEvidenceForFormulaCosted budget worldNames thingNames namedFacts
      worldNames.size thingNames.size tables out trace.env trace.formula

private theorem appendContextEvidenceCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : Array DiagTrace) :
    (appendContextEvidenceCosted budget worldNames thingNames namedFacts tables out traces).value =
      traces.toList.foldl (fun out trace =>
        if out.size < budget then
          appendEvidenceForFormulaSpec budget worldNames thingNames namedFacts
            worldNames.size thingNames.size tables out trace.env trace.formula
        else out) out := by
  rw [appendContextEvidenceCosted, foldDiagArrayCosted_value]
  congr 1
  funext out trace
  simp only [appendEvidenceForFormulaCosted_value]
  split <;> simp_all

private theorem appendContextEvidenceCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : Array DiagTrace)
    (hout : out.size ≤ budget) :
    (appendContextEvidenceCosted budget worldNames thingNames namedFacts tables out traces).value.size ≤
      budget := by
  apply foldDiagArrayCosted_preserves traces out _ _ (fun out => out.size ≤ budget) hout
  intro out trace hOut _
  exact appendEvidenceForFormulaCosted_size_le _ _ _ _ _ _ _ _ _ _ hOut

private theorem appendContextEvidenceCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : Array DiagTrace)
    (nodeLimit envLimit : Nat)
    (hTraces : ∀ trace ∈ traces,
      trace.formula.nodeCount ≤ nodeLimit ∧ trace.env.size ≤ envLimit) :
    (appendContextEvidenceCosted budget worldNames thingNames namedFacts tables out traces).cost ≤
      traces.size * (nodeLimit * (diagAtomCostBound worldNames.size thingNames.size tables envLimit +
        60 * envLimit + 115 + 275 * namedFacts.size) + 21) := by
  have hVisit (out : Array String) (trace : DiagTrace) (ht : trace ∈ traces) :
      (appendEvidenceForFormulaCosted budget worldNames thingNames namedFacts
        worldNames.size thingNames.size tables out trace.env trace.formula).cost ≤
        nodeLimit * (diagAtomCostBound worldNames.size thingNames.size tables envLimit +
          60 * envLimit + 115 + 275 * namedFacts.size) + 15 := by
    have hsize := hTraces trace ht
    have hq : diagAtomCostBound worldNames.size thingNames.size tables trace.env.size ≤
        diagAtomCostBound worldNames.size thingNames.size tables envLimit := by
      unfold diagAtomCostBound
      omega
    exact (appendEvidenceForFormulaCosted_cost_le _ _ _ _ _ _ _ _ _ _).trans
      (appendEvidenceForFormulaCostBound_mono hsize.1 hsize.2 (Nat.le_refl _) hq)
  have bound := foldDiagArrayCosted_cost_le traces out (fun out => budget ≤ out.size)
    (fun out trace => appendEvidenceForFormulaCosted budget worldNames thingNames namedFacts
      worldNames.size thingNames.size tables out trace.env trace.formula)
    (nodeLimit * (diagAtomCostBound worldNames.size thingNames.size tables envLimit +
      60 * envLimit + 115 + 275 * namedFacts.size) + 15) hVisit
  simpa only [appendContextEvidenceCosted, Nat.add_assoc] using bound

/-- One atom contributes a header and its source facts, in source order.
The caller checks that the header fits. Source lookup and header construction
remain in the cost even when the budget retains no source row. -/
private def appendAtomEvidenceCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) :
    Complexity.Costed (Array String) :=
  let evidence := atomEvidenceCosted worldNames thingNames namedFacts env atom
  if evidence.value.isEmpty then
    ⟨out, evidence.cost + 2⟩
  else
    let header := (Complexity.Costed.appendString (.pure "Evidence for ")
      (renderDiagAtomCosted worldNames thingNames env atom)).appendString (.pure ":")
    let lines := appendEvidenceLinesCosted budget (out.push header.value) evidence.value
    ⟨lines.value, evidence.cost + 2 + header.cost + 2 + lines.cost⟩

private theorem appendAtomEvidenceCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) :
    (appendAtomEvidenceCosted budget worldNames thingNames namedFacts env out atom).value =
      let evidence := atomEvidenceSpec worldNames thingNames namedFacts env atom
      if evidence.isEmpty then out else
        let headed := out.push ("Evidence for " ++ renderDiagAtomSpec worldNames thingNames env atom ++ ":")
        headed ++ (evidence.extract 0 (budget - headed.size)).map ("  - " ++ ·) := by
  simp only [appendAtomEvidenceCosted, atomEvidenceCosted_value,
    Complexity.Costed.appendString_value, Complexity.Costed.pure_value, renderDiagAtomCosted_value]
  split <;> simp only [appendEvidenceLinesCosted_value]

private theorem appendAtomEvidenceCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom)
    (hout : out.size < budget) :
    (appendAtomEvidenceCosted budget worldNames thingNames namedFacts env out atom).value.size ≤ budget := by
  unfold appendAtomEvidenceCosted
  dsimp only
  split
  · exact Nat.le_of_lt hout
  · apply appendEvidenceLinesCosted_size_le
    simp only [Array.size_push]
    omega

private theorem appendAtomEvidenceCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) :
    (appendAtomEvidenceCosted budget worldNames thingNames namedFacts env out atom).cost ≤
      40 * env.size + 70 + 275 * namedFacts.size := by
  have hevidence := atomEvidenceCosted_cost_le worldNames thingNames namedFacts env atom
  have hsize : (atomEvidenceCosted worldNames thingNames namedFacts env atom).value.size ≤
      namedFacts.size := by
    rw [atomEvidenceCosted_value]
    exact atomEvidenceSpec_size_le_namedFacts worldNames thingNames namedFacts env atom
  have hrender := renderDiagAtomCosted_cost_le worldNames thingNames env atom
  unfold appendAtomEvidenceCosted
  dsimp only
  split
  · dsimp only
    unfold atomEvidenceCostBound at hevidence
    omega
  · have hlines := appendEvidenceLinesCosted_cost_le budget
      (out.push
        ((Complexity.Costed.appendString (.pure "Evidence for ")
          (renderDiagAtomCosted worldNames thingNames env atom)).appendString (.pure ":")).value)
      (atomEvidenceCosted worldNames thingNames namedFacts env atom).value
    simp only [Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost]
    unfold atomEvidenceCostBound at hevidence
    omega

/-- Visit the atom array in order and stop once the output budget is full.
The loop reads no later atom and creates no list copy. The six operations per
visited atom cover loop control and the checked read. A final stop costs three. -/
private def appendFailingAtomEvidenceCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atoms : Array DiagAtom) :
    Complexity.Costed (Array String) :=
  foldDiagArrayCosted atoms out (fun out => budget ≤ out.size)
    (appendAtomEvidenceCosted budget worldNames thingNames namedFacts env)

private theorem appendFailingAtomEvidenceCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atoms : Array DiagAtom) :
    (appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts env out atoms).value =
      atoms.toList.foldl (fun out atom =>
        if out.size < budget then
          let evidence := atomEvidenceSpec worldNames thingNames namedFacts env atom
          if evidence.isEmpty then out else
            let headed := out.push ("Evidence for " ++ renderDiagAtomSpec worldNames thingNames env atom ++ ":")
            headed ++ (evidence.extract 0 (budget - headed.size)).map ("  - " ++ ·)
        else out) out := by
  rw [appendFailingAtomEvidenceCosted, foldDiagArrayCosted_value]
  congr 1
  funext out atom
  simp only [appendAtomEvidenceCosted_value]
  split <;> simp_all

private theorem appendFailingAtomEvidenceCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atoms : Array DiagAtom)
    (hout : out.size ≤ budget) :
    (appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts env out atoms).value.size ≤
      budget := by
  apply foldDiagArrayCosted_preserves atoms out _ _ (fun out => out.size ≤ budget) hout
  intro out atom _ stopped
  apply appendAtomEvidenceCosted_size_le
  simpa using stopped

private theorem appendFailingAtomEvidenceCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (out : Array String) (atoms : Array DiagAtom) :
    (appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts env out atoms).cost ≤
      atoms.size * (40 * env.size + 76 + 275 * namedFacts.size) := by
  have bound := foldDiagArrayCosted_cost_le atoms out (fun out => budget ≤ out.size)
    (appendAtomEvidenceCosted budget worldNames thingNames namedFacts env)
    (40 * env.size + 70 + 275 * namedFacts.size)
    (by intros; apply appendAtomEvidenceCosted_cost_le)
  have coefficient : 40 * env.size + 70 + 275 * namedFacts.size + 6 =
      40 * env.size + 76 + 275 * namedFacts.size := by omega
  rw [coefficient] at bound
  exact bound

private theorem appendFailingAtomEvidenceCostBound_mono
    {k k' e e' n n' : Nat} (hk : k ≤ k') (he : e ≤ e') (hn : n ≤ n') :
    k * (40 * e + 76 + 275 * n) ≤ k' * (40 * e' + 76 + 275 * n') :=
  Nat.mul_le_mul hk (by omega)


/-- All three text arguments are evaluated before insertion. Their costs
therefore remain in the total even when the output budget has no room. -/
private def appendDiagnosticPreambleCosted
    (budget : Nat) (out : Array String)
    (assignment condition suggestion : Complexity.Costed String) : Complexity.Costed (Array String) := do
  let assignment ← assignment
  let condition ← condition
  let suggestion ← suggestion
  let out ← pushDiagnosticIfRoomCosted budget out assignment
  let out ← pushDiagnosticIfRoomCosted budget out condition
  pushDiagnosticIfRoomCosted budget out suggestion

private theorem appendDiagnosticPreambleCosted_value
    (budget : Nat) (out : Array String) (assignment condition suggestion : Complexity.Costed String) :
    (appendDiagnosticPreambleCosted budget out assignment condition suggestion).value =
      pushDiagnosticIfRoom budget
        (pushDiagnosticIfRoom budget (pushDiagnosticIfRoom budget out assignment.value) condition.value)
        suggestion.value := by
  simp only [appendDiagnosticPreambleCosted, Bind.bind, Complexity.Costed.bind_value,
    pushDiagnosticIfRoomCosted_value]

private theorem appendDiagnosticPreambleCosted_size_le
    (budget : Nat) (out : Array String)
    (assignment condition suggestion : Complexity.Costed String) (hout : out.size ≤ budget) :
    (appendDiagnosticPreambleCosted budget out assignment condition suggestion).value.size ≤
      budget := by
  rw [appendDiagnosticPreambleCosted_value]
  exact pushDiagnosticIfRoom_size_le budget _ suggestion.value
    (pushDiagnosticIfRoom_size_le budget _ condition.value
      (pushDiagnosticIfRoom_size_le budget out assignment.value hout))

private theorem appendDiagnosticPreambleCosted_cost_le
    (budget : Nat) (out : Array String)
    (assignment condition suggestion : Complexity.Costed String) :
    (appendDiagnosticPreambleCosted budget out assignment condition suggestion).cost ≤
      assignment.cost + condition.cost + suggestion.cost + 12 := by
  simp only [appendDiagnosticPreambleCosted, Bind.bind, Complexity.Costed.bind_cost]
  have h1 := pushDiagnosticIfRoomCosted_cost_le budget out assignment.value
  have h2 := pushDiagnosticIfRoomCosted_cost_le budget
    (pushDiagnosticIfRoomCosted budget out assignment.value).value condition.value
  have h3 := pushDiagnosticIfRoomCosted_cost_le budget
    (pushDiagnosticIfRoomCosted budget
      (pushDiagnosticIfRoomCosted budget out assignment.value).value condition.value).value suggestion.value
  omega

/-- Only retained rows pay for writes and emissions. Text costs and all
capacity checks remain, including for initially oversized output. -/
private theorem appendDiagnosticPreambleCosted_cost_eq_emitted
    (budget : Nat) (out : Array String)
    (assignment condition suggestion : Complexity.Costed String) :
    (appendDiagnosticPreambleCosted budget out assignment condition suggestion).cost =
      assignment.cost + condition.cost + suggestion.cost + 6 +
      2 * ((appendDiagnosticPreambleCosted budget out assignment condition suggestion).value.size - out.size) := by
  have h1 := pushDiagnosticIfRoomCosted_accounting budget out assignment.value
  have h2 := pushDiagnosticIfRoomCosted_accounting budget
    (pushDiagnosticIfRoomCosted budget out assignment.value).value condition.value
  have h3 := pushDiagnosticIfRoomCosted_accounting budget
    (pushDiagnosticIfRoomCosted budget
      (pushDiagnosticIfRoomCosted budget out assignment.value).value condition.value).value suggestion.value
  simp only [appendDiagnosticPreambleCosted, Bind.bind, Complexity.Costed.bind_cost,
    Complexity.Costed.bind_value]
  omega

private def genericDiagnosticVisitCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula)
    (out : Array String) (env : Array (String × Nat)) :
    Complexity.Costed (Array String) :=
      let checked := evalDiagFormulaCosted worldNames.size thingNames.size tables env body
      if checked.value then
        -- Charge the failed-test branch in addition to formula evaluation.
        ⟨out, checked.cost + 1⟩
      else
        let minimized := minimizeFailureCosted worldNames.size thingNames.size tables env body
        Id.run do
          let failedFormula := minimized.value.formula
          let failedEnv := minimized.value.env
          let discovered := diagnosticEnvVarsCosted vars failedFormula failedEnv
          let failedVars := discovered.value
          let conditionLine :=
            renderDiagnosticConditionLineCosted worldNames thingNames failedEnv failedFormula
          let assignment := Complexity.Costed.appendString (.pure "Counterexample assignment: ")
            (envSummaryCosted worldNames thingNames failedVars failedEnv)
          let assignment := assignment.appendString (.pure ".")
          let suggestion := Complexity.Costed.appendString (.pure "Suggestion: ")
            (suggestionForFailureCosted worldNames thingNames worldNames.size thingNames.size
              tables failedEnv failedFormula)
          -- Text is constructed before the output-cap checks. Its cost remains
          -- even when the report cannot retain another row.
          let preamble := appendDiagnosticPreambleCosted budget out assignment
            conditionLine suggestion
          let mut out := preamble.value
          let mut cost := checked.cost + minimized.cost + discovered.cost + 1 + preamble.cost
          let contextOut := appendContextEvidenceCosted budget worldNames thingNames namedFacts tables
            out minimized.value.context
          out := contextOut.value
          cost := cost + contextOut.cost
          let failedAtoms := failingAtomsCosted worldNames.size thingNames.size tables failedEnv failedFormula
          let atomOut := appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts
            failedEnv out failedAtoms.value
          out := atomOut.value
          cost := cost + failedAtoms.cost + atomOut.cost
          return ⟨out, cost⟩

private def genericDiagnosticWitnessesCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    Complexity.Costed (Array String) :=
  -- Initialize the assignment environment and report accumulator even when
  -- a zero budget or empty domain prevents the first visit.
  Complexity.Costed.charge 2 <|
  foldDiagEnvsUntilCosted worldNames.size thingNames.size vars 0 #[] (#[] : Array String)
    (fun out => budget ≤ out.size)
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body)

/-- Bound for the current failed-assignment counter. The terms expose
formula evaluation, recursive minimization, retained environment/context size,
source-fact scans, and domain-expanded failing atoms. Context and atom evidence
include their operational component bounds. Other contributing counters still
need repairs, listed in the complexity guide. This bound holds for every budget. -/
private def genericDiagnosticVisitCostBound
    (worldCount thingCount namedFactCount varCount envSize : Nat)
    (tables : FactTables) (body : DiagFormula) : Nat :=
  body.evalCostBound worldCount thingCount
      (diagAtomCostBound worldCount thingCount tables) envSize +
    body.failureMinimizeCostBound worldCount thingCount tables envSize +
    diagnosticEnvVarsCostBound body.nodeCount varCount (body.failureEnvSizeBound envSize) +
    body.failureEnvSizeBound envSize * (4 * body.failureEnvSizeBound envSize + 13) +
    body.nodeCount * (20 * body.failureEnvSizeBound envSize + 56) + 27 +
    body.failureContextSizeBound *
      (body.nodeCount * (diagAtomCostBound worldCount thingCount tables (envSize + body.nodeCount) +
        60 * (envSize + body.nodeCount) + 115 + 275 * namedFactCount) + 21) +
    body.failureAtomEnumerationBound worldCount thingCount *
      (40 * body.failureEnvSizeBound envSize + 76 + 275 * namedFactCount) +
    2 * body.failureDetailCostBound worldCount thingCount
      (diagAtomCostBound worldCount thingCount tables) (body.failureEnvSizeBound envSize) +
    8 * body.nodeCount + 20 * body.failureEnvSizeBound envSize + 53

private theorem genericDiagnosticVisitCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula)
    (out : Array String) (env : Array (String × Nat)) :
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body out env).cost ≤
      genericDiagnosticVisitCostBound worldNames.size thingNames.size namedFacts.size
        vars.size env.size tables body := by
  simp only [genericDiagnosticVisitCosted]
  split
  · change (evalDiagFormulaCosted worldNames.size thingNames.size tables env body).cost + 1 ≤ _
    have hchecked := evalDiagFormulaCosted_concrete_cost_le
      worldNames.size thingNames.size tables env body
    unfold genericDiagnosticVisitCostBound
    omega
  · have hchecked := evalDiagFormulaCosted_concrete_cost_le
      worldNames.size thingNames.size tables env body
    have hmin := minimizeFailureCosted_cost_le worldNames.size thingNames.size tables env body
    have henv := minimizeFailureCosted_env_size_le worldNames.size thingNames.size tables env body
    have hvars := diagnosticEnvVarsCosted_size_le vars
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
    have hsummary := envSummaryCosted_cost_le worldNames thingNames
      (diagnosticEnvVarsCosted vars
        (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
        (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env).value
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
    have hsummaryScaled := envSummaryCostBound_mono (hvars.trans henv) henv
    have hnodes := minimizeFailureCosted_formula_nodeCount_le worldNames.size thingNames.size tables env body
    have hdiscovered := diagnosticEnvVarsCosted_cost_le vars
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
    have hdiscoveredScaled := diagnosticEnvVarsCostBound_mono hnodes (Nat.le_refl vars.size) henv
    have hcondition := renderDiagnosticConditionLineCosted_cost_le worldNames thingNames
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
    have hconditionScaled := renderDiagnosticConditionLineCostBound_mono hnodes henv
    have hcontext := minimizeFailureCosted_context_size_le
      worldNames.size thingNames.size tables env body
    have hminAtoms := minimizeFailureCosted_failingAtomCountBound_le_failureEnumeration
      worldNames.size thingNames.size tables env body
    have hatoms := failingAtomsCosted_size_le worldNames.size thingNames.size tables
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
    have hcontextTraces := minimizeFailureCosted_trace_bounds
      worldNames.size thingNames.size tables env body
    have hcontextCost (out : Array String) := appendContextEvidenceCosted_cost_le
      budget worldNames thingNames namedFacts tables out
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.context
      body.nodeCount (env.size + body.nodeCount) hcontextTraces
    have hcontextScaled := Nat.mul_le_mul_right
      (body.nodeCount *
        (diagAtomCostBound worldNames.size thingNames.size tables (env.size + body.nodeCount) +
          60 * (env.size + body.nodeCount) + 115 + 275 * namedFacts.size) + 21) hcontext
    have hatomsCombined :
        (failingAtomsCosted worldNames.size thingNames.size tables
          (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
          (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula).value.size ≤
          body.failureAtomEnumerationBound worldNames.size thingNames.size :=
      Nat.le_trans hatoms hminAtoms
    have hatomsScaled := Nat.mul_le_mul hatomsCombined
      (show 40 * (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env.size +
          76 + 275 * namedFacts.size ≤
        40 * body.failureEnvSizeBound env.size + 76 + 275 * namedFacts.size by omega)
    have hAtom := evalDiagAtomCosted_cost_le worldNames.size thingNames.size tables
    have hAtomMono : Monotone (diagAtomCostBound worldNames.size thingNames.size tables) := by
      intro e e' h
      unfold diagAtomCostBound
      omega
    have hSuggest := suggestionForFailureCosted_cost_le worldNames thingNames
      worldNames.size thingNames.size tables (diagAtomCostBound worldNames.size thingNames.size tables)
      hAtom (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
    have hFailedAtoms := failingAtomsCosted_cost_le worldNames.size thingNames.size tables
      (diagAtomCostBound worldNames.size thingNames.size tables) hAtom
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
    have hEvalScaled := DiagFormula.evalCostBound_mono_env worldNames.size thingNames.size
      (diagAtomCostBound worldNames.size thingNames.size tables) hAtomMono
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula henv
    have hScanScaled := DiagFormula.failingAtomsCostBound_mono_env worldNames.size thingNames.size
      (diagAtomCostBound worldNames.size thingNames.size tables) hAtomMono
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula henv
    have hDetail := minimizeFailureCosted_detailCostBound worldNames.size thingNames.size tables
      (diagAtomCostBound worldNames.size thingNames.size tables)
      (body.failureEnvSizeBound env.size) env body
    simp only [DiagFormula.suggestionCostBound] at hSuggest
    unfold genericDiagnosticVisitCostBound
    grind [appendDiagnosticPreambleCosted_cost_le, appendDiagnosticPreambleCosted_size_le,
      Complexity.Costed.appendString_cost, Complexity.Costed.pure_cost,
      appendFailingAtomEvidenceCosted_cost_le]

private theorem genericDiagnosticWitnessesCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).cost ≤
      diagEnvDependentFoldCostBound worldNames.size thingNames.size
        (fun envSize => genericDiagnosticVisitCostBound worldNames.size thingNames.size
          namedFacts.size vars.size envSize tables body)
        0 vars.toList + 2 := by
  have h := foldDiagEnvsUntilCosted_dependent_cost_le worldNames.size thingNames.size
    vars 0 #[] (#[] : Array String) (fun out => budget ≤ out.size)
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body)
    (fun envSize => genericDiagnosticVisitCostBound worldNames.size thingNames.size
      namedFacts.size vars.size envSize tables body)
    (by
      intro state env
      exact genericDiagnosticVisitCosted_cost_le budget worldNames thingNames namedFacts
        tables vars body state env)
  simpa [genericDiagnosticWitnessesCosted, Complexity.Costed.charge_cost,
    Nat.add_comm] using Nat.add_le_add_left h 2

private def genericDiagnosticWitnesses
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) : Array String :=
  (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).value

@[simp] private theorem genericDiagnosticWitnessesCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).value =
      genericDiagnosticWitnesses budget worldNames thingNames namedFacts tables vars body := rfl

/-- Select specialized analyzers in order. Each tested field costs one string
comparison and one branch. A match skips all later tests and analyzers.
Fallback rows count their text joins, initialization, writes, and emissions.
The generic branch includes the fixed registry's counted lookup. -/
private def diagnosticWitnessesInnerCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) : Complexity.Costed (Array String) :=
  Complexity.Costed.charge 2 <| if field == "ax68" then
    ax68ClosureAnalysisCosted worldNames thingNames tables
  else Complexity.Costed.charge 2 <| if field == "ax71" then
    ax71FoundationAnalysisCosted worldNames thingNames tables
  else Complexity.Costed.charge 2 <| if field == "ax73" then
    ax73PartCharacterizationAnalysisCosted worldNames thingNames tables
  else Complexity.Costed.charge 2 <| if field == "ax78" then
    ax78FoundationAnalysisCosted budget worldNames thingNames tables
  else Complexity.Costed.charge 2 <| if field == "ax79" then
    ax79FoundationAnalysisCosted worldNames thingNames tables
  else Complexity.Costed.charge 2 <| if field == "ax99" then
    ax99QualityDomainAnalysisCosted worldNames thingNames tables
  else do
    let selected ← diagnosticFormulaCosted field
    Complexity.Costed.charge 1 <| match selected with
    | none => do
        let out ← Complexity.Costed.tick (#[] : Array String) 1
        let text ← Complexity.Costed.tick ("No structured DSL-level witness extractor is registered for " ++ field) 1
        let text ← Complexity.Costed.tick (text ++ " yet.") 1
        Complexity.Costed.tick (out.push text) 2
    | some formula => do
        let peeled ← formula.peelForallsCosted
        let vars := peeled.1
        let body := peeled.2
        let out ← genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body
        Complexity.Costed.charge 2 <| if out.isEmpty then do
          let out ← Complexity.Costed.tick (#[] : Array String) 1
          let text ← Complexity.Costed.tick ("The structured checker did not find a DSL-level witness for " ++ field) 1
          let text ← Complexity.Costed.tick (text ++ ".") 1
          Complexity.Costed.tick (out.push text) 2
        else Complexity.Costed.pure out

/-- Field-sensitive search and rendering bound for the diagnostics dispatcher.
The definition follows the selected specialized analyzer or registered formula
evaluator branch and holds for every evidence budget. -/
def diagnosticWitnessesInnerCostBound
    (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables) (field : String) : Nat :=
  if field == "ax68" then
    ax68ClosureAnalysisCostBound worldNames.size thingNames.size + 2
  else if field == "ax71" then
    ax71FoundationAnalysisCostBound worldNames.size thingNames.size tables + 4
  else if field == "ax73" then
    ax73PartCharacterizationAnalysisCostBound worldNames.size thingNames.size + 6
  else if field == "ax78" then
    ax78FoundationAnalysisCostBound worldNames.size thingNames.size + 8
  else if field == "ax79" then
    ax79FoundationAnalysisCostBound worldNames.size thingNames.size + 10
  else if field == "ax99" then
    ax99QualityDomainAnalysisCostBound worldNames.size thingNames.size tables.productFamilies + 12
  else match diagnosticFormula? field with
  | none => 8 * diagnosticFormulaRegistry.size + 18
  | some formula =>
      let vars := formula.forallVars
      let body := formula.stripForalls
      diagEnvDependentFoldCostBound worldNames.size thingNames.size
        (fun envSize => genericDiagnosticVisitCostBound worldNames.size thingNames.size
          namedFacts.size vars.size envSize tables body)
        0 vars.toList + 3 * vars.size + 8 * diagnosticFormulaRegistry.size + 24

private theorem diagnosticWitnessesInnerCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables) (field : String) :
    (diagnosticWitnessesInnerCosted budget worldNames thingNames namedFacts tables field).cost ≤
      diagnosticWitnessesInnerCostBound worldNames thingNames namedFacts tables field := by
  simp only [diagnosticWitnessesInnerCosted, diagnosticWitnessesInnerCostBound]
  split
  · have h := ax68ClosureAnalysisCosted_cost_le worldNames thingNames tables
    simp only [Complexity.Costed.charge_cost]
    omega
  · split
    · have h := ax71FoundationAnalysisCosted_cost_le worldNames thingNames tables
      simp only [Complexity.Costed.charge_cost]
      omega
    · split
      · have h := ax73PartCharacterizationAnalysisCosted_cost_le worldNames thingNames tables
        simp only [Complexity.Costed.charge_cost]
        omega
      · split
        · have h := ax78FoundationAnalysisCosted_cost_le budget worldNames thingNames tables
          simp only [Complexity.Costed.charge_cost]
          omega
        · split
          · have h := ax79FoundationAnalysisCosted_cost_le worldNames thingNames tables
            simp only [Complexity.Costed.charge_cost]
            omega
          · split
            · have h := ax99QualityDomainAnalysisCosted_cost_le worldNames thingNames tables
              simp only [Complexity.Costed.charge_cost]
              omega
            · have hlookup := diagnosticFormulaCosted_cost_le field
              simp only [Complexity.Costed.charge_cost, Bind.bind,
                Complexity.Costed.bind_cost, diagnosticFormulaCosted_value]
              split
              · simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
                omega
              · rename_i formula hformula
                have hout := genericDiagnosticWitnessesCosted_cost_le budget worldNames thingNames
                  namedFacts tables formula.forallVars formula.stripForalls
                simp only [Complexity.Costed.bind_cost, Complexity.Costed.charge_cost,
                  DiagFormula.peelForallsCosted_value, DiagFormula.peelForallsCosted_cost]
                split
                · simp only [Complexity.Costed.bind_cost, Complexity.Costed.tick_cost]
                  omega
                · simp only [Complexity.Costed.pure_cost]
                  omega

/-- Apply one output cap after the selected analyzer. Generic enumeration also
uses the budget to stop its search. Specialized reports are capped here after
construction. Both paths retain deterministic prefix order. -/
def diagnosticWitnessesBudgetedCosted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) : Complexity.Costed (Array String) := do
  let generated ←
    diagnosticWitnessesInnerCosted budget worldNames thingNames namedFacts tables field
  let kept ← Complexity.boundedEvidenceCosted budget generated
  Complexity.Costed.pure kept.items

def diagnosticWitnessesBudgeted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) : Array String :=
  (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).value

theorem diagnosticWitnessesBudgetedCosted_value
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).value =
      diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field := rfl

/-- Exact output-sensitive composition law for the public producer. Search and
rendering contribute the inner producer cost. The public boundary adds four
operations per emitted item and four fixed operations for the prefix copy. -/
theorem diagnosticWitnessesBudgetedCosted_cost_eq_inner_add_emitted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).cost =
      (diagnosticWitnessesInnerCosted budget worldNames thingNames namedFacts tables field).cost +
        4 * (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size + 4 := by
  unfold diagnosticWitnessesBudgeted diagnosticWitnessesBudgetedCosted
  simp only [Bind.bind, Complexity.Costed.bind_cost, Complexity.Costed.bind_value,
    Complexity.Costed.pure_cost, Complexity.Costed.pure_value,
    Complexity.boundedEvidenceCosted_value, Complexity.boundedEvidenceCosted_cost_eq_emitted]
  omega

/-- Output-sensitive bound for the public diagnostic producer. The inner term
composes the selected analyzer's search and rendering bounds. The final terms
charge the shared prefix copy, with four operations per emitted row and four
fixed operations. All terms use the documented primitive-call model. -/
theorem diagnosticWitnessesBudgetedCosted_cost_le_inner_add_emitted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).cost ≤
      diagnosticWitnessesInnerCostBound worldNames thingNames namedFacts tables field +
        4 * (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size + 4 := by
  rw [diagnosticWitnessesBudgetedCosted_cost_eq_inner_add_emitted]
  have hinner := diagnosticWitnessesInnerCosted_cost_le
    budget worldNames thingNames namedFacts tables field
  omega

theorem diagnosticWitnessesBudgeted_size_le
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size ≤
      budget := by
  unfold diagnosticWitnessesBudgeted diagnosticWitnessesBudgetedCosted
  simp only [Bind.bind, Complexity.Costed.bind_value, Complexity.Costed.pure_value,
    Complexity.boundedEvidenceCosted_value]
  exact Complexity.boundedEvidence_size_le_budget _ _

/-- Production diagnostics use the same 128-item budget as the final widget
boundary. The latter remains as defense in depth for non-witness messages. -/
def diagnosticWitnesses
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) : Array String :=
  diagnosticWitnessesBudgeted 128 worldNames thingNames namedFacts tables field


end LeanUfo.UFO.DSL
