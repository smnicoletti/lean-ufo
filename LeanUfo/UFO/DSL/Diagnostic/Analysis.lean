import Lean
import LeanUfo.UFO.DSL.Compiler
import LeanUfo.UFO.DSL.Complexity.Checker
import LeanUfo.UFO.DSL.Frontend.ModelText

/-!
# Source-level diagnostics for finite UFO DSL models

This module reconstructs explanatory evidence from compiled finite tables after
a generated certificate fails. Diagnostics are separate from the
trusted certificate path: they render counterexamples, missing assertions, and
source-level suggestions, but they are not proof obligations.

The data flow is:

```text
failed checker field
  -> diagnostic formula and finite environment
  -> smallest failing subformula
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
is built with accumulators and an evidence budget, so its separate complexity
result is output-sensitive: producing more diagnostic rows is allowed to cost
more. This separation follows the cost-aware-semantics literature cited in
`docs/dsl/complexity.md`; diagnostic convenience cannot change certification.
-/

open Lean

namespace LeanUfo.UFO.DSL

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

/--
Scan the environment from left to right and retain the last matching binding.
Nested diagnostic quantifiers append bindings, so the last match implements
ordinary lexical shadowing. Each entry costs one iteration and one comparison;
the final default lookup costs one more operation.
-/
private def lookupVarListCosted
    (name : String) (entries : List (String × Nat)) (found : Option Nat) :
    Complexity.Costed Nat :=
  match entries with
  | [] => ⟨found.getD 0, 1⟩
  | List.cons entry entries =>
      let next := if entry.1 == name then some entry.2 else found
      Complexity.Costed.charge 2 (lookupVarListCosted name entries next)

private def lookupVarCosted (env : Array (String × Nat)) (name : String) :
    Complexity.Costed Nat :=
  lookupVarListCosted name env.toList none

private def lookupVar (env : Array (String × Nat)) (name : String) : Nat :=
  (lookupVarCosted env name).value

@[simp] private theorem lookupVarCosted_value
    (env : Array (String × Nat)) (name : String) :
    (lookupVarCosted env name).value = lookupVar env name := rfl

private theorem lookupVarListCosted_cost
    (name : String) (entries : List (String × Nat)) (found : Option Nat) :
    (lookupVarListCosted name entries found).cost = 2 * entries.length + 1 := by
  induction entries generalizing found with
  | nil => simp [lookupVarListCosted]
  | cons entry entries ih =>
      simp [lookupVarListCosted, ih]
      omega

private theorem lookupVarCosted_cost
    (env : Array (String × Nat)) (name : String) :
    (lookupVarCosted env name).cost = 2 * env.size + 1 := by
  simpa [lookupVarCosted] using lookupVarListCosted_cost name env.toList none

private def diagFinThingTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"

private def diagFinWorldTerm (idx : Nat) : String :=
  s!"(⟨{idx}, by decide⟩ : Fin data.worldCount)"

private def hasPossibleInstanceCosted
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) :
    Complexity.Costed Bool :=
  Complexity.anyListCosted (List.range worldCount) fun w =>
    Complexity.anyListCosted (List.range thingCount) fun x =>
      .tick (tables.binaryLookup "inst" x thing w) 1

private def hasPossibleInstance
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) : Bool :=
  (hasPossibleInstanceCosted worldCount thingCount tables thing).value

@[simp] private theorem hasPossibleInstanceCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) :
    (hasPossibleInstanceCosted worldCount thingCount tables thing).value =
      hasPossibleInstance worldCount thingCount tables thing := rfl

/-- The possible-instance search visits at most every world/thing cell. The
bound includes the short-circuit scan overhead and one dense-table access per
cell. -/
private theorem hasPossibleInstanceCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) :
    (hasPossibleInstanceCosted worldCount thingCount tables thing).cost ≤
      worldCount * (thingCount * 3 + 2) := by
  unfold hasPossibleInstanceCosted
  have outer := Complexity.anyListCosted_cost_le
    (List.range worldCount)
    (fun w => Complexity.anyListCosted (List.range thingCount) fun x =>
      Complexity.Costed.tick (tables.binaryLookup "inst" x thing w) 1)
    (thingCount * 3)
    (by
      intro w hw
      have inner := Complexity.anyListCosted_cost_le
        (List.range thingCount)
        (fun x => Complexity.Costed.tick (tables.binaryLookup "inst" x thing w) 1)
        1
        (by intro x hx; simp)
      simpa using inner)
  simpa using outer

private def boxExImpLookupCosted
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  Complexity.allListCosted (List.range worldCount) fun w =>
    Complexity.Costed.implies
      (.tick (tables.unaryLookup "ex" x w) 1)
      (fun _ => .tick (tables.unaryLookup "ex" y w) 1)

private def boxExImpLookup
    (worldCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  (boxExImpLookupCosted worldCount tables x y).value

@[simp] private theorem boxExImpLookupCosted_value
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (boxExImpLookupCosted worldCount tables x y).value =
      boxExImpLookup worldCount tables x y := rfl

/-- Modal existence implication checks at most two `Ex` cells per world. The
constant six also includes implication and universal-scan control operations. -/
private theorem boxExImpLookupCosted_cost_le
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (boxExImpLookupCosted worldCount tables x y).cost ≤ 6 * worldCount := by
  unfold boxExImpLookupCosted
  have scan := Complexity.allListCosted_cost_le
    (List.range worldCount)
    (fun w => Complexity.Costed.implies
      (.tick (tables.unaryLookup "ex" x w) 1)
      (fun _ => .tick (tables.unaryLookup "ex" y w) 1))
    4
    (by
      intro w hw
      exact Complexity.Costed.implies_cost_le _ _ 1 1 (by simp) (by simp))
  simpa [Nat.mul_comm] using scan

private def existentialDependenceLookupCosted
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  boxExImpLookupCosted worldCount tables x y

private def existentialDependenceLookup
    (worldCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  (existentialDependenceLookupCosted worldCount tables x y).value

private def existentialIndependenceLookupCosted
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (Complexity.Costed.not <| existentialDependenceLookupCosted worldCount tables x y)
    (fun _ => Complexity.Costed.not <|
      existentialDependenceLookupCosted worldCount tables y x)

private def existentialIndependenceLookup
    (worldCount : Nat) (tables : FactTables) (x y : Nat) : Bool :=
  (existentialIndependenceLookupCosted worldCount tables x y).value

private def existsWithoutLookupCosted
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed Bool :=
  Complexity.anyListCosted (List.range worldCount) fun w =>
    Complexity.Costed.andThen
      (.tick (tables.unaryLookup "ex" x w) 1)
      (fun _ => Complexity.Costed.not <| .tick (tables.unaryLookup "ex" y w) 1)

private def externallyDependentLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (boxExImpLookupCosted worldCount tables x y)
    (fun _ => Complexity.allListCosted (List.range thingCount) fun z =>
      Complexity.Costed.implies
        (.tick (tables.binaryLookup "inheresIn" x z w) 1)
        (fun _ => Complexity.Costed.andThen
          (existsWithoutLookupCosted worldCount tables y z)
          (fun _ => existsWithoutLookupCosted worldCount tables z y)))

private def externallyDependentLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) : Bool :=
  (externallyDependentLookupCosted worldCount thingCount tables x y w).value

private def externallyDependentModeLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (.tick (tables.unaryLookup "mode" x w) 1)
    (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
      externallyDependentLookupCosted worldCount thingCount tables x y w)

private def externallyDependentModeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (externallyDependentModeLookupCosted worldCount thingCount tables x w).value

@[simp] private theorem existentialDependenceLookupCosted_value
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (existentialDependenceLookupCosted worldCount tables x y).value =
      existentialDependenceLookup worldCount tables x y := rfl

@[simp] private theorem existentialIndependenceLookupCosted_value
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceLookupCosted worldCount tables x y).value =
      existentialIndependenceLookup worldCount tables x y := rfl

@[simp] private theorem externallyDependentLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (externallyDependentLookupCosted worldCount thingCount tables x y w).value =
      externallyDependentLookup worldCount thingCount tables x y w := rfl

@[simp] private theorem externallyDependentModeLookupCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (externallyDependentModeLookupCosted worldCount thingCount tables x w).value =
      externallyDependentModeLookup worldCount thingCount tables x w := rfl

private theorem existsWithoutLookupCosted_cost_le
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (existsWithoutLookupCosted worldCount tables x y).cost ≤ 6 * worldCount := by
  unfold existsWithoutLookupCosted
  have scan := Complexity.anyListCosted_cost_le
    (List.range worldCount)
    (fun w => Complexity.Costed.andThen
      (.tick (tables.unaryLookup "ex" x w) 1)
      (fun _ => Complexity.Costed.not <| .tick (tables.unaryLookup "ex" y w) 1))
    4
    (by
      intro w hw
      exact Complexity.Costed.andThen_cost_le _ _ 1 2 (by simp) (by simp))
  simpa [Nat.mul_comm] using scan

private theorem existentialIndependenceLookupCosted_cost_le
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (existentialIndependenceLookupCosted worldCount tables x y).cost ≤
      12 * worldCount + 3 := by
  unfold existentialIndependenceLookupCosted existentialDependenceLookupCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _ (6 * worldCount + 1)
      (6 * worldCount + 1) ?_ ?_) ?_
  · simpa using Nat.add_le_add_right
      (boxExImpLookupCosted_cost_le worldCount tables x y) 1
  · simpa using Nat.add_le_add_right
      (boxExImpLookupCosted_cost_le worldCount tables y x) 1
  · omega

private theorem externallyDependentLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (externallyDependentLookupCosted worldCount thingCount tables x y w).cost ≤
      6 * worldCount + thingCount * (12 * worldCount + 6) + 1 := by
  unfold externallyDependentLookupCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _ (6 * worldCount)
      (thingCount * (12 * worldCount + 6)) ?_ ?_) ?_
  · exact boxExImpLookupCosted_cost_le worldCount tables x y
  · have scan := Complexity.allListCosted_cost_le
      (List.range thingCount)
      (fun z => Complexity.Costed.implies
        (.tick (tables.binaryLookup "inheresIn" x z w) 1)
        (fun _ => Complexity.Costed.andThen
          (existsWithoutLookupCosted worldCount tables y z)
          (fun _ => existsWithoutLookupCosted worldCount tables z y)))
      (12 * worldCount + 4)
      (by
        intro z hz
        refine le_trans
          (Complexity.Costed.implies_cost_le _ _ 1 (12 * worldCount + 1) ?_ ?_) ?_
        · simp
        · refine le_trans
            (Complexity.Costed.andThen_cost_le _ _ (6 * worldCount) (6 * worldCount)
              ?_ ?_) ?_
          · exact existsWithoutLookupCosted_cost_le worldCount tables y z
          · exact existsWithoutLookupCosted_cost_le worldCount tables z y
          · omega
        · omega)
    simpa using scan
  · omega

private theorem externallyDependentModeLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (externallyDependentModeLookupCosted worldCount thingCount tables x w).cost ≤
      thingCount *
        (6 * worldCount + thingCount * (12 * worldCount + 6) + 3) + 2 := by
  unfold externallyDependentModeLookupCosted
  refine le_trans
    (Complexity.Costed.andThen_cost_le _ _ 1
      (thingCount * (6 * worldCount + thingCount * (12 * worldCount + 6) + 3))
      ?_ ?_) ?_
  · simp
  · have scan := Complexity.anyListCosted_cost_le
      (List.range thingCount)
      (fun y => externallyDependentLookupCosted worldCount thingCount tables x y w)
      (6 * worldCount + thingCount * (12 * worldCount + 6) + 1)
      (by
        intro y hy
        exact externallyDependentLookupCosted_cost_le worldCount thingCount tables x y w)
    simpa using scan
  · omega

private def genericFunctionalDependenceLookupCosted
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.allListCosted (List.range thingCount) fun x =>
    Complexity.Costed.implies
      (Complexity.Costed.andThen
        (.tick (tables.binaryLookup "inst" x x' w) 1)
        (fun _ => .tick (tables.binaryLookup "functionsAs" x x' w) 1))
      (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
        Complexity.Costed.andThen
          (.tick (y != x) 1)
          (fun _ => Complexity.Costed.andThen
            (.tick (tables.binaryLookup "inst" y y' w) 1)
            (fun _ => .tick (tables.binaryLookup "functionsAs" y y' w) 1)))

private def genericFunctionalDependenceLookup
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Bool :=
  (genericFunctionalDependenceLookupCosted thingCount tables x' y' w).value

private def individualFunctionalDependenceLookupCosted
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (genericFunctionalDependenceLookupCosted thingCount tables x' y' w)
    (fun _ => Complexity.Costed.andThen
      (.tick (tables.binaryLookup "inst" x x' w) 1)
      (fun _ => Complexity.Costed.andThen
        (.tick (tables.binaryLookup "inst" y y' w) 1)
        (fun _ => Complexity.Costed.implies
          (.tick (tables.binaryLookup "functionsAs" x x' w) 1)
          (fun _ => .tick (tables.binaryLookup "functionsAs" y y' w) 1))))

private def individualFunctionalDependenceLookup
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  (individualFunctionalDependenceLookupCosted thingCount tables x x' y y' w).value

private def componentOfLookupCosted
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (.tick (tables.binaryLookup "properPart" x y w) 1)
    (fun _ => individualFunctionalDependenceLookupCosted thingCount tables x x' y y' w)

private def componentOfLookup
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  (componentOfLookupCosted thingCount tables x x' y y' w).value

private def genericConstitutionalDependenceLookupCosted
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.allListCosted (List.range thingCount) fun x =>
    Complexity.Costed.implies
      (.tick (tables.binaryLookup "inst" x x' w) 1)
      (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
        Complexity.Costed.andThen
          (.tick (tables.binaryLookup "inst" y y' w) 1)
          (fun _ => .tick (tables.binaryLookup "constitutedBy" x y w) 1))

private def genericConstitutionalDependenceLookup
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Bool :=
  (genericConstitutionalDependenceLookupCosted thingCount tables x' y' w).value

private def constitutionLookupCosted
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    Complexity.Costed Bool :=
  Complexity.Costed.andThen
    (.tick (tables.binaryLookup "inst" x x' w) 1)
    (fun _ => Complexity.Costed.andThen
      (.tick (tables.binaryLookup "inst" y y' w) 1)
      (fun _ => Complexity.Costed.andThen
        (genericConstitutionalDependenceLookupCosted thingCount tables x' y' w)
        (fun _ => .tick (tables.binaryLookup "constitutedBy" x y w) 1)))

private def constitutionLookup
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) : Bool :=
  (constitutionLookupCosted thingCount tables x x' y y' w).value

private def quaIndividualLookupCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed Bool :=
  Complexity.anyListCosted (List.range thingCount) fun y =>
    .tick (tables.binaryLookup "quaIndividualOf" x y w) 1

private def quaIndividualLookup
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (quaIndividualLookupCosted thingCount tables x w).value

private def assertedDerivedPropLookupCosted
    (tables : FactTables) (target : String) : Complexity.Costed Bool :=
  Complexity.anyListCosted tables.derivedProps.toList fun prop =>
    .tick (prop == target) 1

private theorem genericFunctionalDependenceLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    (genericFunctionalDependenceLookupCosted thingCount tables x' y' w).cost ≤
      thingCount * (7 * thingCount + 7) := by
  unfold genericFunctionalDependenceLookupCosted
  have h := Complexity.allListCosted_cost_le (List.range thingCount)
    (fun x => Complexity.Costed.implies
      (Complexity.Costed.andThen
        (.tick (tables.binaryLookup "inst" x x' w) 1)
        (fun _ => .tick (tables.binaryLookup "functionsAs" x x' w) 1))
      (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
        Complexity.Costed.andThen (.tick (y != x) 1) (fun _ =>
          Complexity.Costed.andThen
            (.tick (tables.binaryLookup "inst" y y' w) 1)
            (fun _ => .tick (tables.binaryLookup "functionsAs" y y' w) 1))))
    (7 * thingCount + 5) (by
      intro x hx
      refine le_trans
        (Complexity.Costed.implies_cost_le _ _ 3 (7 * thingCount) ?_ ?_) ?_
      · exact Complexity.Costed.andThen_cost_le _ _ 1 1 (by simp) (by simp)
      · have hscan := Complexity.anyListCosted_cost_le (List.range thingCount)
          (fun y => Complexity.Costed.andThen (.tick (y != x) 1) (fun _ =>
            Complexity.Costed.andThen
              (.tick (tables.binaryLookup "inst" y y' w) 1)
              (fun _ => .tick (tables.binaryLookup "functionsAs" y y' w) 1)))
          5 (by
            intro y hy
            refine Complexity.Costed.andThen_cost_le _ _ 1 3 (by simp) ?_
            exact Complexity.Costed.andThen_cost_le _ _ 1 1 (by simp) (by simp))
        simpa [Nat.mul_comm] using hscan
      · omega)
  have hadd : 7 * thingCount + 5 + 2 = 7 * thingCount + 7 := by omega
  simpa only [List.length_range, hadd] using h

private theorem genericConstitutionalDependenceLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) :
    (genericConstitutionalDependenceLookupCosted thingCount tables x' y' w).cost ≤
      thingCount * (5 * thingCount + 5) := by
  unfold genericConstitutionalDependenceLookupCosted
  have h := Complexity.allListCosted_cost_le (List.range thingCount)
    (fun x => Complexity.Costed.implies
      (.tick (tables.binaryLookup "inst" x x' w) 1)
      (fun _ => Complexity.anyListCosted (List.range thingCount) fun y =>
        Complexity.Costed.andThen
          (.tick (tables.binaryLookup "inst" y y' w) 1)
          (fun _ => .tick (tables.binaryLookup "constitutedBy" x y w) 1)))
    (5 * thingCount + 3) (by
      intro x hx
      refine le_trans
        (Complexity.Costed.implies_cost_le _ _ 1 (5 * thingCount) (by simp) ?_) ?_
      · have hscan := Complexity.anyListCosted_cost_le (List.range thingCount)
          (fun y => Complexity.Costed.andThen
            (.tick (tables.binaryLookup "inst" y y' w) 1)
            (fun _ => .tick (tables.binaryLookup "constitutedBy" x y w) 1))
          3 (by
            intro y hy
            exact Complexity.Costed.andThen_cost_le _ _ 1 1 (by simp) (by simp))
        simpa [Nat.mul_comm] using hscan
      · omega)
  have hadd : 5 * thingCount + 3 + 2 = 5 * thingCount + 5 := by omega
  simpa only [List.length_range, hadd] using h

private theorem quaIndividualLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (quaIndividualLookupCosted thingCount tables x w).cost ≤ 3 * thingCount := by
  unfold quaIndividualLookupCosted
  have h := Complexity.anyListCosted_cost_le (List.range thingCount)
    (fun y => Complexity.Costed.tick (tables.binaryLookup "quaIndividualOf" x y w) 1)
    1 (by intro y hy; simp)
  simpa [Nat.mul_comm] using h

private theorem assertedDerivedPropLookupCosted_cost_le
    (tables : FactTables) (target : String) :
    (assertedDerivedPropLookupCosted tables target).cost ≤
      3 * tables.derivedProps.size := by
  unfold assertedDerivedPropLookupCosted
  have h := Complexity.anyListCosted_cost_le tables.derivedProps.toList
    (fun prop => Complexity.Costed.tick (prop == target) 1) 1
    (by intro prop hp; simp)
  simpa [Nat.mul_comm] using h

private theorem individualFunctionalDependenceLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    (individualFunctionalDependenceLookupCosted thingCount tables x x' y y' w).cost ≤
      thingCount * (7 * thingCount + 7) + 9 := by
  unfold individualFunctionalDependenceLookupCosted
  refine le_trans (Complexity.Costed.andThen_cost_le _ _
    (thingCount * (7 * thingCount + 7)) 8 ?_ ?_) ?_
  · exact genericFunctionalDependenceLookupCosted_cost_le thingCount tables x' y' w
  · refine Complexity.Costed.andThen_cost_le _ _ 1 6 (by simp) ?_
    refine Complexity.Costed.andThen_cost_le _ _ 1 4 (by simp) ?_
    exact Complexity.Costed.implies_cost_le _ _ 1 1 (by simp) (by simp)
  · omega

private theorem componentOfLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    (componentOfLookupCosted thingCount tables x x' y y' w).cost ≤
      thingCount * (7 * thingCount + 7) + 11 := by
  unfold componentOfLookupCosted
  refine le_trans (Complexity.Costed.andThen_cost_le _ _ 1
    (thingCount * (7 * thingCount + 7) + 9) (by simp) ?_) ?_
  · exact individualFunctionalDependenceLookupCosted_cost_le
      thingCount tables x x' y y' w
  · omega

private theorem constitutionLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x x' y y' w : Nat) :
    (constitutionLookupCosted thingCount tables x x' y y' w).cost ≤
      thingCount * (5 * thingCount + 5) + 6 := by
  unfold constitutionLookupCosted
  refine le_trans (Complexity.Costed.andThen_cost_le _ _ 1
    (thingCount * (5 * thingCount + 5) + 4) (by simp) ?_) ?_
  · refine le_trans (Complexity.Costed.andThen_cost_le _ _ 1
      (thingCount * (5 * thingCount + 5) + 2) (by simp) ?_) ?_
    · refine Complexity.Costed.andThen_cost_le _ _
        (thingCount * (5 * thingCount + 5)) 1 ?_ (by simp)
      exact genericConstitutionalDependenceLookupCosted_cost_le
        thingCount tables x' y' w
    · omega
  · omega

/-- One explicit bound that covers every derived-predicate implementation.
It is a sum of the concrete component bounds, rather than a postulated maximum;
this keeps each source of work visible for the later formula theorem. -/
private def derivedLookupCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  (thingCount *
      (6 * worldCount + thingCount * (12 * worldCount + 6) + 3) + 2) +
    (12 * worldCount + 3) +
    (6 * worldCount + thingCount * (12 * worldCount + 6) + 1) +
    thingCount * (7 * thingCount + 7) +
    thingCount * (5 * thingCount + 5) +
    3 * thingCount + 3 * tables.derivedProps.size

private def derivedUnaryLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) :
    Complexity.Costed Bool :=
  match field with
  | "ExternallyDependentMode" =>
      externallyDependentModeLookupCosted worldCount thingCount tables x w
  | "QuaIndividual" => quaIndividualLookupCosted thingCount tables x w
  | _ =>
      assertedDerivedPropLookupCosted tables
        s!"sig.{field} {diagFinThingTerm x} {diagFinWorldTerm w}"

private def derivedUnaryLookup
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) : Bool :=
  (derivedUnaryLookupCosted worldCount thingCount tables field x w).value

private def derivedBinaryLookupCosted
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x y w : Nat) :
    Complexity.Costed Bool :=
  match field with
  | "ExistentialDependence" => existentialDependenceLookupCosted worldCount tables x y
  | "ExistentialIndependence" => existentialIndependenceLookupCosted worldCount tables x y
  | "ExternallyDependent" =>
      externallyDependentLookupCosted worldCount thingCount tables x y w
  | "GenericFunctionalDependence" =>
      genericFunctionalDependenceLookupCosted thingCount tables x y w
  | "GenericConstitutionalDependence" =>
      genericConstitutionalDependenceLookupCosted thingCount tables x y w
  | _ =>
      assertedDerivedPropLookupCosted tables
        s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}"

private def derivedBinaryLookup
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  (derivedBinaryLookupCosted worldCount thingCount tables field x y w).value

private theorem derivedUnaryLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (field : String) (x w : Nat) :
    (derivedUnaryLookupCosted worldCount thingCount tables field x w).cost ≤
      derivedLookupCostBound worldCount thingCount tables := by
  unfold derivedUnaryLookupCosted
  split
  · have h := externallyDependentModeLookupCosted_cost_le
      worldCount thingCount tables x w
    unfold derivedLookupCostBound
    omega
  · have h := quaIndividualLookupCosted_cost_le thingCount tables x w
    unfold derivedLookupCostBound
    omega
  · have h := assertedDerivedPropLookupCosted_cost_le tables
      s!"sig.{field} {diagFinThingTerm x} {diagFinWorldTerm w}"
    unfold derivedLookupCostBound
    omega

private theorem derivedBinaryLookupCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (field : String) (x y w : Nat) :
    (derivedBinaryLookupCosted worldCount thingCount tables field x y w).cost ≤
      derivedLookupCostBound worldCount thingCount tables := by
  unfold derivedBinaryLookupCosted
  split
  · have h : (existentialDependenceLookupCosted worldCount tables x y).cost ≤
        6 * worldCount := by
      simpa [existentialDependenceLookupCosted] using
        boxExImpLookupCosted_cost_le worldCount tables x y
    unfold derivedLookupCostBound
    omega
  · have h := existentialIndependenceLookupCosted_cost_le worldCount tables x y
    unfold derivedLookupCostBound
    omega
  · have h := externallyDependentLookupCosted_cost_le
      worldCount thingCount tables x y w
    unfold derivedLookupCostBound
    omega
  · have h := genericFunctionalDependenceLookupCosted_cost_le
      thingCount tables x y w
    unfold derivedLookupCostBound
    omega
  · have h := genericConstitutionalDependenceLookupCosted_cost_le
      thingCount tables x y w
    unfold derivedLookupCostBound
    omega
  · have h := assertedDerivedPropLookupCosted_cost_le tables
      s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}"
    unfold derivedLookupCostBound
    omega

private def assertedDerivedBinaryLookup
    (tables : FactTables) (field : String) (x y w : Nat) : Bool :=
  tables.derivedProps.any fun prop =>
    prop == s!"sig.{field} {diagFinThingTerm x} {diagFinThingTerm y} {diagFinWorldTerm w}"

private def evalDiagAtomCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagAtom → Complexity.Costed Bool
  | .typeSem thing _world =>
      lookupVarCosted env thing >>= fun thingIdx =>
        hasPossibleInstanceCosted worldCount thingCount tables thingIdx
  | .individualSem thing _world =>
      lookupVarCosted env thing >>= fun thingIdx =>
        Complexity.Costed.not <|
          hasPossibleInstanceCosted worldCount thingCount tables thingIdx
  | .unary field thing world =>
      lookupVarCosted env thing >>= fun thingIdx =>
      lookupVarCosted env world >>= fun worldIdx =>
        .tick (tables.unaryLookup field.toTableField thingIdx worldIdx) 1
  | .derivedUnary field thing world =>
      lookupVarCosted env thing >>= fun thingIdx =>
      lookupVarCosted env world >>= fun worldIdx =>
        derivedUnaryLookupCosted worldCount thingCount tables field thingIdx worldIdx
  | .binary (.part) left right world =>
      lookupVarCosted env left >>= fun leftIdx =>
      lookupVarCosted env right >>= fun rightIdx =>
        Complexity.Costed.orElse
          (.tick (leftIdx == rightIdx) 1)
          (fun _ => lookupVarCosted env world >>= fun worldIdx =>
            .tick (tables.binaryLookup "part" leftIdx rightIdx worldIdx) 1)
  | .binary (.overlap) left right world =>
      lookupVarCosted env left >>= fun leftIdx =>
      lookupVarCosted env right >>= fun rightIdx =>
        Complexity.Costed.orElse
          (.tick (leftIdx == rightIdx) 1)
          (fun _ => lookupVarCosted env world >>= fun worldIdx =>
            .tick (tables.binaryLookup "overlap" leftIdx rightIdx worldIdx) 1)
  | .binary field left right world =>
      lookupVarCosted env left >>= fun leftIdx =>
      lookupVarCosted env right >>= fun rightIdx =>
      lookupVarCosted env world >>= fun worldIdx =>
        .tick (tables.binaryLookup field.toTableField leftIdx rightIdx worldIdx) 1
  | .ternary field first second third world =>
      lookupVarCosted env first >>= fun firstIdx =>
      lookupVarCosted env second >>= fun secondIdx =>
      lookupVarCosted env third >>= fun thirdIdx =>
      lookupVarCosted env world >>= fun worldIdx =>
        .tick (tables.ternaryLookup field.toTableField firstIdx secondIdx thirdIdx worldIdx) 1
  | .derivedBinary field left right world =>
      lookupVarCosted env left >>= fun leftIdx =>
      lookupVarCosted env right >>= fun rightIdx =>
      lookupVarCosted env world >>= fun worldIdx =>
        derivedBinaryLookupCosted worldCount thingCount tables field leftIdx rightIdx worldIdx
  | .quaternary field first second third fourth world =>
      lookupVarCosted env first >>= fun firstIdx =>
      lookupVarCosted env second >>= fun secondIdx =>
      lookupVarCosted env third >>= fun thirdIdx =>
      lookupVarCosted env fourth >>= fun fourthIdx =>
      lookupVarCosted env world >>= fun worldIdx =>
        assertedDerivedPropLookupCosted tables
          s!"sig.{field} {diagFinThingTerm firstIdx} {diagFinThingTerm secondIdx} {diagFinThingTerm thirdIdx} {diagFinThingTerm fourthIdx} {diagFinWorldTerm worldIdx}"

private def evalDiagAtom
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (atom : DiagAtom) : Bool :=
  (evalDiagAtomCosted worldCount thingCount tables env atom).value

/-- Concrete worst-case cost of one diagnostic atom. The terms expose variable
lookup, possible-instance search, and derived-predicate evaluation separately;
the constant covers the remaining dense-table and Boolean operations. -/
private def diagAtomCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (envSize : Nat) : Nat :=
  10 * envSize +
    worldCount * (thingCount * 3 + 2) +
    derivedLookupCostBound worldCount thingCount tables + 10

private theorem evalDiagAtomCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤
      diagAtomCostBound worldCount thingCount tables env.size := by
  cases atom with
  | typeSem thing world =>
      change (lookupVarCosted env thing).cost +
          (hasPossibleInstanceCosted worldCount thingCount tables
            (lookupVarCosted env thing).value).cost ≤ _
      rw [lookupVarCosted_cost]
      have h := hasPossibleInstanceCosted_cost_le worldCount thingCount tables
        (lookupVarCosted env thing).value
      unfold diagAtomCostBound
      omega
  | individualSem thing world =>
      change (lookupVarCosted env thing).cost +
          (hasPossibleInstanceCosted worldCount thingCount tables
            (lookupVarCosted env thing).value).cost + 1 ≤ _
      rw [lookupVarCosted_cost]
      have h := hasPossibleInstanceCosted_cost_le worldCount thingCount tables
        (lookupVarCosted env thing).value
      unfold diagAtomCostBound
      omega
  | unary field thing world =>
      change (lookupVarCosted env thing).cost +
          (lookupVarCosted env world).cost + 1 ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost]
      unfold diagAtomCostBound
      omega
  | derivedUnary field thing world =>
      change (lookupVarCosted env thing).cost +
          ((lookupVarCosted env world).cost +
            (derivedUnaryLookupCosted worldCount thingCount tables field
              (lookupVarCosted env thing).value (lookupVarCosted env world).value).cost) ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost]
      have h := derivedUnaryLookupCosted_cost_le worldCount thingCount tables field
        (lookupVarCosted env thing).value (lookupVarCosted env world).value
      unfold diagAtomCostBound
      omega
  | binary field left right world =>
      have special (relation : String) :
          (do
            let leftIdx ← lookupVarCosted env left
            let rightIdx ← lookupVarCosted env right
            Complexity.Costed.orElse
              (.tick (leftIdx == rightIdx) 1)
              (fun _ => lookupVarCosted env world >>= fun worldIdx =>
                .tick (tables.binaryLookup relation leftIdx rightIdx worldIdx) 1)).cost ≤
            diagAtomCostBound worldCount thingCount tables env.size := by
        change (lookupVarCosted env left).cost +
            ((lookupVarCosted env right).cost +
              (Complexity.Costed.orElse _ _).cost) ≤ _
        have hr : (do
            let worldIdx ← lookupVarCosted env world
            Complexity.Costed.tick
              (tables.binaryLookup relation (lookupVarCosted env left).value
                (lookupVarCosted env right).value worldIdx) 1).cost ≤
              2 * env.size + 2 := by
          change (lookupVarCosted env world).cost + 1 ≤ _
          rw [lookupVarCosted_cost]
        have hor := Complexity.Costed.orElse_cost_le
          (Complexity.Costed.tick
            ((lookupVarCosted env left).value == (lookupVarCosted env right).value) 1)
          (fun _ => do
            let worldIdx ← lookupVarCosted env world
            Complexity.Costed.tick
              (tables.binaryLookup relation (lookupVarCosted env left).value
                (lookupVarCosted env right).value worldIdx) 1)
          1 (2 * env.size + 2) (by simp) hr
        rw [lookupVarCosted_cost, lookupVarCosted_cost]
        unfold diagAtomCostBound
        omega
      cases field <;> simp only [evalDiagAtomCosted]
      case part => exact special "part"
      case overlap => exact special "overlap"
      all_goals
        change (lookupVarCosted env left).cost +
            ((lookupVarCosted env right).cost +
              ((lookupVarCosted env world).cost + 1)) ≤ _
        rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost]
        unfold diagAtomCostBound
        omega
  | ternary field first second third world =>
      change (lookupVarCosted env first).cost +
          ((lookupVarCosted env second).cost +
            ((lookupVarCosted env third).cost +
              ((lookupVarCosted env world).cost + 1))) ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost,
        lookupVarCosted_cost]
      unfold diagAtomCostBound
      omega
  | derivedBinary field left right world =>
      change (lookupVarCosted env left).cost +
          ((lookupVarCosted env right).cost +
            ((lookupVarCosted env world).cost +
              (derivedBinaryLookupCosted worldCount thingCount tables field
                (lookupVarCosted env left).value (lookupVarCosted env right).value
                (lookupVarCosted env world).value).cost)) ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost]
      have h := derivedBinaryLookupCosted_cost_le worldCount thingCount tables field
        (lookupVarCosted env left).value (lookupVarCosted env right).value
        (lookupVarCosted env world).value
      unfold diagAtomCostBound
      omega
  | quaternary field first second third fourth world =>
      change (lookupVarCosted env first).cost +
          ((lookupVarCosted env second).cost +
            ((lookupVarCosted env third).cost +
              ((lookupVarCosted env fourth).cost +
                ((lookupVarCosted env world).cost +
                  (assertedDerivedPropLookupCosted tables _).cost)))) ≤ _
      rw [lookupVarCosted_cost, lookupVarCosted_cost, lookupVarCosted_cost,
        lookupVarCosted_cost, lookupVarCosted_cost]
      have h := assertedDerivedPropLookupCosted_cost_le tables
        s!"sig.{field} {diagFinThingTerm (lookupVarCosted env first).value} {diagFinThingTerm (lookupVarCosted env second).value} {diagFinThingTerm (lookupVarCosted env third).value} {diagFinThingTerm (lookupVarCosted env fourth).value} {diagFinWorldTerm (lookupVarCosted env world).value}"
      unfold diagAtomCostBound derivedLookupCostBound
      omega

@[simp] private theorem evalDiagAtomCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (evalDiagAtomCosted worldCount thingCount tables env atom).value =
      evalDiagAtom worldCount thingCount tables env atom := rfl

private def evalDiagFormulaCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → Complexity.Costed Bool
  | .atom atom => evalDiagAtomCosted worldCount thingCount tables env atom
  | .eqThing left right | .eqWorld left right =>
      lookupVarCosted env left >>= fun leftIdx =>
      lookupVarCosted env right >>= fun rightIdx =>
        .tick (leftIdx == rightIdx) 1
  | .not p =>
      Complexity.Costed.not <| evalDiagFormulaCosted worldCount thingCount tables env p
  | .and p q =>
      Complexity.Costed.andThen
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .or p q =>
      Complexity.Costed.orElse
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .imp p q =>
      Complexity.Costed.implies
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .iff p q =>
      Complexity.Costed.iff
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
  | .forallThing name body =>
      Complexity.allListCosted (List.range thingCount) fun x =>
        Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body
  | .forallWorld name body =>
      Complexity.allListCosted (List.range worldCount) fun w =>
        Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body
  | .existsThing name body =>
      Complexity.anyListCosted (List.range thingCount) fun x =>
        Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body
  | .existsWorld name body =>
      Complexity.anyListCosted (List.range worldCount) fun w =>
        Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body
  | .box _currentWorld witnessWorld body =>
      Complexity.allListCosted (List.range worldCount) fun w =>
        Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables
            (env.push (witnessWorld, w)) body
  | .dia _currentWorld witnessWorld body =>
      Complexity.anyListCosted (List.range worldCount) fun w =>
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
  | .atom _ => atomBound envSize
  | .eqThing _ _ | .eqWorld _ _ => 4 * envSize + 3
  | .not p => p.evalCostBound worldCount thingCount atomBound envSize + 1
  | .and p q | .or p q =>
      p.evalCostBound worldCount thingCount atomBound envSize +
        q.evalCostBound worldCount thingCount atomBound envSize + 1
  | .imp p q | .iff p q =>
      p.evalCostBound worldCount thingCount atomBound envSize +
        q.evalCostBound worldCount thingCount atomBound envSize + 2
  | .forallThing _ body | .existsThing _ body =>
      thingCount * (body.evalCostBound worldCount thingCount atomBound (envSize + 1) + 3)
  | .forallWorld _ body | .existsWorld _ body | .box _ _ body | .dia _ _ body =>
      worldCount * (body.evalCostBound worldCount thingCount atomBound (envSize + 1) + 3)

private theorem evalDiagFormulaCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (atomBound : Nat → Nat)
    (hAtom : ∀ (env : Array (String × Nat)) (atom : DiagAtom),
      (evalDiagAtomCosted worldCount thingCount tables env atom).cost ≤ atomBound env.size)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (evalDiagFormulaCosted worldCount thingCount tables env formula).cost ≤
      formula.evalCostBound worldCount thingCount atomBound env.size := by
  induction formula generalizing env with
  | atom atom => simpa [evalDiagFormulaCosted, DiagFormula.evalCostBound] using hAtom env atom
  | eqThing left right | eqWorld left right =>
      change (lookupVarCosted env left).cost +
          (lookupVarCosted env right).cost + 1 ≤ 4 * env.size + 3
      rw [lookupVarCosted_cost, lookupVarCosted_cost]
      omega
  | not p ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound,
        Complexity.Costed.not_cost]
      exact Nat.add_le_add_right (ih env) 1
  | and p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.Costed.andThen_cost_le
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
        (p.evalCostBound worldCount thingCount atomBound env.size)
        (q.evalCostBound worldCount thingCount atomBound env.size)
        (ihp env) (ihq env)
      omega
  | or p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.Costed.orElse_cost_le
        (evalDiagFormulaCosted worldCount thingCount tables env p)
        (fun _ => evalDiagFormulaCosted worldCount thingCount tables env q)
        (p.evalCostBound worldCount thingCount atomBound env.size)
        (q.evalCostBound worldCount thingCount atomBound env.size)
        (ihp env) (ihq env)
      omega
  | imp p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      exact Complexity.Costed.implies_cost_le _ _ _ _ (ihp env) (ihq env)
  | iff p q ihp ihq =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      exact Complexity.Costed.iff_cost_le _ _ _ _ (ihp env) (ihq env)
  | forallThing name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.allListCosted_cost_le (List.range thingCount)
        (fun x => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro x hx
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, x))
          simp only [Array.size_push] at hbody
          omega)
      simpa [Nat.add_assoc] using h
  | existsThing name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.anyListCosted_cost_le (List.range thingCount)
        (fun x => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, x)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro x hx
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, x))
          simp only [Array.size_push] at hbody
          omega)
      simpa [Nat.add_assoc] using h
  | forallWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.allListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simpa [Nat.add_assoc] using h
  | existsWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.anyListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simpa [Nat.add_assoc] using h
  | box currentWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.allListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simpa [Nat.add_assoc] using h
  | dia currentWorld name body ih =>
      simp only [evalDiagFormulaCosted, DiagFormula.evalCostBound]
      have h := Complexity.anyListCosted_cost_le (List.range worldCount)
        (fun w => Complexity.Costed.charge 1 <|
          evalDiagFormulaCosted worldCount thingCount tables (env.push (name, w)) body)
        (body.evalCostBound worldCount thingCount atomBound (env.size + 1) + 1) (by
          intro w hw
          simp only [Complexity.Costed.charge_cost]
          have hbody := ih (env.push (name, w))
          simp only [Array.size_push] at hbody
          omega)
      simpa [Nat.add_assoc] using h

/-- Fully instantiated evaluator bound: unlike the compositional helper above,
this statement has no assumed atomic-cost oracle. Every term is determined by
the formula, explicit model dimensions, environment size, and compiled tables. -/
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

/--
Visit quantified environments in the same lexicographic order as the former
array-expansion implementation, but without constructing the full Cartesian
product first.  The caller's `stop` predicate is checked before descending and
between siblings, so an evidence budget also bounds assignment generation once
enough output has been produced.
-/
private def foldDiagDomainCosted
    (domain : List Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) : Complexity.Costed σ :=
  match domain with
  | [] => .pure state
  | List.cons i rest =>
      if stop state then
        -- The executable traversal retains the loop iteration after the output
        -- budget is reached, but does not descend or allocate an environment.
        Complexity.Costed.charge 2 (foldDiagDomainCosted rest state stop visit)
      else
        let child := visit state i
        let tail := foldDiagDomainCosted rest child.value stop visit
        ⟨tail.value, child.cost + 3 + tail.cost⟩

private def foldDiagVarsCosted
    (worldCount thingCount : Nat) (vars : List DiagVar)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ) :
    Complexity.Costed σ :=
  if stop state then
    -- One budget/stop comparison.
    ⟨state, 1⟩
  else
    match vars with
    | [] =>
        -- Charge the successful stop test and the end-of-variable lookup.
        Complexity.Costed.charge 2 (visit state env)
    | List.cons var rest =>
        let bound :=
          match var.kind with
          | .thing => thingCount
          | .world => worldCount
        -- Stop test, variable lookup, and bound selection are charged once;
        -- each domain item then follows the original left-to-right traversal.
        Complexity.Costed.charge 3 <|
          foldDiagDomainCosted (List.range bound) state stop fun state i =>
            foldDiagVarsCosted worldCount thingCount rest
              (env.push (var.name, i)) state stop visit

private def foldDiagEnvsUntilCosted
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ)
    (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ) :
    Complexity.Costed σ :=
  foldDiagVarsCosted worldCount thingCount (vars.toList.drop index)
    env state stop visit

private theorem foldDiagDomainCosted_cost_le
    (domain : List Nat) (state : σ) (stop : σ → Bool)
    (visit : σ → Nat → Complexity.Costed σ) (perItem : Nat)
    (hVisit : ∀ state i, i ∈ domain → (visit state i).cost ≤ perItem) :
    (foldDiagDomainCosted domain state stop visit).cost ≤
      domain.length * (perItem + 3) := by
  induction domain generalizing state with
  | nil => simp [foldDiagDomainCosted]
  | cons i rest ih =>
      rw [foldDiagDomainCosted]
      split
      · simp only [Complexity.Costed.charge_cost]
        have htail := ih state (by
          intro state' j hj
          exact hVisit state' j (by simp [hj]))
        simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega
      · change (visit state i).cost + 3 +
            (foldDiagDomainCosted rest (visit state i).value stop visit).cost ≤ _
        have hhead := hVisit state i (by simp)
        have htail := ih (visit state i).value (by
          intro state' j hj
          exact hVisit state' j (by simp [hj]))
        simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega

private def DiagVar.domainSize (worldCount thingCount : Nat) (var : DiagVar) : Nat :=
  match var.kind with
  | .thing => thingCount
  | .world => worldCount

/-- Cost recurrence for the executable environment traversal. It preserves the
individual domain size of every quantified variable instead of replacing the
Cartesian product with a single largest-domain envelope. -/
private def diagEnvFoldCostBound
    (worldCount thingCount visitBound : Nat) : List DiagVar → Nat
  | [] => visitBound + 2
  | List.cons var rest =>
      3 + var.domainSize worldCount thingCount *
        (diagEnvFoldCostBound worldCount thingCount visitBound rest + 3)

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
          (List.range (var.domainSize worldCount thingCount)) state stop
          (fun state i => foldDiagVarsCosted worldCount thingCount rest
            (env.push (var.name, i)) state stop visit)
          (diagEnvFoldCostBound worldCount thingCount visitBound rest) (by
            intro state' i hi
            exact ih (env.push (var.name, i)) state')
        simpa [DiagVar.domainSize] using Nat.add_le_add_left hdomain 3

private theorem foldDiagEnvsUntilCosted_cost_le
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ)
    (visitBound : Nat)
    (hVisit : ∀ state env, (visit state env).cost ≤ visitBound) :
    (foldDiagEnvsUntilCosted worldCount thingCount vars index env state stop visit).cost ≤
      diagEnvFoldCostBound worldCount thingCount visitBound
        (vars.toList.drop index) := by
  exact foldDiagVarsCosted_cost_le worldCount thingCount
    (vars.toList.drop index) env state stop visit visitBound hVisit

/-- Environment-sensitive counterpart of `diagEnvFoldCostBound`. Unlike a
single visit envelope, this recurrence records the one-cell environment
extension performed at each concrete quantifier level. -/
private def diagEnvDependentFoldCostBound
    (worldCount thingCount : Nat) (visitBound : Nat → Nat) :
    Nat → List DiagVar → Nat
  | envSize, [] => visitBound envSize + 2
  | envSize, List.cons var rest =>
      3 + var.domainSize worldCount thingCount *
        (diagEnvDependentFoldCostBound worldCount thingCount visitBound (envSize + 1) rest + 3)

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
          (List.range (var.domainSize worldCount thingCount)) state stop
          (fun state i => foldDiagVarsCosted worldCount thingCount rest
            (env.push (var.name, i)) state stop visit)
          (diagEnvDependentFoldCostBound worldCount thingCount visitBound (env.size + 1) rest) (by
            intro state' i hi
            simpa using ih (env.push (var.name, i)) state')
        simpa [DiagVar.domainSize] using Nat.add_le_add_left hdomain 3

private theorem foldDiagEnvsUntilCosted_dependent_cost_le
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ) (stop : σ → Bool)
    (visit : σ → Array (String × Nat) → Complexity.Costed σ)
    (visitBound : Nat → Nat)
    (hVisit : ∀ state env, (visit state env).cost ≤ visitBound env.size) :
    (foldDiagEnvsUntilCosted worldCount thingCount vars index env state stop visit).cost ≤
      diagEnvDependentFoldCostBound worldCount thingCount visitBound env.size
        (vars.toList.drop index) := by
  exact foldDiagVarsCosted_dependent_cost_le worldCount thingCount
    (vars.toList.drop index) env state stop visit visitBound hVisit

private def foldDiagEnvsUntil
    (worldCount thingCount : Nat) (vars : Array DiagVar) (index : Nat)
    (env : Array (String × Nat)) (state : σ)
    (stop : σ → Bool) (visit : σ → Array (String × Nat) → σ) : σ :=
  (foldDiagEnvsUntilCosted worldCount thingCount vars index env state stop
    (fun state env => ⟨visit state env, 0⟩)).value

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

private def renderDiagAtom
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

private partial def renderDiagFormula
    (worldNames thingNames : Array Name) (env : Array (String × Nat)) : DiagFormula → String
  | .atom atom => renderDiagAtom worldNames thingNames env atom
  | .eqThing left right =>
      s!"{indexedName thingNames (lookupVar env left)} = {indexedName thingNames (lookupVar env right)}"
  | .eqWorld left right =>
      s!"{indexedName worldNames (lookupVar env left)} = {indexedName worldNames (lookupVar env right)}"
  | .not p => s!"not ({renderDiagFormula worldNames thingNames env p})"
  | .and p q => s!"({renderDiagFormula worldNames thingNames env p}) and ({renderDiagFormula worldNames thingNames env q})"
  | .or p q => s!"({renderDiagFormula worldNames thingNames env p}) or ({renderDiagFormula worldNames thingNames env q})"
  | .imp p q => s!"({renderDiagFormula worldNames thingNames env p}) implies ({renderDiagFormula worldNames thingNames env q})"
  | .iff p q => s!"({renderDiagFormula worldNames thingNames env p}) iff ({renderDiagFormula worldNames thingNames env q})"
  | .forallThing name body => s!"for every thing {name}, {renderDiagFormula worldNames thingNames env body}"
  | .forallWorld name body => s!"for every world {name}, {renderDiagFormula worldNames thingNames env body}"
  | .existsThing name body => s!"there exists thing {name}, {renderDiagFormula worldNames thingNames env body}"
  | .existsWorld name body => s!"there exists world {name}, {renderDiagFormula worldNames thingNames env body}"
  | .box currentWorld witnessWorld body =>
      s!"from world {indexedName worldNames (lookupVar env currentWorld)}, in every accessible world {witnessWorld}, {renderDiagFormula worldNames thingNames env body}"
  | .dia currentWorld witnessWorld body =>
      s!"from world {indexedName worldNames (lookupVar env currentWorld)}, in some accessible world {witnessWorld}, {renderDiagFormula worldNames thingNames env body}"

private partial def flattenDiagAndInto
    (out : Array DiagFormula) : DiagFormula → Array DiagFormula
  | .and p q => flattenDiagAndInto (flattenDiagAndInto out p) q
  | p => out.push p

private def flattenDiagAnd (formula : DiagFormula) : Array DiagFormula :=
  flattenDiagAndInto #[] formula

private partial def flattenDiagOrInto
    (out : Array DiagFormula) : DiagFormula → Array DiagFormula
  | .or p q => flattenDiagOrInto (flattenDiagOrInto out p) q
  | p => out.push p

private def flattenDiagOr (formula : DiagFormula) : Array DiagFormula :=
  flattenDiagOrInto #[] formula

private def formulaHasDistinctnessRequirement : DiagFormula → Bool
  | .not (.eqThing _ _) => true
  | .not (.eqWorld _ _) => true
  | _ => false

private def diagnosticConditionLabel (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ => "Need one of"
  | .not _ => "Forbidden condition"
  | .atom _ => "Required but missing"
  | .eqThing _ _ => "Required but missing"
  | .eqWorld _ _ => "Required but missing"
  | .and _ _ =>
      if (flattenDiagAnd formula).any formulaHasDistinctnessRequirement then
        "Missing witness requirements"
      else
        "Required together"
  | .existsThing _ _ => "Missing witness requirements"
  | .existsWorld _ _ => "Missing witness requirements"
  | _ => "Failed condition"

private def renderDiagnosticCondition
    (worldNames thingNames : Array Name) (env : Array (String × Nat))
    (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ =>
      String.intercalate "\n" <|
        (flattenDiagOr formula).toList.map fun option =>
          s!"- {renderDiagFormula worldNames thingNames env option}"
  | .and _ _ =>
      String.intercalate "\n" <|
        (flattenDiagAnd formula).toList.map fun requirement =>
          s!"- {renderDiagFormula worldNames thingNames env requirement}"
  | _ => renderDiagFormula worldNames thingNames env formula

private def envSummary
    (worldNames thingNames : Array Name) (vars : Array DiagVar) (env : Array (String × Nat)) :
    String :=
  String.intercalate ", " <| vars.toList.map fun var =>
    let idx := lookupVar env var.name
    match var.kind with
    | .thing => s!"{var.name} = {indexedName thingNames idx}"
    | .world => s!"{var.name} = {indexedName worldNames idx}"

private def envVarKind? (outerVars : Array DiagVar) (name : String) : Option DiagVarKind :=
  outerVars.findSome? fun var =>
    if var.name == name then some var.kind else none

private partial def formulaBoundVarKindsInto
    (out : Array DiagVar) (formula : DiagFormula) : Array DiagVar :=
  match formula with
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => out
  | .not p => formulaBoundVarKindsInto out p
  | .and p q | .or p q | .imp p q | .iff p q =>
      formulaBoundVarKindsInto (formulaBoundVarKindsInto out p) q
  | .forallThing name body | .existsThing name body =>
      formulaBoundVarKindsInto (out.push ⟨name, .thing⟩) body
  | .forallWorld name body | .existsWorld name body =>
      formulaBoundVarKindsInto (out.push ⟨name, .world⟩) body
  | .box _ witnessWorld body | .dia _ witnessWorld body =>
      formulaBoundVarKindsInto (out.push ⟨witnessWorld, .world⟩) body

private def formulaBoundVarKinds (formula : DiagFormula) : Array DiagVar :=
  formulaBoundVarKindsInto #[] formula

private def diagnosticEnvVarsInto
    (candidates : Array DiagVar) (seen : Std.HashSet String)
    (out : Array DiagVar) (entries : List (String × Nat)) : Array DiagVar :=
  match entries with
  | List.nil => out
  | List.cons entry rest =>
      let name := entry.1
      if seen.contains name then
        diagnosticEnvVarsInto candidates seen out rest
      else
        match envVarKind? candidates name with
        | some kind =>
            diagnosticEnvVarsInto candidates (seen.insert name) (out.push ⟨name, kind⟩) rest
        | none => diagnosticEnvVarsInto candidates seen out rest

private def diagnosticEnvVars (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) : Array DiagVar :=
  diagnosticEnvVarsInto (outerVars ++ formulaBoundVarKinds formula) {} #[] env.toList

private theorem diagnosticEnvVarsInto_size_le
    (candidates : Array DiagVar) (seen : Std.HashSet String)
    (out : Array DiagVar) (entries : List (String × Nat)) :
    (diagnosticEnvVarsInto candidates seen out entries).size ≤ out.size + entries.length := by
  induction entries generalizing seen out with
  | nil => simp [diagnosticEnvVarsInto]
  | cons entry rest ih =>
      simp only [diagnosticEnvVarsInto, List.length_cons]
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

private theorem diagnosticEnvVars_size_le
    (outerVars : Array DiagVar) (formula : DiagFormula)
    (env : Array (String × Nat)) :
    (diagnosticEnvVars outerVars formula env).size ≤ env.size := by
  unfold diagnosticEnvVars
  simpa using diagnosticEnvVarsInto_size_le
    (outerVars ++ formulaBoundVarKinds formula) {} (#[] : Array DiagVar) env.toList

private def firstMatchingEnvCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (wanted : Bool) : List Nat →
    Complexity.Costed (Option (Array (String × Nat)))
  | [] => ⟨none, 1⟩
  | List.cons i indices =>
      let env' := env.push (name, i)
      let checked := evalDiagFormulaCosted worldCount thingCount tables env' body
      if checked.value == wanted then
        -- Charge the environment extension and result comparison.
        ⟨some env', checked.cost + 2⟩
      else
        let rest := firstMatchingEnvCosted worldCount thingCount tables env kind name
          body wanted indices
        -- The recursive branch performs the same two control operations.
        ⟨rest.value, checked.cost + rest.cost + 2⟩

private theorem firstMatchingEnvCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (wanted : Bool) (indices : List Nat) :
    (firstMatchingEnvCosted worldCount thingCount tables env kind name body
      wanted indices).cost ≤
      indices.length *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 2) + 1 := by
  induction indices with
  | nil => simp [firstMatchingEnvCosted]
  | cons i indices ih =>
      rw [firstMatchingEnvCosted]
      split
      · have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables (env.push (name, i)) body
        simp only [Array.size_push] at hchecked
        simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega
      · have hchecked := evalDiagFormulaCosted_concrete_cost_le
          worldCount thingCount tables (env.push (name, i)) body
        simp only [Array.size_push] at hchecked
        simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega

private theorem firstMatchingEnvCosted_some_size
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (wanted : Bool) (indices : List Nat)
    (env' : Array (String × Nat))
    (hSome : (firstMatchingEnvCosted worldCount thingCount tables env kind name body
      wanted indices).value = some env') :
    env'.size = env.size + 1 := by
  induction indices with
  | nil => simp [firstMatchingEnvCosted] at hSome
  | cons i indices ih =>
      rw [firstMatchingEnvCosted] at hSome
      split at hSome
      · injection hSome with heq
        subst env'
        simp
      · exact ih hSome

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
    firstMatchingEnvCosted worldCount thingCount tables env kind name body false
      (List.range bound)

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
    firstMatchingEnvCosted worldCount thingCount tables env kind name body true
      (List.range bound)

private theorem firstFailureEnvCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 2) + 2 := by
  unfold firstFailureEnvCosted
  simp only [Complexity.Costed.charge_cost]
  have h := firstMatchingEnvCosted_cost_le worldCount thingCount tables env kind
    name body false (List.range (kind.domainSize worldCount thingCount))
  cases kind <;>
    simp only [DiagVarKind.domainSize, List.length_range] at h ⊢ <;>
    omega

private theorem firstSuccessEnvCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) :
    (firstSuccessEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 2) + 2 := by
  unfold firstSuccessEnvCosted
  simp only [Complexity.Costed.charge_cost]
  have h := firstMatchingEnvCosted_cost_le worldCount thingCount tables env kind
    name body true (List.range (kind.domainSize worldCount thingCount))
  cases kind <;>
    simp only [DiagVarKind.domainSize, List.length_range] at h ⊢ <;>
    omega

private theorem firstFailureEnvCosted_cost_le_of_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (kind : DiagVarKind) (name : String)
    (body : DiagFormula) (result : Option (Array (String × Nat)))
    (_hValue : firstFailureEnv worldCount thingCount tables env kind name body = result) :
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost ≤
      kind.domainSize worldCount thingCount *
        (body.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 2) + 2 :=
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
  apply firstMatchingEnvCosted_some_size worldCount thingCount tables env kind name body
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
  apply firstMatchingEnvCosted_some_size worldCount thingCount tables env kind name body
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
          (diagAtomCostBound worldCount thingCount tables) (env.size + 1) + 2) + 2 :=
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

/--
Collect subformulas that succeeded on the current path to a failure.

The rendered diagnostic reports what is missing and why the missing obligation
applied. These traces become the evidence section of the widget. They are
explanatory data, not trusted proof data.
-/
private def successTracesIntoCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace)
    (formula : DiagFormula) : Complexity.Costed (Array DiagTrace) :=
  let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
  if !checked.value then
    ⟨out, checked.cost + 1⟩
  else
    match formula with
    | .atom _ | .eqThing _ _ | .eqWorld _ _ | .not _ =>
        ⟨out.push ⟨formula, env⟩, checked.cost + 2⟩
    | .and p q =>
        let left := successTracesIntoCosted worldCount thingCount tables env out p
        let right := successTracesIntoCosted worldCount thingCount tables env left.value q
        ⟨right.value, checked.cost + left.cost + right.cost + 1⟩
    | .or p q =>
        let leftChecked := evalDiagFormulaCosted worldCount thingCount tables env p
        if leftChecked.value then
          let traces := successTracesIntoCosted worldCount thingCount tables env out p
          ⟨traces.value, checked.cost + leftChecked.cost + traces.cost + 2⟩
        else
          let traces := successTracesIntoCosted worldCount thingCount tables env out q
          ⟨traces.value, checked.cost + leftChecked.cost + traces.cost + 2⟩
    | .imp p q =>
        let antecedent := evalDiagFormulaCosted worldCount thingCount tables env p
        if antecedent.value then
          let traces := successTracesIntoCosted worldCount thingCount tables env out q
          ⟨traces.value, checked.cost + antecedent.cost + traces.cost + 2⟩
        else
          ⟨out.push ⟨formula, env⟩, checked.cost + antecedent.cost + 2⟩
    | .iff _ _ | .forallThing _ _ | .forallWorld _ _ =>
        ⟨out.push ⟨formula, env⟩, checked.cost + 2⟩
    | .existsThing name body =>
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .thing name body
        match witness.value with
        | some env' =>
            let traces := successTracesIntoCosted worldCount thingCount tables env' out body
            ⟨traces.value, checked.cost + witness.cost + traces.cost + 1⟩
        | none => ⟨out.push ⟨formula, env⟩, checked.cost + witness.cost + 2⟩
    | .existsWorld name body =>
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world name body
        match witness.value with
        | some env' =>
            let traces := successTracesIntoCosted worldCount thingCount tables env' out body
            ⟨traces.value, checked.cost + witness.cost + traces.cost + 1⟩
        | none => ⟨out.push ⟨formula, env⟩, checked.cost + witness.cost + 2⟩
    | .box _ _ _ => ⟨out.push ⟨formula, env⟩, checked.cost + 2⟩
    | .dia _ witnessWorld body =>
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world witnessWorld body
        match witness.value with
        | some env' =>
            let traces := successTracesIntoCosted worldCount thingCount tables env' out body
            ⟨traces.value, checked.cost + witness.cost + traces.cost + 1⟩
        | none => ⟨out.push ⟨formula, env⟩, checked.cost + witness.cost + 2⟩

private def successTracesInto
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagTrace)
    (formula : DiagFormula) : Array DiagTrace :=
  (successTracesIntoCosted worldCount thingCount tables env out formula).value

private def successTraces
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Array DiagTrace :=
  successTracesInto worldCount thingCount tables env #[] formula

private def successTracesCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    Complexity.Costed (Array DiagTrace) :=
  successTracesIntoCosted worldCount thingCount tables env #[] formula

private def firstMatchCostBound
    (worldCount thingCount : Nat) (tables : FactTables)
    (kind : DiagVarKind) (envSize : Nat) (body : DiagFormula) : Nat :=
  kind.domainSize worldCount thingCount *
      (body.evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) (envSize + 1) + 2) + 2

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
        (diagAtomCostBound worldCount thingCount tables) envSize + 2
  | formula@(.and p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.successTraceCostBound worldCount thingCount tables envSize + 1
  | formula@(.or p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.successTraceCostBound worldCount thingCount tables envSize + 2
  | formula@(.imp p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        q.successTraceCostBound worldCount thingCount tables envSize + 2
  | formula@(.existsThing _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .thing envSize body +
        body.successTraceCostBound worldCount thingCount tables (envSize + 1) + 2
  | formula@(.existsWorld _ body) | formula@(.dia _ _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .world envSize body +
        body.successTraceCostBound worldCount thingCount tables (envSize + 1) + 2

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
              (successTracesIntoCosted worldCount thingCount tables env out p).value q).cost + 1 ≤ _
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

private def DiagFormula.nodeCount : DiagFormula → Nat
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => 1
  | .not p | .forallThing _ p | .forallWorld _ p | .existsThing _ p |
      .existsWorld _ p | .box _ _ p | .dia _ _ p => p.nodeCount + 1
  | .and p q | .or p q | .imp p q | .iff p q => p.nodeCount + q.nodeCount + 1

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

@[simp] private theorem successTracesCosted_value
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTracesCosted worldCount thingCount tables env formula).value =
      successTraces worldCount thingCount tables env formula := rfl

/--
Find the smallest useful failed subformula for a counterexample environment.

For implications and biconditionals this keeps the successful antecedent/context
beside the failing consequent. For quantifiers and modal boxes it also records
the witness assignment that makes the failure concrete in DSL names.
-/
private def minimizeFailureCosted
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) : DiagFormula → Complexity.Costed MinimizedFailure
  | formula@(.atom _) => ⟨failedHere formula env, 1⟩
  | formula@(.eqThing _ _) => ⟨failedHere formula env, 1⟩
  | formula@(.eqWorld _ _) => ⟨failedHere formula env, 1⟩
  | formula@(.not p) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 1⟩
      else
        match p with
        | .not q =>
            Complexity.Costed.charge (checked.cost + 1) <|
              minimizeFailureCosted worldCount thingCount tables env q
        | .forallThing name body =>
            let witness := firstFailureEnvCosted worldCount thingCount tables env .thing name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
        | .forallWorld name body =>
            let witness := firstFailureEnvCosted worldCount thingCount tables env .world name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
        | .existsThing name body =>
            let witness := firstSuccessEnvCosted worldCount thingCount tables env .thing name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
        | .existsWorld name body =>
            let witness := firstSuccessEnvCosted worldCount thingCount tables env .world name body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
        | .box _ witnessWorld body =>
            let witness := firstFailureEnvCosted worldCount thingCount tables env .world witnessWorld body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
        | .dia _ witnessWorld body =>
            let witness := firstSuccessEnvCosted worldCount thingCount tables env .world witnessWorld body
            match witness.value with
            | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
                minimizeFailureCosted worldCount thingCount tables env' body
            | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
        | _ => ⟨failedHere formula env, checked.cost + 1⟩
  | formula@(.and p q) =>
      let leftChecked := evalDiagFormulaCosted worldCount thingCount tables env p
      if !leftChecked.value then
        Complexity.Costed.charge (leftChecked.cost + 1) <|
          minimizeFailureCosted worldCount thingCount tables env p
      else
        let rightChecked := evalDiagFormulaCosted worldCount thingCount tables env q
        if !rightChecked.value then
          let traces := successTracesCosted worldCount thingCount tables env p
          let failure := minimizeFailureCosted worldCount thingCount tables env q
          ⟨withContext traces.value failure.value,
            leftChecked.cost + rightChecked.cost + traces.cost + failure.cost +
              traces.value.size + 2⟩
        else
          ⟨failedHere formula env, leftChecked.cost + rightChecked.cost + 2⟩
  | formula@(.or p q) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 1⟩
      else
        let pFailure := minimizeFailureCosted worldCount thingCount tables env p
        let qFailure := minimizeFailureCosted worldCount thingCount tables env q
        ⟨{
          formula := .or pFailure.value.formula qFailure.value.formula,
          env := pFailure.value.env ++ qFailure.value.env,
          context := pFailure.value.context ++ qFailure.value.context
        }, checked.cost + pFailure.cost + qFailure.cost +
          pFailure.value.env.size + pFailure.value.context.size + 2⟩
  | formula@(.imp p q) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 1⟩
      else
        let traces := successTracesCosted worldCount thingCount tables env p
        let failure := minimizeFailureCosted worldCount thingCount tables env q
        ⟨withContext traces.value failure.value,
          checked.cost + traces.cost + failure.cost + traces.value.size + 1⟩
  | formula@(.iff p q) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        ⟨failedHere formula env, checked.cost + 1⟩
      else
        let leftChecked := evalDiagFormulaCosted worldCount thingCount tables env p
        if leftChecked.value then
          let traces := successTracesCosted worldCount thingCount tables env p
          let failure := minimizeFailureCosted worldCount thingCount tables env q
          ⟨withContext traces.value failure.value,
            checked.cost + leftChecked.cost + traces.cost + failure.cost +
              traces.value.size + 2⟩
        else
          let rightChecked := evalDiagFormulaCosted worldCount thingCount tables env q
          if rightChecked.value then
            let traces := successTracesCosted worldCount thingCount tables env q
            let failure := minimizeFailureCosted worldCount thingCount tables env p
            ⟨withContext traces.value failure.value,
              checked.cost + leftChecked.cost + rightChecked.cost + traces.cost + failure.cost +
                traces.value.size + 3⟩
          else
            ⟨failedHere formula env, checked.cost + leftChecked.cost + rightChecked.cost + 3⟩
  | formula@(.forallThing name body) =>
      let witness := firstFailureEnvCosted worldCount thingCount tables env .thing name body
      match witness.value with
      | some env' => Complexity.Costed.charge (witness.cost + 1) <|
          minimizeFailureCosted worldCount thingCount tables env' body
      | none => ⟨failedHere formula env, witness.cost + 1⟩
  | formula@(.forallWorld name body) =>
      let witness := firstFailureEnvCosted worldCount thingCount tables env .world name body
      match witness.value with
      | some env' => Complexity.Costed.charge (witness.cost + 1) <|
          minimizeFailureCosted worldCount thingCount tables env' body
      | none => ⟨failedHere formula env, witness.cost + 1⟩
  | formula@(.existsThing name body) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .thing name body
        match witness.value with
        | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
            minimizeFailureCosted worldCount thingCount tables env' body
        | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
      else
        ⟨failedHere formula env, checked.cost + 1⟩
  | formula@(.existsWorld name body) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world name body
        match witness.value with
        | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
            minimizeFailureCosted worldCount thingCount tables env' body
        | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
      else
        ⟨failedHere formula env, checked.cost + 1⟩
  | formula@(.box _ witnessWorld body) =>
      let witness := firstFailureEnvCosted worldCount thingCount tables env .world witnessWorld body
      match witness.value with
      | some env' => Complexity.Costed.charge (witness.cost + 1) <|
          minimizeFailureCosted worldCount thingCount tables env' body
      | none => ⟨failedHere formula env, witness.cost + 1⟩
  | formula@(.dia _ witnessWorld body) =>
      let checked := evalDiagFormulaCosted worldCount thingCount tables env formula
      if checked.value then
        let witness := firstSuccessEnvCosted worldCount thingCount tables env .world witnessWorld body
        match witness.value with
        | some env' => Complexity.Costed.charge (checked.cost + witness.cost + 1) <|
            minimizeFailureCosted worldCount thingCount tables env' body
        | none => ⟨failedHere formula env, checked.cost + witness.cost + 1⟩
      else
        ⟨failedHere formula env, checked.cost + 1⟩

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
      formula.successTraceCostBound worldCount thingCount tables env.size := by
  unfold successTracesCosted
  simpa using successTracesIntoCosted_cost_le
    worldCount thingCount tables env (#[] : Array DiagTrace) formula

private theorem successTraces_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (successTraces worldCount thingCount tables env formula).size ≤ formula.nodeCount := by
  rw [← successTracesCosted_value]
  exact successTracesCosted_size_le worldCount thingCount tables env formula

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
  | .atom _ | .eqThing _ _ | .eqWorld _ _ => 1
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
        | _ => 0) + 2
  | .and p q =>
      p.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        q.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        p.failureMinimizeCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        p.nodeCount + 3
  | formula@(.or p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.failureMinimizeCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        p.failureEnvSizeBound envSize + p.failureContextSizeBound + 2
  | formula@(.imp p q) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        p.successTraceCostBound worldCount thingCount tables envSize +
        q.failureMinimizeCostBound worldCount thingCount tables envSize +
        p.nodeCount + 2
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
        p.nodeCount + q.nodeCount + 4
  | formula@(.forallThing _ body) | formula@(.existsThing _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .thing envSize body +
        body.failureMinimizeCostBound worldCount thingCount tables (envSize + 1) + 2
  | formula@(.forallWorld _ body) | formula@(.existsWorld _ body) |
      formula@(.box _ _ body) | formula@(.dia _ _ body) =>
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) envSize +
        firstMatchCostBound worldCount thingCount tables .world envSize body +
        body.failureMinimizeCostBound worldCount thingCount tables (envSize + 1) + 2

private theorem DiagFormula.not_evalCostBound_add_one_le_failureMinimizeCostBound
    (worldCount thingCount : Nat) (tables : FactTables) (envSize : Nat)
    (p : DiagFormula) :
    (DiagFormula.not p).evalCostBound worldCount thingCount
        (diagAtomCostBound worldCount thingCount tables) envSize + 1 ≤
      (DiagFormula.not p).failureMinimizeCostBound worldCount thingCount tables envSize := by
  cases p <;> simp [failureMinimizeCostBound] <;> omega

private theorem evalDiagFormulaCosted_not_cost_add_one_le_failureMinimizeCostBound
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (p : DiagFormula) :
    (evalDiagFormulaCosted worldCount thingCount tables env (.not p)).cost + 1 ≤
      (DiagFormula.not p).failureMinimizeCostBound
        worldCount thingCount tables env.size := by
  have heval := evalDiagFormulaCosted_concrete_cost_le
    worldCount thingCount tables env (.not p)
  have hstruct := DiagFormula.not_evalCostBound_add_one_le_failureMinimizeCostBound
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
          (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost + 1 +
        (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) env.size +
        firstMatchCostBound worldCount thingCount tables kind env.size body +
        body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1) + 2 := by
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
          (firstSuccessEnvCosted worldCount thingCount tables env kind name body).cost + 1 +
        (minimizeFailureCosted worldCount thingCount tables env' body).cost ≤
      formula.evalCostBound worldCount thingCount
          (diagAtomCostBound worldCount thingCount tables) env.size +
        firstMatchCostBound worldCount thingCount tables kind env.size body +
        body.failureMinimizeCostBound worldCount thingCount tables (env.size + 1) + 2 := by
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
    (firstFailureEnvCosted worldCount thingCount tables env kind name body).cost + 1 +
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
    exact evalDiagFormulaCosted_not_cost_add_one_le_failureMinimizeCostBound _ _ _ _ _
  case case20 hleft hright ih =>
    rename_i leftChecked rightChecked traces failure
    have hleftCost : leftChecked.cost ≤ _ :=
      evalDiagFormulaCosted_concrete_cost_le _ _ _ _ _
    have hrightCost : rightChecked.cost ≤ _ :=
      evalDiagFormulaCosted_concrete_cost_le _ _ _ _ _
    have htraceCost : traces.cost ≤ _ := successTracesCosted_cost_le _ _ _ _ _
    have htraceSize : traces.value.size ≤ _ := successTracesCosted_size_le _ _ _ _ _
    dsimp only [leftChecked] at hleftCost
    dsimp only [rightChecked] at hrightCost
    dsimp only [traces] at htraceCost
    rw [successTracesCosted_value] at htraceSize
    omega
  case case25 failure hchecked ih =>
    rename_i q checked traces
    have hcheckedCost : checked.cost ≤ _ :=
      evalDiagFormulaCosted_concrete_cost_le _ _ _ _ _
    have htraceCost : traces.cost ≤ _ := successTracesCosted_cost_le _ _ _ _ _
    have htraceSize : traces.value.size ≤ _ := successTracesCosted_size_le _ _ _ _ _
    dsimp only [checked] at hcheckedCost
    dsimp only [traces] at htraceCost
    rw [successTracesCosted_value] at htraceSize
    omega
  case case27 hchecked hleft ih =>
    rename_i checked leftChecked traces failure
    have hcheckedCost : checked.cost ≤ _ :=
      evalDiagFormulaCosted_concrete_cost_le _ _ _ _ _
    have hleftCost : leftChecked.cost ≤ _ :=
      evalDiagFormulaCosted_concrete_cost_le _ _ _ _ _
    have htraceCost : traces.cost ≤ _ := successTracesCosted_cost_le _ _ _ _ _
    have htraceSize : traces.value.size ≤ _ := successTracesCosted_size_le _ _ _ _ _
    dsimp only [checked] at hcheckedCost
    dsimp only [leftChecked] at hleftCost
    dsimp only [traces] at htraceCost
    rw [successTracesCosted_value] at htraceSize
    omega
  case case28 hleft hright ih =>
    rename_i traces failure hchecked
    have hcheckedCost := evalDiagFormulaCosted_concrete_cost_le_of_value
      _ _ _ _ _ _ hchecked
    have hleftCost := evalDiagFormulaCosted_concrete_cost_le_of_value
      _ _ _ _ _ _ hleft
    have hrightCost := evalDiagFormulaCosted_concrete_cost_le_of_value
      _ _ _ _ _ _ hright
    have htraceCost : traces.cost ≤ _ := successTracesCosted_cost_le _ _ _ _ _
    have htraceSize : traces.value.size ≤ _ := successTracesCosted_size_le _ _ _ _ _
    dsimp only [traces] at htraceCost
    rw [successTracesCosted_value] at htraceSize
    omega
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

private def scopeCoversWorld (worldNames : Array Name) (scope : NamedFactScope) (worldIdx : Nat) :
    Bool :=
  match scope with
  | .everywhere => true
  | .at world => world == indexedName worldNames worldIdx

private def unaryFactImplies (source target : UnaryField) : Bool :=
  (expandUnaryTaxonomyFact source 0 0).any fun
    | .unary field _ _ => field == target
    | _ => false

private def collectNamedFactEvidence
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Option String) : Array String :=
  (namedFacts.toList.filterMap render?).toArray

private theorem collectNamedFactEvidence_size_le
    (namedFacts : Array NamedScopedFact)
    (render? : NamedScopedFact → Option String) :
    (collectNamedFactEvidence namedFacts render?).size ≤ namedFacts.size := by
  unfold collectNamedFactEvidence
  simpa using List.length_filterMap_le render? namedFacts.toList

private def unaryEvidence
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (thingIdx worldIdx : Nat) (field : UnaryField) : Array String :=
  let thing := indexedName thingNames thingIdx
  collectNamedFactEvidence namedFacts fun fact =>
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

private def atomEvidence
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) : DiagAtom → Array String
  | .unary field thing world =>
      unaryEvidence worldNames thingNames namedFacts
        (lookupVar env thing) (lookupVar env world) field
  | .derivedUnary field thing world =>
      let thingName := indexedName thingNames (lookupVar env thing)
      let worldIdx := lookupVar env world
      collectNamedFactEvidence namedFacts fun fact => match fact with
        | .derived (.unary sourceField sourceThing) scope =>
            if sourceField == field && sourceThing == thingName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | .typeSem thing world =>
      let thingIdx := lookupVar env thing
      let worldIdx := lookupVar env world
      collectNamedFactEvidence namedFacts fun fact => match fact with
        | .binary .inst _ target scope =>
            if target == indexedName thingNames thingIdx && scopeCoversWorld worldNames scope worldIdx then
              some s!"{namedFactSummary fact} (makes {indexedName thingNames thingIdx} a possible type)"
            else none
        | _ => none
  | .binary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldIdx := lookupVar env world
      collectNamedFactEvidence namedFacts fun fact => match fact with
        | .binary sourceField sourceLeft sourceRight scope =>
            if sourceField == field && sourceLeft == leftName && sourceRight == rightName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | .derivedBinary field left right world =>
      let leftName := indexedName thingNames (lookupVar env left)
      let rightName := indexedName thingNames (lookupVar env right)
      let worldIdx := lookupVar env world
      collectNamedFactEvidence namedFacts fun fact => match fact with
        | .derived (.binary sourceField sourceLeft sourceRight) scope =>
            if sourceField == field && sourceLeft == leftName && sourceRight == rightName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | .ternary field first second third world =>
      let firstName := indexedName thingNames (lookupVar env first)
      let secondName := indexedName thingNames (lookupVar env second)
      let thirdName := indexedName thingNames (lookupVar env third)
      let worldIdx := lookupVar env world
      collectNamedFactEvidence namedFacts fun fact => match fact with
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
      collectNamedFactEvidence namedFacts fun fact => match fact with
        | .derived (.quaternary sourceField sourceFirst sourceSecond sourceThird sourceFourth) scope =>
            if sourceField == field && sourceFirst == firstName && sourceSecond == secondName &&
                sourceThird == thirdName && sourceFourth == fourthName &&
                scopeCoversWorld worldNames scope worldIdx then some (namedFactSummary fact) else none
        | _ => none
  | _ => #[]

private theorem atomEvidence_size_le_namedFacts
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (env : Array (String × Nat)) (atom : DiagAtom) :
    (atomEvidence worldNames thingNames namedFacts env atom).size ≤ namedFacts.size := by
  cases atom <;> simp [atomEvidence, unaryEvidence, collectNamedFactEvidence_size_le]

private def collectAtomsInto
    (out : Array DiagAtom) : DiagFormula → Array DiagAtom
  | .atom atom => out.push atom
  | .eqThing _ _ | .eqWorld _ _ => out
  | .not p => collectAtomsInto out p
  | .and p q | .or p q | .imp p q | .iff p q =>
      collectAtomsInto (collectAtomsInto out p) q
  | .forallThing _ body | .forallWorld _ body |
      .existsThing _ body | .existsWorld _ body |
      .box _ _ body | .dia _ _ body => collectAtomsInto out body

private def collectAtoms (formula : DiagFormula) : Array DiagAtom :=
  collectAtomsInto #[] formula

private theorem collectAtomsInto_size_le
    (out : Array DiagAtom) (formula : DiagFormula) :
    (collectAtomsInto out formula).size ≤ out.size + formula.nodeCount := by
  induction formula generalizing out with
  | atom atom => simp [collectAtomsInto, DiagFormula.nodeCount]
  | eqThing | eqWorld => simp [collectAtomsInto, DiagFormula.nodeCount]
  | not p ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega
  | and p q ihp ihq | or p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have hp := ihp out
      have hq := ihq (collectAtomsInto out p)
      omega
  | forallThing name body ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega
  | forallWorld name body ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega
  | existsThing name body ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega
  | existsWorld name body ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega
  | box currentWorld witnessWorld body ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega
  | dia currentWorld witnessWorld body ih =>
      simp only [collectAtomsInto, DiagFormula.nodeCount]
      have h := ih out
      omega

private theorem collectAtoms_size_le (formula : DiagFormula) :
    (collectAtoms formula).size ≤ formula.nodeCount := by
  unfold collectAtoms
  simpa using collectAtomsInto_size_le (#[] : Array DiagAtom) formula

private def failingAtomsInto
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
      failingAtomsInto worldCount thingCount tables env
        (failingAtomsInto worldCount thingCount tables env out p) q
  | .or p q =>
      if evalDiagFormula worldCount thingCount tables env (.or p q) then out else
        failingAtomsInto worldCount thingCount tables env
          (failingAtomsInto worldCount thingCount tables env out p) q
  | .imp p q =>
      if evalDiagFormula worldCount thingCount tables env (.imp p q) then out else
        failingAtomsInto worldCount thingCount tables env (collectAtomsInto out p) q
  | .iff p q =>
      if evalDiagFormula worldCount thingCount tables env (.iff p q) then out else
        failingAtomsInto worldCount thingCount tables env
          (failingAtomsInto worldCount thingCount tables env out p) q
  | .forallThing name body =>
      Id.run do
        let mut out := out
        for x in [:thingCount] do
          out := failingAtomsInto worldCount thingCount tables
            (env.push (name, x)) out body
        return out
  | .forallWorld name body =>
      Id.run do
        let mut out := out
        for w in [:worldCount] do
          out := failingAtomsInto worldCount thingCount tables
            (env.push (name, w)) out body
        return out
  | .existsThing name body =>
      if evalDiagFormula worldCount thingCount tables env (.existsThing name body) then out else
        Id.run do
          let mut out := out
          for x in [:thingCount] do
            out := failingAtomsInto worldCount thingCount tables
              (env.push (name, x)) out body
          return out
  | .existsWorld name body =>
      if evalDiagFormula worldCount thingCount tables env (.existsWorld name body) then out else
        Id.run do
          let mut out := out
          for w in [:worldCount] do
            out := failingAtomsInto worldCount thingCount tables
              (env.push (name, w)) out body
          return out
  | .box _currentWorld witnessWorld body =>
      (List.range worldCount).foldl (fun out w =>
        let env' := env.push (witnessWorld, w)
        if !evalDiagFormula worldCount thingCount tables env' body then
          failingAtomsInto worldCount thingCount tables env' out body
        else out) out
  | .dia currentWorld witnessWorld body =>
      if evalDiagFormula worldCount thingCount tables env (.dia currentWorld witnessWorld body) then out else
        Id.run do
          let mut out := out
          for w in [:worldCount] do
            out := failingAtomsInto worldCount thingCount tables
              (env.push (witnessWorld, w)) out body
          return out
termination_by formula => formula.nodeCount
decreasing_by
  all_goals simp only [DiagFormula.nodeCount]
  all_goals omega

private def failingAtoms
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : Array DiagAtom :=
  failingAtomsInto worldCount thingCount tables env #[] formula

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

private theorem failingAfterCollect_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (p q : DiagFormula)
    (hrec : (failingAtomsInto worldCount thingCount tables env
      (collectAtomsInto out p) q).size ≤
        (collectAtomsInto out p).size + q.failingAtomCountBound worldCount thingCount) :
    (failingAtomsInto worldCount thingCount tables env
      (collectAtomsInto out p) q).size ≤
        out.size + (p.nodeCount + q.failingAtomCountBound worldCount thingCount) := by
  have hcollect := collectAtomsInto_size_le out p
  omega

private theorem failingAtomsInto_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array DiagAtom) (formula : DiagFormula) :
    (failingAtomsInto worldCount thingCount tables env out formula).size ≤
      out.size + formula.failingAtomCountBound worldCount thingCount := by
  fun_induction failingAtomsInto
  all_goals simp_all [DiagFormula.failingAtomCountBound]
  all_goals try omega
  case case12 =>
    apply failingAfterCollect_size_le
    assumption
  case case15 | case16 | case18 | case20 | case23 =>
    apply foldlRangeFromZeroSize_le
    intro item acc
    apply_assumption
  case case21 =>
    apply foldlRangeSize_le
    intro item acc
    split <;> simp_all

private theorem failingAtoms_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) :
    (failingAtoms worldCount thingCount tables env formula).size ≤
      formula.failingAtomCountBound worldCount thingCount := by
  unfold failingAtoms
  simpa using failingAtomsInto_size_le worldCount thingCount tables env #[] formula

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

private def appendEvidenceItemsBudgeted
    (budget : Nat) (out : Array String) (items : Array String) : Array String :=
  items.toList.foldl (fun out item => pushDiagnosticIfRoom budget out s!"  - {item}") out

private theorem appendEvidenceItemsBudgeted_size_le
    (budget : Nat) (out items : Array String) (hout : out.size ≤ budget) :
    (appendEvidenceItemsBudgeted budget out items).size ≤ budget := by
  unfold appendEvidenceItemsBudgeted
  apply foldl_preserves_array_size_le items.toList out budget _ hout
  intro acc item hacc
  exact pushDiagnosticIfRoom_size_le budget acc _ hacc

private def appendEvidenceAtomBudgeted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom) : Array String :=
  if out.size < budget then
    let evidence := atomEvidence worldNames thingNames namedFacts env atom
    if evidence.isEmpty then
      if evalDiagAtom worldCount thingCount tables env atom then
        pushDiagnosticIfRoom budget out
          s!"  - {renderDiagAtom worldNames thingNames env atom} (present in generated finite model)"
      else out
    else appendEvidenceItemsBudgeted budget out evidence
  else out

private theorem appendEvidenceAtomBudgeted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (out : Array String) (atom : DiagAtom)
    (hout : out.size ≤ budget) :
    (appendEvidenceAtomBudgeted budget worldNames thingNames namedFacts worldCount thingCount
      tables env out atom).size ≤ budget := by
  simp only [appendEvidenceAtomBudgeted]
  split
  · split
    · split
      · exact pushDiagnosticIfRoom_size_le budget out _ hout
      · exact hout
    · exact appendEvidenceItemsBudgeted_size_le budget out _ hout
  · exact hout

private def appendEvidenceForFormulaBudgeted
    (budget : Nat)
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula) :
    Array String :=
  let header := pushDiagnosticIfRoom budget out
    s!"Evidence for {renderDiagFormula worldNames thingNames env formula}:"
  let out := (collectAtoms formula).toList.foldl
    (appendEvidenceAtomBudgeted budget worldNames thingNames namedFacts worldCount thingCount tables env) header
  if out.size == header.size then
    pushDiagnosticIfRoom budget out
      s!"  - {renderDiagFormula worldNames thingNames env formula} (true in generated finite model)"
  else out

private theorem appendEvidenceForFormulaBudgeted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula)
    (hout : out.size ≤ budget) :
    (appendEvidenceForFormulaBudgeted budget worldNames thingNames namedFacts worldCount thingCount
      tables out env formula).size ≤ budget := by
  simp only [appendEvidenceForFormulaBudgeted]
  split
  · apply pushDiagnosticIfRoom_size_le
    apply foldl_preserves_array_size_le
    · exact pushDiagnosticIfRoom_size_le budget out _ hout
    · intro acc atom hacc
      exact appendEvidenceAtomBudgeted_size_le budget worldNames thingNames namedFacts
        worldCount thingCount tables env acc atom hacc
  · apply foldl_preserves_array_size_le
    · exact pushDiagnosticIfRoom_size_le budget out _ hout
    · intro acc atom hacc
      exact appendEvidenceAtomBudgeted_size_le budget worldNames thingNames namedFacts
        worldCount thingCount tables env acc atom hacc

private theorem appendEvidenceForFormulaBudgeted_growth_le_budget
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (worldCount thingCount : Nat) (tables : FactTables)
    (out : Array String) (env : Array (String × Nat)) (formula : DiagFormula)
    (hout : out.size ≤ budget) :
    (appendEvidenceForFormulaBudgeted budget worldNames thingNames namedFacts worldCount thingCount
      tables out env formula).size - out.size ≤ budget := by
  have hsize := appendEvidenceForFormulaBudgeted_size_le budget worldNames thingNames namedFacts
    worldCount thingCount tables out env formula hout
  omega

private def suggestionForAtom
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

private def suggestionForFailure
    (worldNames thingNames : Array Name) (worldCount thingCount : Nat) (tables : FactTables)
    (env : Array (String × Nat)) (formula : DiagFormula) : String :=
  match formula with
  | .or _ _ =>
      "Add at least one of the alternatives listed here, or remove/relax the evidence for this counterexample that makes this alternative obligation apply."
  | .and _ _ =>
      if (flattenDiagAnd formula).any formulaHasDistinctnessRequirement then
        "Add a witness satisfying all listed requirements, including the distinctness condition, or remove/relax the evidence for this counterexample that makes this witness obligation apply."
      else
        let atoms := failingAtoms worldCount thingCount tables env formula
        match atoms[0]? with
        | some atom =>
            if atoms.size == 1 then
              suggestionForAtom worldNames thingNames env atom true
            else
              "Add all missing facts listed here, or remove/relax the evidence for this counterexample that makes these requirements apply."
        | none =>
            "Use the listed requirements and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."
  | .not (.atom atom) =>
      if evalDiagAtom worldCount thingCount tables env atom then
        suggestionForAtom worldNames thingNames env atom false
      else
        "Inspect the evidence for this counterexample: this forbidden condition holds, but the diagnostic could not reduce it to a single asserted DSL fact."
  | .atom atom =>
      suggestionForAtom worldNames thingNames env atom true
  | _ =>
      let atoms := failingAtoms worldCount thingCount tables env formula
      match atoms[0]? with
      | some atom =>
          if atoms.size == 1 then
            suggestionForAtom worldNames thingNames env atom true
          else
            "Several obligations fail together here. Add the missing facts named in the condition, or remove/relax the evidence for this counterexample that makes all of them required."
      | none =>
          "Use the condition and evidence for this counterexample to either add the missing DSL assertion or remove the DSL facts that make the obligation apply."

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
  String.intercalate " InheresIn " <| path.toList.map (indexedName thingNames ·)

private structure UltimateBearerCandidate where
  bearer : Nat
  path : Array Nat
  deriving Inhabited

private def ultimateBearerCandidatesFromCosted
    (thingCount : Nat) (tables : FactTables) (w m : Nat)
    (out : Array UltimateBearerCandidate) : List Nat →
    Complexity.Costed (Array UltimateBearerCandidate)
  | List.nil => .pure out
  | List.cons b rest =>
      if tables.unaryLookup "moment" b w then
        let tail := ultimateBearerCandidatesFromCosted thingCount tables w m out rest
        ⟨tail.value, 2 + tail.cost⟩
      else
        let path := tables.momentOfPathCosted thingCount w m b
        let out := match path.value with
          | some path => out.push ⟨b, path⟩
          | none => out
        let emitted := if path.value.isSome then 1 else 0
        let tail := ultimateBearerCandidatesFromCosted thingCount tables w m out rest
        ⟨tail.value, path.cost + 3 + emitted + tail.cost⟩

private def ultimateBearerCandidatesCosted
    (thingCount : Nat) (tables : FactTables) (w m : Nat) :
    Complexity.Costed (Array UltimateBearerCandidate) :=
  ultimateBearerCandidatesFromCosted thingCount tables w m #[] (List.range thingCount)

private theorem ultimateBearerCandidatesFromCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (w m : Nat)
    (out : Array UltimateBearerCandidate) (bearers : List Nat) :
    (ultimateBearerCandidatesFromCosted thingCount tables w m out bearers).cost ≤
      bearers.length *
        (thingCount + thingCount + thingCount + thingCount + 7) := by
  induction bearers generalizing out with
  | nil => simp [ultimateBearerCandidatesFromCosted]
  | cons b rest ih =>
      rw [ultimateBearerCandidatesFromCosted]
      split
      · have htail := ih out
        simp only [List.length_cons, Nat.succ_mul]
        omega
      · let path := tables.momentOfPathCosted thingCount w m b
        let nextOut := match path.value with
          | some path => out.push ⟨b, path⟩
          | none => out
        let emitted := if path.value.isSome then 1 else 0
        have hpath : path.cost ≤ thingCount + thingCount + thingCount + thingCount + 3 := by
          have h := FactTables.momentOfPathCosted_cost_le tables thingCount w m b
          change path.cost ≤ 4 * thingCount + 3 at h
          omega
        have hemitted : emitted ≤ 1 := by
          unfold emitted
          split <;> simp
        have htail := ih nextOut
        change path.cost + 3 + emitted +
          (ultimateBearerCandidatesFromCosted thingCount tables w m nextOut rest).cost ≤ _
        simp only [List.length_cons, Nat.succ_mul]
        omega

private theorem ultimateBearerCandidatesCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (w m : Nat) :
    (ultimateBearerCandidatesCosted thingCount tables w m).cost ≤
      thingCount * (thingCount + thingCount + thingCount + thingCount + 7) := by
  unfold ultimateBearerCandidatesCosted
  simpa using ultimateBearerCandidatesFromCosted_cost_le thingCount tables w m #[]
    (List.range thingCount)

private theorem ultimateBearerCandidatesFromCosted_size_le
    (thingCount : Nat) (tables : FactTables) (w m : Nat)
    (out : Array UltimateBearerCandidate) (bearers : List Nat) :
    (ultimateBearerCandidatesFromCosted thingCount tables w m out bearers).value.size ≤
      out.size + bearers.length := by
  induction bearers generalizing out with
  | nil => simp [ultimateBearerCandidatesFromCosted]
  | cons b rest ih =>
      rw [ultimateBearerCandidatesFromCosted]
      split
      · have htail := ih out
        simp only [List.length_cons]
        omega
      · let path := tables.momentOfPathCosted thingCount w m b
        let nextOut := match path.value with
          | some path => out.push ⟨b, path⟩
          | none => out
        have hnext : nextOut.size ≤ out.size + 1 := by
          unfold nextOut
          split <;> simp
        have htail := ih nextOut
        change (ultimateBearerCandidatesFromCosted thingCount tables w m nextOut rest).value.size ≤ _
        simp only [List.length_cons]
        omega

private theorem ultimateBearerCandidatesCosted_size_le
    (thingCount : Nat) (tables : FactTables) (w m : Nat) :
    (ultimateBearerCandidatesCosted thingCount tables w m).value.size ≤ thingCount := by
  unfold ultimateBearerCandidatesCosted
  simpa using ultimateBearerCandidatesFromCosted_size_le thingCount tables w m #[]
    (List.range thingCount)

private def ultimateBearerCandidates
    (thingCount : Nat) (tables : FactTables) (w m : Nat) :
    Array UltimateBearerCandidate :=
  (ultimateBearerCandidatesCosted thingCount tables w m).value

@[simp] private theorem ultimateBearerCandidatesCosted_value
    (thingCount : Nat) (tables : FactTables) (w m : Nat) :
    (ultimateBearerCandidatesCosted thingCount tables w m).value =
      ultimateBearerCandidates thingCount tables w m := rfl

private def momentCoordinates (worldCount thingCount : Nat) : List (Nat × Nat) :=
  (List.range worldCount).flatMap fun w => (List.range thingCount).map (w, ·)

private def firstMomentCandidatesWhereCosted
    (thingCount : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Bool) : List (Nat × Nat) →
    Complexity.Costed (Option (Nat × Nat × Array UltimateBearerCandidate))
  | List.nil => ⟨none, 1⟩
  | List.cons (w, m) rest =>
      if tables.unaryLookup "moment" m w then
        let candidates := ultimateBearerCandidatesCosted thingCount tables w m
        if accept candidates.value then
          ⟨some (w, m, candidates.value), candidates.cost + 4⟩
        else
          let tail := firstMomentCandidatesWhereCosted thingCount tables accept rest
          ⟨tail.value, candidates.cost + 3 + tail.cost⟩
      else
        let tail := firstMomentCandidatesWhereCosted thingCount tables accept rest
        ⟨tail.value, 2 + tail.cost⟩

private theorem firstMomentCandidatesWhereCosted_cost_le
    (thingCount : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Bool) (coordinates : List (Nat × Nat)) :
    (firstMomentCandidatesWhereCosted thingCount tables accept coordinates).cost ≤
      coordinates.length *
        (thingCount * (thingCount + thingCount + thingCount + thingCount + 7) + 4) + 1 := by
  induction coordinates with
  | nil => simp [firstMomentCandidatesWhereCosted]
  | cons coordinate rest ih =>
      rcases coordinate with ⟨w, m⟩
      rw [firstMomentCandidatesWhereCosted]
      split
      · let candidates := ultimateBearerCandidatesCosted thingCount tables w m
        have hcandidates := ultimateBearerCandidatesCosted_cost_le thingCount tables w m
        change candidates.cost ≤ _ at hcandidates
        simp only
        split
        · change candidates.cost + 4 ≤ _
          simp only [List.length_cons, Nat.succ_mul]
          omega
        · have htail := ih
          change candidates.cost + 3 +
            (firstMomentCandidatesWhereCosted thingCount tables accept rest).cost ≤ _
          simp only [List.length_cons, Nat.succ_mul]
          omega
      · simp only [List.length_cons, Nat.succ_mul]
        omega

private theorem firstMomentCandidatesWhereCosted_candidate_size_le
    (thingCount : Nat) (tables : FactTables)
    (accept : Array UltimateBearerCandidate → Bool) (coordinates : List (Nat × Nat))
    (w m : Nat) (candidates : Array UltimateBearerCandidate)
    (hfound : (firstMomentCandidatesWhereCosted thingCount tables accept coordinates).value =
      some (w, m, candidates)) :
    candidates.size ≤ thingCount := by
  induction coordinates with
  | nil => simp [firstMomentCandidatesWhereCosted] at hfound
  | cons coordinate rest ih =>
      rcases coordinate with ⟨w', m'⟩
      rw [firstMomentCandidatesWhereCosted] at hfound
      split at hfound
      · simp only at hfound
        split at hfound
        · simp only [Option.some.injEq, Prod.mk.injEq] at hfound
          rw [← hfound.2.2]
          exact ultimateBearerCandidatesCosted_size_le thingCount tables w' m'
        · exact ih hfound
      · exact ih hfound

private theorem momentCoordinates_length
    (worldCount thingCount : Nat) :
    (momentCoordinates worldCount thingCount).length = worldCount * thingCount := by
  unfold momentCoordinates
  simp only [List.length_flatMap, List.length_map, List.length_range]
  rw [List.map_const']
  simp

private def firstMomentWithoutUltimateBearerCosted
    (worldCount thingCount : Nat) (tables : FactTables) :
    Complexity.Costed (Option (Nat × Nat)) :=
  let found := firstMomentCandidatesWhereCosted thingCount tables Array.isEmpty
    (momentCoordinates worldCount thingCount)
  ⟨found.value.map fun result => (result.1, result.2.1), found.cost⟩

private def firstMomentWithoutUltimateBearer
    (worldCount thingCount : Nat) (tables : FactTables) : Option (Nat × Nat) :=
  (firstMomentWithoutUltimateBearerCosted worldCount thingCount tables).value

private def firstMomentWithMultipleUltimateBearersCosted
    (worldCount thingCount : Nat) (tables : FactTables) :
    Complexity.Costed (Option (Nat × Nat × Array UltimateBearerCandidate)) :=
  firstMomentCandidatesWhereCosted thingCount tables (fun candidates => candidates.size > 1)
    (momentCoordinates worldCount thingCount)

private theorem firstMomentWithoutUltimateBearerCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) :
    (firstMomentWithoutUltimateBearerCosted worldCount thingCount tables).cost ≤
      worldCount * thingCount *
        (thingCount * (thingCount + thingCount + thingCount + thingCount + 7) + 4) + 1 := by
  unfold firstMomentWithoutUltimateBearerCosted
  simpa [momentCoordinates_length] using firstMomentCandidatesWhereCosted_cost_le
    thingCount tables Array.isEmpty (momentCoordinates worldCount thingCount)

private theorem firstMomentWithMultipleUltimateBearersCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) :
    (firstMomentWithMultipleUltimateBearersCosted worldCount thingCount tables).cost ≤
      worldCount * thingCount *
        (thingCount * (thingCount + thingCount + thingCount + thingCount + 7) + 4) + 1 := by
  unfold firstMomentWithMultipleUltimateBearersCosted
  simpa [momentCoordinates_length] using firstMomentCandidatesWhereCosted_cost_le
    thingCount tables (fun candidates => candidates.size > 1)
      (momentCoordinates worldCount thingCount)

private theorem firstMomentWithMultipleUltimateBearersCosted_candidate_size_le
    (worldCount thingCount : Nat) (tables : FactTables)
    (w m : Nat) (candidates : Array UltimateBearerCandidate)
    (hfound : (firstMomentWithMultipleUltimateBearersCosted worldCount thingCount tables).value =
      some (w, m, candidates)) :
    candidates.size ≤ thingCount := by
  unfold firstMomentWithMultipleUltimateBearersCosted at hfound
  exact firstMomentCandidatesWhereCosted_candidate_size_le thingCount tables
    (fun candidates => candidates.size > 1) (momentCoordinates worldCount thingCount)
    w m candidates hfound

private def firstMomentWithMultipleUltimateBearers
    (worldCount thingCount : Nat) (tables : FactTables) :
    Option (Nat × Nat × Array UltimateBearerCandidate) :=
  (firstMomentWithMultipleUltimateBearersCosted worldCount thingCount tables).value

def ax68ClosureAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) :=
  let missing :=
    firstMomentWithoutUltimateBearerCosted worldNames.size thingNames.size tables
  match missing.value with
  | some (w, m) =>
      ⟨#[
        s!"Closure check for ax68: `{indexedName thingNames m}` is a moment at `{indexedName worldNames w}`, but no non-moment ultimate bearer is reachable through `InheresIn`.",
        s!"Suggestion: add an inherence chain from `{indexedName thingNames m}` to a concrete non-moment bearer, or reclassify the endpoint so it is not a moment."
      ], missing.cost + 2⟩
  | none =>
      let multiple :=
        firstMomentWithMultipleUltimateBearersCosted worldNames.size thingNames.size tables
      match multiple.value with
      | some (w, m, candidates) =>
          let rendered :=
            candidates.map (fun c =>
              s!"`{indexedName thingNames c.bearer}` via `{renderThingPath thingNames c.path}`")
          let renderedText := String.intercalate ", " rendered.toList
          ⟨#[
            s!"Closure check for ax68: `{indexedName thingNames m}` has multiple reachable non-moment bearers at `{indexedName worldNames w}`.",
            s!"Reachable bearers: {renderedText}.",
            "Suggestion: remove the competing inherence branch, or reclassify the unintended endpoint so it is not an ultimate bearer."
          ], missing.cost + multiple.cost + candidates.size + 3⟩
      | none =>
          ⟨#[
            "Closure check for ax68: every generated moment has exactly one reachable non-moment bearer in the finite `InheresIn` closure.",
            "The remaining failure is therefore in the Lean proof bridge from the computed closure to the inductive `MomentOf`, not in the DSL model data."
          ], missing.cost + multiple.cost + 2⟩

private theorem ax68ClosureAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).cost ≤
      2 * (worldNames.size * thingNames.size *
        (thingNames.size *
          (thingNames.size + thingNames.size + thingNames.size + thingNames.size + 7) + 4) + 1) +
        thingNames.size + 3 := by
  unfold ax68ClosureAnalysisCosted
  have hmissing := firstMomentWithoutUltimateBearerCosted_cost_le
    worldNames.size thingNames.size tables
  simp only
  split
  · change (firstMomentWithoutUltimateBearerCosted worldNames.size thingNames.size tables).cost + 2 ≤ _
    omega
  · have hmultiple := firstMomentWithMultipleUltimateBearersCosted_cost_le
      worldNames.size thingNames.size tables
    split
    · rename_i multiple hmissingValue w m candidates hmultipleValue
      have hcandidates := firstMomentWithMultipleUltimateBearersCosted_candidate_size_le
        worldNames.size thingNames.size tables w m candidates hmultipleValue
      change (firstMomentWithoutUltimateBearerCosted worldNames.size thingNames.size tables).cost +
        (firstMomentWithMultipleUltimateBearersCosted worldNames.size thingNames.size tables).cost +
        candidates.size + 3 ≤ _
      omega
    · change (firstMomentWithoutUltimateBearerCosted worldNames.size thingNames.size tables).cost +
        (firstMomentWithMultipleUltimateBearersCosted worldNames.size thingNames.size tables).cost + 2 ≤ _
      omega

def ax68ClosureAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax68ClosureAnalysisCosted worldNames thingNames tables).value

@[simp] theorem ax68ClosureAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax68ClosureAnalysisCosted worldNames thingNames tables).value =
      ax68ClosureAnalysis worldNames thingNames tables := rfl

def hasAx68ClosureFailure (worldCount thingCount : Nat) (tables : FactTables) : Bool :=
  (firstMomentWithoutUltimateBearer worldCount thingCount tables).isSome ||
    (firstMomentWithMultipleUltimateBearers worldCount thingCount tables).isSome

private def partLookup (tables : FactTables) (x y w : Nat) : Bool :=
  x == y || tables.binaryLookup "part" x y w

private def partLookupCosted (tables : FactTables) (x y w : Nat) : Complexity.Costed Bool :=
  if x == y then
    ⟨true, 1⟩
  else
    ⟨tables.binaryLookup "part" x y w, 2⟩

@[simp] private theorem partLookupCosted_value
    (tables : FactTables) (x y w : Nat) :
    (partLookupCosted tables x y w).value = partLookup tables x y w := by
  by_cases h : x = y <;> simp [partLookupCosted, partLookup, h]

private theorem partLookupCosted_cost_le
    (tables : FactTables) (x y w : Nat) :
    (partLookupCosted tables x y w).cost ≤ 2 := by
  simp only [partLookupCosted]
  split <;> simp

private def overlapLookup (tables : FactTables) (x y w : Nat) : Bool :=
  x == y || tables.binaryLookup "overlap" x y w

private def foundationCandidatesFromCosted
    (tables : FactTables) (x w : Nat) (ys : List Nat) (out : Array Nat) :
      Complexity.Costed (Array Nat) :=
  match ys with
  | .nil => ⟨out, 0⟩
  | .cons y ys =>
      if tables.binaryLookup "foundedBy" x y w then
        Complexity.Costed.charge 3 <| foundationCandidatesFromCosted tables x w ys (out.push y)
      else
        Complexity.Costed.charge 2 <| foundationCandidatesFromCosted tables x w ys out

private def foundationCandidatesCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  foundationCandidatesFromCosted tables x w (List.range thingCount) #[]

private theorem foundationCandidatesFromCosted_cost_le
    (tables : FactTables) (x w : Nat) (ys : List Nat) (out : Array Nat) :
    (foundationCandidatesFromCosted tables x w ys out).cost ≤ 3 * ys.length := by
  induction ys generalizing out with
  | nil => simp [foundationCandidatesFromCosted]
  | cons y ys ih =>
      simp only [foundationCandidatesFromCosted]
      split <;> simp only [Complexity.Costed.charge_cost] <;>
        simp only [List.length_cons]
      · have hih := ih (out := out.push y)
        omega
      · have hih := ih (out := out)
        omega

private theorem foundationCandidatesCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted thingCount tables x w).cost ≤ 3 * thingCount := by
  simpa [foundationCandidatesCosted] using
    foundationCandidatesFromCosted_cost_le tables x w (List.range thingCount) #[]

private theorem foundationCandidatesFromCosted_size_le
    (tables : FactTables) (x w : Nat) (ys : List Nat) (out : Array Nat) :
    (foundationCandidatesFromCosted tables x w ys out).value.size ≤ out.size + ys.length := by
  induction ys generalizing out with
  | nil => simp [foundationCandidatesFromCosted]
  | cons y ys ih =>
      simp only [foundationCandidatesFromCosted]
      split
      · simp only [Complexity.Costed.charge_value, List.length_cons]
        have h := ih (out := out.push y)
        simp only [Array.size_push] at h
        omega
      · simp only [Complexity.Costed.charge_value, List.length_cons]
        have h := ih (out := out)
        omega

private theorem foundationCandidatesCosted_size_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted thingCount tables x w).value.size ≤ thingCount := by
  simpa [foundationCandidatesCosted] using
    foundationCandidatesFromCosted_size_le tables x w (List.range thingCount) #[]

private def foundationCandidates (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Array Nat :=
  (foundationCandidatesCosted thingCount tables x w).value

private def uniqueFoundationCosted (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Option Nat) :=
  let candidates := foundationCandidatesCosted thingCount tables x w
  if candidates.value.size == 1 then
    ⟨candidates.value[0]?, candidates.cost + 2⟩
  else
    ⟨none, candidates.cost + 1⟩

private def uniqueFoundation? (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Option Nat :=
  (uniqueFoundationCosted thingCount tables x w).value

private theorem uniqueFoundationCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (uniqueFoundationCosted thingCount tables x w).cost ≤ 3 * thingCount + 2 := by
  have hcandidates := foundationCandidatesCosted_cost_le thingCount tables x w
  simp only [uniqueFoundationCosted]
  split
  · change (foundationCandidatesCosted thingCount tables x w).cost + 2 ≤ _
    omega
  · change (foundationCandidatesCosted thingCount tables x w).cost + 1 ≤ _
    omega

private def renderFoundationStatusCosted
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed String :=
  let candidates := foundationCandidatesCosted thingNames.size tables x w
  if candidates.value.isEmpty then
    ⟨"no `FoundedBy` fact", candidates.cost + 1⟩
  else if candidates.value.size == 1 then
    ⟨s!"foundation `{indexedName thingNames (candidates.value[0]!)}`",
      candidates.cost + 2⟩
  else
    let rendered := String.intercalate "; " <| candidates.value.toList.map fun y =>
      s!"`{indexedName thingNames y}`"
    ⟨s!"ambiguous foundations {rendered}", candidates.cost + candidates.value.size + 2⟩

private def renderFoundationStatus
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) : String :=
  (renderFoundationStatusCosted thingNames tables x w).value

private theorem renderFoundationStatusCosted_cost_le
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderFoundationStatusCosted thingNames tables x w).cost ≤
      4 * thingNames.size + 2 := by
  have hcost := foundationCandidatesCosted_cost_le thingNames.size tables x w
  have hsize := foundationCandidatesCosted_size_le thingNames.size tables x w
  simp only [renderFoundationStatusCosted]
  split
  · change (foundationCandidatesCosted thingNames.size tables x w).cost + 1 ≤ _
    omega
  · split
    · change (foundationCandidatesCosted thingNames.size tables x w).cost + 2 ≤ _
      omega
    · change (foundationCandidatesCosted thingNames.size tables x w).cost +
        (foundationCandidatesCosted thingNames.size tables x w).value.size + 2 ≤ _
      omega

private def foundationEqCosted
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed (Option Bool) :=
  let left := uniqueFoundationCosted thingCount tables x w
  let right := uniqueFoundationCosted thingCount tables y w
  match left.value, right.value with
  | some fx, some fy => ⟨some (fx == fy), left.cost + right.cost + 2⟩
  | _, _ => ⟨none, left.cost + right.cost + 1⟩

private def foundationEq?
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) : Option Bool :=
  (foundationEqCosted thingCount tables x y w).value

private theorem foundationEqCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (foundationEqCosted thingCount tables x y w).cost ≤ 6 * thingCount + 6 := by
  have hleft := uniqueFoundationCosted_cost_le thingCount tables x w
  have hright := uniqueFoundationCosted_cost_le thingCount tables y w
  simp only [foundationEqCosted]
  split
  · change (uniqueFoundationCosted thingCount tables x w).cost +
      (uniqueFoundationCosted thingCount tables y w).cost + 2 ≤ _
    omega
  · change (uniqueFoundationCosted thingCount tables x w).cost +
      (uniqueFoundationCosted thingCount tables y w).cost + 1 ≤ _
    omega

private def sameFoundationLookupFromCosted
    (tables : FactTables) (x y w : Nat) (foundations : List Nat) : Complexity.Costed Bool :=
  match foundations with
  | .nil => ⟨false, 1⟩
  | .cons foundation foundations =>
      if tables.binaryLookup "foundedBy" x foundation w then
        if tables.binaryLookup "foundedBy" y foundation w then
          ⟨true, 4⟩
        else
          Complexity.Costed.charge 3 <|
            sameFoundationLookupFromCosted tables x y w foundations
      else
        Complexity.Costed.charge 2 <|
          sameFoundationLookupFromCosted tables x y w foundations

private def sameFoundationLookupCosted
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed Bool :=
  sameFoundationLookupFromCosted tables x y w (List.range thingCount)

private theorem sameFoundationLookupFromCosted_cost_le
    (tables : FactTables) (x y w : Nat) (foundations : List Nat) :
    (sameFoundationLookupFromCosted tables x y w foundations).cost ≤
      4 * foundations.length + 1 := by
  induction foundations with
  | nil => simp [sameFoundationLookupFromCosted]
  | cons foundation foundations ih =>
      simp only [sameFoundationLookupFromCosted]
      split
      · split
        · simp only [List.length_cons]
          omega
        · simp only [Complexity.Costed.charge_cost]
          simp only [List.length_cons]
          omega
      · simp only [Complexity.Costed.charge_cost]
        simp only [List.length_cons]
        omega

private theorem sameFoundationLookupCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (sameFoundationLookupCosted thingCount tables x y w).cost ≤ 4 * thingCount + 1 := by
  simpa [sameFoundationLookupCosted] using
    sameFoundationLookupFromCosted_cost_le tables x y w (List.range thingCount)

private def sameFoundationLookup
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) : Bool :=
  (sameFoundationLookupCosted thingCount tables x y w).value

/-- The right-hand side of ax73's part characterization, evaluated in the
same short-circuit order as the Boolean checker. -/
private def ax73CharacterizedCosted
    (worldCount thingCount : Nat) (tables : FactTables) (z x y w : Nat) :
    Complexity.Costed Bool :=
  let mode := derivedUnaryLookupCosted worldCount thingCount tables
    "ExternallyDependentMode" z w
  if !mode.value then
    ⟨false, mode.cost + 1⟩
  else if !tables.binaryLookup "inheresIn" z y w then
    ⟨false, mode.cost + 2⟩
  else
    Complexity.Costed.charge (mode.cost + 2) <|
      sameFoundationLookupCosted thingCount tables z x w

private def ax73Characterized
    (worldCount thingCount : Nat) (tables : FactTables) (z x y w : Nat) : Bool :=
  (ax73CharacterizedCosted worldCount thingCount tables z x y w).value

@[simp] private theorem ax73CharacterizedCosted_value
    (worldCount thingCount : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73CharacterizedCosted worldCount thingCount tables z x y w).value =
      ax73Characterized worldCount thingCount tables z x y w := rfl

private theorem ax73CharacterizedCosted_cost_le
    (worldCount thingCount : Nat) (tables : FactTables) (z x y w : Nat) :
    (ax73CharacterizedCosted worldCount thingCount tables z x y w).cost ≤
      derivedLookupCostBound worldCount thingCount tables + 4 * thingCount + 3 := by
  have hmode := derivedUnaryLookupCosted_cost_le worldCount thingCount tables
    "ExternallyDependentMode" z w
  have hfoundation := sameFoundationLookupCosted_cost_le thingCount tables z x w
  simp only [ax73CharacterizedCosted]
  split
  · change (derivedUnaryLookupCosted worldCount thingCount tables
      "ExternallyDependentMode" z w).cost + 1 ≤ _
    omega
  · split
    · change (derivedUnaryLookupCosted worldCount thingCount tables
        "ExternallyDependentMode" z w).cost + 2 ≤ _
      omega
    · change (derivedUnaryLookupCosted worldCount thingCount tables
        "ExternallyDependentMode" z w).cost + 2 +
          (sameFoundationLookupCosted thingCount tables z x w).cost ≤ _
      omega

@[simp] private theorem foundationCandidatesCosted_value
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (foundationCandidatesCosted thingCount tables x w).value =
      foundationCandidates thingCount tables x w := rfl

@[simp] private theorem foundationEqCosted_value
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (foundationEqCosted thingCount tables x y w).value =
      foundationEq? thingCount tables x y w := rfl

@[simp] private theorem sameFoundationLookupCosted_value
    (thingCount : Nat) (tables : FactTables) (x y w : Nat) :
    (sameFoundationLookupCosted thingCount tables x y w).value =
      sameFoundationLookup thingCount tables x y w := rfl

/-
DSL-level reconstruction for ax99.

The axiom quantifies over an existential finite family `ys zs : Fin n → Thing`,
so it does not fit the simple `DiagFormula` language above.  The helpers here
perform the corresponding finite search directly over characterization,
association, membership, and tuple-projection tables.
-/
private def memberLookup (tables : FactTables) (x s w : Nat) : Bool :=
  tables.binaryLookup "memberOf" x s w

private def tupleProjectionValueFromCosted (tables : FactTables)
    (p i w : Nat) : List Nat → Complexity.Costed Nat
  | List.nil => ⟨p, 1⟩
  | List.cons candidate candidates =>
      if tables.tupleProjectionLookup p i candidate w then
        ⟨candidate, 3⟩
      else
        Complexity.Costed.charge 2 <|
          tupleProjectionValueFromCosted tables p i w candidates

private def tupleProjectionValueCosted (thingCount : Nat) (tables : FactTables)
    (p i w : Nat) : Complexity.Costed Nat :=
  tupleProjectionValueFromCosted tables p i w (List.range thingCount)

private theorem tupleProjectionValueFromCosted_cost_le
    (tables : FactTables) (p i w : Nat) (candidates : List Nat) :
    (tupleProjectionValueFromCosted tables p i w candidates).cost ≤
      3 * candidates.length + 1 := by
  induction candidates with
  | nil => simp [tupleProjectionValueFromCosted]
  | cons candidate candidates ih =>
      simp only [tupleProjectionValueFromCosted, List.length_cons]
      split
      · change 3 ≤ 3 * (candidates.length + 1) + 1
        omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private theorem tupleProjectionValueCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (p i w : Nat) :
    (tupleProjectionValueCosted thingCount tables p i w).cost ≤ 3 * thingCount + 1 := by
  simpa [tupleProjectionValueCosted] using
    tupleProjectionValueFromCosted_cost_le tables p i w (List.range thingCount)

private def tupleProjectionValue (thingCount : Nat) (tables : FactTables)
    (p i w : Nat) : Nat :=
  (tupleProjectionValueCosted thingCount tables p i w).value

private def characterizationTargetsFromCosted
    (tables : FactTables) (t w : Nat) (zs : List Nat) (out : Array Nat) :
    Complexity.Costed (Array Nat) :=
  match zs with
  | List.nil => ⟨out, 0⟩
  | List.cons z zs =>
      if tables.binaryLookup "characterization" t z w then
        Complexity.Costed.charge 3 <|
          characterizationTargetsFromCosted tables t w zs (out.push z)
      else
        Complexity.Costed.charge 2 <|
          characterizationTargetsFromCosted tables t w zs out

private def characterizationTargetsCosted
    (thingCount : Nat) (tables : FactTables) (t w : Nat) :
    Complexity.Costed (Array Nat) :=
  characterizationTargetsFromCosted tables t w (List.range thingCount) #[]

private theorem characterizationTargetsFromCosted_cost_le
    (tables : FactTables) (t w : Nat) (zs : List Nat) (out : Array Nat) :
    (characterizationTargetsFromCosted tables t w zs out).cost ≤ 3 * zs.length := by
  induction zs generalizing out with
  | nil => simp [characterizationTargetsFromCosted]
  | cons z zs ih =>
      simp only [characterizationTargetsFromCosted, List.length_cons]
      split
      · simp only [Complexity.Costed.charge_cost]
        have htail := ih (out := out.push z)
        omega
      · simp only [Complexity.Costed.charge_cost]
        have htail := ih (out := out)
        omega

private theorem characterizationTargetsCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (t w : Nat) :
    (characterizationTargetsCosted thingCount tables t w).cost ≤ 3 * thingCount := by
  simpa [characterizationTargetsCosted] using
    characterizationTargetsFromCosted_cost_le tables t w (List.range thingCount) #[]

private theorem characterizationTargetsFromCosted_size_le
    (tables : FactTables) (t w : Nat) (zs : List Nat) (out : Array Nat) :
    (characterizationTargetsFromCosted tables t w zs out).value.size ≤
      out.size + zs.length := by
  induction zs generalizing out with
  | nil => simp [characterizationTargetsFromCosted]
  | cons z zs ih =>
      simp only [characterizationTargetsFromCosted, List.length_cons]
      split
      · simp only [Complexity.Costed.charge_value]
        have htail := ih (out := out.push z)
        simp only [Array.size_push] at htail
        omega
      · simp only [Complexity.Costed.charge_value]
        have htail := ih (out := out)
        omega

private theorem characterizationTargetsCosted_size_le
    (thingCount : Nat) (tables : FactTables) (t w : Nat) :
    (characterizationTargetsCosted thingCount tables t w).value.size ≤ thingCount := by
  simpa [characterizationTargetsCosted] using
    characterizationTargetsFromCosted_size_le tables t w (List.range thingCount) #[]

private def characterizationTargets
    (thingCount : Nat) (tables : FactTables) (t w : Nat) : Array Nat :=
  (characterizationTargetsCosted thingCount tables t w).value

private def productSubsetIndicesCosted
    (thingCount : Nat) (tables : FactTables) (w p : Nat) (ys : Array Nat) :
    List Nat → Complexity.Costed Bool
  | List.nil => ⟨true, 0⟩
  | List.cons i indices =>
      let projection := tupleProjectionValueCosted thingCount tables p i w
      if !memberLookup tables projection.value (ys[i]!) w then
        ⟨false, projection.cost + 3⟩
      else
        Complexity.Costed.charge (projection.cost + 2) <|
          productSubsetIndicesCosted thingCount tables w p ys indices

private theorem productSubsetIndicesCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (w p : Nat) (ys : Array Nat)
    (indices : List Nat) :
    (productSubsetIndicesCosted thingCount tables w p ys indices).cost ≤
      indices.length * (3 * thingCount + 4) := by
  induction indices with
  | nil => simp [productSubsetIndicesCosted]
  | cons i indices ih =>
      have hprojection := tupleProjectionValueCosted_cost_le thingCount tables p i w
      simp only [productSubsetIndicesCosted, List.length_cons, Nat.add_mul]
      split
      · change (tupleProjectionValueCosted thingCount tables p i w).cost + 3 ≤ _
        omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def productSubsetMembersCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat) :
    List Nat → Complexity.Costed Bool
  | List.nil => ⟨true, 1⟩
  | List.cons p members =>
      if memberLookup tables p x w then
        let indices := productSubsetIndicesCosted thingCount tables w p ys
          (List.range ys.size)
        if !indices.value then
          ⟨false, indices.cost + 2⟩
        else
          Complexity.Costed.charge (indices.cost + 2) <|
            productSubsetMembersCosted thingCount tables x w ys members
      else
        Complexity.Costed.charge 2 <|
          productSubsetMembersCosted thingCount tables x w ys members

private theorem productSubsetMembersCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat)
    (members : List Nat) :
    (productSubsetMembersCosted thingCount tables x w ys members).cost ≤
      members.length * (ys.size * (3 * thingCount + 4) + 2) + 1 := by
  induction members with
  | nil => simp [productSubsetMembersCosted]
  | cons p members ih =>
      have hindices := productSubsetIndicesCosted_cost_le thingCount tables w p ys
        (List.range ys.size)
      simp only [List.length_range] at hindices
      simp only [productSubsetMembersCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (productSubsetIndicesCosted thingCount tables w p ys
            (List.range ys.size)).cost + 2 ≤ _
          omega
        · simp only [Complexity.Costed.charge_cost]
          omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def productSubsetHoldsCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat) :
    Complexity.Costed Bool :=
  productSubsetMembersCosted thingCount tables x w ys (List.range thingCount)

private theorem productSubsetHoldsCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat) :
    (productSubsetHoldsCosted thingCount tables x w ys).cost ≤
      thingCount * (ys.size * (3 * thingCount + 4) + 2) + 1 := by
  simpa [productSubsetHoldsCosted] using
    productSubsetMembersCosted_cost_le thingCount tables x w ys (List.range thingCount)

private def productSubsetHolds
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat) : Bool :=
  (productSubsetHoldsCosted thingCount tables x w ys).value

@[simp] private theorem tupleProjectionValueCosted_value
    (thingCount : Nat) (tables : FactTables) (p i w : Nat) :
    (tupleProjectionValueCosted thingCount tables p i w).value =
      tupleProjectionValue thingCount tables p i w := rfl

@[simp] private theorem characterizationTargetsCosted_value
    (thingCount : Nat) (tables : FactTables) (t w : Nat) :
    (characterizationTargetsCosted thingCount tables t w).value =
      characterizationTargets thingCount tables t w := rfl

@[simp] private theorem productSubsetHoldsCosted_value
    (thingCount : Nat) (tables : FactTables) (x w : Nat) (ys : Array Nat) :
    (productSubsetHoldsCosted thingCount tables x w ys).value =
      productSubsetHolds thingCount tables x w ys := rfl

private def productPrefixMembersCosted
    (thingCount : Nat) (tables : FactTables) (x y i w : Nat) :
    List Nat → Complexity.Costed Bool
  | List.nil => ⟨true, 1⟩
  | List.cons p members =>
      if memberLookup tables p x w then
        let projection := tupleProjectionValueCosted thingCount tables p i w
        if !memberLookup tables projection.value y w then
          ⟨false, projection.cost + 4⟩
        else
          Complexity.Costed.charge (projection.cost + 3) <|
            productPrefixMembersCosted thingCount tables x y i w members
      else
        Complexity.Costed.charge 2 <|
          productPrefixMembersCosted thingCount tables x y i w members

private theorem productPrefixMembersCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x y i w : Nat) (members : List Nat) :
    (productPrefixMembersCosted thingCount tables x y i w members).cost ≤
      members.length * (3 * thingCount + 5) + 1 := by
  induction members with
  | nil => simp [productPrefixMembersCosted]
  | cons p members ih =>
      have hprojection := tupleProjectionValueCosted_cost_le thingCount tables p i w
      simp only [productPrefixMembersCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (tupleProjectionValueCosted thingCount tables p i w).cost + 4 ≤ _
          omega
        · simp only [Complexity.Costed.charge_cost]
          omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def productPrefixHoldsCosted
    (thingCount : Nat) (tables : FactTables) (x y i w : Nat) : Complexity.Costed Bool :=
  productPrefixMembersCosted thingCount tables x y i w (List.range thingCount)

private theorem productPrefixHoldsCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x y i w : Nat) :
    (productPrefixHoldsCosted thingCount tables x y i w).cost ≤
      thingCount * (3 * thingCount + 5) + 1 := by
  simpa [productPrefixHoldsCosted] using
    productPrefixMembersCosted_cost_le thingCount tables x y i w (List.range thingCount)

private def firstProductDimensionCandidateFromCosted
    (thingCount : Nat) (tables : FactTables) (x z i w : Nat) :
    List Nat → Complexity.Costed (Option Nat)
  | List.nil => ⟨none, 0⟩
  | List.cons y candidates =>
      if tables.binaryLookup "associatedWith" y z w then
        let prefixOk := productPrefixHoldsCosted thingCount tables x y i w
        if prefixOk.value then
          ⟨some y, prefixOk.cost + 4⟩
        else
          Complexity.Costed.charge (prefixOk.cost + 3) <|
            firstProductDimensionCandidateFromCosted thingCount tables x z i w candidates
      else
        Complexity.Costed.charge 2 <|
          firstProductDimensionCandidateFromCosted thingCount tables x z i w candidates

private def productDimensionCandidateCostBound (thingCount : Nat) : Nat :=
  thingCount * (thingCount * (3 * thingCount + 5) + 5)

private theorem firstProductDimensionCandidateFromCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x z i w : Nat) (candidates : List Nat) :
    (firstProductDimensionCandidateFromCosted thingCount tables x z i w candidates).cost ≤
      candidates.length * (thingCount * (3 * thingCount + 5) + 5) := by
  induction candidates with
  | nil => simp [firstProductDimensionCandidateFromCosted]
  | cons y candidates ih =>
      have hprefix := productPrefixHoldsCosted_cost_le thingCount tables x y i w
      simp only [firstProductDimensionCandidateFromCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (productPrefixHoldsCosted thingCount tables x y i w).cost + 4 ≤ _
          omega
        · simp only [Complexity.Costed.charge_cost]
          omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def firstProductDimensionCandidateCosted
    (thingCount : Nat) (tables : FactTables) (x z i w : Nat) :
    Complexity.Costed (Option Nat) :=
  firstProductDimensionCandidateFromCosted thingCount tables x z i w
    (List.range thingCount)

private theorem firstProductDimensionCandidateCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x z i w : Nat) :
    (firstProductDimensionCandidateCosted thingCount tables x z i w).cost ≤
      productDimensionCandidateCostBound thingCount := by
  simpa [firstProductDimensionCandidateCosted, productDimensionCandidateCostBound] using
    firstProductDimensionCandidateFromCosted_cost_le thingCount tables x z i w
      (List.range thingCount)

private def productDimensionsCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    List Nat → Nat → Array Nat → Complexity.Costed (Option (Array Nat))
  | List.nil, _, ys => ⟨some ys, 0⟩
  | List.cons z zs, i, ys =>
      let candidate := firstProductDimensionCandidateCosted thingCount tables x z i w
      match candidate.value with
      | none => ⟨none, candidate.cost + 1⟩
      | some y =>
          Complexity.Costed.charge (candidate.cost + 1) <|
            productDimensionsCosted thingCount tables x w zs (i + 1) (ys.push y)

private theorem productDimensionsCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat)
    (zs : List Nat) (i : Nat) (ys : Array Nat) :
    (productDimensionsCosted thingCount tables x w zs i ys).cost ≤
      zs.length * (productDimensionCandidateCostBound thingCount + 1) := by
  induction zs generalizing i ys with
  | nil => simp [productDimensionsCosted]
  | cons z zs ih =>
      have hcandidate := firstProductDimensionCandidateCosted_cost_le
        thingCount tables x z i w
      rw [productDimensionsCosted]
      cases hvalue : (firstProductDimensionCandidateCosted thingCount tables x z i w).value with
      | none =>
        simp only [List.length_cons, Nat.add_mul]
        omega
      | some y =>
        simp only [Complexity.Costed.charge_cost, List.length_cons, Nat.add_mul]
        have htail := ih (i := i + 1) (ys := ys.push y)
        omega

private theorem productDimensionsCosted_size_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat)
    (zs : List Nat) (i : Nat) (ys result : Array Nat)
    (hresult : (productDimensionsCosted thingCount tables x w zs i ys).value =
      some result) :
    result.size ≤ ys.size + zs.length := by
  induction zs generalizing i ys result with
  | nil =>
      simp [productDimensionsCosted] at hresult
      subst result
      omega
  | cons z zs ih =>
      rw [productDimensionsCosted] at hresult
      cases hvalue : (firstProductDimensionCandidateCosted thingCount tables x z i w).value with
      | none => simp [hvalue] at hresult
      | some y =>
        simp only [hvalue] at hresult
        have htail := ih (i := i + 1) (ys := ys.push y) (result := result) hresult
        simp only [Array.size_push, List.length_cons] at htail ⊢
        omega

private def productWitnessCosted
    (thingCount : Nat) (tables : FactTables) (x t w : Nat) :
    Complexity.Costed (Option (Array Nat × Array Nat)) :=
  let zs := characterizationTargetsCosted thingCount tables t w
  if zs.value.isEmpty then
    ⟨some (#[], #[]), zs.cost + 1⟩
  else
    let dimensions := productDimensionsCosted thingCount tables x w zs.value.toList 0 #[]
    match dimensions.value with
    | none => ⟨none, zs.cost + dimensions.cost + 1⟩
    | some ys =>
        let subset := productSubsetHoldsCosted thingCount tables x w ys
        if subset.value then
          ⟨some (ys, zs.value), zs.cost + dimensions.cost + subset.cost + 2⟩
        else
          ⟨none, zs.cost + dimensions.cost + subset.cost + 2⟩

private def productWitnessCostBound (thingCount : Nat) : Nat :=
  3 * thingCount +
    thingCount * (productDimensionCandidateCostBound thingCount + 1) +
    thingCount * (thingCount * (3 * thingCount + 4) + 2) + 3

private theorem productWitnessCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x t w : Nat) :
    (productWitnessCosted thingCount tables x t w).cost ≤
      productWitnessCostBound thingCount := by
  let zs := characterizationTargetsCosted thingCount tables t w
  have hzsCost : zs.cost ≤ 3 * thingCount := by
    simpa [zs] using characterizationTargetsCosted_cost_le thingCount tables t w
  have hzsSize : zs.value.size ≤ thingCount := by
    simpa [zs] using characterizationTargetsCosted_size_le thingCount tables t w
  dsimp only [zs] at hzsCost hzsSize
  rw [productWitnessCosted]
  split
  · change (characterizationTargetsCosted thingCount tables t w).cost + 1 ≤
      productWitnessCostBound thingCount
    simp only [productWitnessCostBound]
    omega
  · let dimensions :=
      productDimensionsCosted thingCount tables x w zs.value.toList 0 #[]
    have hdimensions := productDimensionsCosted_cost_le
      thingCount tables x w zs.value.toList 0 #[]
    simp only [Array.length_toList] at hdimensions
    have hdimensions' : dimensions.cost ≤
        thingCount * (productDimensionCandidateCostBound thingCount + 1) := by
      apply le_trans hdimensions
      exact Nat.mul_le_mul_right (productDimensionCandidateCostBound thingCount + 1) hzsSize
    dsimp only [dimensions, zs] at hdimensions'
    have hdimensionsFinal :
        (productDimensionsCosted thingCount tables x w
          (characterizationTargets thingCount tables t w).toList 0 #[]).cost ≤
            thingCount * (productDimensionCandidateCostBound thingCount + 1) := by
      simpa only [characterizationTargetsCosted_value] using hdimensions'
    cases hvalue : dimensions.value with
    | none =>
        simp only [dimensions, zs] at hvalue
        simp only [hvalue]
        simp only [productWitnessCostBound]
        omega
    | some ys =>
        simp only [dimensions, zs] at hvalue
        have hysSizeRaw := productDimensionsCosted_size_le
          thingCount tables x w zs.value.toList 0 #[] ys hvalue
        simp only [Array.size_empty, Nat.zero_add, Array.length_toList] at hysSizeRaw
        have hysSize : ys.size ≤ thingCount := le_trans hysSizeRaw hzsSize
        let subset := productSubsetHoldsCosted thingCount tables x w ys
        have hsubset := productSubsetHoldsCosted_cost_le thingCount tables x w ys
        have hinner : ys.size * (3 * thingCount + 4) + 2 ≤
            thingCount * (3 * thingCount + 4) + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right (3 * thingCount + 4) hysSize) 2
        have hsubset' : subset.cost ≤
            thingCount * (thingCount * (3 * thingCount + 4) + 2) + 1 := by
          apply le_trans hsubset
          exact Nat.add_le_add_right (Nat.mul_le_mul_left thingCount hinner) 1
        dsimp only [subset] at hsubset'
        simp only [hvalue]
        split <;> simp only <;>
          simp [productWitnessCostBound] <;> omega

private def productWitness?
    (thingCount : Nat) (tables : FactTables) (x t w : Nat) :
    Option (Array Nat × Array Nat) :=
  (productWitnessCosted thingCount tables x t w).value

@[simp] private theorem productWitnessCosted_value
    (thingCount : Nat) (tables : FactTables) (x t w : Nat) :
    (productWitnessCosted thingCount tables x t w).value =
      productWitness? thingCount tables x t w := rfl

private def productFamilyEntryPresentCosted (x t : Nat) :
    List ProductFamilySpec → Complexity.Costed Bool
  | List.nil => ⟨false, 0⟩
  | List.cons family families =>
      if family.domain == x then
        if family.qualityType == t then
          ⟨true, 4⟩
        else
          Complexity.Costed.charge 3 <|
            productFamilyEntryPresentCosted x t families
      else
        Complexity.Costed.charge 2 <|
          productFamilyEntryPresentCosted x t families

private theorem productFamilyEntryPresentCosted_cost_le
    (x t : Nat) (families : List ProductFamilySpec) :
    (productFamilyEntryPresentCosted x t families).cost ≤ 4 * families.length := by
  induction families with
  | nil => simp [productFamilyEntryPresentCosted]
  | cons family families ih =>
      simp only [productFamilyEntryPresentCosted, List.length_cons, Nat.mul_add]
      split
      · split
        · change 4 ≤ 4 * families.length + 4
          omega
        · simp only [Complexity.Costed.charge_cost]
          omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def productFamilyEntryPresentCostedIn
    (tables : FactTables) (x t : Nat) : Complexity.Costed Bool :=
  productFamilyEntryPresentCosted x t tables.productFamilies.toList

private theorem productFamilyEntryPresentCostedIn_cost_le
    (tables : FactTables) (x t : Nat) :
    (productFamilyEntryPresentCostedIn tables x t).cost ≤
      4 * tables.productFamilies.size := by
  simpa [productFamilyEntryPresentCostedIn] using
    productFamilyEntryPresentCosted_cost_le x t tables.productFamilies.toList

private def ax99FailureEvidenceCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x t w : Nat) (entryPresent : Bool) : Complexity.Costed (Array String) :=
  let zs := characterizationTargetsCosted thingNames.size tables t w
  let renderedZs :=
    if zs.value.isEmpty then
      "none"
    else
      String.intercalate ", " <| zs.value.toList.map (indexedName thingNames ·)
  if entryPresent then
    ⟨#[
      s!"Product-family witness data is present for x = {indexedName thingNames x}, t = {indexedName thingNames t}, w = {indexedName worldNames w}, but it does not satisfy ax99.",
      s!"The witness must list one quality dimension for each characterization of `{indexedName thingNames t}` and prove that every member of `{indexedName thingNames x}` projects into the corresponding dimension.",
      "Check the `dimensions` and `types` listed in the `product_family` block, the `Characterization(t, z)` facts, the `AssociatedWith(y, z)` facts for the listed dimensions, and the `TupleProjection(tuple, i, component)` plus `MemberOf(component, y)` facts for every domain member.",
      s!"Characterization targets found for `{indexedName thingNames t}`: {renderedZs}."
    ], zs.cost + zs.value.size + 5⟩
  else
    ⟨#[
      s!"Missing product-family witness data for x = {indexedName thingNames x}, t = {indexedName thingNames t}, w = {indexedName worldNames w}.",
      s!"The model says `{indexedName thingNames x}` is a quality domain associated with `{indexedName thingNames t}`, so ax99 needs an explicit finite product-family witness for that pair.",
      s!"Add a block of the form `product_family {indexedName thingNames x} for {indexedName thingNames t}:` with one `dimensions` entry and one `types` entry for each component quality type characterizing `{indexedName thingNames t}`.",
      "For each listed dimension/type pair, also provide the ordinary facts that make the witness meaningful: `Characterization(t, z)`, `AssociatedWith(y, z)`, `MemberOf(tuple, x)` for domain members, `TupleProjection(tuple, i, component)`, and `MemberOf(component, y)`.",
      s!"Characterization targets currently found for `{indexedName thingNames t}`: {renderedZs}."
    ], zs.cost + zs.value.size + 6⟩

private theorem ax99FailureEvidenceCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x t w : Nat) (entryPresent : Bool) :
    (ax99FailureEvidenceCosted worldNames thingNames tables x t w entryPresent).cost ≤
      4 * thingNames.size + 6 := by
  have hcost := characterizationTargetsCosted_cost_le thingNames.size tables t w
  have hsize := characterizationTargetsCosted_size_le thingNames.size tables t w
  simp only [ax99FailureEvidenceCosted]
  split
  · change (characterizationTargetsCosted thingNames.size tables t w).cost +
        (characterizationTargetsCosted thingNames.size tables t w).value.size + 5 ≤ _
    omega
  · change (characterizationTargetsCosted thingNames.size tables t w).cost +
        (characterizationTargetsCosted thingNames.size tables t w).value.size + 6 ≤ _
    omega

private def ax99TypeCostBound (thingCount familyCount : Nat) : Nat :=
  4 * familyCount + productWitnessCostBound thingCount + 4 * thingCount + 9

private def ax99TypesCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (w x : Nat) :
    List Nat → Complexity.Costed (Option (Array String))
  | List.nil => ⟨none, 0⟩
  | List.cons t types =>
      if tables.binaryLookup "associatedWith" x t w then
        let entry := productFamilyEntryPresentCostedIn tables x t
        let witness := productWitnessCosted thingNames.size tables x t w
        match witness.value with
        | none =>
            let evidence := ax99FailureEvidenceCosted
              worldNames thingNames tables x t w entry.value
            ⟨some evidence.value, entry.cost + witness.cost + evidence.cost + 3⟩
        | some _ => Complexity.Costed.charge (entry.cost + witness.cost + 3) <|
            ax99TypesCosted worldNames thingNames tables w x types
      else
        Complexity.Costed.charge 2 <|
          ax99TypesCosted worldNames thingNames tables w x types

private theorem ax99TypesCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (w x : Nat)
    (types : List Nat) :
    (ax99TypesCosted worldNames thingNames tables w x types).cost ≤
      types.length * ax99TypeCostBound thingNames.size tables.productFamilies.size := by
  induction types with
  | nil => simp [ax99TypesCosted]
  | cons t types ih =>
      have hentry := productFamilyEntryPresentCostedIn_cost_le tables x t
      have hwitness := productWitnessCosted_cost_le thingNames.size tables x t w
      have hevidence := ax99FailureEvidenceCosted_cost_le
        worldNames thingNames tables x t w
          (productFamilyEntryPresentCostedIn tables x t).value
      simp only [ax99TypesCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (productFamilyEntryPresentCostedIn tables x t).cost +
              (productWitnessCosted thingNames.size tables x t w).cost +
              (ax99FailureEvidenceCosted worldNames thingNames tables x t w
                (productFamilyEntryPresentCostedIn tables x t).value).cost + 3 ≤ _
          unfold ax99TypeCostBound
          omega
        · simp only [Complexity.Costed.charge_cost]
          unfold ax99TypeCostBound at ih ⊢
          omega
      · simp only [Complexity.Costed.charge_cost]
        unfold ax99TypeCostBound at ih ⊢
        omega

private def ax99ThingsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (w : Nat) :
    List Nat → Complexity.Costed (Option (Array String))
  | List.nil => ⟨none, 0⟩
  | List.cons x things =>
      if tables.unaryLookup "qualityDomain" x w then
        let failure := ax99TypesCosted worldNames thingNames tables w x
          (List.range thingNames.size)
        match failure.value with
        | some evidence => ⟨some evidence, failure.cost + 2⟩
        | none => Complexity.Costed.charge (failure.cost + 2) <|
            ax99ThingsCosted worldNames thingNames tables w things
      else
        Complexity.Costed.charge 2 <|
          ax99ThingsCosted worldNames thingNames tables w things

private def ax99ThingCostBound (thingCount familyCount : Nat) : Nat :=
  2 + thingCount * ax99TypeCostBound thingCount familyCount

private theorem ax99ThingsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (w : Nat)
    (things : List Nat) :
    (ax99ThingsCosted worldNames thingNames tables w things).cost ≤
      things.length * ax99ThingCostBound thingNames.size tables.productFamilies.size := by
  induction things with
  | nil => simp [ax99ThingsCosted]
  | cons x things ih =>
      have htypes := ax99TypesCosted_cost_le worldNames thingNames tables w x
        (List.range thingNames.size)
      simp only [List.length_range] at htypes
      simp only [ax99ThingsCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (ax99TypesCosted worldNames thingNames tables w x
              (List.range thingNames.size)).cost + 2 ≤ _
          unfold ax99ThingCostBound
          omega
        · simp only [Complexity.Costed.charge_cost]
          unfold ax99ThingCostBound at ih ⊢
          omega
      · simp only [Complexity.Costed.charge_cost]
        unfold ax99ThingCostBound at ih ⊢
        omega

private def ax99WorldsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    List Nat → Complexity.Costed (Array String)
  | List.nil => ⟨#[
      "Product check for ax99: every asserted quality-domain association has a finite product witness in the DSL tables.",
      "If ax99 is still reported, the remaining issue is likely missing or mismatched product-family witness data rather than an obvious table mismatch."
    ], 2⟩
  | List.cons w worlds =>
      let failure := ax99ThingsCosted worldNames thingNames tables w
        (List.range thingNames.size)
      match failure.value with
      | some evidence => ⟨evidence, failure.cost⟩
      | none => Complexity.Costed.charge failure.cost <|
          ax99WorldsCosted worldNames thingNames tables worlds

private theorem ax99WorldsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (worlds : List Nat) :
    (ax99WorldsCosted worldNames thingNames tables worlds).cost ≤
      worlds.length * thingNames.size *
        ax99ThingCostBound thingNames.size tables.productFamilies.size + 2 := by
  induction worlds with
  | nil => simp [ax99WorldsCosted]
  | cons w worlds ih =>
      have hthings := ax99ThingsCosted_cost_le worldNames thingNames tables w
        (List.range thingNames.size)
      simp only [List.length_range] at hthings
      simp only [ax99WorldsCosted, List.length_cons, Nat.add_mul, Nat.one_mul]
      split
      · change (ax99ThingsCosted worldNames thingNames tables w
            (List.range thingNames.size)).cost ≤ _
        omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def ax99QualityDomainAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) :=
  ax99WorldsCosted worldNames thingNames tables (List.range worldNames.size)

private theorem ax99QualityDomainAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax99QualityDomainAnalysisCosted worldNames thingNames tables).cost ≤
      worldNames.size * thingNames.size *
        ax99ThingCostBound thingNames.size tables.productFamilies.size + 2 := by
  unfold ax99QualityDomainAnalysisCosted
  simpa using ax99WorldsCosted_cost_le worldNames thingNames tables
    (List.range worldNames.size)

private def ax99QualityDomainAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax99QualityDomainAnalysisCosted worldNames thingNames tables).value

@[simp] private theorem ax99QualityDomainAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax99QualityDomainAnalysisCosted worldNames thingNames tables).value =
      ax99QualityDomainAnalysis worldNames thingNames tables := rfl

private def thingIndexByString? (thingNames : Array Name) (thing : String) : Option Nat :=
  thingNames.findIdx? (fun name => name.toString == thing)

private def resolvedScopeWorlds (worldNames : Array Name) : FactScope → Array Nat
  | .at w => #[w]
  | .everywhere => Array.range worldNames.size

/-
Derived assertions are checked before certification as generated theorems.
When one fails, these evaluators reconstruct the same definition-like relation
from finite tables so the widget can report the false assertion in DSL terms.
-/
private def typeLookup
    (worldCount thingCount : Nat) (tables : FactTables) (thing : Nat) : Bool :=
  hasPossibleInstance worldCount thingCount tables thing

private def subsetLookup (thingCount : Nat) (tables : FactTables) (s t w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if memberLookup tables x s w && !memberLookup tables x t w then
        return false
    return true

private def properSubsetLookup (thingCount : Nat) (tables : FactTables) (s t w : Nat) : Bool :=
  subsetLookup thingCount tables s t w &&
    Id.run do
      for x in [:thingCount] do
        if memberLookup tables x t w && !memberLookup tables x s w then
          return true
      return false

private def properSubLookup (tables : FactTables) (x y w : Nat) : Bool :=
  tables.binaryLookup "sub" x y w && !tables.binaryLookup "sub" y x w

private def isDisjointWithLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t t' w : Nat) : Bool :=
  typeLookup worldCount thingCount tables t &&
    typeLookup worldCount thingCount tables t' &&
    Id.run do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x t w && tables.binaryLookup "inst" x t' w then
          return false
      return true

private def isCompletelyCoveredByLookup
    (thingCount : Nat) (tables : FactTables) (t t' t'' w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x t w &&
          !(tables.binaryLookup "inst" x t' w || tables.binaryLookup "inst" x t'' w) then
        return false
    return true

private def isPartitionedIntoLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t t' t'' w : Nat) : Bool :=
  isCompletelyCoveredByLookup thingCount tables t t' t'' w &&
    isDisjointWithLookup worldCount thingCount tables t' t'' w

private def categorizesLookup
    (worldCount thingCount : Nat) (tables : FactTables) (t1 t2 w : Nat) : Bool :=
  typeLookup worldCount thingCount tables t1 &&
    Id.run do
      for t3 in [:thingCount] do
        if tables.binaryLookup "inst" t3 t1 w && !tables.binaryLookup "sub" t3 t2 w then
          return false
      return true

private def qualityLookup (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  Id.run do
    let mut found? : Option Nat := none
    for q in [:thingCount] do
      if tables.unaryLookup "qualityKind" q w && tables.binaryLookup "inst" x q w then
        match found? with
        | none => found? := some q
        | some _ => return false
    return found?.isSome

private def nonEmptySetLookup (thingCount : Nat) (tables : FactTables) (s w : Nat) : Bool :=
  Id.run do
    for x in [:thingCount] do
      if memberLookup tables x s w then
        return true
    return false

private def uniqueThing? (thingCount : Nat) (p : Nat → Bool) : Option Nat :=
  Id.run do
    let mut found? : Option Nat := none
    for x in [:thingCount] do
      if p x then
        match found? with
        | none => found? := some x
        | some _ => return none
    return found?

private def qualityStructureLookup
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  (uniqueThing? thingCount fun t =>
    tables.unaryLookup "qualityType" t w &&
      tables.binaryLookup "associatedWith" x t w).isSome

private def simpleQualityLookup (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  qualityLookup thingCount tables x w &&
    Id.run do
      for y in [:thingCount] do
        if tables.binaryLookup "inheresIn" y x w then
          return false
      return true

private def complexQualityLookup (thingCount : Nat) (tables : FactTables) (x w : Nat) : Bool :=
  qualityLookup thingCount tables x w &&
    Id.run do
      for y in [:thingCount] do
        if tables.binaryLookup "inheresIn" y x w then
          return true
      return false

private def simpleQualityTypeLookup
    (thingCount : Nat) (tables : FactTables) (t w : Nat) : Bool :=
  tables.unaryLookup "qualityType" t w &&
    Id.run do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x t w &&
            !simpleQualityLookup thingCount tables x w then
          return false
      return true

private def complexQualityTypeLookup
    (thingCount : Nat) (tables : FactTables) (t w : Nat) : Bool :=
  tables.unaryLookup "qualityType" t w &&
    Id.run do
      for x in [:thingCount] do
        if tables.binaryLookup "inst" x t w &&
            !complexQualityLookup thingCount tables x w then
          return false
      return true

private def ultimateBearerOfLookup
    (thingCount : Nat) (tables : FactTables) (b m w : Nat) : Bool :=
  !tables.unaryLookup "moment" b w &&
    tables.momentOfClosure thingCount w m b

private def evalNamedDerivedFact?
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Option Bool := do
  match fact with
  | .unary "Quality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| qualityLookup thingNames.size tables x w
  | .unary "NonEmptySet" x =>
      let x ← thingIndexByString? thingNames x
      pure <| nonEmptySetLookup thingNames.size tables x w
  | .unary "QualityStructure" x =>
      let x ← thingIndexByString? thingNames x
      pure <| qualityStructureLookup thingNames.size tables x w
  | .unary "SimpleQuality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| simpleQualityLookup thingNames.size tables x w
  | .unary "ComplexQuality" x =>
      let x ← thingIndexByString? thingNames x
      pure <| complexQualityLookup thingNames.size tables x w
  | .unary "SimpleQualityType" x =>
      let x ← thingIndexByString? thingNames x
      pure <| simpleQualityTypeLookup thingNames.size tables x w
  | .unary "ComplexQualityType" x =>
      let x ← thingIndexByString? thingNames x
      pure <| complexQualityTypeLookup thingNames.size tables x w
  | .unary field x =>
      let x ← thingIndexByString? thingNames x
      pure <| derivedUnaryLookup worldNames.size thingNames.size tables field x w
  | .binary "UltimateBearerOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| ultimateBearerOfLookup thingNames.size tables x y w
  | .binary "ProperSub" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| properSubLookup tables x y w
  | .binary "SubsetOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| subsetLookup thingNames.size tables x y w
  | .binary "ProperSubsetOf" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| properSubsetLookup thingNames.size tables x y w
  | .binary "IsDisjointWith" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| isDisjointWithLookup worldNames.size thingNames.size tables x y w
  | .binary "Categorizes" x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| categorizesLookup worldNames.size thingNames.size tables x y w
  | .binary field x y =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      pure <| derivedBinaryLookup worldNames.size thingNames.size tables field x y w
  | .ternary "IsCompletelyCoveredBy" x y z =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      let z ← thingIndexByString? thingNames z
      pure <| isCompletelyCoveredByLookup thingNames.size tables x y z w
  | .ternary "IsPartitionedInto" x y z =>
      let x ← thingIndexByString? thingNames x
      let y ← thingIndexByString? thingNames y
      let z ← thingIndexByString? thingNames z
      pure <| isPartitionedIntoLookup worldNames.size thingNames.size tables x y z w
  | .ternary _ _ _ _ =>
      none
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| individualFunctionalDependenceLookup thingNames.size tables x x' y y' w
  | .quaternary "ComponentOf" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| componentOfLookup thingNames.size tables x x' y y' w
  | .quaternary "Constitution" x x' y y' =>
      let x ← thingIndexByString? thingNames x
      let x' ← thingIndexByString? thingNames x'
      let y ← thingIndexByString? thingNames y
      let y' ← thingIndexByString? thingNames y'
      pure <| constitutionLookup thingNames.size tables x x' y y' w
  | .quaternary _ _ _ _ _ =>
      none

private def derivedAssertionSuggestion (fact : NamedDerivedFact) : String :=
  match fact with
  | .unary "Quality" _ =>
      "Computed from `QualityKind(k)` plus `x :: k`, with exactly one such quality kind. Add exactly one quality-kind instantiation for the individual, and avoid competing quality-kind instantiations."
  | .unary "ExternallyDependentMode" _ =>
      "Computed from `Mode(x)` plus some computed `ExternallyDependent(x, y)`. `ExternallyDependent` itself is computed from modal existential dependence and independence from each bearer reached by `InheresIn`. Add `Mode`, `InheresIn`, and modal `Ex` facts that make a witness true, or remove the unsupported assertion."
  | .unary "QuaIndividual" _ =>
      "Computed from `QuaIndividualOf(x, y)`. Add a matching `QuaIndividualOf` fact and satisfy the §3.10 foundation requirements checked by the relator axioms, or remove the unsupported assertion."
  | .unary "NonEmptySet" _ =>
      "Computed from membership at the current world. Add at least one `MemberOf(member, set)` fact at this world, or remove the unsupported assertion."
  | .unary "QualityStructure" _ =>
      "Computed from exactly one association with a `QualityType`. Add exactly one `AssociatedWith(structure, qualityType)` fact whose target is a `QualityType`, or remove the unsupported assertion."
  | .unary "SimpleQuality" _ =>
      "Computed from `Quality(x)` plus absence of `InheresIn(_, x)`. Make the thing a computed `Quality` and ensure no other thing inheres in it at this world."
  | .unary "ComplexQuality" _ =>
      "Computed from `Quality(x)` plus at least one `InheresIn(_, x)`. Make the thing a computed `Quality` and add at least one `InheresIn(part, quality)` fact."
  | .unary "SimpleQualityType" _ =>
      "Computed from `QualityType(t)` plus every current instance of `t` being a computed `SimpleQuality`. Assert `QualityType(type)` and repair any non-simple-quality instance."
  | .unary "ComplexQualityType" _ =>
      "Computed from `QualityType(t)` plus every current instance of `t` being a computed `ComplexQuality`. Assert `QualityType(type)` and repair any non-complex-quality instance."
  | .binary "ProperSub" _ _ =>
      "Computed from `Sub(left, right)` and absence of reverse `Sub(right, left)`. Add the forward `Sub` fact and ensure the reverse `Sub` fact is not present."
  | .binary "GenericFunctionalDependence" _ _ =>
      "Computed from `Inst` and `FunctionsAs`: every instance functioning as the source type needs a distinct instance functioning as the target type."
  | .quaternary "IndividualFunctionalDependence" _ _ _ _ =>
      "Computed from generic functional dependence, the two instantiations, and the source-to-target `FunctionsAs` implication. Make the type-level dependence true, add the required instantiations, and ensure the target functions whenever the source functions."
  | .quaternary "ComponentOf" _ _ _ _ =>
      "Computed from `ProperPart(component, whole)` plus the corresponding computed `IndividualFunctionalDependence`. Add the proper-part fact and repair the functional-dependence side."
  | .binary "GenericConstitutionalDependence" _ _ =>
      "Computed from `Inst` and `ConstitutedBy`: every source-type instance needs a target-type instance that constitutionally bears it."
  | .quaternary "Constitution" _ _ _ _ =>
      "Computed from the two instantiations, computed generic constitutional dependence, and `ConstitutedBy(instance, constituter)`. Add the required instantiations, repair generic constitutional dependence, and add the concrete `ConstitutedBy` fact."
  | .binary "ExternallyDependent" _ _ =>
      "Computed from modal existential dependence plus existential independence from every bearer reached by `InheresIn`. Add modal `Ex` variation and `InheresIn` facts that satisfy external dependence, or remove the unsupported assertion."
  | .binary "ExistentialDependence" _ _ =>
      "Computed from `Ex` facts across worlds: every world where the dependent exists must also have the target existing. Add the missing `Ex` facts, or remove the unsupported assertion."
  | .binary "ExistentialIndependence" _ _ =>
      "Computed from `Ex` facts across worlds: each side must have a witness world where it exists without the other. Add those modal `Ex` variations, or remove the unsupported assertion."
  | .binary "UltimateBearerOf" _ _ =>
      "Computed from the `InheresIn` transitive closure and `Moment`: the bearer must be non-moment and reachable from the moment. Add an `InheresIn` path from the moment to the bearer and ensure the bearer is not a moment."
  | .binary "SubsetOf" _ _ =>
      "Computed from `MemberOf`: every member of the left set must also be a member of the right set at this world."
  | .binary "ProperSubsetOf" _ _ =>
      "Computed from `SubsetOf(left, right)` plus a strictness witness: some right-set member must not be in the left set."
  | .binary "IsDisjointWith" _ _ =>
      "Computed from typehood and `Inst`: the two types must have no shared instance. Remove the assertion, or remove the common instance facts that make the two types overlap."
  | .ternary "IsCompletelyCoveredBy" _ _ _ =>
      "Computed from `Inst`: every instance of the covered type must instantiate at least one covering type. Add missing instantiation facts, or remove the assertion."
  | .ternary "IsPartitionedInto" _ _ _ =>
      "Computed from complete coverage plus disjointness of the two covering types. Make the cover complete and the covering types disjoint, or remove the assertion."
  | .binary "Categorizes" _ _ =>
      "Computed from typehood, `Inst`, and `Sub`: every type instantiating the category must specialize the categorized type. Add missing specialization facts, or remove the assertion."
  | _ =>
      "Remove the assertion, or add the primitive DSL facts needed to make this derived relation true in the generated finite model."

private def firstExWithoutFromCosted
    (tables : FactTables) (x y : Nat) : List Nat → Complexity.Costed (Option Nat)
  | List.nil => ⟨none, 1⟩
  | List.cons w worlds =>
      if tables.unaryLookup "ex" x w then
        if !tables.unaryLookup "ex" y w then
          ⟨some w, 4⟩
        else
          Complexity.Costed.charge 3 <| firstExWithoutFromCosted tables x y worlds
      else
        Complexity.Costed.charge 2 <| firstExWithoutFromCosted tables x y worlds

private def firstExWithoutCosted
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    Complexity.Costed (Option Nat) :=
  firstExWithoutFromCosted tables x y (List.range worldCount)

private theorem firstExWithoutFromCosted_cost_le
    (tables : FactTables) (x y : Nat) (worlds : List Nat) :
    (firstExWithoutFromCosted tables x y worlds).cost ≤ 4 * worlds.length + 1 := by
  induction worlds with
  | nil => simp [firstExWithoutFromCosted]
  | cons w worlds ih =>
      simp only [firstExWithoutFromCosted, List.length_cons]
      split
      · split
        · change 4 ≤ 4 * (worlds.length + 1) + 1
          omega
        · simp only [Complexity.Costed.charge_cost]
          omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private theorem firstExWithoutCosted_cost_le
    (worldCount : Nat) (tables : FactTables) (x y : Nat) :
    (firstExWithoutCosted worldCount tables x y).cost ≤ 4 * worldCount + 1 := by
  simpa [firstExWithoutCosted] using
    firstExWithoutFromCosted_cost_le tables x y (List.range worldCount)

private def firstBoxExImpFailureCosted
    (worldNames : Array Name) (tables : FactTables) (x y : Nat) :
    Complexity.Costed (Option Nat) :=
  firstExWithoutCosted worldNames.size tables x y

private def firstBoxExImpFailure?
    (worldNames : Array Name) (tables : FactTables) (x y : Nat) : Option Nat :=
  (firstBoxExImpFailureCosted worldNames tables x y).value

private def firstExternalIndependenceFailureCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    Complexity.Costed (Option String) :=
  let yWithoutZ := firstExWithoutCosted worldNames.size tables y z
  let zWithoutY := firstExWithoutCosted worldNames.size tables z y
  match yWithoutZ.value, zWithoutY.value with
  | none, none =>
      ⟨some s!"the assertion needs one witness world where Ex({indexedName thingNames y}) holds without Ex({indexedName thingNames z}), and one witness world where Ex({indexedName thingNames z}) holds without Ex({indexedName thingNames y}); neither witness exists in the current `Ex` facts",
        yWithoutZ.cost + zWithoutY.cost + 1⟩
  | none, some _ =>
      ⟨some s!"the assertion needs a witness world where Ex({indexedName thingNames y}) holds without Ex({indexedName thingNames z}), but no such world exists in the current `Ex` facts",
        yWithoutZ.cost + zWithoutY.cost + 1⟩
  | some _, none =>
      ⟨some s!"the assertion needs a witness world where Ex({indexedName thingNames z}) holds without Ex({indexedName thingNames y}), but no such world exists in the current `Ex` facts",
        yWithoutZ.cost + zWithoutY.cost + 1⟩
  | some _, some _ => ⟨none, yWithoutZ.cost + zWithoutY.cost + 1⟩

private def firstExternalIndependenceFailure?
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    Option String :=
  (firstExternalIndependenceFailureCosted worldNames thingNames tables y z).value

private theorem firstExternalIndependenceFailureCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (y z : Nat) :
    (firstExternalIndependenceFailureCosted worldNames thingNames tables y z).cost ≤
      8 * worldNames.size + 3 := by
  have hyz := firstExWithoutCosted_cost_le worldNames.size tables y z
  have hzy := firstExWithoutCosted_cost_le worldNames.size tables z y
  simp only [firstExternalIndependenceFailureCosted]
  split <;> change
      (firstExWithoutCosted worldNames.size tables y z).cost +
        (firstExWithoutCosted worldNames.size tables z y).cost + 1 ≤ _ <;>
    omega

private def firstExternalBearerFailureFromCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    List Nat → Complexity.Costed String
  | List.nil =>
      ⟨"no concrete missing `Ex` witness was isolated; inspect the `Ex` and `InheresIn` facts used by external dependence.", 1⟩
  | List.cons z zs =>
      if tables.binaryLookup "inheresIn" x z w then
        let independence :=
          firstExternalIndependenceFailureCosted worldNames thingNames tables y z
        match independence.value with
        | some reason =>
            ⟨s!"`{indexedName thingNames x}` inheres in `{indexedName thingNames z}` at `{indexedName worldNames w}`, but `{indexedName thingNames y}` is not existentially independent from that bearer: {reason}.",
              independence.cost + 4⟩
        | none =>
            Complexity.Costed.charge (independence.cost + 3) <|
              firstExternalBearerFailureFromCosted worldNames thingNames tables x y w zs
      else
        Complexity.Costed.charge 2 <|
          firstExternalBearerFailureFromCosted worldNames thingNames tables x y w zs

private theorem firstExternalBearerFailureFromCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat)
    (zs : List Nat) :
    (firstExternalBearerFailureFromCosted worldNames thingNames tables x y w zs).cost ≤
      zs.length * (8 * worldNames.size + 7) + 1 := by
  induction zs with
  | nil => simp [firstExternalBearerFailureFromCosted]
  | cons z zs ih =>
      have hindependence := firstExternalIndependenceFailureCosted_cost_le
        worldNames thingNames tables y z
      simp only [firstExternalBearerFailureFromCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (firstExternalIndependenceFailureCosted
            worldNames thingNames tables y z).cost + 4 ≤ _
          omega
        · simp only [Complexity.Costed.charge_cost]
          omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def firstExternallyDependentFailureReasonCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    Complexity.Costed String :=
  let boxFailure := firstBoxExImpFailureCosted worldNames tables x y
  match boxFailure.value with
  | some witnessWorld =>
      ⟨s!"`{indexedName thingNames x}` exists at `{indexedName worldNames witnessWorld}`, but `{indexedName thingNames y}` does not; this breaks existential dependence.",
        boxFailure.cost + 1⟩
  | none =>
      Complexity.Costed.charge boxFailure.cost <|
        firstExternalBearerFailureFromCosted worldNames thingNames tables x y w
          (List.range thingNames.size)

private theorem firstExternallyDependentFailureReasonCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    (firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w).cost ≤
      4 * worldNames.size + 1 +
        thingNames.size * (8 * worldNames.size + 7) + 1 := by
  have hbox := firstExWithoutCosted_cost_le worldNames.size tables x y
  change (firstBoxExImpFailureCosted worldNames tables x y).cost ≤
    4 * worldNames.size + 1 at hbox
  have hbearer := firstExternalBearerFailureFromCosted_cost_le
    worldNames thingNames tables x y w (List.range thingNames.size)
  simp only [List.length_range] at hbearer
  simp only [firstExternallyDependentFailureReasonCosted]
  split
  · change (firstBoxExImpFailureCosted worldNames tables x y).cost + 1 ≤ _
    exact Nat.le_trans (Nat.add_le_add_right hbox 1) (by omega)
  · simp only [Complexity.Costed.charge_cost]
    change (firstBoxExImpFailureCosted worldNames tables x y).cost +
      (firstExternalBearerFailureFromCosted worldNames thingNames tables x y w
        (List.range thingNames.size)).cost ≤ _
    omega

private def firstExternallyDependentFailureReason
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) : String :=
  (firstExternallyDependentFailureReasonCosted worldNames thingNames tables x y w).value

private def externallyDependentWitnessesFromCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (ys : List Nat) (out : Array Nat) : Complexity.Costed (Array Nat) :=
  match ys with
  | List.nil => ⟨out, 0⟩
  | List.cons y ys =>
      let dependent := externallyDependentLookupCosted
        worldNames.size thingNames.size tables x y w
      if dependent.value then
        Complexity.Costed.charge (dependent.cost + 2) <|
          externallyDependentWitnessesFromCosted worldNames thingNames tables x w ys
            (out.push y)
      else
        Complexity.Costed.charge (dependent.cost + 1) <|
          externallyDependentWitnessesFromCosted worldNames thingNames tables x w ys out

private def externallyDependentWitnessesCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  externallyDependentWitnessesFromCosted worldNames thingNames tables x w
    (List.range thingNames.size) #[]

private def externallyDependentWitnessCostBound (worldCount thingCount : Nat) : Nat :=
  6 * worldCount + thingCount * (12 * worldCount + 6) + 3

private theorem externallyDependentWitnessesFromCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (ys : List Nat) (out : Array Nat) :
    (externallyDependentWitnessesFromCosted worldNames thingNames tables x w ys out).cost ≤
      ys.length * externallyDependentWitnessCostBound worldNames.size thingNames.size := by
  induction ys generalizing out with
  | nil => simp [externallyDependentWitnessesFromCosted]
  | cons y ys ih =>
      have hdependent := externallyDependentLookupCosted_cost_le
        worldNames.size thingNames.size tables x y w
      simp only [externallyDependentWitnessesFromCosted, List.length_cons, Nat.add_mul]
      split
      · simp only [Complexity.Costed.charge_cost]
        have htail := ih (out := out.push y)
        unfold externallyDependentWitnessCostBound at htail ⊢
        omega
      · simp only [Complexity.Costed.charge_cost]
        have htail := ih (out := out)
        unfold externallyDependentWitnessCostBound at htail ⊢
        omega

private theorem externallyDependentWitnessesCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).cost ≤
      thingNames.size *
        externallyDependentWitnessCostBound worldNames.size thingNames.size := by
  simpa [externallyDependentWitnessesCosted] using
    externallyDependentWitnessesFromCosted_cost_le worldNames thingNames tables x w
      (List.range thingNames.size) #[]

private theorem externallyDependentWitnessesFromCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (ys : List Nat) (out : Array Nat) :
    (externallyDependentWitnessesFromCosted worldNames thingNames tables x w ys out).value.size ≤
      out.size + ys.length := by
  induction ys generalizing out with
  | nil => simp [externallyDependentWitnessesFromCosted]
  | cons y ys ih =>
      simp only [externallyDependentWitnessesFromCosted, List.length_cons]
      split
      · simp only [Complexity.Costed.charge_value]
        have htail := ih (out := out.push y)
        simp only [Array.size_push] at htail
        omega
      · simp only [Complexity.Costed.charge_value]
        have htail := ih (out := out)
        omega

private theorem externallyDependentWitnessesCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value.size ≤
      thingNames.size := by
  simpa [externallyDependentWitnessesCosted] using
    externallyDependentWitnessesFromCosted_size_le worldNames thingNames tables x w
      (List.range thingNames.size) #[]

private def externallyDependentWitnesses
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array Nat :=
  (externallyDependentWitnessesCosted worldNames thingNames tables x w).value

@[simp] private theorem externallyDependentWitnessesCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (externallyDependentWitnessesCosted worldNames thingNames tables x w).value =
      externallyDependentWitnesses worldNames thingNames tables x w := rfl

private def declaredExternalCandidatesFromCosted
    (tables : FactTables) (x w : Nat) (ys : List Nat) (out : Array Nat) :
    Complexity.Costed (Array Nat) :=
  match ys with
  | List.nil => ⟨out, 0⟩
  | List.cons y ys =>
      if tables.binaryLookup "externallyDependent" x y w then
        Complexity.Costed.charge 3 <|
          declaredExternalCandidatesFromCosted tables x w ys (out.push y)
      else if assertedDerivedBinaryLookup tables "ExternallyDependent" x y w then
        Complexity.Costed.charge 4 <|
          declaredExternalCandidatesFromCosted tables x w ys (out.push y)
      else
        Complexity.Costed.charge 3 <|
          declaredExternalCandidatesFromCosted tables x w ys out

private def declaredExternalCandidatesCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  declaredExternalCandidatesFromCosted tables x w (List.range thingCount) #[]

private theorem declaredExternalCandidatesFromCosted_cost_le
    (tables : FactTables) (x w : Nat) (ys : List Nat) (out : Array Nat) :
    (declaredExternalCandidatesFromCosted tables x w ys out).cost ≤ 4 * ys.length := by
  induction ys generalizing out with
  | nil => simp [declaredExternalCandidatesFromCosted]
  | cons y ys ih =>
      simp only [declaredExternalCandidatesFromCosted, List.length_cons]
      split
      · simp only [Complexity.Costed.charge_cost]
        have htail := ih (out := out.push y)
        omega
      · split
        · simp only [Complexity.Costed.charge_cost]
          have htail := ih (out := out.push y)
          omega
        · simp only [Complexity.Costed.charge_cost]
          have htail := ih (out := out)
          omega

private theorem declaredExternalCandidatesCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (declaredExternalCandidatesCosted thingCount tables x w).cost ≤ 4 * thingCount := by
  simpa [declaredExternalCandidatesCosted] using
    declaredExternalCandidatesFromCosted_cost_le tables x w (List.range thingCount) #[]

private theorem declaredExternalCandidatesFromCosted_size_le
    (tables : FactTables) (x w : Nat) (ys : List Nat) (out : Array Nat) :
    (declaredExternalCandidatesFromCosted tables x w ys out).value.size ≤
      out.size + ys.length := by
  induction ys generalizing out with
  | nil => simp [declaredExternalCandidatesFromCosted]
  | cons y ys ih =>
      simp only [declaredExternalCandidatesFromCosted, List.length_cons]
      split
      · simp only [Complexity.Costed.charge_value]
        have htail := ih (out := out.push y)
        simp only [Array.size_push] at htail
        omega
      · split
        · simp only [Complexity.Costed.charge_value]
          have htail := ih (out := out.push y)
          simp only [Array.size_push] at htail
          omega
        · simp only [Complexity.Costed.charge_value]
          have htail := ih (out := out)
          omega

private theorem declaredExternalCandidatesCosted_size_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (declaredExternalCandidatesCosted thingCount tables x w).value.size ≤ thingCount := by
  simpa [declaredExternalCandidatesCosted] using
    declaredExternalCandidatesFromCosted_size_le tables x w (List.range thingCount) #[]

private def firstInheresCandidateFromCosted
    (tables : FactTables) (x w : Nat) (fallback : Option Nat) :
    List Nat → Complexity.Costed (Option Nat)
  | List.nil => ⟨fallback, 1⟩
  | List.cons z zs =>
      if tables.binaryLookup "inheresIn" x z w then
        ⟨some z, 3⟩
      else
        Complexity.Costed.charge 2 <|
          firstInheresCandidateFromCosted tables x w fallback zs

private theorem firstInheresCandidateFromCosted_cost_le
    (tables : FactTables) (x w : Nat) (fallback : Option Nat) (zs : List Nat) :
    (firstInheresCandidateFromCosted tables x w fallback zs).cost ≤
      3 * zs.length + 1 := by
  induction zs with
  | nil => simp [firstInheresCandidateFromCosted]
  | cons z zs ih =>
      simp only [firstInheresCandidateFromCosted, List.length_cons]
      split
      · change 3 ≤ 3 * (zs.length + 1) + 1
        omega
      · simp only [Complexity.Costed.charge_cost]
        omega

private def firstModeStatusCandidateCosted
    (thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (declared : Array Nat) : Complexity.Costed (Option Nat) :=
  match declared[0]? with
  | some candidate => ⟨some candidate, 1⟩
  | none =>
      firstInheresCandidateFromCosted tables x w
        (if thingNames.isEmpty then none else some 0) (List.range thingNames.size)

private theorem firstModeStatusCandidateCosted_cost_le
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) (declared : Array Nat) :
    (firstModeStatusCandidateCosted thingNames tables x w declared).cost ≤
      3 * thingNames.size + 1 := by
  unfold firstModeStatusCandidateCosted
  split
  · change 1 ≤ 3 * thingNames.size + 1
    omega
  · simpa using firstInheresCandidateFromCosted_cost_le tables x w
      (if thingNames.isEmpty then none else some 0) (List.range thingNames.size)

private def renderExternallyDependentModeStatusCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array String) :=
  if !tables.unaryLookup "mode" x w then
    ⟨#[s!"  - Computed ExternallyDependentMode: false, because `{indexedName thingNames x}` is not a `Mode` at `{indexedName worldNames w}`."], 2⟩
  else
    let witnesses := externallyDependentWitnessesCosted worldNames thingNames tables x w
    if witnesses.value.isEmpty then
      let declaredCandidates :=
        declaredExternalCandidatesCosted thingNames.size tables x w
      let candidate :=
        firstModeStatusCandidateCosted thingNames tables x w declaredCandidates.value
      let firstReason : Complexity.Costed String :=
        match candidate.value with
        | none =>
          ⟨"there are no candidate things to witness external dependence.", 1⟩
        | some candidate =>
          firstExternallyDependentFailureReasonCosted worldNames thingNames tables x candidate w
      let out := #[
          s!"  - Computed ExternallyDependentMode: false. `{indexedName thingNames x}` is a `Mode`, but no thing witnesses computed `ExternallyDependent({indexedName thingNames x}, y)`.",
          s!"  - First candidate check: {firstReason.value}"
        ]
      let cost := witnesses.cost + declaredCandidates.cost + candidate.cost +
        firstReason.cost + 4
      if !declaredCandidates.value.isEmpty then
        let declared := String.intercalate ", " <|
          declaredCandidates.value.toList.map (indexedName thingNames ·)
        ⟨out.push s!"  - Note: asserted `ExternallyDependent` facts name candidate(s) {declared}, but certification uses the computed external-dependence semantics.",
          cost + declaredCandidates.value.size + 1⟩
      else
        ⟨out, cost⟩
    else
      let rendered := String.intercalate ", " <|
        witnesses.value.toList.map (indexedName thingNames ·)
      ⟨#[s!"  - Computed ExternallyDependentMode: true, witnessed by {rendered}."],
        witnesses.cost + witnesses.value.size + 2⟩

private def renderExternallyDependentModeStatus
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value

private def externallyDependentModeStatusCostBound
    (worldCount thingCount : Nat) : Nat :=
  thingCount * externallyDependentWitnessCostBound worldCount thingCount +
    8 * thingCount +
    (4 * worldCount + 1 + thingCount * (8 * worldCount + 7) + 1) + 6

private theorem renderExternallyDependentModeStatusCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).cost ≤
      externallyDependentModeStatusCostBound worldNames.size thingNames.size := by
  have hwitnessCost := externallyDependentWitnessesCosted_cost_le
    worldNames thingNames tables x w
  have hwitnessSize := externallyDependentWitnessesCosted_size_le
    worldNames thingNames tables x w
  have hdeclaredCost := declaredExternalCandidatesCosted_cost_le
    thingNames.size tables x w
  have hdeclaredSize := declaredExternalCandidatesCosted_size_le
    thingNames.size tables x w
  simp only [renderExternallyDependentModeStatusCosted]
  split
  · unfold externallyDependentModeStatusCostBound
    change 2 ≤ _
    omega
  · split
    · have hcandidate := firstModeStatusCandidateCosted_cost_le thingNames tables x w
        (declaredExternalCandidatesCosted thingNames.size tables x w).value
      have hreason :
          (match (firstModeStatusCandidateCosted thingNames tables x w
              (declaredExternalCandidatesCosted thingNames.size tables x w).value).value with
            | none => (⟨"there are no candidate things to witness external dependence.", 1⟩ :
                Complexity.Costed String)
            | some candidate =>
                firstExternallyDependentFailureReasonCosted
                  worldNames thingNames tables x candidate w).cost ≤
            4 * worldNames.size + 1 +
              thingNames.size * (8 * worldNames.size + 7) + 1 := by
        split
        · change 1 ≤ 4 * worldNames.size + 1 +
            thingNames.size * (8 * worldNames.size + 7) + 1
          omega
        · exact firstExternallyDependentFailureReasonCosted_cost_le
            worldNames thingNames tables x _ w
      split
      · change (externallyDependentWitnessesCosted worldNames thingNames tables x w).cost +
          (declaredExternalCandidatesCosted thingNames.size tables x w).cost +
          (firstModeStatusCandidateCosted thingNames tables x w
            (declaredExternalCandidatesCosted thingNames.size tables x w).value).cost +
          (match (firstModeStatusCandidateCosted thingNames tables x w
              (declaredExternalCandidatesCosted thingNames.size tables x w).value).value with
            | none => (⟨"there are no candidate things to witness external dependence.", 1⟩ :
                Complexity.Costed String)
            | some candidate => firstExternallyDependentFailureReasonCosted
                worldNames thingNames tables x candidate w).cost + 4 +
          (declaredExternalCandidatesCosted thingNames.size tables x w).value.size + 1 ≤ _
        unfold externallyDependentModeStatusCostBound
        omega
      · change (externallyDependentWitnessesCosted worldNames thingNames tables x w).cost +
          (declaredExternalCandidatesCosted thingNames.size tables x w).cost +
          (firstModeStatusCandidateCosted thingNames tables x w
            (declaredExternalCandidatesCosted thingNames.size tables x w).value).cost +
          (match (firstModeStatusCandidateCosted thingNames tables x w
              (declaredExternalCandidatesCosted thingNames.size tables x w).value).value with
            | none => (⟨"there are no candidate things to witness external dependence.", 1⟩ :
                Complexity.Costed String)
            | some candidate => firstExternallyDependentFailureReasonCosted
                worldNames thingNames tables x candidate w).cost + 4 ≤ _
        unfold externallyDependentModeStatusCostBound
        omega
    · change (externallyDependentWitnessesCosted worldNames thingNames tables x w).cost +
        (externallyDependentWitnessesCosted worldNames thingNames tables x w).value.size + 2 ≤ _
      unfold externallyDependentModeStatusCostBound
      omega

private theorem renderExternallyDependentModeStatusCosted_size_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value.size ≤ 3 := by
  simp only [renderExternallyDependentModeStatusCosted]
  split
  · simp
  · split
    · split <;> simp
    · simp

@[simp] private theorem renderExternallyDependentModeStatusCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value =
      renderExternallyDependentModeStatus worldNames thingNames tables x w := rfl

private def qualityKindCandidates
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    for q in [:thingCount] do
      if tables.unaryLookup "qualityKind" q w && tables.binaryLookup "inst" x q w then
        out := out.push q
    return out

private def qualityStatusEvidence
    (thingNames : Array Name) (tables : FactTables) (x w : Nat) : Array String :=
  let candidates := qualityKindCandidates thingNames.size tables x w
  if candidates.isEmpty then
    #[s!"  - Computed Quality: false, because `{indexedName thingNames x}` instantiates no `QualityKind` at this world."]
  else if candidates.size == 1 then
    let q := candidates[0]!
    #[s!"  - Computed Quality: true, uniquely witnessed by `QualityKind({indexedName thingNames q})` and `{indexedName thingNames x} :: {indexedName thingNames q}`."]
  else
    let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
    #[s!"  - Computed Quality: false, because `{indexedName thingNames x}` instantiates multiple quality kinds at this world: {rendered}."]

private def qualityTypeAssociations
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Array Nat :=
  Id.run do
    let mut out := #[]
    for t in [:thingCount] do
      if tables.unaryLookup "qualityType" t w && tables.binaryLookup "associatedWith" x t w then
        out := out.push t
    return out

private def firstInheringThing?
    (thingCount : Nat) (tables : FactTables) (x w : Nat) : Option Nat :=
  Id.run do
    for y in [:thingCount] do
      if tables.binaryLookup "inheresIn" y x w then
        return some y
    return none

private def firstMember?
    (thingCount : Nat) (tables : FactTables) (s w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if memberLookup tables x s w then
        return some x
    return none

private def firstCoveredInstanceFailure?
    (thingCount : Nat) (tables : FactTables) (t t' t'' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x t w &&
          !(tables.binaryLookup "inst" x t' w || tables.binaryLookup "inst" x t'' w) then
        return some x
    return none

private def firstSharedInstance?
    (thingCount : Nat) (tables : FactTables) (t t' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x t w && tables.binaryLookup "inst" x t' w then
        return some x
    return none

private def firstCategorizationFailure?
    (thingCount : Nat) (tables : FactTables) (category target w : Nat) :
    Option Nat :=
  Id.run do
    for instType in [:thingCount] do
      if tables.binaryLookup "inst" instType category w &&
          !tables.binaryLookup "sub" instType target w then
        return some instType
    return none

private def firstGfdFailure?
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x x' w && tables.binaryLookup "functionsAs" x x' w then
        let found := Id.run do
          for y in [:thingCount] do
            if y != x && tables.binaryLookup "inst" y y' w &&
                tables.binaryLookup "functionsAs" y y' w then
              return true
          return false
        if !found then
          return some x
    return none

private def firstGcdFailure?
    (thingCount : Nat) (tables : FactTables) (x' y' w : Nat) : Option Nat :=
  Id.run do
    for x in [:thingCount] do
      if tables.binaryLookup "inst" x x' w then
        let found := Id.run do
          for y in [:thingCount] do
            if tables.binaryLookup "inst" y y' w &&
                tables.binaryLookup "constitutedBy" x y w then
              return true
          return false
        if !found then
          return some x
    return none

private def derivedAssertionRequiredMissing
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : String :=
  let fallback :=
    s!"asserted derived relation `{namedDerivedFactSummary fact}` must be true under the computed semantics at `{indexedName worldNames w}`, but its definition evaluates to false."
  match fact with
  | .unary "Quality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let candidates := qualityKindCandidates thingNames.size tables xIdx w
          if candidates.isEmpty then
            s!"`Quality({indexedName thingNames xIdx})` requires exactly one `QualityKind` instantiation; missing any `QualityKind(k)` with `{indexedName thingNames xIdx} :: k` at `{indexedName worldNames w}`."
          else
            let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
            s!"`Quality({indexedName thingNames xIdx})` requires exactly one `QualityKind` instantiation; found competing quality kinds {rendered} at `{indexedName worldNames w}`."
      | none => fallback
  | .unary "ExternallyDependentMode" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "mode" xIdx w then
            s!"`ExternallyDependentMode({indexedName thingNames xIdx})` requires `Mode({indexedName thingNames xIdx})` and some computed `ExternallyDependent({indexedName thingNames xIdx}, y)`; missing `Mode({indexedName thingNames xIdx})` at `{indexedName worldNames w}`."
          else
            let declaredCandidates := Id.run do
              let mut out := #[]
              for y in [:thingNames.size] do
                if tables.binaryLookup "externallyDependent" xIdx y w ||
                    assertedDerivedBinaryLookup tables "ExternallyDependent" xIdx y w then
                  out := out.push y
              return out
            let candidate? :=
              declaredCandidates[0]? <|>
                Id.run do
                  for z in [:thingNames.size] do
                    if tables.binaryLookup "inheresIn" xIdx z w then
                      return some z
                  return none
            match candidate? with
            | some yIdx =>
                s!"`ExternallyDependentMode({indexedName thingNames xIdx})` requires `Mode({indexedName thingNames xIdx})` and at least one computed `ExternallyDependent({indexedName thingNames xIdx}, y)`; missing such a witness. Candidate `{indexedName thingNames yIdx}` fails because {firstExternallyDependentFailureReason worldNames thingNames tables xIdx yIdx w}"
            | none =>
                s!"`ExternallyDependentMode({indexedName thingNames xIdx})` requires `Mode({indexedName thingNames xIdx})` and at least one computed `ExternallyDependent({indexedName thingNames xIdx}, y)`; missing any candidate witness and any relevant `InheresIn` bearer evidence."
      | none => fallback
  | .binary "ExternallyDependent" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          s!"`ExternallyDependent({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires existential dependence plus independence from every bearer of `{indexedName thingNames xIdx}`; missing condition: {firstExternallyDependentFailureReason worldNames thingNames tables xIdx yIdx w}"
      | _, _ => fallback
  | .binary "ExistentialDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstBoxExImpFailure? worldNames tables xIdx yIdx with
          | some witnessWorld =>
              s!"`ExistentialDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires `Ex({indexedName thingNames yIdx})` in every world where `Ex({indexedName thingNames xIdx})` holds; missing `Ex({indexedName thingNames yIdx})` at `{indexedName worldNames witnessWorld}`."
          | none => fallback
      | _, _ => fallback
  | .binary "ExistentialIndependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstExternalIndependenceFailure? worldNames thingNames tables xIdx yIdx with
          | some reason =>
              s!"`ExistentialIndependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires two modal `Ex` separation witnesses; missing condition: {reason}."
          | none => fallback
      | _, _ => fallback
  | .unary "NonEmptySet" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          s!"`NonEmptySet({indexedName thingNames xIdx})` requires some `MemberOf(member, {indexedName thingNames xIdx})`; missing any member at `{indexedName worldNames w}`."
      | none => fallback
  | .unary "QualityStructure" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let candidates := qualityTypeAssociations thingNames.size tables xIdx w
          if candidates.isEmpty then
            s!"`QualityStructure({indexedName thingNames xIdx})` requires exactly one associated `QualityType`; missing any `AssociatedWith({indexedName thingNames xIdx}, t)` where `QualityType(t)` holds."
          else
            let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
            s!"`QualityStructure({indexedName thingNames xIdx})` requires exactly one associated `QualityType`; found competing associated quality types {rendered}."
      | none => fallback
  | .unary "SimpleQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            s!"`SimpleQuality({indexedName thingNames xIdx})` requires computed `Quality({indexedName thingNames xIdx})`; missing the quality condition."
          else
            match firstInheringThing? thingNames.size tables xIdx w with
            | some yIdx =>
                s!"`SimpleQuality({indexedName thingNames xIdx})` requires no thing to inhere in it; conflicting `InheresIn({indexedName thingNames yIdx}, {indexedName thingNames xIdx})` is present."
            | none => fallback
      | none => fallback
  | .unary "ComplexQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            s!"`ComplexQuality({indexedName thingNames xIdx})` requires computed `Quality({indexedName thingNames xIdx})`; missing the quality condition."
          else
            s!"`ComplexQuality({indexedName thingNames xIdx})` requires at least one `InheresIn(part, {indexedName thingNames xIdx})`; missing any inhering part."
      | none => fallback
  | .unary "SimpleQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            s!"`SimpleQualityType({indexedName thingNames xIdx})` requires `QualityType({indexedName thingNames xIdx})`; missing that primitive classification."
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !simpleQualityLookup thingNames.size tables y w then
                  return s!"`SimpleQualityType({indexedName thingNames xIdx})` requires every instance to be a computed `SimpleQuality`; instance `{indexedName thingNames y}` is not simple."
              return fallback
      | none => fallback
  | .unary "ComplexQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            s!"`ComplexQualityType({indexedName thingNames xIdx})` requires `QualityType({indexedName thingNames xIdx})`; missing that primitive classification."
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !complexQualityLookup thingNames.size tables y w then
                  return s!"`ComplexQualityType({indexedName thingNames xIdx})` requires every instance to be a computed `ComplexQuality`; instance `{indexedName thingNames y}` is not complex."
              return fallback
      | none => fallback
  | .unary "QuaIndividual" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          s!"`QuaIndividual({indexedName thingNames xIdx})` requires some `QuaIndividualOf({indexedName thingNames xIdx}, y)`; missing any such fact at `{indexedName worldNames w}`."
      | none => fallback
  | .binary "UltimateBearerOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if tables.unaryLookup "moment" xIdx w then
            s!"`UltimateBearerOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires bearer `{indexedName thingNames xIdx}` not to be a `Moment`; conflicting `Moment({indexedName thingNames xIdx})` holds."
          else
            s!"`UltimateBearerOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires an `InheresIn` path from `{indexedName thingNames yIdx}` to bearer `{indexedName thingNames xIdx}`; missing that path at `{indexedName worldNames w}`."
      | _, _ => fallback
  | .binary "SubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          Id.run do
            for z in [:thingNames.size] do
              if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                return s!"`SubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires every left member to be a right member; `{indexedName thingNames z}` is in `{indexedName thingNames xIdx}` but missing from `{indexedName thingNames yIdx}`."
            return fallback
      | _, _ => fallback
  | .binary "ProperSubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !subsetLookup thingNames.size tables xIdx yIdx w then
            Id.run do
              for z in [:thingNames.size] do
                if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                  return s!"`ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` first requires `SubsetOf`; `{indexedName thingNames z}` is in the left set but missing from the right set."
              return s!"`ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` first requires `SubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; that subset condition is false."
          else
            s!"`ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires strictness; missing a member of `{indexedName thingNames yIdx}` that is not also a member of `{indexedName thingNames xIdx}`."
      | _, _ => fallback
  | .binary "ProperSub" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !tables.binaryLookup "sub" xIdx yIdx w then
            s!"`ProperSub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires `Sub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; missing the forward `Sub` fact."
          else
            s!"`ProperSub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires absence of reverse `Sub`; conflicting `Sub({indexedName thingNames yIdx}, {indexedName thingNames xIdx})` is present."
      | _, _ => fallback
  | .binary "GenericFunctionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGfdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              s!"`GenericFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires a distinct target-functioning witness for source-functioning `{indexedName thingNames witness}`; missing such a `{indexedName thingNames yIdx}` instance."
          | none => fallback
      | _, _ => fallback
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !genericFunctionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `GenericFunctionalDependence({indexedName thingNames xTypeIdx}, {indexedName thingNames yTypeIdx})`; that computed type-level dependence is false."
          else if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}`; missing that instantiation."
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}`; missing that instantiation."
          else
            s!"`IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames yIdx}` to function as `{indexedName thingNames yTypeIdx}` whenever `{indexedName thingNames xIdx}` functions as `{indexedName thingNames xTypeIdx}`; missing the target `FunctionsAs` fact."
      | _, _, _, _ => fallback
  | .quaternary "ComponentOf" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "properPart" xIdx yIdx w then
            s!"`ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `ProperPart({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; missing that proper-part fact."
          else
            s!"`ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` also requires computed `IndividualFunctionalDependence`; that dependence is false."
      | _, _, _, _ => fallback
  | .binary "GenericConstitutionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGcdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              s!"`GenericConstitutionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires a `{indexedName thingNames yIdx}` instance that constitutionally bears source instance `{indexedName thingNames witness}`; missing such a `ConstitutedBy({indexedName thingNames witness}, _)` witness."
          | none => fallback
      | _, _ => fallback
  | .quaternary "Constitution" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}`; missing that instantiation."
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}`; missing that instantiation."
          else if !genericConstitutionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires computed `GenericConstitutionalDependence({indexedName thingNames xTypeIdx}, {indexedName thingNames yTypeIdx})`; that dependence is false."
          else
            s!"`Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})` requires `ConstitutedBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`; missing that fact."
      | _, _, _, _ => fallback
  | .binary "Categorizes" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !typeLookup worldNames.size thingNames.size tables xIdx then
            s!"`Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires `{indexedName thingNames xIdx}` to be a computed `Type`; missing any possible instance."
          else
            match firstCategorizationFailure? thingNames.size tables xIdx yIdx w with
            | some instType =>
                s!"`Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires each category-instance type to specialize `{indexedName thingNames yIdx}`; missing `Sub({indexedName thingNames instType}, {indexedName thingNames yIdx})`."
            | none => fallback
      | _, _ => fallback
  | .binary "IsDisjointWith" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstSharedInstance? thingNames.size tables xIdx yIdx w with
          | some z =>
              s!"`IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires no shared instance; `{indexedName thingNames z}` instantiates both types."
          | none =>
              s!"`IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` requires both arguments to be computed types and have no shared instance; missing typehood for one argument."
      | _, _ => fallback
  | .ternary "IsCompletelyCoveredBy" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              s!"`IsCompletelyCoveredBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})` requires every `{indexedName thingNames xIdx}` instance to instantiate at least one covering type; `{indexedName thingNames instIdx}` instantiates neither `{indexedName thingNames yIdx}` nor `{indexedName thingNames zIdx}`."
          | none => fallback
      | _, _, _ => fallback
  | .ternary "IsPartitionedInto" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              s!"`IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})` first requires complete coverage; `{indexedName thingNames instIdx}` instantiates the partitioned type but neither part type."
          | none =>
              match firstSharedInstance? thingNames.size tables yIdx zIdx w with
              | some instIdx =>
                  s!"`IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})` also requires disjoint parts; `{indexedName thingNames instIdx}` instantiates both part types."
              | none => fallback
      | _, _, _ => fallback
  | _ => fallback

private def derivedAssertionEvidence
    (worldNames thingNames : Array Name) (tables : FactTables)
    (fact : NamedDerivedFact) (w : Nat) : Array String :=
  match fact with
  | .unary "Quality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          #[s!"  - User assertion: `Quality({indexedName thingNames xIdx})`."] ++
            qualityStatusEvidence thingNames tables xIdx w
      | none => #[]
  | .unary "ExternallyDependentMode" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          #[
            s!"  - User assertion: `ExternallyDependentMode({indexedName thingNames xIdx})`.",
            "  - Certification treats this as a computed predicate, not as a primitive classification."
          ] ++ renderExternallyDependentModeStatus worldNames thingNames tables xIdx w
      | none => #[]
  | .binary "ExternallyDependent" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          #[
            s!"  - User assertion: `ExternallyDependent({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
            "  - Certification computes this from existential dependence plus existential independence from every bearer.",
            s!"  - Computed ExternallyDependent: false. {firstExternallyDependentFailureReason worldNames thingNames tables xIdx yIdx w}"
          ]
      | _, _ => #[]
  | .binary "ExistentialDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstBoxExImpFailure? worldNames tables xIdx yIdx with
          | some witnessWorld =>
              #[
                s!"  - User assertion: `ExistentialDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed ExistentialDependence: false, because `{indexedName thingNames xIdx}` exists at `{indexedName worldNames witnessWorld}` but `{indexedName thingNames yIdx}` does not."
              ]
          | none =>
              #[
                s!"  - User assertion: `ExistentialDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              "  - No concrete `Ex` counter-witness was isolated; inspect world-scoped `Ex` facts."
              ]
      | _, _ => #[]
  | .binary "UltimateBearerOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          let bearerIsMoment := tables.unaryLookup "moment" xIdx w
          let path? := tables.momentOfPath? thingNames.size w yIdx xIdx
          let pathEvidence :=
            match path? with
            | some path =>
                s!"`InheresIn` path exists: {renderThingPath thingNames path}."
            | none =>
                s!"no `InheresIn` path reaches `{indexedName thingNames xIdx}` from `{indexedName thingNames yIdx}` at `{indexedName worldNames w}`."
          #[
            s!"  - User assertion: `UltimateBearerOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
            s!"  - Bearer `{indexedName thingNames xIdx}` is a Moment: {if bearerIsMoment then "true" else "false"}.",
            s!"  - {pathEvidence}"
          ]
      | _, _ => #[]
  | .binary "ExistentialIndependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstExternalIndependenceFailure? worldNames thingNames tables xIdx yIdx with
          | some reason =>
              #[
                s!"  - User assertion: `ExistentialIndependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed ExistentialIndependence: false: {reason}."
              ]
          | none =>
              #[
                s!"  - User assertion: `ExistentialIndependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              "  - No concrete missing independence witness was isolated; inspect world-scoped `Ex` facts."
              ]
      | _, _ => #[]
  | .unary "NonEmptySet" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          match firstMember? thingNames.size tables xIdx w with
          | some member =>
              #[
                s!"  - User assertion: `NonEmptySet({indexedName thingNames xIdx})`.",
                s!"  - Computed NonEmptySet: true, witnessed by `MemberOf({indexedName thingNames member}, {indexedName thingNames xIdx})` at `{indexedName worldNames w}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `NonEmptySet({indexedName thingNames xIdx})`.",
                s!"  - Computed NonEmptySet: false, because no `MemberOf(_, {indexedName thingNames xIdx})` fact holds at `{indexedName worldNames w}`."
              ]
      | none => #[]
  | .unary "QualityStructure" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let candidates := qualityTypeAssociations thingNames.size tables xIdx w
          if candidates.isEmpty then
            #[
              s!"  - User assertion: `QualityStructure({indexedName thingNames xIdx})`.",
              s!"  - Computed QualityStructure: false, because `{indexedName thingNames xIdx}` is not associated with any `QualityType` at `{indexedName worldNames w}`."
            ]
          else if candidates.size == 1 then
            #[
              s!"  - User assertion: `QualityStructure({indexedName thingNames xIdx})`.",
              s!"  - Computed QualityStructure: true, uniquely associated with `{indexedName thingNames candidates[0]!}`."
            ]
          else
            let rendered := String.intercalate ", " <| candidates.toList.map (indexedName thingNames ·)
            #[
              s!"  - User assertion: `QualityStructure({indexedName thingNames xIdx})`.",
              s!"  - Computed QualityStructure: false, because multiple associated quality types are present: {rendered}."
            ]
      | none => #[]
  | .unary "SimpleQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            #[s!"  - User assertion: `SimpleQuality({indexedName thingNames xIdx})`."] ++
              qualityStatusEvidence thingNames tables xIdx w
          else
            match firstInheringThing? thingNames.size tables xIdx w with
            | some yIdx =>
                #[
                  s!"  - User assertion: `SimpleQuality({indexedName thingNames xIdx})`.",
                  s!"  - Computed SimpleQuality: false, because `{indexedName thingNames yIdx}` inheres in `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `SimpleQuality({indexedName thingNames xIdx})`.",
                  "  - Computed SimpleQuality: true, because it is a computed `Quality` and no thing inheres in it."
                ]
      | none => #[]
  | .unary "ComplexQuality" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !qualityLookup thingNames.size tables xIdx w then
            #[s!"  - User assertion: `ComplexQuality({indexedName thingNames xIdx})`."] ++
              qualityStatusEvidence thingNames tables xIdx w
          else
            match firstInheringThing? thingNames.size tables xIdx w with
            | some yIdx =>
                #[
                  s!"  - User assertion: `ComplexQuality({indexedName thingNames xIdx})`.",
                  s!"  - Computed ComplexQuality: true, witnessed by `InheresIn({indexedName thingNames yIdx}, {indexedName thingNames xIdx})` at `{indexedName worldNames w}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `ComplexQuality({indexedName thingNames xIdx})`.",
                  "  - Computed ComplexQuality: false, because it is a computed `Quality` but no thing inheres in it."
                ]
      | none => #[]
  | .unary "SimpleQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            #[
              s!"  - User assertion: `SimpleQualityType({indexedName thingNames xIdx})`.",
              s!"  - Computed SimpleQualityType: false, because `QualityType({indexedName thingNames xIdx})` is not true at `{indexedName worldNames w}`."
            ]
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !simpleQualityLookup thingNames.size tables y w then
                  return #[
                    s!"  - User assertion: `SimpleQualityType({indexedName thingNames xIdx})`.",
                    s!"  - Computed SimpleQualityType: false, because instance `{indexedName thingNames y}` is not a computed `SimpleQuality` at `{indexedName worldNames w}`."
                  ] ++ qualityStatusEvidence thingNames tables y w
              return #[
                s!"  - User assertion: `SimpleQualityType({indexedName thingNames xIdx})`.",
                "  - Computed SimpleQualityType: true; every current instance is a computed `SimpleQuality`."
              ]
      | none => #[]
  | .unary "ComplexQualityType" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          if !tables.unaryLookup "qualityType" xIdx w then
            #[
              s!"  - User assertion: `ComplexQualityType({indexedName thingNames xIdx})`.",
              s!"  - Computed ComplexQualityType: false, because `QualityType({indexedName thingNames xIdx})` is not true at `{indexedName worldNames w}`."
            ]
          else
            Id.run do
              for y in [:thingNames.size] do
                if tables.binaryLookup "inst" y xIdx w &&
                    !complexQualityLookup thingNames.size tables y w then
                  return #[
                    s!"  - User assertion: `ComplexQualityType({indexedName thingNames xIdx})`.",
                    s!"  - Computed ComplexQualityType: false, because instance `{indexedName thingNames y}` is not a computed `ComplexQuality` at `{indexedName worldNames w}`."
                  ] ++ qualityStatusEvidence thingNames tables y w
              return #[
                s!"  - User assertion: `ComplexQualityType({indexedName thingNames xIdx})`.",
                "  - Computed ComplexQualityType: true; every current instance is a computed `ComplexQuality`."
              ]
      | none => #[]
  | .unary "QuaIndividual" x =>
      match thingIndexByString? thingNames x with
      | some xIdx =>
          let qs := Id.run do
            let mut out := #[]
            for y in [:thingNames.size] do
              if tables.binaryLookup "quaIndividualOf" xIdx y w then
                out := out.push y
            return out
          if qs.isEmpty then
            #[
              s!"  - User assertion: `QuaIndividual({indexedName thingNames xIdx})`.",
              "  - Computed QuaIndividual: false, because no `QuaIndividualOf` fact has this thing on the left."
            ]
          else
            let rendered := String.intercalate ", " <| qs.toList.map (indexedName thingNames ·)
            #[
              s!"  - User assertion: `QuaIndividual({indexedName thingNames xIdx})`.",
              s!"  - `QuaIndividualOf` candidate(s) exist: {rendered}; inspect the corresponding §3.10 foundation diagnostics if certification still fails."
            ]
      | none => #[]
  | .binary "IsDisjointWith" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          Id.run do
            for z in [:thingNames.size] do
              if tables.binaryLookup "inst" z xIdx w && tables.binaryLookup "inst" z yIdx w then
                return #[
                  s!"  - User assertion: `IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed IsDisjointWith: false, because `{indexedName thingNames z}` instantiates both types at `{indexedName worldNames w}`."
                ]
            return #[
              s!"  - User assertion: `IsDisjointWith({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              "  - No shared instance was isolated; inspect typehood and instantiation facts."
            ]
      | _, _ => #[]
  | .binary "SubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          Id.run do
            for z in [:thingNames.size] do
              if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                return #[
                  s!"  - User assertion: `SubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed SubsetOf: false, because `{indexedName thingNames z}` is a member of `{indexedName thingNames xIdx}` but not of `{indexedName thingNames yIdx}` at `{indexedName worldNames w}`."
                ]
            return #[]
      | _, _ => #[]
  | .binary "ProperSubsetOf" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          let subsetOk := subsetLookup thingNames.size tables xIdx yIdx w
          if !subsetOk then
            Id.run do
              for z in [:thingNames.size] do
                if memberLookup tables z xIdx w && !memberLookup tables z yIdx w then
                  return #[
                    s!"  - User assertion: `ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                    s!"  - Computed ProperSubsetOf: false, because the subset condition already fails: `{indexedName thingNames z}` is a member of `{indexedName thingNames xIdx}` but not of `{indexedName thingNames yIdx}` at `{indexedName worldNames w}`."
                  ]
              return #[
                s!"  - User assertion: `ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                "  - Computed ProperSubsetOf: false, because the subset condition fails."
              ]
          else
            #[
              s!"  - User assertion: `ProperSubsetOf({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              s!"  - Computed ProperSubsetOf: false, because no member of `{indexedName thingNames yIdx}` is outside `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`."
            ]
      | _, _ => #[]
  | .binary "ProperSub" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          let sub := tables.binaryLookup "sub" xIdx yIdx w
          let reverse := tables.binaryLookup "sub" yIdx xIdx w
          #[
            s!"  - User assertion: `ProperSub({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
            s!"  - Sub({indexedName thingNames xIdx}, {indexedName thingNames yIdx}): {if sub then "true" else "false"}.",
            s!"  - Reverse Sub({indexedName thingNames yIdx}, {indexedName thingNames xIdx}): {if reverse then "true" else "false"}."
          ]
      | _, _ => #[]
  | .binary "GenericFunctionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGfdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              #[
                s!"  - User assertion: `GenericFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed GenericFunctionalDependence: false, because `{indexedName thingNames witness}` instantiates and functions as `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`, but there is no distinct thing that instantiates and functions as `{indexedName thingNames yIdx}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `GenericFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                "  - Computed GenericFunctionalDependence: true; every current source-functioning instance has a distinct target-functioning witness."
              ]
      | _, _ => #[]
  | .quaternary "IndividualFunctionalDependence" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !genericFunctionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            match firstGfdFailure? thingNames.size tables xTypeIdx yTypeIdx w with
            | some witness =>
                #[
                  s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  s!"  - Computed IndividualFunctionalDependence: false, because type-level functional dependence fails for source witness `{indexedName thingNames witness}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  "  - Computed IndividualFunctionalDependence: false, because type-level functional dependence is false."
                ]
          else if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else
            #[
              s!"  - User assertion: `IndividualFunctionalDependence({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed IndividualFunctionalDependence: false, because `{indexedName thingNames xIdx}` functions as `{indexedName thingNames xTypeIdx}` but `{indexedName thingNames yIdx}` does not function as `{indexedName thingNames yTypeIdx}` at `{indexedName worldNames w}`."
            ]
      | _, _, _, _ => #[]
  | .quaternary "ComponentOf" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "properPart" xIdx yIdx w then
            #[
              s!"  - User assertion: `ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed ComponentOf: false, because `ProperPart({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` is missing at `{indexedName worldNames w}`."
            ]
          else
            let ifdReason :=
              if !genericFunctionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
                match firstGfdFailure? thingNames.size tables xTypeIdx yTypeIdx w with
                | some witness =>
                    s!"type-level functional dependence fails for source witness `{indexedName thingNames witness}`"
                | none => "type-level functional dependence is false"
              else if !tables.binaryLookup "inst" xIdx xTypeIdx w then
                s!"`{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}` is missing"
              else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
                s!"`{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}` is missing"
              else
                s!"`{indexedName thingNames xIdx}` functions as `{indexedName thingNames xTypeIdx}` but `{indexedName thingNames yIdx}` does not function as `{indexedName thingNames yTypeIdx}`"
            #[
              s!"  - User assertion: `ComponentOf({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed ComponentOf: false, because the required individual functional dependence is false: {ifdReason}."
            ]
      | _, _, _, _ => #[]
  | .binary "GenericConstitutionalDependence" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          match firstGcdFailure? thingNames.size tables xIdx yIdx w with
          | some witness =>
              #[
                s!"  - User assertion: `GenericConstitutionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                s!"  - Computed GenericConstitutionalDependence: false, because `{indexedName thingNames witness}` instantiates `{indexedName thingNames xIdx}` at `{indexedName worldNames w}`, but no `{indexedName thingNames yIdx}` instance is related by `ConstitutedBy({indexedName thingNames witness}, _)`."
              ]
          | none =>
              #[
                s!"  - User assertion: `GenericConstitutionalDependence({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                "  - Computed GenericConstitutionalDependence: true; every current source instance has a constituting target instance."
              ]
      | _, _ => #[]
  | .quaternary "Constitution" x x' y y' =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames x',
        thingIndexByString? thingNames y, thingIndexByString? thingNames y' with
      | some xIdx, some xTypeIdx, some yIdx, some yTypeIdx =>
          if !tables.binaryLookup "inst" xIdx xTypeIdx w then
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed Constitution: false, because `{indexedName thingNames xIdx} :: {indexedName thingNames xTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else if !tables.binaryLookup "inst" yIdx yTypeIdx w then
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed Constitution: false, because `{indexedName thingNames yIdx} :: {indexedName thingNames yTypeIdx}` is missing at `{indexedName worldNames w}`."
            ]
          else if !genericConstitutionalDependenceLookup thingNames.size tables xTypeIdx yTypeIdx w then
            match firstGcdFailure? thingNames.size tables xTypeIdx yTypeIdx w with
            | some witness =>
                #[
                  s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  s!"  - Computed Constitution: false, because generic constitutional dependence fails for source witness `{indexedName thingNames witness}`."
                ]
            | none =>
                #[
                  s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
                  "  - Computed Constitution: false, because generic constitutional dependence is false."
                ]
          else
            #[
              s!"  - User assertion: `Constitution({indexedName thingNames xIdx}, {indexedName thingNames xTypeIdx}, {indexedName thingNames yIdx}, {indexedName thingNames yTypeIdx})`.",
              s!"  - Computed Constitution: false, because `ConstitutedBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx})` is missing at `{indexedName worldNames w}`."
            ]
      | _, _, _, _ => #[]
  | .binary "Categorizes" x y =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y with
      | some xIdx, some yIdx =>
          if !typeLookup worldNames.size thingNames.size tables xIdx then
            #[
              s!"  - User assertion: `Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
              s!"  - Computed Categorizes: false, because `{indexedName thingNames xIdx}` is not a computed `Type`."
            ]
          else
            match firstCategorizationFailure? thingNames.size tables xIdx yIdx w with
            | some instType =>
                #[
                  s!"  - User assertion: `Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed Categorizes: false, because `{indexedName thingNames instType}` instantiates `{indexedName thingNames xIdx}` at `{indexedName worldNames w}` but `Sub({indexedName thingNames instType}, {indexedName thingNames yIdx})` is missing."
                ]
            | none =>
                #[
                  s!"  - User assertion: `Categorizes({indexedName thingNames xIdx}, {indexedName thingNames yIdx})`.",
                  s!"  - Computed Categorizes: true; every instance type of `{indexedName thingNames xIdx}` specializes `{indexedName thingNames yIdx}`."
                ]
      | _, _ => #[]
  | .ternary "IsCompletelyCoveredBy" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              #[
                s!"  - User assertion: `IsCompletelyCoveredBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                s!"  - Computed IsCompletelyCoveredBy: false, because `{indexedName thingNames instIdx}` instantiates `{indexedName thingNames xIdx}` but instantiates neither covering type at `{indexedName worldNames w}`."
              ]
          | none =>
              #[
                s!"  - User assertion: `IsCompletelyCoveredBy({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                "  - Computed IsCompletelyCoveredBy: true; every current covered instance is assigned to at least one covering type."
              ]
      | _, _, _ => #[]
  | .ternary "IsPartitionedInto" x y z =>
      match thingIndexByString? thingNames x, thingIndexByString? thingNames y,
        thingIndexByString? thingNames z with
      | some xIdx, some yIdx, some zIdx =>
          match firstCoveredInstanceFailure? thingNames.size tables xIdx yIdx zIdx w with
          | some instIdx =>
              #[
                s!"  - User assertion: `IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                s!"  - Computed IsPartitionedInto: false, because coverage fails: `{indexedName thingNames instIdx}` instantiates `{indexedName thingNames xIdx}` but instantiates neither covering type at `{indexedName worldNames w}`."
              ]
          | none =>
              match firstSharedInstance? thingNames.size tables yIdx zIdx w with
              | some instIdx =>
                  #[
                    s!"  - User assertion: `IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                    s!"  - Computed IsPartitionedInto: false, because disjointness fails: `{indexedName thingNames instIdx}` instantiates both covering types at `{indexedName worldNames w}`."
                  ]
              | none =>
                  #[
                    s!"  - User assertion: `IsPartitionedInto({indexedName thingNames xIdx}, {indexedName thingNames yIdx}, {indexedName thingNames zIdx})`.",
                    "  - Coverage and disjointness counterexamples were not isolated; inspect typehood and instantiation facts."
                  ]
      | _, _, _ => #[]
  | _ => #[]

def derivedAssertionFailure?
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Option (Array String) :=
  Id.run do
    for i in [:namedFacts.size] do
      match namedFacts[i]?, scopedFacts[i]? with
      | some (.derived fact scope), some (.derived _ resolvedScope) =>
          for w in resolvedScopeWorlds worldNames resolvedScope do
            match evalNamedDerivedFact? worldNames thingNames tables fact w with
            | some true => pure ()
            | some false =>
                return some <| #[
                  s!"Counterexample assignment: w = {indexedName worldNames w}.",
                  s!"Required but missing: {derivedAssertionRequiredMissing worldNames thingNames tables fact w}",
                  s!"Suggestion: {derivedAssertionSuggestion fact}",
                  s!"Evidence: the assertion was written at `{namedScopeSummary scope}` and expands to world `{indexedName worldNames w}`."
                ] ++ derivedAssertionEvidence worldNames thingNames tables fact w
            | none =>
                return some #[
                  s!"Could not reconstruct the asserted derived relation `{namedDerivedFactSummary fact}` at the DSL level.",
                  "Suggestion: check that all mentioned things are declared and that the relation has a registered diagnostic evaluator."
                ]
      | _, _ => pure ()
    return none

def derivedAssertionAnalysis
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (scopedFacts : Array ScopedCompiledFact) (tables : FactTables) : Array String :=
  (derivedAssertionFailure? worldNames thingNames namedFacts scopedFacts tables).getD
    #["A user-written derived relation assertion failed, but the structured checker could not isolate a false asserted derived fact."]

private def ax71Coordinates (worldCount thingCount : Nat) : List (Nat × Nat × Nat) :=
  (List.range worldCount).flatMap fun w =>
    (List.range thingCount).flatMap fun x => (List.range thingCount).map (w, x, ·)

private theorem ax71Coordinates_length
    (worldCount thingCount : Nat) :
    (ax71Coordinates worldCount thingCount).length =
      worldCount * thingCount * thingCount := by
  unfold ax71Coordinates
  simp only [List.length_flatMap, List.length_map, List.length_range]
  rw [List.map_const']
  have hinner : (List.map (fun _ : Nat => thingCount) (List.range thingCount)).sum =
      thingCount * thingCount := by
    rw [List.map_const']
    simp
  rw [hinner]
  simp
  exact (Nat.mul_assoc worldCount thingCount thingCount).symm

private def ax71ClassificationCosted (mode relator : Bool) : Complexity.Costed Bool :=
  if mode then ⟨true, 0⟩ else ⟨relator, 1⟩

private theorem ax71ClassificationCosted_cost_le (mode relator : Bool) :
    (ax71ClassificationCosted mode relator).cost ≤ 1 := by
  simp only [ax71ClassificationCosted]
  split
  · change 0 ≤ 1
    omega
  · change 1 ≤ 1
    omega

private def ax71AssignmentsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    List (Nat × Nat × Nat) → Complexity.Costed (Array String)
  | List.nil => ⟨#[
      "Foundation check for ax71: every `FoundedBy` fact has a computed externally dependent mode or relator on the left and a perdurant on the right."
    ], 1⟩
  | List.cons (w, x, y) assignments =>
      if tables.binaryLookup "foundedBy" x y w then
        let mode := externallyDependentModeLookupCosted worldNames.size
          thingNames.size tables x w
        let classification := ax71ClassificationCosted mode.value
          (tables.unaryLookup "relator" x w)
        let foundationOk := tables.unaryLookup "perdurant" y w
        if !(classification.value && foundationOk) then
          let modeStatus :=
            renderExternallyDependentModeStatusCosted worldNames thingNames tables x w
          let base := #[
            s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
            s!"Triggered by: `FoundedBy({indexedName thingNames x}, {indexedName thingNames y})`.",
            "Required together: the founded thing must be a computed `ExternallyDependentMode` or a `Relator`, and the foundation must be a `Perdurant`.",
            s!"  - Relator({indexedName thingNames x}): {if tables.unaryLookup "relator" x w then "true" else "false"}.",
            s!"  - Perdurant({indexedName thingNames y}): {if foundationOk then "true" else "false"}."
          ] ++ modeStatus.value
          let suggestion :=
            if !classification.value then
              "Suggestion: add the modal `Ex` variation and `InheresIn` facts needed for computed external dependence, or remove/relax the `FoundedBy` fact if this thing is not a relator or externally dependent mode."
            else
              s!"Suggestion: classify `{indexedName thingNames y}` as `Perdurant`, or change the `FoundedBy` target to a perdurant foundation."
          ⟨base.push suggestion,
            mode.cost + classification.cost + modeStatus.cost + modeStatus.value.size + 11⟩
        else
          Complexity.Costed.charge (mode.cost + classification.cost + 4) <|
            ax71AssignmentsCosted worldNames thingNames tables assignments
      else
        Complexity.Costed.charge 2 <|
          ax71AssignmentsCosted worldNames thingNames tables assignments

private def ax71AssignmentCostBound
    (worldCount thingCount : Nat) : Nat :=
  thingCount * (6 * worldCount + thingCount * (12 * worldCount + 6) + 3) + 2 +
    externallyDependentModeStatusCostBound worldCount thingCount + 15

private theorem ax71AssignmentsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (assignments : List (Nat × Nat × Nat)) :
    (ax71AssignmentsCosted worldNames thingNames tables assignments).cost ≤
      assignments.length * ax71AssignmentCostBound worldNames.size thingNames.size + 1 := by
  induction assignments with
  | nil => simp [ax71AssignmentsCosted]
  | cons assignment assignments ih =>
      rcases assignment with ⟨w, x, y⟩
      have hmode := externallyDependentModeLookupCosted_cost_le
        worldNames.size thingNames.size tables x w
      have hstatus := renderExternallyDependentModeStatusCosted_cost_le
        worldNames thingNames tables x w
      have hstatusSize := renderExternallyDependentModeStatusCosted_size_le
        worldNames thingNames tables x w
      have hclassification := ax71ClassificationCosted_cost_le
        (externallyDependentModeLookupCosted worldNames.size thingNames.size tables x w).value
        (tables.unaryLookup "relator" x w)
      simp only [ax71AssignmentsCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (externallyDependentModeLookupCosted worldNames.size
              thingNames.size tables x w).cost +
            (ax71ClassificationCosted
              (externallyDependentModeLookupCosted worldNames.size
                thingNames.size tables x w).value
              (tables.unaryLookup "relator" x w)).cost +
            (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).cost +
            (renderExternallyDependentModeStatusCosted worldNames thingNames tables x w).value.size + 11 ≤ _
          unfold ax71AssignmentCostBound
          omega
        · simp only [Complexity.Costed.charge_cost]
          unfold ax71AssignmentCostBound at ih ⊢
          omega
      · simp only [Complexity.Costed.charge_cost]
        unfold ax71AssignmentCostBound at ih ⊢
        omega

private def ax71FoundationAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) :=
  ax71AssignmentsCosted worldNames thingNames tables
    (ax71Coordinates worldNames.size thingNames.size)

private theorem ax71FoundationAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax71FoundationAnalysisCosted worldNames thingNames tables).cost ≤
      worldNames.size * thingNames.size * thingNames.size *
        ax71AssignmentCostBound worldNames.size thingNames.size + 1 := by
  unfold ax71FoundationAnalysisCosted
  simpa [ax71Coordinates_length] using
    ax71AssignmentsCosted_cost_le worldNames thingNames tables
      (ax71Coordinates worldNames.size thingNames.size)

private def ax71FoundationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax71FoundationAnalysisCosted worldNames thingNames tables).value

@[simp] private theorem ax71FoundationAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax71FoundationAnalysisCosted worldNames thingNames tables).value =
      ax71FoundationAnalysis worldNames thingNames tables := rfl

private def ax73PrimaryZScanCosted
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) : List Nat → Complexity.Costed (Option (Array String))
  | List.nil => ⟨none, 0⟩
  | List.cons z zs =>
      let isPart := partLookupCosted tables z x w
      let isEDM := derivedUnaryLookupCosted worldNames.size thingNames.size tables
        "ExternallyDependentMode" z w
      let inheres := tables.binaryLookup "inheresIn" z y w
      let sameFoundation := sameFoundationLookupCosted thingNames.size tables z x w
      let prefixCost := isPart.cost + isEDM.cost + sameFoundation.cost + 2
      let assignment :=
        s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}."
      if qio && isPart.value && !isEDM.value then
        ⟨some #[
          assignment,
          s!"Required but missing: constituent `{indexedName thingNames z}` is a part of qua individual `{indexedName thingNames x}` but is not a computed `ExternallyDependentMode`.",
          "Suggestion: supply the mode, modal existence, and inherence facts needed for external dependence, or revise the `Part`/`QuaIndividualOf` assertions."
        ], prefixCost + 3⟩
      else if qio && isPart.value && !inheres then
        ⟨some #[
          assignment,
          s!"Required but missing: constituent `{indexedName thingNames z}` must `InheresIn({indexedName thingNames z}, {indexedName thingNames y})` because it is a part of `QuaIndividualOf({indexedName thingNames x}, {indexedName thingNames y})`.",
          "Suggestion: add the constituent's inherence in the asserted bearer, or revise the `Part`/`QuaIndividualOf` assertions."
        ], prefixCost + 3⟩
      else if qio && isPart.value && isEDM.value && inheres && !sameFoundation.value then
        let equality := foundationEqCosted thingNames.size tables z x w
        let reason := match equality.value with
          | some false => "different foundations"
          | none => "missing or ambiguous foundation data"
          | some true => "matching foundations"
        let zStatus := renderFoundationStatusCosted thingNames tables z w
        let xStatus := renderFoundationStatusCosted thingNames tables x w
        ⟨some #[
          assignment,
          s!"Required but missing: constituent `{indexedName thingNames z}` and qua individual `{indexedName thingNames x}` must share `FoundationOf`; the tables show {reason}.",
          s!"  - {indexedName thingNames z}: {zStatus.value}",
          s!"  - {indexedName thingNames x}: {xStatus.value}",
          "Suggestion: give both constituents exactly one common `FoundedBy` target, or revise the `Part`/`QuaIndividualOf` assertions."
        ], prefixCost + equality.cost + zStatus.cost + xStatus.cost + 5⟩
      else if qio && !isPart.value && isEDM.value && inheres && sameFoundation.value then
        ⟨some #[
          assignment,
          s!"Required but missing: `Part({indexedName thingNames z}, {indexedName thingNames x})`; the entity is an externally dependent mode that inheres in the asserted bearer and shares the qua individual's foundation.",
          "Suggestion: add the missing constituent part fact, or revise the facts that satisfy the right-hand characterization."
        ], prefixCost + 3⟩
      else
        Complexity.Costed.charge prefixCost <|
          ax73PrimaryZScanCosted worldNames thingNames tables qio x y w zs

private def ax73PrimaryZCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  derivedLookupCostBound worldCount thingCount tables + 18 * thingCount + 20

private theorem ax73PrimaryZScanCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (qio : Bool) (x y w : Nat) (zs : List Nat) :
    (ax73PrimaryZScanCosted worldNames thingNames tables qio x y w zs).cost ≤
      zs.length * ax73PrimaryZCostBound worldNames.size thingNames.size tables := by
  induction zs with
  | nil => simp [ax73PrimaryZScanCosted]
  | cons z zs ih =>
      have hpart := partLookupCosted_cost_le tables z x w
      have hedm := derivedUnaryLookupCosted_cost_le worldNames.size thingNames.size tables
        "ExternallyDependentMode" z w
      have hsame := sameFoundationLookupCosted_cost_le thingNames.size tables z x w
      have hequality := foundationEqCosted_cost_le thingNames.size tables z x w
      have hzStatus := renderFoundationStatusCosted_cost_le thingNames tables z w
      have hxStatus := renderFoundationStatusCosted_cost_le thingNames tables x w
      simp only [ax73PrimaryZScanCosted, List.length_cons, Nat.add_mul]
      split
      · change (partLookupCosted tables z x w).cost +
          (derivedUnaryLookupCosted worldNames.size thingNames.size tables
            "ExternallyDependentMode" z w).cost +
          (sameFoundationLookupCosted thingNames.size tables z x w).cost + 5 ≤ _
        unfold ax73PrimaryZCostBound
        omega
      · split
        · change (partLookupCosted tables z x w).cost +
            (derivedUnaryLookupCosted worldNames.size thingNames.size tables
              "ExternallyDependentMode" z w).cost +
            (sameFoundationLookupCosted thingNames.size tables z x w).cost + 5 ≤ _
          unfold ax73PrimaryZCostBound
          omega
        · split
          · change (partLookupCosted tables z x w).cost +
              (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                "ExternallyDependentMode" z w).cost +
              (sameFoundationLookupCosted thingNames.size tables z x w).cost + 2 +
              (foundationEqCosted thingNames.size tables z x w).cost +
              (renderFoundationStatusCosted thingNames tables z w).cost +
              (renderFoundationStatusCosted thingNames tables x w).cost + 5 ≤ _
            unfold ax73PrimaryZCostBound
            omega
          · split
            · change (partLookupCosted tables z x w).cost +
                (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                  "ExternallyDependentMode" z w).cost +
                (sameFoundationLookupCosted thingNames.size tables z x w).cost + 5 ≤ _
              unfold ax73PrimaryZCostBound
              omega
            · simp only [Complexity.Costed.charge_cost]
              unfold ax73PrimaryZCostBound at ih ⊢
              omega

private def ax73CharacterizationZScanCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x y w : Nat) :
    List Nat → Complexity.Costed Bool
  | List.nil => ⟨true, 0⟩
  | List.cons z zs =>
      let isPart := partLookupCosted tables z x w
      let characterized := ax73CharacterizedCosted worldNames.size thingNames.size
        tables z x y w
      let tail := ax73CharacterizationZScanCosted worldNames thingNames tables x y w zs
      ⟨(isPart.value == characterized.value) && tail.value,
        isPart.cost + characterized.cost + tail.cost + 2⟩

private def ax73CharacterizationZCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  derivedLookupCostBound worldCount thingCount tables + 4 * thingCount + 7

private theorem ax73CharacterizationZScanCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (x y w : Nat) (zs : List Nat) :
    (ax73CharacterizationZScanCosted worldNames thingNames tables x y w zs).cost ≤
      zs.length *
        ax73CharacterizationZCostBound worldNames.size thingNames.size tables := by
  induction zs with
  | nil => simp [ax73CharacterizationZScanCosted]
  | cons z zs ih =>
      have hpart := partLookupCosted_cost_le tables z x w
      have hcharacterized := ax73CharacterizedCosted_cost_le
        worldNames.size thingNames.size tables z x y w
      simp only [ax73CharacterizationZScanCosted, List.length_cons, Nat.add_mul]
      unfold ax73CharacterizationZCostBound at ih ⊢
      omega

private def ax73Coordinates (worldCount thingCount : Nat) : List (Nat × Nat × Nat) :=
  (List.range worldCount).flatMap fun w =>
    (List.range thingCount).flatMap fun x => (List.range thingCount).map (w, x, ·)

private theorem ax73Coordinates_length
    (worldCount thingCount : Nat) :
    (ax73Coordinates worldCount thingCount).length =
      worldCount * thingCount * thingCount := by
  unfold ax73Coordinates
  simp only [List.length_flatMap, List.length_map, List.length_range]
  rw [List.map_const']
  have hinner : (List.map (fun _ : Nat => thingCount) (List.range thingCount)).sum =
      thingCount * thingCount := by
    rw [List.map_const']
    simp
  rw [hinner]
  simp
  exact (Nat.mul_assoc worldCount thingCount thingCount).symm

private def ax73AssignmentsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    List (Nat × Nat × Nat) → Complexity.Costed (Array String)
  | List.nil => ⟨#[
      "Part-characterization check for ax73 found no direct mismatch in either direction of the biconditional."
    ], 1⟩
  | List.cons (w, x, y) assignments =>
      let qio := tables.binaryLookup "quaIndividualOf" x y w
      let primary := ax73PrimaryZScanCosted worldNames thingNames tables qio x y w
        (List.range thingNames.size)
      match primary.value with
      | some evidence => ⟨evidence, primary.cost + 2⟩
      | none =>
          if !qio then
            let characterization := ax73CharacterizationZScanCosted
              worldNames thingNames tables x y w (List.range thingNames.size)
            if characterization.value then
              ⟨#[
                s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}.",
                s!"Required but missing: `QuaIndividualOf({indexedName thingNames x}, {indexedName thingNames y})`; its complete part characterization holds.",
                "Suggestion: add the missing `QuaIndividualOf` fact, or revise a constituent part, inherence, external-dependence, or foundation fact."
              ], primary.cost + characterization.cost + 5⟩
            else
              Complexity.Costed.charge (primary.cost + characterization.cost + 2) <|
                ax73AssignmentsCosted worldNames thingNames tables assignments
          else
            Complexity.Costed.charge (primary.cost + 2) <|
              ax73AssignmentsCosted worldNames thingNames tables assignments

private def ax73AssignmentCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  thingCount * ax73PrimaryZCostBound worldCount thingCount tables +
    thingCount * ax73CharacterizationZCostBound worldCount thingCount tables + 5

private theorem ax73AssignmentsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (assignments : List (Nat × Nat × Nat)) :
    (ax73AssignmentsCosted worldNames thingNames tables assignments).cost ≤
      assignments.length *
        ax73AssignmentCostBound worldNames.size thingNames.size tables + 1 := by
  induction assignments with
  | nil => simp [ax73AssignmentsCosted]
  | cons assignment assignments ih =>
      rcases assignment with ⟨w, x, y⟩
      have hprimary := ax73PrimaryZScanCosted_cost_le worldNames thingNames tables
        (tables.binaryLookup "quaIndividualOf" x y w) x y w (List.range thingNames.size)
      have hcharacterization := ax73CharacterizationZScanCosted_cost_le
        worldNames thingNames tables x y w (List.range thingNames.size)
      simp only [List.length_range] at hprimary hcharacterization
      simp only [ax73AssignmentsCosted, List.length_cons, Nat.add_mul]
      split
      · change (ax73PrimaryZScanCosted worldNames thingNames tables
          (tables.binaryLookup "quaIndividualOf" x y w) x y w
          (List.range thingNames.size)).cost + 2 ≤ _
        unfold ax73AssignmentCostBound
        omega
      · split
        · split
          · change (ax73PrimaryZScanCosted worldNames thingNames tables
              (tables.binaryLookup "quaIndividualOf" x y w) x y w
              (List.range thingNames.size)).cost +
              (ax73CharacterizationZScanCosted worldNames thingNames tables x y w
                (List.range thingNames.size)).cost + 5 ≤ _
            unfold ax73AssignmentCostBound
            omega
          · simp only [Complexity.Costed.charge_cost]
            unfold ax73AssignmentCostBound at ih ⊢
            omega
        · simp only [Complexity.Costed.charge_cost]
          unfold ax73AssignmentCostBound at ih ⊢
          omega

private def ax73PartCharacterizationAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) :=
  ax73AssignmentsCosted worldNames thingNames tables
    (ax73Coordinates worldNames.size thingNames.size)

private theorem ax73PartCharacterizationAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).cost ≤
      worldNames.size * thingNames.size * thingNames.size *
        ax73AssignmentCostBound worldNames.size thingNames.size tables + 1 := by
  unfold ax73PartCharacterizationAnalysisCosted
  simpa [ax73Coordinates_length] using
    ax73AssignmentsCosted_cost_le worldNames thingNames tables
      (ax73Coordinates worldNames.size thingNames.size)

private def ax73PartCharacterizationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).value

@[simp] private theorem ax73PartCharacterizationAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables).value =
      ax73PartCharacterizationAnalysis worldNames thingNames tables := rfl

private def foundationCoordinates (worldCount thingCount : Nat) : List (Nat × Nat × Nat) :=
  (List.range worldCount).flatMap fun w =>
    (List.range thingCount).flatMap fun x => (List.range thingCount).map (w, x, ·)

private theorem foundationCoordinates_length
    (worldCount thingCount : Nat) :
    (foundationCoordinates worldCount thingCount).length =
      worldCount * thingCount * thingCount := by
  unfold foundationCoordinates
  simp only [List.length_flatMap, List.length_map, List.length_range]
  rw [List.map_const']
  have hinner : (List.map (fun _ : Nat => thingCount) (List.range thingCount)).sum =
      thingCount * thingCount := by
    rw [List.map_const']
    simp
  rw [hinner]
  simp
  exact (Nat.mul_assoc worldCount thingCount thingCount).symm

private def ax78FoundationScanCosted
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (coordinates : List (Nat × Nat × Nat)) (out : Array String) :
    Complexity.Costed (Array String) :=
  match coordinates with
  | .nil => ⟨out, 0⟩
  | .cons (w, x, y) coordinates =>
      if tables.unaryLookup "relator" x w &&
          out.size < budget && partLookup tables y x w then
        let equality := foundationEqCosted thingNames.size tables x y w
        match equality.value with
        | some true =>
            Complexity.Costed.charge (equality.cost + 3) <|
              ax78FoundationScanCosted budget worldNames thingNames tables coordinates out
        | some false =>
            let leftStatus := renderFoundationStatusCosted thingNames tables x w
            let rightStatus := renderFoundationStatusCosted thingNames tables y w
            let next := out
              |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
              |>.push s!"Required but missing: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` must share the same `FoundationOf`."
              |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
              |>.push s!"  - {indexedName thingNames x}: {leftStatus.value}"
              |>.push s!"  - {indexedName thingNames y}: {rightStatus.value}"
            Complexity.Costed.charge
              (equality.cost + leftStatus.cost + rightStatus.cost + 8) <|
                ax78FoundationScanCosted budget worldNames thingNames tables coordinates next
        | none =>
            let leftStatus := renderFoundationStatusCosted thingNames tables x w
            let rightStatus := renderFoundationStatusCosted thingNames tables y w
            let next := out
              |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
              |>.push s!"Missing witness requirements: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations."
              |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
              |>.push s!"  - {indexedName thingNames x}: {leftStatus.value}"
              |>.push s!"  - {indexedName thingNames y}: {rightStatus.value}"
            Complexity.Costed.charge
              (equality.cost + leftStatus.cost + rightStatus.cost + 8) <|
                ax78FoundationScanCosted budget worldNames thingNames tables coordinates next
      else
        Complexity.Costed.charge 2 <|
          ax78FoundationScanCosted budget worldNames thingNames tables coordinates out

/-- A compositional bound for ax78's production evidence scan. As in the
cost-aware operational semantics of Niu et al. (POPL 2022), the theorem follows
the executable recursion itself: every `(world, relator, part)` coordinate pays
for its table tests, foundation comparison, and any evidence that it emits. -/
private theorem ax78FoundationScanCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (coordinates : List (Nat × Nat × Nat)) (out : Array String) :
    (ax78FoundationScanCosted budget worldNames thingNames tables coordinates out).cost ≤
      coordinates.length * (14 * thingNames.size + 18) := by
  induction coordinates generalizing out with
  | nil => simp [ax78FoundationScanCosted]
  | cons coordinate coordinates ih =>
      rcases coordinate with ⟨w, x, y⟩
      simp only [ax78FoundationScanCosted]
      split
      · have hequality := foundationEqCosted_cost_le thingNames.size tables x y w
        split
        · simp only [Complexity.Costed.charge_cost, List.length_cons, Nat.add_mul]
          have htail := ih (out := out)
          omega
        · have hleft := renderFoundationStatusCosted_cost_le thingNames tables x w
          have hright := renderFoundationStatusCosted_cost_le thingNames tables y w
          simp only [Complexity.Costed.charge_cost, List.length_cons, Nat.add_mul]
          have htail := ih (out := out
            |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
            |>.push s!"Required but missing: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` must share the same `FoundationOf`."
            |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
            |>.push s!"  - {indexedName thingNames x}: {(renderFoundationStatusCosted thingNames tables x w).value}"
            |>.push s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted thingNames tables y w).value}")
          omega
        · have hleft := renderFoundationStatusCosted_cost_le thingNames tables x w
          have hright := renderFoundationStatusCosted_cost_le thingNames tables y w
          simp only [Complexity.Costed.charge_cost, List.length_cons, Nat.add_mul]
          have htail := ih (out := out
            |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
            |>.push s!"Missing witness requirements: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations."
            |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
            |>.push s!"  - {indexedName thingNames x}: {(renderFoundationStatusCosted thingNames tables x w).value}"
            |>.push s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted thingNames tables y w).value}")
          omega
      · simp only [Complexity.Costed.charge_cost, List.length_cons, Nat.add_mul]
        have htail := ih (out := out)
        omega

private theorem ax78FoundationScanCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables)
    (coordinates : List (Nat × Nat × Nat)) (out : Array String) :
    (ax78FoundationScanCosted budget worldNames thingNames tables coordinates out).value.size ≤
      out.size + 5 * coordinates.length := by
  induction coordinates generalizing out with
  | nil => simp [ax78FoundationScanCosted]
  | cons coordinate coordinates ih =>
      rcases coordinate with ⟨w, x, y⟩
      simp only [ax78FoundationScanCosted]
      split
      · split
        · simp only [Complexity.Costed.charge_value, List.length_cons, Nat.mul_add]
          have htail := ih (out := out)
          omega
        · simp only [Complexity.Costed.charge_value, List.length_cons, Nat.mul_add]
          have htail := ih (out := out
            |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
            |>.push s!"Required but missing: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` must share the same `FoundationOf`."
            |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
            |>.push s!"  - {indexedName thingNames x}: {(renderFoundationStatusCosted thingNames tables x w).value}"
            |>.push s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted thingNames tables y w).value}")
          simp only [Array.size_push] at htail
          omega
        · simp only [Complexity.Costed.charge_value, List.length_cons, Nat.mul_add]
          have htail := ih (out := out
            |>.push s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, w = {indexedName worldNames w}."
            |>.push s!"Missing witness requirements: Relator `{indexedName thingNames x}` and its part `{indexedName thingNames y}` are compared with `FoundationOf`, but the DSL facts do not determine unique foundations."
            |>.push s!"Evidence for FoundationOf({indexedName thingNames x}) = FoundationOf({indexedName thingNames y}):"
            |>.push s!"  - {indexedName thingNames x}: {(renderFoundationStatusCosted thingNames tables x w).value}"
            |>.push s!"  - {indexedName thingNames y}: {(renderFoundationStatusCosted thingNames tables y w).value}")
          simp only [Array.size_push] at htail
          omega
      · simp only [Complexity.Costed.charge_value, List.length_cons, Nat.mul_add]
        have htail := ih (out := out)
        omega

private def ax78FoundationAnalysisCosted
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) :=
  let scanned := ax78FoundationScanCosted budget worldNames thingNames tables
    (foundationCoordinates worldNames.size thingNames.size) #[]
  if !scanned.value.isEmpty then
    if scanned.value.size < budget then
      ⟨scanned.value.push "Suggestion: align the `FoundedBy` facts for the relator and every relevant part, or remove/relax the `Relator`/`Part` assertions.", scanned.cost + 2⟩
    else
      ⟨scanned.value, scanned.cost + 1⟩
  else
    ⟨(#[
      "Foundation check for ax78: every relator/part pair with unique DSL foundations has matching foundations.",
      "If Lean still reports ax78, inspect relator parts whose foundations are not explicitly determined by `FoundedBy` facts."
    ]).extract 0 (min budget 2), scanned.cost + min budget 2 + 2⟩

private theorem ax78FoundationAnalysisCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax78FoundationAnalysisCosted budget worldNames thingNames tables).cost ≤
      worldNames.size * thingNames.size * thingNames.size *
        (14 * thingNames.size + 18) + min budget 2 + 2 := by
  have hscan := ax78FoundationScanCosted_cost_le budget worldNames thingNames tables
    (foundationCoordinates worldNames.size thingNames.size) #[]
  rw [foundationCoordinates_length] at hscan
  simp only [ax78FoundationAnalysisCosted]
  split
  · split
    · change (ax78FoundationScanCosted budget worldNames thingNames tables
        (foundationCoordinates worldNames.size thingNames.size) #[]).cost + 2 ≤ _
      omega
    · change (ax78FoundationScanCosted budget worldNames thingNames tables
        (foundationCoordinates worldNames.size thingNames.size) #[]).cost + 1 ≤ _
      omega
  · change (ax78FoundationScanCosted budget worldNames thingNames tables
      (foundationCoordinates worldNames.size thingNames.size) #[]).cost + min budget 2 + 2 ≤ _
    omega

private def ax78FoundationAnalysis
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax78FoundationAnalysisCosted budget worldNames thingNames tables).value

@[simp] private theorem ax78FoundationAnalysisCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax78FoundationAnalysisCosted budget worldNames thingNames tables).value =
      ax78FoundationAnalysis budget worldNames thingNames tables := rfl

private def properPartCandidatesFromCosted
    (tables : FactTables) (x w : Nat) (candidates : List Nat) (out : Array Nat) :
    Complexity.Costed (Array Nat) :=
  match candidates with
  | .nil => ⟨out, 0⟩
  | .cons y candidates =>
      if tables.binaryLookup "properPart" y x w then
        Complexity.Costed.charge 3 <|
          properPartCandidatesFromCosted tables x w candidates (out.push y)
      else
        Complexity.Costed.charge 2 <|
          properPartCandidatesFromCosted tables x w candidates out

private def properPartCandidatesCosted
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    Complexity.Costed (Array Nat) :=
  properPartCandidatesFromCosted tables x w (List.range thingCount) #[]

private theorem properPartCandidatesFromCosted_cost_le
    (tables : FactTables) (x w : Nat) (candidates : List Nat) (out : Array Nat) :
    (properPartCandidatesFromCosted tables x w candidates out).cost ≤
      3 * candidates.length := by
  induction candidates generalizing out with
  | nil => simp [properPartCandidatesFromCosted]
  | cons y candidates ih =>
      simp only [properPartCandidatesFromCosted]
      split
      · simp only [Complexity.Costed.charge_cost, List.length_cons]
        have htail := ih (out := out.push y)
        omega
      · simp only [Complexity.Costed.charge_cost, List.length_cons]
        have htail := ih (out := out)
        omega

private theorem properPartCandidatesCosted_cost_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted thingCount tables x w).cost ≤ 3 * thingCount := by
  simpa [properPartCandidatesCosted] using
    properPartCandidatesFromCosted_cost_le tables x w (List.range thingCount) #[]

private theorem properPartCandidatesFromCosted_size_le
    (tables : FactTables) (x w : Nat) (candidates : List Nat) (out : Array Nat) :
    (properPartCandidatesFromCosted tables x w candidates out).value.size ≤
      out.size + candidates.length := by
  induction candidates generalizing out with
  | nil => simp [properPartCandidatesFromCosted]
  | cons y candidates ih =>
      simp only [properPartCandidatesFromCosted]
      split
      · simp only [Complexity.Costed.charge_value, List.length_cons]
        have htail := ih (out := out.push y)
        simp only [Array.size_push] at htail
        omega
      · simp only [Complexity.Costed.charge_value, List.length_cons]
        have htail := ih (out := out)
        omega

private theorem properPartCandidatesCosted_size_le
    (thingCount : Nat) (tables : FactTables) (x w : Nat) :
    (properPartCandidatesCosted thingCount tables x w).value.size ≤ thingCount := by
  simpa [properPartCandidatesCosted] using
    properPartCandidatesFromCosted_size_le tables x w (List.range thingCount) #[]

private def properPartPairs (parts : Array Nat) : List (Nat × Nat) :=
  parts.toList.flatMap fun y => parts.toList.map (y, ·)

private theorem properPartPairs_length (parts : Array Nat) :
    (properPartPairs parts).length = parts.size * parts.size := by
  unfold properPartPairs
  simp only [List.length_flatMap, List.length_map, Array.length_toList]
  rw [List.map_const']
  simp

private def ax79PartPairsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    List (Nat × Nat) → Complexity.Costed (Option (Array String))
  | List.nil => ⟨none, 0⟩
  | List.cons (y, z) pairs =>
      let yQua := derivedUnaryLookupCosted worldNames.size thingNames.size tables
        "QuaIndividual" y w
      if !yQua.value then
        ⟨some #[
          s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
          s!"Required together: proper parts of relator `{indexedName thingNames x}` must be qua individuals.",
          "Suggestion: add the missing `QuaIndividual(...)` derived assertions or remove/relax the `Relator`/`ProperPart` assertions."
        ], yQua.cost + 6⟩
      else
        let zQua := derivedUnaryLookupCosted worldNames.size thingNames.size tables
          "QuaIndividual" z w
        if !zQua.value then
          ⟨some #[
            s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
            s!"Required together: proper parts of relator `{indexedName thingNames x}` must be qua individuals.",
            "Suggestion: add the missing `QuaIndividual(...)` derived assertions or remove/relax the `Relator`/`ProperPart` assertions."
          ], yQua.cost + zQua.cost + 7⟩
        else
          let equality := foundationEqCosted thingNames.size tables y z w
          match equality.value with
          | some false =>
              let yStatus := renderFoundationStatusCosted thingNames tables y w
              let zStatus := renderFoundationStatusCosted thingNames tables z w
              ⟨some #[
                s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                s!"Required but missing: proper parts of relator `{indexedName thingNames x}` must share a foundation.",
                "Suggestion: align the `FoundedBy` facts for the relator's qua-individual parts.",
                s!"Evidence for FoundationOf({indexedName thingNames y}) = FoundationOf({indexedName thingNames z}):",
                s!"  - {indexedName thingNames y}: {yStatus.value}",
                s!"  - {indexedName thingNames z}: {zStatus.value}"
              ], yQua.cost + zQua.cost + equality.cost + yStatus.cost + zStatus.cost + 11⟩
          | none =>
              let yStatus := renderFoundationStatusCosted thingNames tables y w
              let zStatus := renderFoundationStatusCosted thingNames tables z w
              ⟨some #[
                s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                s!"Missing witness requirements: ax79 compares `FoundationOf` for relator parts, but the DSL facts do not determine unique foundations.",
                "Suggestion: add exactly one `FoundedBy` fact for each qua-individual part of the relator.",
                s!"Evidence for FoundationOf({indexedName thingNames y}) = FoundationOf({indexedName thingNames z}):",
                s!"  - {indexedName thingNames y}: {yStatus.value}",
                s!"  - {indexedName thingNames z}: {zStatus.value}"
              ], yQua.cost + zQua.cost + equality.cost + yStatus.cost + zStatus.cost + 11⟩
          | some true =>
              let yzDependence := derivedBinaryLookupCosted worldNames.size thingNames.size tables
                "ExistentialDependence" y z w
              if !yzDependence.value then
                ⟨some #[
                  s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                  s!"Required together: proper parts of relator `{indexedName thingNames x}` must be mutually existentially dependent.",
                  "Suggestion: add the missing `ExistentialDependence(...)` derived assertions or remove/relax the `Relator`/`ProperPart` assertions."
                ], yQua.cost + zQua.cost + equality.cost + yzDependence.cost + 9⟩
              else
                let zyDependence := derivedBinaryLookupCosted worldNames.size thingNames.size tables
                  "ExistentialDependence" z y w
                if !zyDependence.value then
                  ⟨some #[
                    s!"Counterexample assignment: x = {indexedName thingNames x}, y = {indexedName thingNames y}, z = {indexedName thingNames z}, w = {indexedName worldNames w}.",
                    s!"Required together: proper parts of relator `{indexedName thingNames x}` must be mutually existentially dependent.",
                    "Suggestion: add the missing `ExistentialDependence(...)` derived assertions or remove/relax the `Relator`/`ProperPart` assertions."
                  ], yQua.cost + zQua.cost + equality.cost + yzDependence.cost +
                    zyDependence.cost + 10⟩
                else
                  Complexity.Costed.charge
                    (yQua.cost + zQua.cost + equality.cost + yzDependence.cost +
                      zyDependence.cost + 7) <|
                    ax79PartPairsCosted worldNames thingNames tables x w pairs

private def ax79PartPairCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  4 * derivedLookupCostBound worldCount thingCount tables + 14 * thingCount + 24

/-- The ordered-pair checker stops at the first counterexample. Its bound still
charges every possible pair and each concrete lookup that a successful pair
can force, so the theorem follows Lean's executable short-circuit order. -/
private theorem ax79PartPairsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat)
    (pairs : List (Nat × Nat)) :
    (ax79PartPairsCosted worldNames thingNames tables x w pairs).cost ≤
      pairs.length * ax79PartPairCostBound worldNames.size thingNames.size tables := by
  induction pairs with
  | nil => simp [ax79PartPairsCosted]
  | cons pair pairs ih =>
      rcases pair with ⟨y, z⟩
      have hyQua := derivedUnaryLookupCosted_cost_le worldNames.size thingNames.size tables
        "QuaIndividual" y w
      have hzQua := derivedUnaryLookupCosted_cost_le worldNames.size thingNames.size tables
        "QuaIndividual" z w
      have hequality := foundationEqCosted_cost_le thingNames.size tables y z w
      have hyStatus := renderFoundationStatusCosted_cost_le thingNames tables y w
      have hzStatus := renderFoundationStatusCosted_cost_le thingNames tables z w
      have hyz := derivedBinaryLookupCosted_cost_le worldNames.size thingNames.size tables
        "ExistentialDependence" y z w
      have hzy := derivedBinaryLookupCosted_cost_le worldNames.size thingNames.size tables
        "ExistentialDependence" z y w
      simp only [ax79PartPairsCosted]
      simp only [List.length_cons, Nat.add_mul]
      split
      · change (derivedUnaryLookupCosted worldNames.size thingNames.size tables
          "QuaIndividual" y w).cost + 6 ≤ _
        unfold ax79PartPairCostBound
        omega
      · split
        · change (derivedUnaryLookupCosted worldNames.size thingNames.size tables
            "QuaIndividual" y w).cost +
              (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                "QuaIndividual" z w).cost + 7 ≤ _
          unfold ax79PartPairCostBound
          omega
        · split
          · change (derivedUnaryLookupCosted worldNames.size thingNames.size tables
              "QuaIndividual" y w).cost +
                (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                  "QuaIndividual" z w).cost +
                (foundationEqCosted thingNames.size tables y z w).cost +
                (renderFoundationStatusCosted thingNames tables y w).cost +
                (renderFoundationStatusCosted thingNames tables z w).cost + 11 ≤ _
            unfold ax79PartPairCostBound
            omega
          · change (derivedUnaryLookupCosted worldNames.size thingNames.size tables
              "QuaIndividual" y w).cost +
                (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                  "QuaIndividual" z w).cost +
                (foundationEqCosted thingNames.size tables y z w).cost +
                (renderFoundationStatusCosted thingNames tables y w).cost +
                (renderFoundationStatusCosted thingNames tables z w).cost + 11 ≤ _
            unfold ax79PartPairCostBound
            omega
          · split
            · change (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                "QuaIndividual" y w).cost +
                  (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                    "QuaIndividual" z w).cost +
                  (foundationEqCosted thingNames.size tables y z w).cost +
                  (derivedBinaryLookupCosted worldNames.size thingNames.size tables
                    "ExistentialDependence" y z w).cost + 9 ≤ _
              unfold ax79PartPairCostBound
              omega
            · split
              · change (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                  "QuaIndividual" y w).cost +
                    (derivedUnaryLookupCosted worldNames.size thingNames.size tables
                      "QuaIndividual" z w).cost +
                    (foundationEqCosted thingNames.size tables y z w).cost +
                    (derivedBinaryLookupCosted worldNames.size thingNames.size tables
                      "ExistentialDependence" y z w).cost +
                    (derivedBinaryLookupCosted worldNames.size thingNames.size tables
                      "ExistentialDependence" z y w).cost + 10 ≤ _
                unfold ax79PartPairCostBound
                omega
              · simp only [Complexity.Costed.charge_cost]
                unfold ax79PartPairCostBound at ih ⊢
                omega

private theorem ax79ProperPartPairsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) (x w : Nat) :
    (ax79PartPairsCosted worldNames thingNames tables x w
      (properPartPairs
        (properPartCandidatesCosted thingNames.size tables x w).value)).cost ≤
      thingNames.size * thingNames.size *
        ax79PartPairCostBound worldNames.size thingNames.size tables := by
  have hpairs := ax79PartPairsCosted_cost_le worldNames thingNames tables x w
    (properPartPairs (properPartCandidatesCosted thingNames.size tables x w).value)
  rw [properPartPairs_length] at hpairs
  have hsize := properPartCandidatesCosted_size_le thingNames.size tables x w
  have hsquare := Nat.mul_le_mul hsize hsize
  exact Nat.le_trans hpairs (Nat.mul_le_mul_right _ hsquare)

private def ax79RelatorsCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    List (Nat × Nat) → Complexity.Costed (Array String)
  | List.nil => ⟨#[
      "Foundation check for ax79: no obvious DSL-level relator/foundation mismatch was found.",
      "If Lean still reports ax79, the remaining issue may involve the full closure direction of the relator definition."
    ], 2⟩
  | List.cons (w, x) coordinates =>
      if tables.unaryLookup "relator" x w then
        let parts := properPartCandidatesCosted thingNames.size tables x w
        if parts.value.isEmpty then
          ⟨#[
            s!"Counterexample assignment: x = {indexedName thingNames x}, w = {indexedName worldNames w}.",
            s!"Missing witness requirements: Relator `{indexedName thingNames x}` must have at least one proper part in the finite DSL model.",
            "Suggestion: add `ProperPart(part, relator)` facts and the corresponding qua-individual/dependence/foundation facts, or remove/relax the `Relator` assertion."
          ], parts.cost + 6⟩
        else
          let pairFailure := ax79PartPairsCosted worldNames thingNames tables x w
            (properPartPairs parts.value)
          match pairFailure.value with
          | some evidence => ⟨evidence, parts.cost + pairFailure.cost + 3⟩
          | none => Complexity.Costed.charge (parts.cost + pairFailure.cost + 3) <|
              ax79RelatorsCosted worldNames thingNames tables coordinates
      else
        Complexity.Costed.charge 2 <|
          ax79RelatorsCosted worldNames thingNames tables coordinates

private def ax79RelatorCostBound
    (worldCount thingCount : Nat) (tables : FactTables) : Nat :=
  3 * thingCount + 6 + thingCount * thingCount *
    ax79PartPairCostBound worldCount thingCount tables

private theorem ax79RelatorsCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables)
    (coordinates : List (Nat × Nat)) :
    (ax79RelatorsCosted worldNames thingNames tables coordinates).cost ≤
      coordinates.length *
        ax79RelatorCostBound worldNames.size thingNames.size tables + 2 := by
  induction coordinates with
  | nil => simp [ax79RelatorsCosted]
  | cons coordinate coordinates ih =>
      rcases coordinate with ⟨w, x⟩
      have hparts := properPartCandidatesCosted_cost_le thingNames.size tables x w
      have hpairs := ax79ProperPartPairsCosted_cost_le worldNames thingNames tables x w
      simp only [ax79RelatorsCosted, List.length_cons, Nat.add_mul]
      split
      · split
        · change (properPartCandidatesCosted thingNames.size tables x w).cost + 6 ≤ _
          unfold ax79RelatorCostBound
          omega
        · split
          · change (properPartCandidatesCosted thingNames.size tables x w).cost +
              (ax79PartPairsCosted worldNames thingNames tables x w
                (properPartPairs
                  (properPartCandidatesCosted thingNames.size tables x w).value)).cost + 3 ≤ _
            unfold ax79RelatorCostBound
            omega
          · simp only [Complexity.Costed.charge_cost]
            unfold ax79RelatorCostBound at ih ⊢
            omega
      · simp only [Complexity.Costed.charge_cost]
        unfold ax79RelatorCostBound at ih ⊢
        omega

private def ax79FoundationAnalysisCosted
    (worldNames thingNames : Array Name) (tables : FactTables) :
    Complexity.Costed (Array String) :=
  ax79RelatorsCosted worldNames thingNames tables
    (momentCoordinates worldNames.size thingNames.size)

private theorem ax79FoundationAnalysisCosted_cost_le
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79FoundationAnalysisCosted worldNames thingNames tables).cost ≤
      worldNames.size * thingNames.size *
        ax79RelatorCostBound worldNames.size thingNames.size tables + 2 := by
  unfold ax79FoundationAnalysisCosted
  simpa [momentCoordinates_length] using
    ax79RelatorsCosted_cost_le worldNames thingNames tables
      (momentCoordinates worldNames.size thingNames.size)

private def ax79FoundationAnalysis
    (worldNames thingNames : Array Name) (tables : FactTables) : Array String :=
  (ax79FoundationAnalysisCosted worldNames thingNames tables).value

@[simp] private theorem ax79FoundationAnalysisCosted_value
    (worldNames thingNames : Array Name) (tables : FactTables) :
    (ax79FoundationAnalysisCosted worldNames thingNames tables).value =
      ax79FoundationAnalysis worldNames thingNames tables := rfl

/--
Structured diagnostic mirrors for selected certificate fields.

These formulas are not the authoritative axiom statements; they are finite-table
explainers used after Lean has already reported that a generated certificate
field failed. Keep them close to source-level vocabulary so the widget can point
modelers to facts they can add, remove, or re-scope.
-/
private def diagnosticFormula? : String → Option DiagFormula
  | "ax1" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dType "x" "w")
          (.dia "w" "w'" <| .existsThing "y" <| dInst "y" "x" "w'")
  | "ax2" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dIndividual "x" "w")
          (.box "w" "w'" <| .not <| .existsThing "y" <| dInst "y" "x" "w'")
  | "ax3" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dInst "x" "y" "w")
          (.or (dType "x" "w") (dIndividual "x" "w"))
  | "ax4" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| .existsThing "y" <| .existsThing "z" <|
          dAndList [
            dType "x" "w",
            dInst "x" "y" "w",
            dInst "y" "z" "w"
          ]
  | "ax5" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dSub "x" "y" "w")
          (dAndList [
            dType "x" "w",
            dType "y" "w",
            .box "w" "w'" <| .forallThing "z" <|
              .imp (dInst "z" "x" "w'") (dInst "z" "y" "w'")
          ])
  | "ax6" =>
      some <| .forallThing "t1" <| .forallThing "t2" <| .forallThing "x" <|
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
              ]))
  | "ax7" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .concreteIndividual "x" "w") (dIndividual "x" "w")
  | "ax8" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .abstractIndividual "x" "w") (dIndividual "x" "w")
  | "ax9" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .concreteIndividual "x" "w")
          (.not (dUnary .abstractIndividual "x" "w"))
  | "ax10" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dIndividual "x" "w")
          (.or
            (dUnary .concreteIndividual "x" "w")
            (dUnary .abstractIndividual "x" "w"))
  | "ax11" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .endurant "x" "w") (dUnary .concreteIndividual "x" "w")
  | "ax12" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .perdurant "x" "w") (dUnary .concreteIndividual "x" "w")
  | "ax13" =>
      some <|
        .forallThing "x" <| .forallWorld "w" <|
          .imp
            (dUnary .endurant "x" "w")
            (.not (dUnary .perdurant "x" "w"))
  | "ax14" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dUnary .concreteIndividual "x" "w")
          (.or
            (dUnary .endurant "x" "w")
            (dUnary .perdurant "x" "w"))
  | "ax15" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .endurantType "x" "w") (dType "x" "w")
  | "ax16" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .perdurantType "x" "w") (dType "x" "w")
  | "ax17" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurantType "x" "w")
          (.not (dUnary .perdurantType "x" "w"))
  | "ax18" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .rigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .forallThing "x" <|
              .imp
                (.dia "w" "w'" <| dInst "x" "t" "w'")
                (.box "w" "w'" <| dInst "x" "t" "w'")
          ])
  | "ax19" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .antiRigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .forallThing "x" <|
              .imp
                (.dia "w" "w'" <| dInst "x" "t" "w'")
                (.dia "w" "w'" <| .not (dInst "x" "t" "w'"))
          ])
  | "ax20" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .semiRigid "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .not (dUnary .rigid "t" "w"),
            .not (dUnary .antiRigid "t" "w")
          ])
  | "ax21" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurant "x" "w")
          (.existsThing "k" <| dAndList [
            dUnary .kind "k" "w",
            .box "w" "w'" <| dInst "x" "k" "w'"
          ])
  | "ax22" =>
      some <| .forallThing "k" <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .kind "k" "w",
            dInst "x" "k" "w"
          ])
          (.not <| .dia "w" "w'" <| .existsThing "z" <| dAndList [
            dUnary .kind "z" "w'",
            dInst "x" "z" "w'",
            dNeThing "z" "k"
          ])
  | "ax23" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .sortal "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .existsThing "k" <| dAndList [
              dUnary .kind "k" "w",
              .box "w" "w'" <| .forallThing "x" <|
                .imp (dInst "x" "t" "w'") (dInst "x" "k" "w'")
            ]
          ])
  | "ax24" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .nonSortal "t" "w")
          (dAndList [
            dUnary .endurantType "t" "w",
            .not (dUnary .sortal "t" "w")
          ])
  | "ax25" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .kind "t" "w",
          dUnary .subKind "t" "w"
        ]
  | "ax26" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .kind "t" "w",
            dUnary .subKind "t" "w"
          ])
          (dAndList [
            dUnary .rigid "t" "w",
            dUnary .sortal "t" "w"
          ])
  | "ax_kindStable" =>
      some <| .forallThing "k" <| .forallWorld "w" <| .forallWorld "v" <|
        .imp
          (dUnary .kind "k" "w")
          (dUnary .kind "k" "v")
  | "ax_instEndurant" =>
      some <| .forallThing "t" <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .endurantType "t" "w",
            dInst "x" "t" "w"
          ])
          (dUnary .endurant "x" "w")
  | "ax_sub_kind_sortal" =>
      some <| .forallThing "a" <| .forallThing "k" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dSub "a" "k" "w",
            dUnary .kind "k" "w"
          ])
          (dUnary .sortal "a" "w")
  | "ax_nonSortal_up" =>
      some <| .forallThing "a" <| .forallThing "b" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .nonSortal "a" "w",
            dSub "a" "b" "w"
          ])
          (dUnary .nonSortal "b" "w")
  | "ax27" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .phase "t" "w",
          dUnary .role "t" "w"
        ]
  | "ax28" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .phase "t" "w",
            dUnary .role "t" "w"
          ])
          (dAndList [
            dUnary .antiRigid "t" "w",
            dUnary .sortal "t" "w"
          ])
  | "ax29" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .semiRigidSortal "t" "w")
          (dAndList [
            dUnary .semiRigid "t" "w",
            dUnary .sortal "t" "w"
          ])
  | "ax30" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .category "t" "w")
          (dAndList [
            dUnary .rigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])
  | "ax31" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dUnary .mixin "t" "w")
          (dAndList [
            dUnary .semiRigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])
  | "ax32" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "t" <| dAndList [
          dUnary .phaseMixin "t" "w",
          dUnary .roleMixin "t" "w"
        ]
  | "ax33" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .phaseMixin "t" "w",
            dUnary .roleMixin "t" "w"
          ])
          (dAndList [
            dUnary .antiRigid "t" "w",
            dUnary .nonSortal "t" "w"
          ])
  | "ax34" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .substantial "x" "w",
            dUnary .moment "x" "w"
          ])
          (dUnary .endurant "x" "w")
  | "ax35" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .substantial "x" "w",
          dUnary .moment "x" "w"
        ]
  | "ax36" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .object "x" "w",
            dUnary .collective "x" "w",
            dUnary .quantity "x" "w"
          ])
          (dUnary .substantial "x" "w")
  | "ax37" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .object "x" "w",
          dUnary .collective "x" "w"
        ]
  | "ax38" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .object "x" "w",
          dUnary .quantity "x" "w"
        ]
  | "ax39" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .collective "x" "w",
          dUnary .quantity "x" "w"
        ]
  | "ax40" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .relator "x" "w",
            dUnary .intrinsicMoment "x" "w"
          ])
          (dUnary .moment "x" "w")
  | "ax41" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .relator "x" "w",
          dUnary .intrinsicMoment "x" "w"
        ]
  | "ax42" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dOrList [
            dUnary .mode "x" "w",
            dQuality "x" "w"
          ])
          (dUnary .intrinsicMoment "x" "w")
  | "ax43" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .mode "x" "w",
          dQuality "x" "w"
        ]
  | "ax44" =>
      some <| .forallThing "t" <| .forallWorld "w" <| dAndList [
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
      ]
  | "ax45" =>
      some <| .forallThing "t" <| .forallWorld "w" <| dAndList [
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
      ]
  | "ax46" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .endurant "x" "w")
          (.dia "w" "w'" <| .existsThing "k" <| dAndList [
            dSpecificEndurantKind "k" "w'",
            dInst "x" "k" "w'"
          ])
  | "ax47" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        dPart "x" "x" "w"
  | "ax48" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dPart "x" "y" "w",
            dPart "y" "x" "w"
          ])
          (.eqThing "x" "y")
  | "ax49" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dPart "x" "y" "w",
              dPart "y" "z" "w"
            ])
            (dPart "x" "z" "w")
  | "ax50" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dOverlap "x" "y" "w")
          (.existsThing "z" <| dAndList [
            dPart "z" "x" "w",
            dPart "z" "y" "w"
          ])
  | "ax51" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (.not (dPart "y" "x" "w"))
          (.existsThing "z" <| dAndList [
            dPart "z" "y" "w",
            .not (dOverlap "z" "x" "w")
          ])
  | "ax52" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dProperPart "x" "y" "w")
          (dAndList [
            dPart "x" "y" "w",
            .not (dPart "y" "x" "w")
          ])
  | "ax53" =>
      some <| .forallThing "x'" <| .forallThing "y'" <| .forallWorld "w" <|
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
              ]))
  | "ax54" =>
      some <| .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
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
            ])
  | "ax55" =>
      some <| .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dComponentOf "x" "x'" "y" "y'" "w")
            (dAndList [
              dProperPart "x" "y" "w",
              dIndividualFunctionalDependence "x" "x'" "y" "y'" "w"
            ])
  | "ax56" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .constitutedBy "x" "y" "w")
          (dAndList [
            .iff (dUnary .endurant "x" "w") (dUnary .endurant "y" "w"),
            .iff (dUnary .perdurant "x" "w") (dUnary .perdurant "y" "w")
          ])
  | "ax57" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "x'" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .constitutedBy "x" "y" "w",
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              dUnary .kind "x'" "w",
              dUnary .kind "y'" "w"
            ])
            (dNeThing "x'" "y'")
  | "ax58" =>
      some <| .forallThing "x'" <| .forallThing "y'" <| .forallWorld "w" <|
        .iff
          (dGenericConstitutionalDependence "x'" "y'" "w")
          (.forallThing "x" <|
            .imp
              (dInst "x" "x'" "w")
              (.existsThing "y" <| dAndList [
                dInst "y" "y'" "w",
                dBinary .constitutedBy "x" "y" "w"
              ]))
  | "ax59" =>
      some <| .forallThing "x" <| .forallThing "x'" <| .forallThing "y" <|
        .forallThing "y'" <| .forallWorld "w" <|
          .iff
            (dConstitution "x" "x'" "y" "y'" "w")
            (dAndList [
              dInst "x" "x'" "w",
              dInst "y" "y'" "w",
              dGenericConstitutionalDependence "x'" "y'" "w",
              dBinary .constitutedBy "x" "y" "w"
            ])
  | "ax60" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dAndList [
            dUnary .perdurant "x" "w",
            dBinary .constitutedBy "x" "y" "w"
          ])
          (.box "w" "w'" <|
            .imp
              (dUnary .ex "x" "w'")
              (dBinary .constitutedBy "x" "y" "w'"))
  | "ax61" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .constitutedBy "x" "y" "w")
          (.not (dBinary .constitutedBy "y" "x" "w"))
  | "ax62" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp (dUnary .ex "x" "w") (.eqThing "x" "x")
  | "ax63" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExistentialDependence "x" "y" "w")
          (.box "w" "w'" <|
            .imp
              (dUnary .ex "x" "w'")
              (dUnary .ex "y" "w'"))
  | "ax64" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExistentialIndependence "x" "y" "w")
          (dAndList [
            .not (dExistentialDependence "x" "y" "w"),
            .not (dExistentialDependence "y" "x" "w")
          ])
  | "ax65" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .inheresIn "x" "y" "w")
          (dExistentialDependence "x" "y" "w")
  | "ax66" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .inheresIn "x" "y" "w")
          (dAndList [
            dUnary .moment "x" "w",
            .or (dType "y" "w") (dUnary .concreteIndividual "y" "w")
          ])
  | "ax67" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .inheresIn "x" "y" "w",
              dBinary .inheresIn "x" "z" "w"
            ])
            (.eqThing "y" "z")
  | "ax69" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dExternallyDependent "x" "y" "w")
          (dAndList [
            dExistentialDependence "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dBinary .inheresIn "x" "z" "w")
                (dExistentialIndependence "y" "z" "w")
          ])
  | "ax70" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dExternallyDependentMode "x" "w")
          (dAndList [
            dUnary .mode "x" "w",
            .existsThing "y" <| dExternallyDependent "x" "y" "w"
          ])
  | "ax71" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dFoundedBy "x" "y" "w")
          (dAndList [
            .or (dExternallyDependentMode "x" "w") (dUnary .relator "x" "w"),
            dUnary .perdurant "y" "w"
          ])
  | "ax72" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dExternallyDependentMode "x" "w")
          (.existsThing "y" <| dAndList [
            dFoundedBy "x" "y" "w",
            .forallThing "z" <|
              .imp (dFoundedBy "x" "z" "w") (.eqThing "z" "y")
          ])
  | "ax74" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dQuaIndividual "x" "w")
          (.existsThing "y" <| dQuaIndividualOf "x" "y" "w")
  | "ax75" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQuaIndividual "x" "w")
          (dExternallyDependentMode "x" "w")
  | "ax76" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "y'" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              dQuaIndividualOf "x" "y" "w",
              dQuaIndividualOf "x" "y'" "w"
            ])
            (.eqThing "y" "y'")
  | "ax77" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .relator "x" "w")
          (.existsThing "y" <| dAndList [
            dFoundedBy "x" "y" "w",
            .forallThing "z" <|
              .imp (dFoundedBy "x" "z" "w") (.eqThing "z" "y")
          ])
  | "ax80" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .iff
          (dMediates "x" "y" "w")
          (dAndList [
            dUnary .relator "x" "w",
            dUnary .endurant "y" "w",
            .existsThing "z" <| dAndList [
              dQuaIndividualOf "z" "y" "w",
              dPart "z" "x" "w"
            ]
          ])
  | "axQuaIndividualOfEndurant" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dQuaIndividualOf "x" "y" "w")
          (dUnary .endurant "y" "w")
  | "ax81" =>
      some <| .forallThing "t" <| .forallThing "m" <| .forallWorld "w" <|
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
          ])
  | "ax82" =>
      some <| .forallThing "t" <| .forallThing "q" <| .forallWorld "w" <|
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
              ]))
  | "ax83" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .quale "x" "w")
          (dUnary .abstractIndividual "x" "w")
  | "ax84" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .set_ "x" "w")
          (dUnary .abstractIndividual "x" "w")
  | "ax85" =>
      some <| .forallWorld "w" <|
        .not <| .existsThing "x" <| dAndList [
          dUnary .quale "x" "w",
          dUnary .set_ "x" "w"
        ]
  | "ax86" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQualityStructure "x" "w")
          (dAndList [
            dUnary .set_ "x" "w",
            dNonEmptySet "x" "w"
          ])
  | "ax87" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
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
          ])
  | "ax88" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .iff
          (dQualityStructure "x" "w")
          (.or
            (dUnary .qualityDomain "x" "w")
            (dUnary .qualityDimension "x" "w"))
  | "ax89" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dUnary .qualityDomain "x" "w")
          (.not (dUnary .qualityDimension "x" "w"))
  | "ax90" =>
      some <| .forallThing "s" <| .forallThing "t" <| .forallThing "s'" <|
        .forallThing "t'" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dBinary .associatedWith "s" "t" "w",
              dBinary .associatedWith "s'" "t'" "w",
              dProperSub "t'" "t" "w"
            ])
            (dProperSubsetOf "s'" "s" "w")
  | "ax91" =>
      some <| .forallThing "t" <| .forallWorld "w" <|
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
          ])
  | "ax92" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .hasValue "x" "y" "w")
          (dAndList [
            dQuality "x" "w",
            dUnary .quale "y" "w"
          ])
  | "ax93" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dQuality "x" "w")
          (.existsThing "y" <| dAndList [
            dBinary .hasValue "x" "y" "w",
            .forallThing "z" <|
              .imp
                (dBinary .hasValue "x" "z" "w")
                (.eqThing "z" "y")
          ])
  | "ax94" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .hasValue "x" "y" "w")
          (.existsThing "t" <| .existsThing "s" <| dAndList [
            dInst "x" "t" "w",
            dBinary .associatedWith "s" "t" "w",
            dMemberOf "y" "s" "w"
          ])
  | "ax95" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .associatedWith "x" "y" "w")
          (.iff
            (dUnary .qualityDimension "x" "w")
            (dSimpleQualityType "y" "w"))
  | "ax96" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .associatedWith "x" "y" "w")
          (.iff
            (dUnary .qualityDomain "x" "w")
            (dComplexQualityType "y" "w"))
  | "ax97" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
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
            (.eqThing "y" "z")
  | "ax98" =>
      some <| .forallThing "x" <| .forallWorld "w" <|
        .imp
          (dComplexQuality "x" "w")
          (.forallThing "y" <|
            .imp
              (dBinary .inheresIn "y" "x" "w")
              (dSimpleQuality "y" "w"))
  | "ax100" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
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
            ])
  | "ax101" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
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
          ])
  | "axDistanceIdentity" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dAndList [
              .eqThing "x" "y",
              dDistance "x" "y" "r" "w"
            ])
            (dDistanceZero "r" "w")
  | "axDistanceSymmetry" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "r" <|
        .forallWorld "w" <|
          .imp
            (dDistance "x" "y" "r" "w")
            (dDistance "y" "x" "r" "w")
  | "axDistanceTriangle" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallThing "z" <|
        .forallThing "r0" <| .forallThing "r1" <| .forallThing "r2" <|
        .forallThing "s" <| .forallWorld "w" <|
          .imp
            (dAndList [
              dDistance "x" "y" "r0" "w",
              dDistance "y" "z" "r1" "w",
              dDistance "x" "z" "r2" "w",
              dDistanceSum "r0" "r1" "s" "w"
            ])
            (dDistanceGreaterEq "s" "r2" "w")
  | "ax102" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .manifests "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .endurant "y" "w"
          ])
  | "ax103" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
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
          ])
  | "ax104" =>
      some <| .forallThing "x" <| .forallThing "y" <| .forallWorld "w" <|
        .imp
          (dBinary .meet "x" "y" "w")
          (dAndList [
            dUnary .perdurant "x" "w",
            dUnary .perdurant "y" "w"
          ])
  | _ => none

/--
Produce source-level witness text for a failed certificate field.

Specialized analyzers handle fields where the generic formula minimizer loses
important domain structure. All other registered formulas go through the same
evaluate-minimize-render pipeline.
-/
private def appendContextEvidenceCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) : List DiagTrace → Complexity.Costed (Array String)
  | List.nil => .pure out
  | List.cons trace rest =>
      if out.size < budget then
        let next := appendEvidenceForFormulaBudgeted budget worldNames thingNames namedFacts
          worldNames.size thingNames.size tables out trace.env trace.formula
        let tail := appendContextEvidenceCosted budget worldNames thingNames namedFacts tables next rest
        ⟨tail.value, namedFacts.size + (next.size - out.size) + 3 + tail.cost⟩
      else
        let tail := appendContextEvidenceCosted budget worldNames thingNames namedFacts tables out rest
        ⟨tail.value, 1 + tail.cost⟩

private theorem appendContextEvidenceCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : List DiagTrace)
    (hout : out.size ≤ budget) :
    (appendContextEvidenceCosted budget worldNames thingNames namedFacts tables out traces).value.size ≤
      budget := by
  induction traces generalizing out with
  | nil => simpa [appendContextEvidenceCosted] using hout
  | cons trace rest ih =>
      rw [appendContextEvidenceCosted]
      split
      · exact ih _ (appendEvidenceForFormulaBudgeted_size_le budget worldNames thingNames namedFacts
          worldNames.size thingNames.size tables out trace.env trace.formula hout)
      · exact ih out hout

private theorem appendContextEvidenceCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (out : Array String) (traces : List DiagTrace) :
    (appendContextEvidenceCosted budget worldNames thingNames namedFacts tables out traces).cost ≤
      traces.length * (namedFacts.size + budget + 3) := by
  induction traces generalizing out with
  | nil => simp [appendContextEvidenceCosted]
  | cons trace rest ih =>
      rw [appendContextEvidenceCosted]
      split
      · have hout : out.size ≤ budget := by omega
        let next := appendEvidenceForFormulaBudgeted budget worldNames thingNames namedFacts
          worldNames.size thingNames.size tables out trace.env trace.formula
        have hnext : next.size ≤ budget := appendEvidenceForFormulaBudgeted_size_le budget
          worldNames thingNames namedFacts worldNames.size thingNames.size tables out trace.env
          trace.formula hout
        have hgrowth : next.size - out.size ≤ budget :=
          appendEvidenceForFormulaBudgeted_growth_le_budget budget worldNames thingNames namedFacts
            worldNames.size thingNames.size tables out trace.env trace.formula hout
        have htail := ih next
        simp only [List.length_cons, Nat.succ_mul]
        change namedFacts.size + (next.size - out.size) + 3 +
          (appendContextEvidenceCosted budget worldNames thingNames namedFacts tables next rest).cost ≤ _
        omega
      · have htail := ih out
        simp only [List.length_cons, Nat.succ_mul]
        omega

private def appendEvidenceLinesCosted
    (budget : Nat) (out : Array String) : List String → Complexity.Costed (Array String)
  | List.nil => .pure out
  | List.cons item rest =>
      if out.size < budget then
        let tail := appendEvidenceLinesCosted budget (out.push s!"  - {item}") rest
        ⟨tail.value, 2 + tail.cost⟩
      else
        let tail := appendEvidenceLinesCosted budget out rest
        ⟨tail.value, 1 + tail.cost⟩

private theorem appendEvidenceLinesCosted_size_le
    (budget : Nat) (out : Array String) (items : List String) (hout : out.size ≤ budget) :
    (appendEvidenceLinesCosted budget out items).value.size ≤ budget := by
  induction items generalizing out with
  | nil => simpa [appendEvidenceLinesCosted] using hout
  | cons item rest ih =>
      rw [appendEvidenceLinesCosted]
      split
      · apply ih
        simp only [Array.size_push]
        omega
      · exact ih out hout

private theorem appendEvidenceLinesCosted_cost_le
    (budget : Nat) (out : Array String) (items : List String) :
    (appendEvidenceLinesCosted budget out items).cost ≤ 2 * items.length := by
  induction items generalizing out with
  | nil => simp [appendEvidenceLinesCosted]
  | cons item rest ih =>
      rw [appendEvidenceLinesCosted]
      split
      · have htail := ih (out.push s!"  - {item}")
        simp only [List.length_cons]
        omega
      · have htail := ih out
        simp only [List.length_cons]
        omega

private def appendFailingAtomEvidenceCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (failedEnv : Array (String × Nat)) (out : Array String) :
    List DiagAtom → Complexity.Costed (Array String)
  | List.nil => .pure out
  | List.cons atom rest =>
      if out.size < budget then
        let evidence := atomEvidence worldNames thingNames namedFacts failedEnv atom
        if evidence.isEmpty then
          let tail := appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts
            failedEnv out rest
          ⟨tail.value, namedFacts.size + 2 + tail.cost⟩
        else
          let lines := appendEvidenceLinesCosted budget
            (out.push s!"Evidence for {renderDiagAtom worldNames thingNames failedEnv atom}:") evidence.toList
          let tail := appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts
            failedEnv lines.value rest
          ⟨tail.value, namedFacts.size + 3 + lines.cost + tail.cost⟩
      else
        let tail := appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts
          failedEnv out rest
        ⟨tail.value, 1 + tail.cost⟩

private theorem appendFailingAtomEvidenceCosted_size_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (failedEnv : Array (String × Nat)) (out : Array String) (atoms : List DiagAtom)
    (hout : out.size ≤ budget) :
    (appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts failedEnv out atoms).value.size ≤
      budget := by
  induction atoms generalizing out with
  | nil => simpa [appendFailingAtomEvidenceCosted] using hout
  | cons atom rest ih =>
      rw [appendFailingAtomEvidenceCosted]
      split
      · simp only
        split
        · exact ih out hout
        · apply ih
          apply appendEvidenceLinesCosted_size_le
          simp only [Array.size_push]
          omega
      · exact ih out hout

private theorem appendFailingAtomEvidenceCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (failedEnv : Array (String × Nat)) (out : Array String) (atoms : List DiagAtom) :
    (appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts failedEnv out atoms).cost ≤
      atoms.length *
        (namedFacts.size + namedFacts.size + namedFacts.size + 3) := by
  induction atoms generalizing out with
  | nil => simp [appendFailingAtomEvidenceCosted]
  | cons atom rest ih =>
      rw [appendFailingAtomEvidenceCosted]
      split
      · simp only
        split
        · have htail := ih out
          simp only [List.length_cons, Nat.succ_mul]
          omega
        · let evidence := atomEvidence worldNames thingNames namedFacts failedEnv atom
          let lines := appendEvidenceLinesCosted budget
            (out.push s!"Evidence for {renderDiagAtom worldNames thingNames failedEnv atom}:") evidence.toList
          have hevidence : evidence.size ≤ namedFacts.size :=
            atomEvidence_size_le_namedFacts worldNames thingNames namedFacts failedEnv atom
          have hlines : lines.cost ≤ 2 * evidence.size := by
            simpa [lines] using appendEvidenceLinesCosted_cost_le budget
              (out.push s!"Evidence for {renderDiagAtom worldNames thingNames failedEnv atom}:") evidence.toList
          have htail := ih lines.value
          simp only [List.length_cons, Nat.succ_mul]
          change namedFacts.size + 3 + lines.cost +
            (appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts
              failedEnv lines.value rest).cost ≤ _
          omega
      · have htail := ih out
        simp only [List.length_cons, Nat.succ_mul]
        omega

private def appendDiagnosticPreambleCosted
    (budget assignmentExtra : Nat) (out : Array String)
    (assignment condition suggestion : String) : Complexity.Costed (Array String) :=
  let assignmentCost := if out.size < budget then assignmentExtra + 2 else 0
  let out := pushDiagnosticIfRoom budget out assignment
  let conditionCost := if out.size < budget then 2 else 0
  let out := pushDiagnosticIfRoom budget out condition
  let suggestionCost := if out.size < budget then 2 else 0
  let out := pushDiagnosticIfRoom budget out suggestion
  ⟨out, assignmentCost + conditionCost + suggestionCost⟩

private theorem appendDiagnosticPreambleCosted_size_le
    (budget assignmentExtra : Nat) (out : Array String)
    (assignment condition suggestion : String) (hout : out.size ≤ budget) :
    (appendDiagnosticPreambleCosted budget assignmentExtra out assignment condition suggestion).value.size ≤
      budget := by
  unfold appendDiagnosticPreambleCosted
  exact pushDiagnosticIfRoom_size_le budget _ suggestion
    (pushDiagnosticIfRoom_size_le budget _ condition
      (pushDiagnosticIfRoom_size_le budget out assignment hout))

private theorem appendDiagnosticPreambleCosted_cost_le
    (budget assignmentExtra : Nat) (out : Array String)
    (assignment condition suggestion : String) :
    (appendDiagnosticPreambleCosted budget assignmentExtra out assignment condition suggestion).cost ≤
      assignmentExtra + 6 := by
  simp only [appendDiagnosticPreambleCosted]
  split
  all_goals split
  all_goals split <;> simp_all

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
          let failedVars := diagnosticEnvVars vars failedFormula failedEnv
          let renderedCondition :=
            renderDiagnosticCondition worldNames thingNames failedEnv failedFormula
          let conditionLine :=
            if renderedCondition.contains '\n' then
              s!"{diagnosticConditionLabel failedFormula}:\n{renderedCondition}"
            else
              s!"{diagnosticConditionLabel failedFormula}: {renderedCondition}."
          -- Structural setup: failed branch, variable discovery, and condition rendering.
          let preamble := appendDiagnosticPreambleCosted budget failedVars.size out
            s!"Counterexample assignment: {envSummary worldNames thingNames failedVars failedEnv}."
            conditionLine
            s!"Suggestion: {suggestionForFailure worldNames thingNames worldNames.size thingNames.size tables failedEnv failedFormula}"
          let mut out := preamble.value
          let mut cost := checked.cost + minimized.cost + failedEnv.size + vars.size + 3 + preamble.cost
          let contextOut := appendContextEvidenceCosted budget worldNames thingNames namedFacts tables
            out minimized.value.context.toList
          out := contextOut.value
          cost := cost + contextOut.cost
          let atomOut := appendFailingAtomEvidenceCosted budget worldNames thingNames namedFacts
            failedEnv out (failingAtoms worldNames.size thingNames.size tables failedEnv failedFormula).toList
          out := atomOut.value
          cost := cost + atomOut.cost
          return ⟨out, cost⟩

private def genericDiagnosticWitnessesCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    Complexity.Costed (Array String) :=
  foldDiagEnvsUntilCosted worldNames.size thingNames.size vars 0 #[] (#[] : Array String)
    (fun out => budget ≤ out.size)
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body)

/-- Concrete cost recurrence for one failed-assignment visit. The terms expose
formula evaluation, recursive minimization, retained environment/context size,
source-fact scans, the evidence budget, and domain-expanded failing atoms.
This follows the cost-aware-semantics discipline of Niu et al. (POPL 2022):
the recurrence is attached to the executable visitor whose erasure produces
the diagnostic value. -/
private def genericDiagnosticVisitCostBound
    (budget worldCount thingCount namedFactCount varCount envSize : Nat)
    (tables : FactTables) (body : DiagFormula) : Nat :=
  body.evalCostBound worldCount thingCount
      (diagAtomCostBound worldCount thingCount tables) envSize +
    body.failureMinimizeCostBound worldCount thingCount tables envSize +
    2 * body.failureEnvSizeBound envSize + varCount + 9 +
    body.failureContextSizeBound * (namedFactCount + budget + 3) +
    body.failureAtomEnumerationBound worldCount thingCount *
      (namedFactCount + namedFactCount + namedFactCount + 3)

private theorem genericDiagnosticVisitCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula)
    (out : Array String) (env : Array (String × Nat)) :
    (genericDiagnosticVisitCosted budget worldNames thingNames namedFacts tables vars body out env).cost ≤
      genericDiagnosticVisitCostBound budget worldNames.size thingNames.size namedFacts.size
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
    have hvars := diagnosticEnvVars_size_le vars
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
    have hcontext := minimizeFailureCosted_context_size_le
      worldNames.size thingNames.size tables env body
    have hminAtoms := minimizeFailureCosted_failingAtomCountBound_le_failureEnumeration
      worldNames.size thingNames.size tables env body
    have hatoms := failingAtoms_size_le worldNames.size thingNames.size tables
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
      (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula
    have hcontextScaled := Nat.mul_le_mul_right (namedFacts.size + budget + 3) hcontext
    have hatomsCombined :
        (failingAtoms worldNames.size thingNames.size tables
          (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.env
          (minimizeFailureCosted worldNames.size thingNames.size tables env body).value.formula).size ≤
          body.failureAtomEnumerationBound worldNames.size thingNames.size :=
      Nat.le_trans hatoms hminAtoms
    have hatomsScaled := Nat.mul_le_mul_right
      (namedFacts.size + namedFacts.size + namedFacts.size + 3) hatomsCombined
    unfold genericDiagnosticVisitCostBound
    grind [appendDiagnosticPreambleCosted_cost_le, appendDiagnosticPreambleCosted_size_le,
      appendContextEvidenceCosted_cost_le,
      appendFailingAtomEvidenceCosted_cost_le]

private theorem genericDiagnosticWitnessesCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).cost ≤
      diagEnvDependentFoldCostBound worldNames.size thingNames.size
        (fun envSize => genericDiagnosticVisitCostBound budget worldNames.size thingNames.size
          namedFacts.size vars.size envSize tables body)
        0 vars.toList := by
  unfold genericDiagnosticWitnessesCosted
  apply foldDiagEnvsUntilCosted_dependent_cost_le
  intro state env
  exact genericDiagnosticVisitCosted_cost_le budget worldNames thingNames namedFacts
    tables vars body state env

private def genericDiagnosticWitnesses
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) : Array String :=
  (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).value

@[simp] private theorem genericDiagnosticWitnessesCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (vars : Array DiagVar) (body : DiagFormula) :
    (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body).value =
      genericDiagnosticWitnesses budget worldNames thingNames namedFacts tables vars body := rfl

private def capDiagnosticCosted (budget : Nat)
    (items : Complexity.Costed (Array String)) : Complexity.Costed (Array String) :=
  let emitted := min budget items.value.size
  ⟨items.value.extract 0 emitted, items.cost + emitted + 2⟩

private theorem capDiagnosticCosted_cost_eq_emitted (budget : Nat)
    (items : Complexity.Costed (Array String)) :
    (capDiagnosticCosted budget items).cost =
      items.cost + (capDiagnosticCosted budget items).value.size + 2 := by
  simp [capDiagnosticCosted]

private theorem capDiagnosticCosted_cost_le
    (budget : Nat) (items : Complexity.Costed (Array String)) :
    (capDiagnosticCosted budget items).cost ≤ items.cost + budget + 2 := by
  unfold capDiagnosticCosted
  simp

private def diagnosticWitnessesUnboundedCosted
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) : Complexity.Costed (Array String) :=
  if field == "ax68" then
    capDiagnosticCosted budget <| Complexity.Costed.charge 1 <|
      ax68ClosureAnalysisCosted worldNames thingNames tables
  else if field == "ax71" then
    capDiagnosticCosted budget <| Complexity.Costed.charge 2 <|
      ax71FoundationAnalysisCosted worldNames thingNames tables
  else if field == "ax73" then
    capDiagnosticCosted budget <| Complexity.Costed.charge 3 <|
      ax73PartCharacterizationAnalysisCosted worldNames thingNames tables
  else if field == "ax78" then
    Complexity.Costed.charge 4 <|
      ax78FoundationAnalysisCosted budget worldNames thingNames tables
  else if field == "ax79" then
    capDiagnosticCosted budget <| Complexity.Costed.charge 5 <|
      ax79FoundationAnalysisCosted worldNames thingNames tables
  else if field == "ax99" then
    capDiagnosticCosted budget <| Complexity.Costed.charge 6 <|
      ax99QualityDomainAnalysisCosted worldNames thingNames tables
  else match diagnosticFormula? field with
  | none =>
      capDiagnosticCosted budget
        ⟨#[s!"No structured DSL-level witness extractor is registered for {field} yet."], 8⟩
  | some formula =>
      let vars := formula.forallVars
      let body := formula.stripForalls
      let out := genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts tables vars body
      if out.value.isEmpty then
        capDiagnosticCosted budget
          ⟨#[s!"The structured checker did not find a DSL-level witness for {field}."],
            out.cost + 9⟩
      else
        capDiagnosticCosted budget (Complexity.Costed.charge 8 out)

private def diagnosticWitnessesUnbounded
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) : Array String :=
  (diagnosticWitnessesUnboundedCosted budget worldNames thingNames namedFacts tables field).value

private theorem diagnosticWitnessesUnboundedCosted_value
    (budget : Nat) (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) :
    (diagnosticWitnessesUnboundedCosted budget worldNames thingNames namedFacts tables field).value =
      diagnosticWitnessesUnbounded budget worldNames thingNames namedFacts tables field := rfl

/-- Field-sensitive search and rendering bound for the diagnostics dispatcher.
The definition follows the selected specialized analyzer or registered formula
evaluator branch. -/
def diagnosticWitnessesInnerCostBound
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables) (field : String) : Nat :=
  if field == "ax68" then
    2 * (worldNames.size * thingNames.size *
      (thingNames.size *
        (thingNames.size + thingNames.size + thingNames.size + thingNames.size + 7) + 4) + 1) +
      thingNames.size + 3 + 1 + budget + 2
  else if field == "ax71" then
    worldNames.size * thingNames.size * thingNames.size *
      ax71AssignmentCostBound worldNames.size thingNames.size + 1 + 2 + budget + 2
  else if field == "ax73" then
    worldNames.size * thingNames.size * thingNames.size *
      ax73AssignmentCostBound worldNames.size thingNames.size tables + 1 + 3 + budget + 2
  else if field == "ax78" then
    worldNames.size * thingNames.size * thingNames.size *
      (14 * thingNames.size + 18) + min budget 2 + 2 + 4
  else if field == "ax79" then
    worldNames.size * thingNames.size *
      ax79RelatorCostBound worldNames.size thingNames.size tables + 2 + 5 + budget + 2
  else if field == "ax99" then
    worldNames.size * thingNames.size *
      ax99ThingCostBound thingNames.size tables.productFamilies.size + 2 + 6 + budget + 2
  else match diagnosticFormula? field with
  | none => 8 + budget + 2
  | some formula =>
      let vars := formula.forallVars
      let body := formula.stripForalls
      diagEnvDependentFoldCostBound worldNames.size thingNames.size
        (fun envSize => genericDiagnosticVisitCostBound budget worldNames.size thingNames.size
          namedFacts.size vars.size envSize tables body)
        0 vars.toList + budget + 11

private theorem diagnosticWitnessesUnboundedCosted_cost_le
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables) (field : String) :
    (diagnosticWitnessesUnboundedCosted budget worldNames thingNames namedFacts tables field).cost ≤
      diagnosticWitnessesInnerCostBound budget worldNames thingNames namedFacts tables field := by
  simp only [diagnosticWitnessesUnboundedCosted, diagnosticWitnessesInnerCostBound]
  split
  · have h := ax68ClosureAnalysisCosted_cost_le worldNames thingNames tables
    have hcap := capDiagnosticCosted_cost_le budget
      (Complexity.Costed.charge 1 (ax68ClosureAnalysisCosted worldNames thingNames tables))
    simp only [Complexity.Costed.charge_cost] at hcap
    omega
  · split
    · have h := ax71FoundationAnalysisCosted_cost_le worldNames thingNames tables
      have hcap := capDiagnosticCosted_cost_le budget
        (Complexity.Costed.charge 2 (ax71FoundationAnalysisCosted worldNames thingNames tables))
      simp only [Complexity.Costed.charge_cost] at hcap
      omega
    · split
      · have h := ax73PartCharacterizationAnalysisCosted_cost_le worldNames thingNames tables
        have hcap := capDiagnosticCosted_cost_le budget
          (Complexity.Costed.charge 3
            (ax73PartCharacterizationAnalysisCosted worldNames thingNames tables))
        simp only [Complexity.Costed.charge_cost] at hcap
        omega
      · split
        · have h := ax78FoundationAnalysisCosted_cost_le budget worldNames thingNames tables
          simp only [Complexity.Costed.charge_cost]
          omega
        · split
          · have h := ax79FoundationAnalysisCosted_cost_le worldNames thingNames tables
            have hcap := capDiagnosticCosted_cost_le budget
              (Complexity.Costed.charge 5
                (ax79FoundationAnalysisCosted worldNames thingNames tables))
            simp only [Complexity.Costed.charge_cost] at hcap
            omega
          · split
            · have h := ax99QualityDomainAnalysisCosted_cost_le worldNames thingNames tables
              have hcap := capDiagnosticCosted_cost_le budget
                (Complexity.Costed.charge 6
                  (ax99QualityDomainAnalysisCosted worldNames thingNames tables))
              simp only [Complexity.Costed.charge_cost] at hcap
              omega
            · split
              · have hcap := capDiagnosticCosted_cost_le budget
                  (⟨#[s!"No structured DSL-level witness extractor is registered for {field} yet."], 8⟩)
                omega
              · rename_i formula hformula
                let vars := formula.forallVars
                let body := formula.stripForalls
                have hout := genericDiagnosticWitnessesCosted_cost_le budget worldNames thingNames
                  namedFacts tables vars body
                split
                · have hcap := capDiagnosticCosted_cost_le budget
                    (⟨#[s!"The structured checker did not find a DSL-level witness for {field}."],
                      (genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts
                        tables vars body).cost + 9⟩)
                  dsimp only [vars, body] at hout hcap
                  omega
                · have hcap := capDiagnosticCosted_cost_le budget
                    (Complexity.Costed.charge 8 <|
                      genericDiagnosticWitnessesCosted budget worldNames thingNames namedFacts
                        tables vars body)
                  simp only [Complexity.Costed.charge_cost] at hcap
                  dsimp only [vars, body] at hout hcap
                  omega

/-- Budget-aware diagnostic producer. The budget is part of the producer API,
so callers do not need to construct an unbounded result before deciding how
much evidence may leave the diagnostic subsystem. Specialized and generic
analyzers retain deterministic prefix order. -/
def diagnosticWitnessesBudgetedCosted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) : Complexity.Costed (Array String) :=
  let generated :=
    diagnosticWitnessesUnboundedCosted budget worldNames thingNames namedFacts tables field
  capDiagnosticCosted budget generated

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
rendering contribute the inner producer cost; the public boundary adds one
operation per emitted item and two operations for prefix selection. -/
theorem diagnosticWitnessesBudgetedCosted_cost_eq_inner_add_emitted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).cost =
      (diagnosticWitnessesUnboundedCosted budget worldNames thingNames namedFacts tables field).cost +
        (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size + 2 := by
  unfold diagnosticWitnessesBudgetedCosted diagnosticWitnessesBudgeted
  exact capDiagnosticCosted_cost_eq_emitted _ _

/-- Output-sensitive public diagnostics theorem. The field-sensitive inner
term accounts for formula evaluation, model scans, registry scans, and evidence
construction. The final two terms charge the emitted prefix and its selection.
This is a bound on the executable producer, not on a separately defined
envelope. -/
theorem diagnosticWitnessesBudgetedCosted_cost_le_inner_add_emitted
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgetedCosted budget worldNames thingNames namedFacts tables field).cost ≤
      diagnosticWitnessesInnerCostBound budget worldNames thingNames namedFacts tables field +
        (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size + 2 := by
  rw [diagnosticWitnessesBudgetedCosted_cost_eq_inner_add_emitted]
  have hinner := diagnosticWitnessesUnboundedCosted_cost_le
    budget worldNames thingNames namedFacts tables field
  omega

theorem diagnosticWitnessesBudgeted_size_le
    (budget : Nat) (worldNames thingNames : Array Name)
    (namedFacts : Array NamedScopedFact) (tables : FactTables)
    (field : String) :
    (diagnosticWitnessesBudgeted budget worldNames thingNames namedFacts tables field).size ≤
      budget := by
  unfold diagnosticWitnessesBudgeted diagnosticWitnessesBudgetedCosted capDiagnosticCosted
  simp

/-- Production diagnostics use the same 128-item budget as the final widget
boundary. The latter remains as defense in depth for non-witness messages. -/
def diagnosticWitnesses
    (worldNames thingNames : Array Name) (namedFacts : Array NamedScopedFact)
    (tables : FactTables) (field : String) : Array String :=
  diagnosticWitnessesBudgeted 128 worldNames thingNames namedFacts tables field


end LeanUfo.UFO.DSL
