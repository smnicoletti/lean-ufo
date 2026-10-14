import LeanUfo.UFO.DSL.Compiler.AST
import LeanUfo.UFO.DSL.Complexity.CostModel

/-!
# Derived-assertion proposition construction

A resolved assertion contains a field name and at most four thing coordinates.
The renderer inserts those coordinates and one world coordinate into Lean
source text. Unary and binary fields can name definitions on an earlier UFO
signature, so rendering first selects the required signature projection.

The counted renderer charges field comparisons, selected branches, numeric
formatting calls, and string concatenations. Its value equals the independent
text specification. Costs are at most 28 unit operations and do not depend on
the numeric coordinates. Character processing inside string primitives is
outside that model. This compositional treatment follows Haslbeck's time-bound
rules and Niu et al.'s separation of values from costs; the complexity guide
gives the references and execution-model qualifications.
-/

namespace LeanUfo.UFO.DSL

open Complexity

private def finSourceCosted (suffix : String) (idx : Nat) : Costed String :=
  Costed.appendString
    (Costed.appendString (Costed.pure "(⟨") (Costed.tick (toString idx) 1))
    (Costed.pure suffix)

private theorem finSourceCosted_value (suffix : String) (idx : Nat) :
    (finSourceCosted suffix idx).value = "(⟨" ++ toString idx ++ suffix := rfl

private theorem finSourceCosted_cost (suffix : String) (idx : Nat) :
    (finSourceCosted suffix idx).cost = 3 := rfl

private def finThingSourceCosted (idx : Nat) : Costed String :=
  finSourceCosted ", by decide⟩ : Fin data.thingCount)" idx

private def finWorldSourceCosted (idx : Nat) : Costed String :=
  finSourceCosted ", by decide⟩ : Fin data.worldCount)" idx

private def definedUnaryPredicateCosted (field : String) : Costed (Option (String × String)) :=
  Costed.branch (Costed.tick (field == "Quality") 1)
    (fun _ => Costed.pure (some ("Quality", "sig.toUFOSignature3_3"))) (fun _ =>
  Costed.branch (Costed.tick (field == "NonEmptySet") 1)
    (fun _ => Costed.pure (some ("NonEmptySet", "sig.toUFOSignature3_12"))) (fun _ =>
  Costed.branch (Costed.tick (field == "QualityStructure") 1)
    (fun _ => Costed.pure (some ("QualityStructure", "sig.toUFOSignature3_12"))) (fun _ =>
  Costed.branch (Costed.tick (field == "SimpleQuality") 1)
    (fun _ => Costed.pure (some ("SimpleQuality", "sig.toUFOSignature3_12"))) (fun _ =>
  Costed.branch (Costed.tick (field == "ComplexQuality") 1)
    (fun _ => Costed.pure (some ("ComplexQuality", "sig.toUFOSignature3_12"))) (fun _ =>
  Costed.branch (Costed.tick (field == "SimpleQualityType") 1)
    (fun _ => Costed.pure (some ("SimpleQualityType", "sig.toUFOSignature3_12"))) (fun _ =>
  Costed.branch (Costed.tick (field == "ComplexQualityType") 1)
    (fun _ => Costed.pure (some ("ComplexQualityType", "sig.toUFOSignature3_12")))
    (fun _ => Costed.pure none)))))))

private def definedBinaryPredicateCosted (field : String) : Costed (Option (String × String)) :=
  Costed.branch (Costed.tick (field == "ProperSub") 1)
    (fun _ => Costed.pure (some ("ProperSub", "sig.toUFOSignature3_1"))) (fun _ =>
  Costed.branch (Costed.tick (field == "UltimateBearerOf") 1)
    (fun _ => Costed.pure (some ("UltimateBearerOf", "sig.toUFOSignature3_9"))) (fun _ =>
  Costed.branch (Costed.tick (field == "SubsetOf") 1)
    (fun _ => Costed.pure (some ("SubsetOf", "sig.toUFOSignature3_12"))) (fun _ =>
  Costed.branch (Costed.tick (field == "ProperSubsetOf") 1)
    (fun _ => Costed.pure (some ("ProperSubsetOf", "sig.toUFOSignature3_12")))
    (fun _ => Costed.pure none))))

private def unaryDefinition? (field : String) : Option (String × String) :=
  match field with
  | "Quality" => some ("Quality", "sig.toUFOSignature3_3")
  | "NonEmptySet" => some ("NonEmptySet", "sig.toUFOSignature3_12")
  | "QualityStructure" => some ("QualityStructure", "sig.toUFOSignature3_12")
  | "SimpleQuality" => some ("SimpleQuality", "sig.toUFOSignature3_12")
  | "ComplexQuality" => some ("ComplexQuality", "sig.toUFOSignature3_12")
  | "SimpleQualityType" => some ("SimpleQualityType", "sig.toUFOSignature3_12")
  | "ComplexQualityType" => some ("ComplexQualityType", "sig.toUFOSignature3_12")
  | _ => none

private def binaryDefinition? (field : String) : Option (String × String) :=
  match field with
  | "ProperSub" => some ("ProperSub", "sig.toUFOSignature3_1")
  | "UltimateBearerOf" => some ("UltimateBearerOf", "sig.toUFOSignature3_9")
  | "SubsetOf" => some ("SubsetOf", "sig.toUFOSignature3_12")
  | "ProperSubsetOf" => some ("ProperSubsetOf", "sig.toUFOSignature3_12")
  | _ => none

private theorem definedUnaryPredicateCosted_value (field : String) :
    (definedUnaryPredicateCosted field).value = unaryDefinition? field := by
  simp [definedUnaryPredicateCosted, Costed.branch_value, unaryDefinition?]
  repeat' first | split | simp_all

private theorem definedBinaryPredicateCosted_value (field : String) :
    (definedBinaryPredicateCosted field).value = binaryDefinition? field := by
  simp [definedBinaryPredicateCosted, Costed.branch_value, binaryDefinition?]
  repeat' first | split | simp_all

private theorem definedUnaryPredicateCosted_cost_le (field : String) :
    (definedUnaryPredicateCosted field).cost ≤ 14 := by
  simp [definedUnaryPredicateCosted, Costed.branch]
  repeat' first | split | simp_all

private theorem definedBinaryPredicateCosted_cost_le (field : String) :
    (definedBinaryPredicateCosted field).cost ≤ 8 := by
  simp [definedBinaryPredicateCosted, Costed.branch]
  repeat' first | split | simp_all

private def predicateHeadCosted (field : String)
    (selected : Costed (Option (String × String))) : Costed String :=
  Costed.charge 1 <| selected.bind fun
    | some (definition, signature) =>
        Costed.appendString
          (Costed.appendString (Costed.pure definition) (Costed.pure " "))
          (Costed.pure signature)
    | none => Costed.appendString (Costed.pure "sig.") (Costed.pure field)

private theorem predicateHeadCosted_value (field : String)
    (selected : Costed (Option (String × String))) :
    (predicateHeadCosted field selected).value =
      match selected.value with
      | some (definition, signature) => definition ++ " " ++ signature
      | none => "sig." ++ field := by
  cases h : selected.value <;> simp [predicateHeadCosted, Costed.bind, h]

private theorem predicateHeadCosted_cost_le (field : String)
    (selected : Costed (Option (String × String))) :
    (predicateHeadCosted field selected).cost ≤ selected.cost + 3 := by
  cases h : selected.value <;> simp [predicateHeadCosted, Costed.bind, h] <;> omega

private def appendArgumentCosted (textBefore argument : Costed String) : Costed String :=
  Costed.appendString (Costed.appendString textBefore (Costed.pure " ")) argument

private theorem appendArgumentCosted_value (textBefore argument : Costed String) :
    (appendArgumentCosted textBefore argument).value = textBefore.value ++ " " ++ argument.value := rfl

private theorem appendArgumentCosted_cost (textBefore argument : Costed String) :
    (appendArgumentCosted textBefore argument).cost = textBefore.cost + argument.cost + 2 := by
  simp [appendArgumentCosted]
  omega

/-- Render the exact proposition stored for one resolved assertion and world.
Only unary and binary fields need the fixed definition-name selection. -/
def renderDerivedFactCosted (fact : ResolvedDerivedFact) (world : Nat) : Costed String :=
  Costed.charge 1 <| match fact with
  | .unary field thing =>
      appendArgumentCosted
        (appendArgumentCosted
          (predicateHeadCosted field (definedUnaryPredicateCosted field))
          (finThingSourceCosted thing))
        (finWorldSourceCosted world)
  | .binary field left right =>
      appendArgumentCosted
        (appendArgumentCosted
          (appendArgumentCosted
            (predicateHeadCosted field (definedBinaryPredicateCosted field))
            (finThingSourceCosted left))
          (finThingSourceCosted right))
        (finWorldSourceCosted world)
  | .ternary field first second third =>
      appendArgumentCosted
        (appendArgumentCosted
          (appendArgumentCosted
            (appendArgumentCosted (Costed.appendString (Costed.pure "sig.") (Costed.pure field))
              (finThingSourceCosted first))
            (finThingSourceCosted second))
          (finThingSourceCosted third))
        (finWorldSourceCosted world)
  | .quaternary field first second third fourth =>
      appendArgumentCosted
        (appendArgumentCosted
          (appendArgumentCosted
            (appendArgumentCosted
              (appendArgumentCosted (Costed.appendString (Costed.pure "sig.") (Costed.pure field))
                (finThingSourceCosted first))
              (finThingSourceCosted second))
            (finThingSourceCosted third))
          (finThingSourceCosted fourth))
        (finWorldSourceCosted world)

def renderDerivedFact (fact : ResolvedDerivedFact) (world : Nat) : String :=
  (renderDerivedFactCosted fact world).value

/-- Text specification for the existing generated certificate syntax.
This function is used for correspondence proofs, not production rendering. -/
def renderDerivedFactSpecification (fact : ResolvedDerivedFact) (world : Nat) : String :=
  let thing := fun idx => s!"(⟨{idx}, by decide⟩ : Fin data.thingCount)"
  let atWorld := s!"(⟨{world}, by decide⟩ : Fin data.worldCount)"
  match fact with
  | .unary field x =>
      match unaryDefinition? field with
      | some (definition, signature) => s!"{definition} {signature} {thing x} {atWorld}"
      | none => s!"sig.{field} {thing x} {atWorld}"
  | .binary field x y =>
      match binaryDefinition? field with
      | some (definition, signature) => s!"{definition} {signature} {thing x} {thing y} {atWorld}"
      | none => s!"sig.{field} {thing x} {thing y} {atWorld}"
  | .ternary field x y z => s!"sig.{field} {thing x} {thing y} {thing z} {atWorld}"
  | .quaternary field x y z t => s!"sig.{field} {thing x} {thing y} {thing z} {thing t} {atWorld}"

theorem renderDerivedFactCosted_value (fact : ResolvedDerivedFact) (world : Nat) :
    (renderDerivedFactCosted fact world).value = renderDerivedFactSpecification fact world := by
  cases fact <;>
    simp [renderDerivedFactCosted, appendArgumentCosted_value, predicateHeadCosted_value,
      definedUnaryPredicateCosted_value, definedBinaryPredicateCosted_value,
      finThingSourceCosted, finWorldSourceCosted, finSourceCosted_value,
      renderDerivedFactSpecification]
  all_goals first | rfl | (split <;> rfl)

/-- Formatting has fixed arity. The largest branch is a unary definition at
the last of seven selection positions: 14+1+2 for its head, ten for its two
coordinates and separators, and one arity-dispatch operation. -/
theorem renderDerivedFactCosted_cost_le (fact : ResolvedDerivedFact) (world : Nat) :
    (renderDerivedFactCosted fact world).cost ≤ 28 := by
  cases fact with
  | unary field thing =>
      have head := predicateHeadCosted_cost_le field (definedUnaryPredicateCosted field)
      have selected := definedUnaryPredicateCosted_cost_le field
      simp only [renderDerivedFactCosted, Costed.charge_cost, appendArgumentCosted_cost,
        finThingSourceCosted, finWorldSourceCosted, finSourceCosted_cost]
      omega
  | binary field left right =>
      have head := predicateHeadCosted_cost_le field (definedBinaryPredicateCosted field)
      have selected := definedBinaryPredicateCosted_cost_le field
      simp only [renderDerivedFactCosted, Costed.charge_cost, appendArgumentCosted_cost,
        finThingSourceCosted, finWorldSourceCosted, finSourceCosted_cost]
      omega
  | ternary field first second third =>
      simp [renderDerivedFactCosted, appendArgumentCosted_cost,
        finThingSourceCosted, finWorldSourceCosted, finSourceCosted_cost]
  | quaternary field first second third fourth =>
      simp [renderDerivedFactCosted, appendArgumentCosted_cost,
        finThingSourceCosted, finWorldSourceCosted, finSourceCosted_cost]

/-- World coordinates change the text but not the number of selected string
operations. Numeric character lengths are outside the unit-cost interface. -/
theorem renderDerivedFactCosted_cost_world (fact : ResolvedDerivedFact) (world other : Nat) :
    (renderDerivedFactCosted fact world).cost = (renderDerivedFactCosted fact other).cost := by
  cases fact <;>
    simp [renderDerivedFactCosted, appendArgumentCosted_cost, finWorldSourceCosted,
      finSourceCosted_cost]

end LeanUfo.UFO.DSL
