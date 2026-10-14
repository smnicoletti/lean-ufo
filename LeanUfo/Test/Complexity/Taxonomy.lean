import LeanUfo.UFO.DSL.Compiler

/-!
# Taxonomy membership and ordering

This characterization test records every unary field's ancestor sequence.
Shared ancestors occur once, at their first depth-first visit. Changes to the
fixed taxonomy require review of both the
expected membership and the ordering contract.
-/

namespace LeanUfo.Test.Complexity.Taxonomy

open LeanUfo.UFO.DSL

private def expectedAncestors : Array (String × Array String) :=
  #[("concreteIndividual", #["concreteIndividual"]), ("abstractIndividual", #["abstractIndividual"]),
  ("endurant", #["endurant", "concreteIndividual"]), ("perdurant", #["perdurant", "concreteIndividual"]),
  ("endurantType", #["endurantType"]), ("perdurantType", #["perdurantType"]), ("rigid", #["rigid"]),
  ("antiRigid", #["antiRigid"]), ("semiRigid", #["semiRigid"]), ("kind", #["kind", "rigid", "sortal", "endurantType"]),
  ("sortal", #["sortal", "endurantType"]), ("nonSortal", #["nonSortal", "endurantType"]),
  ("subKind", #["subKind", "rigid", "sortal", "endurantType"]),
  ("phase", #["phase", "antiRigid", "sortal", "endurantType"]),
  ("role", #["role", "antiRigid", "sortal", "endurantType"]),
  ("semiRigidSortal", #["semiRigidSortal", "semiRigid", "sortal", "endurantType"]),
  ("category", #["category", "rigid", "nonSortal", "endurantType"]),
  ("mixin", #["mixin", "semiRigid", "nonSortal", "endurantType"]),
  ("phaseMixin", #["phaseMixin", "antiRigid", "nonSortal", "endurantType"]),
  ("roleMixin", #["roleMixin", "antiRigid", "nonSortal", "endurantType"]),
  ("substantial", #["substantial", "endurant", "concreteIndividual"]),
  ("moment", #["moment", "endurant", "concreteIndividual"]),
  ("object", #["object", "substantial", "endurant", "concreteIndividual"]),
  ("collective", #["collective", "substantial", "endurant", "concreteIndividual"]),
  ("quantity", #["quantity", "substantial", "endurant", "concreteIndividual"]),
  ("relator", #["relator", "moment", "endurant", "concreteIndividual"]),
  ("intrinsicMoment", #["intrinsicMoment", "moment", "endurant", "concreteIndividual"]),
  ("mode", #["mode", "intrinsicMoment", "moment", "endurant", "concreteIndividual"]),
  ("qualityKind",
    #["qualityKind", "qualityType", "intrinsicMomentType", "momentType", "endurantType", "kind", "rigid", "sortal"]),
  ("substantialType", #["substantialType", "endurantType"]), ("momentType", #["momentType", "endurantType"]),
  ("objectType", #["objectType", "substantialType", "endurantType"]),
  ("collectiveType", #["collectiveType", "substantialType", "endurantType"]),
  ("quantityType", #["quantityType", "substantialType", "endurantType"]),
  ("relatorType", #["relatorType", "momentType", "endurantType"]),
  ("modeType", #["modeType", "intrinsicMomentType", "momentType", "endurantType"]),
  ("qualityType", #["qualityType", "intrinsicMomentType", "momentType", "endurantType"]),
  ("objectKind", #["objectKind", "objectType", "substantialType", "endurantType", "kind", "rigid", "sortal"]),
  ("collectiveKind",
    #["collectiveKind", "collectiveType", "substantialType", "endurantType", "kind", "rigid", "sortal"]),
  ("quantityKind", #["quantityKind", "quantityType", "substantialType", "endurantType", "kind", "rigid", "sortal"]),
  ("relatorKind", #["relatorKind", "relatorType", "momentType", "endurantType", "kind", "rigid", "sortal"]),
  ("modeKind",
    #["modeKind", "modeType", "intrinsicMomentType", "momentType", "endurantType", "kind", "rigid", "sortal"]),
  ("ex", #["ex"]), ("quale", #["quale", "abstractIndividual"]), ("set_", #["set_", "abstractIndividual"]),
  ("qualityDomain", #["qualityDomain"]), ("qualityDimension", #["qualityDimension"]),
  ("intrinsicMomentType", #["intrinsicMomentType", "momentType", "endurantType"]), ("distanceZero", #["distanceZero"])]

/-- Check the entire fixed field registry, including roots and shared paths. -/
example :
    (UnaryField.all.map fun field =>
      (field.toTableField, (expandUnaryTaxonomyFields field).map UnaryField.toTableField)) =
        expectedAncestors := by
  native_decide

/-- Raw string interfaces also support two names outside the typed registry. -/
example :
    unaryTaxonomyParents "externallyDependentMode" = #["mode"] ∧
    unaryTaxonomyParents "quaIndividual" = #["externallyDependentMode"] ∧
    unaryTaxonomyParents "unknown" = #[] := by native_decide

/-- A root needs a depth test, a visited-result test, an output write, and a
parent lookup. The empty visited and parent arrays need no iterations. -/
example : (Complexity.Taxonomy.ancestorsCosted .ex).cost = 4 := by native_decide

example : (addTaxonomyFactsCosted #[]).cost = 0 := by native_decide

/-- The batch adds two input-traversal operations, a tag test, and three
operations to copy the root into the fact output: 4 + 2 + 1 + 3 = 10. -/
example : (addTaxonomyFactsCosted #[.unary .ex 3 7]).cost = 10 := by native_decide

/-- The longest search reaches the proved bound: 202 search operations,
eight copies at three operations each, and three batch operations. -/
example :
    let result := addTaxonomyFactsCosted #[.unary .modeKind 3 7]
    result.cost = 229 ∧ result.value.size = 8 := by native_decide

/-- Facts of other arities are preserved in order. Repeated source facts
remain repeated here; only duplicate ancestors within one search are removed. -/
example :
    let result := addTaxonomyFactsCosted #[.unary .ex 3 7, .binary .inst 1 2 4,
      .ternary .distance 0 1 2 3, .tupleProjection 4 2 5 6,
      .derived "retained", .unary .ex 3 7]
    (match result.value.toList with
      | [.unary .ex 3 7, .binary .inst 1 2 4, .ternary .distance 0 1 2 3,
         .tupleProjection 4 2 5 6, .derived "retained", .unary .ex 3 7] => true
      | _ => false) = true ∧ result.cost = 36 := by native_decide

/-- Each search starts with its own empty visited set, but emitted facts
accumulate in one array. Input construction is outside the measured call. -/
example :
    let result := addTaxonomyFactsCosted (Array.replicate 10000 (.unary .modeKind 3 7))
    result.cost = 2290000 ∧ result.value.size = 80000 := by native_decide

end LeanUfo.Test.Complexity.Taxonomy
