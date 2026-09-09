import LeanUfo.UFO.DSL.Complexity.Tables

/-!
# Verified native model interpretation

Compiled facts justify the equality required by `FactTables.verifiedLookups`.
The frontend passes this proof with its generated tables to
`FactTables.toFiniteModel4Verified`, so native checking reads dense tables while
kernel reduction retains the compact sparse definitions. The equality covers
the exact tables and finite dimensions passed to the constructor.
-/

namespace LeanUfo.UFO.DSL

open Complexity.Production

instance (worldCount thingCount : Nat) (fact : CompiledFact) :
    Decidable (factWellBounded worldCount thingCount fact) := by
  cases fact <;> unfold factWellBounded <;> infer_instance

instance (ast : ModelAST) : Decidable (explicitModelWellBounded ast) := by
  unfold explicitModelWellBounded
  infer_instance

private theorem foldFamilies_eq (families : Array ProductFamilySpec) (tables : FactTables) :
    families.foldl addProductFamily tables =
      { tables with productFamilies :=
          (families.foldl (fun out family => out.push family) tables.productFamilies) } := by
  simp only [← Array.foldl_toList]
  generalize families.toList = items
  induction items generalizing tables with
  | nil => rfl
  | cons family items ih => simp only [List.foldl_cons, ih, addProductFamily]

private theorem writeDenseFact_families (tables : FactTables)
    (families : Array ProductFamilySpec) (fact : CompiledFact) :
    FactTables.writeDenseFact { tables with productFamilies := families } fact =
      { FactTables.writeDenseFact tables fact with productFamilies := families } := by
  cases fact <;> rfl

private theorem foldDense_families (facts : Array CompiledFact) (tables : FactTables)
    (families : Array ProductFamilySpec) :
    facts.foldl FactTables.writeDenseFact { tables with productFamilies := families } =
      { facts.foldl FactTables.writeDenseFact tables with productFamilies := families } := by
  simp only [← Array.foldl_toList]
  generalize facts.toList = items
  induction items generalizing tables with
  | nil => rfl
  | cons fact items ih => simp only [List.foldl_cons, writeDenseFact_families, ih]

private theorem withDenseFacts_families (tables : FactTables)
    (families : Array ProductFamilySpec) (worldCount thingCount : Nat)
    (facts : Array CompiledFact) :
    FactTables.withDenseFacts { tables with productFamilies := families }
        worldCount thingCount facts =
      { tables.withDenseFacts worldCount thingCount facts with productFamilies := families } := by
  unfold FactTables.withDenseFacts
  have hinit :
      FactTables.initializeDense { tables with productFamilies := families }
          worldCount thingCount (projectionArityOfFacts facts) =
        { tables.initializeDense worldCount thingCount (projectionArityOfFacts facts)
          with productFamilies := families } := rfl
  simp only [hinit, foldDense_families]
  rfl

/-- Product-family storage does not alter any primitive table lookup. -/
theorem compiledLookups_agree (ast : ModelAST)
    (bounded : explicitModelWellBounded ast) :
    FactTables.sparseLookups ast.worldCount ast.thingCount (compileExplicitModelAST ast) =
      FactTables.denseLookups ast.worldCount ast.thingCount (compileExplicitModelAST ast) := by
  have correspondence := explicitCompilationTableCorrespondence ast bounded
  simp only [compileExplicitModelAST, foldFamilies_eq, withDenseFacts_families,
    FactTables.sparseLookups, FactTables.denseLookups]
  congr 1
  · funext field x w
    exact correspondence.unary field x w
  · funext field x y w
    exact correspondence.binary field x y w
  · funext field x y z w
    exact correspondence.ternary field x y z w
  · funext p slot w
    exact correspondence.projection p slot w

/-- Bounded explicit facts produce a model with proved native/kernel agreement. -/
def compileVerifiedModel (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) : FiniteModel4 :=
  (compileExplicitModelAST ast).toFiniteModel4Verified
    ast.worldCount ast.thingCount worldPositive thingPositive (compiledLookups_agree ast bounded)

theorem compileVerifiedModel_eq (ast : ModelAST)
    (worldPositive : 0 < ast.worldCount) (thingPositive : 0 < ast.thingCount)
    (bounded : explicitModelWellBounded ast) :
    compileVerifiedModel ast worldPositive thingPositive bounded =
      compileExplicitModel ast worldPositive thingPositive := rfl

end LeanUfo.UFO.DSL
