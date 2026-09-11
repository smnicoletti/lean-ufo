import LeanUfo.UFO.DSL.Compiler

/-!
# Product-family conversion regressions

Exact counts distinguish skipped fields from continued array traversal.
The output cases cover order, duplicate retention, malformed families, and the
production finite-model field. Native evaluation is used only for these tests.
-/

namespace LeanUfo.Test.Complexity.ProductFamilyConversion

open LeanUfo.UFO.DSL
open FactTables
open private natArrayToFinArrayCosted from LeanUfo.UFO.DSL.Compiler.ProductFamilies

private def family : ProductFamilySpec := ⟨0, 1, #[0], #[1]⟩

-- Empty-array initialization costs one. Valid elements cost seven each.
example : (natArrayToFinArrayCosted 2 #[]).cost = 1 := by native_decide
example : (natArrayToFinArrayCosted 2 #[0, 1]).cost = 15 := by native_decide
-- After the first failure, the last element costs only the traversal/read
-- pair and accumulator test. Its coordinate is no longer validated.
example : (natArrayToFinArrayCosted 2 #[2, 0]).cost = 10 := by native_decide
example : (natArrayToFinArrayCosted 2 #[0, 2]).cost = 14 := by native_decide

example : (productFamilyWitnessesCosted 2 2 #[]).cost = 1 := by native_decide
example : (productFamilyWitnessesCosted 0 2 #[family]).cost = 3 := by native_decide
example : (productFamilyWitnessesCosted 1 2 #[family]).cost = 37 := by native_decide
example : (productFamilyWitnessesCosted 2 2 #[family]).cost = 71 := by native_decide
example : (productFamilyWitnessesCosted 1 2 #[⟨0, 1, #[], #[]⟩]).cost = 23 := by native_decide

-- A failed field must not pay for the fields to its right.
example : (productFamilyWitnessesCosted 1 2 #[{ family with domain := 2 }]).cost = 7 := by
  native_decide
example : (productFamilyWitnessesCosted 1 2 #[{ family with qualityType := 2 }]).cost = 10 := by
  native_decide
example : (productFamilyWitnessesCosted 1 2 #[{ family with dimensionThings := #[2] }]).cost = 21 := by
  native_decide
example : (productFamilyWitnessesCosted 1 2 #[{ family with typeThings := #[2] }]).cost = 30 := by
  native_decide
example : (productFamilyWitnessesCosted 1 2 #[{ family with typeThings := #[] }]).cost = 28 := by
  native_decide

example :
    ((productFamilyWitnesses 2 2 #[family, { family with domain := 1 }, family]).map
      (fun witness => (witness.domain.val, witness.world.val))) =
        #[(0, 0), (0, 1), (1, 0), (1, 1), (0, 0), (0, 1)] := by
  native_decide

example :
    ((productFamilyWitnesses 2 2 #[{ family with dimensionThings := #[2] }, family]).map
      (fun witness => (witness.dimensionThings.map Fin.val, witness.typeThings.map Fin.val))) =
        #[(#[0], #[1]), (#[0], #[1])] := by
  native_decide

example : (productFamilyWitnesses 0 2 #[family]).isEmpty = true := by native_decide
example : (productFamilyWitnesses 1 0 #[family]).isEmpty = true := by native_decide

-- The field consumed by axiom 99 is the value of the counted converter.
example (W T : Nat) (worldPositive : 0 < W) (thingPositive : 0 < T)
    (tables : FactTables) (lookups : TableLookups W T) :
    (toFiniteModel4WithLookups W T worldPositive thingPositive tables lookups).productFamilies =
      (productFamilyWitnessesCosted W T tables.productFamilies).value := rfl

-- Model construction adds one lookup-bundle record and one model record.
-- With a supplied lookup bundle, only the model record remains to assemble.
example : (toFiniteModel4Costed 1 2 (by decide) (by decide) {}).cost = 3 := by
  native_decide

private def familyTables : FactTables := { productFamilies := #[family] }

example : (toFiniteModel4Costed 1 2 (by decide) (by decide) familyTables).cost = 39 := by
  native_decide
example : (toFiniteModel4Costed 2 2 (by decide) (by decide) familyTables).cost = 73 := by
  native_decide
example : (toFiniteModel4WithLookupsCosted 1 2 (by decide) (by decide) familyTables
    (sparseLookups 1 2 familyTables)).cost = 38 := by
  native_decide
example : (toFiniteModel4Costed 1 2 (by decide) (by decide)
    { productFamilies := #[{ family with domain := 2 }] }).cost = 9 := by
  native_decide

example (W T : Nat) (hw : 0 < W) (ht : 0 < T) (tables : FactTables) (agreement) :
    (toFiniteModel4VerifiedCosted W T hw ht tables agreement).cost =
      (toFiniteModel4Costed W T hw ht tables).cost := by
  rw [toFiniteModel4VerifiedCosted_eq]

example (W T : Nat) (hw : 0 < W) (ht : 0 < T) (tables : FactTables)
    (lookups : TableLookups W T) :
    (toFiniteModel4WithLookupsCosted W T hw ht tables lookups).value.inst =
      lookups.binary .inst := rfl

example :
    (toFiniteModel4 1 2 (by decide) (by decide) familyTables).part
      (0 : Fin 2) (0 : Fin 2) (0 : Fin 1) = true := rfl

example :
    (toFiniteModel4 1 2 (by decide) (by decide) familyTables).productFamilies.size = 1 := by
  native_decide

end LeanUfo.Test.Complexity.ProductFamilyConversion
