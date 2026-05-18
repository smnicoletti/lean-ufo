import LeanUfo.UFO.DSL.Checker.Axioms

/-!
# Step bounds for reflective checkers

These bounds are deliberately conservative. They are formal statements about
the abstract `Stepped` checker interface, not claims about wall-clock runtime or
Lean kernel checking.

The step-envelope interpretation is syntactic and auditable: visible scans over
`Fin M.thingCount` contribute thing factors, visible scans over
`Fin M.worldCount` contribute world factors, and primitive table lookups/Boolean
connectives are treated as constant work. Axioms whose checkers hide finite
search behind `decide`, reachability, product-family witnesses, or derived
helpers remain on the global envelope until those helpers receive their own
expanded justification. This prevents the polynomial statement from depending
on unexplained exponent choices.

The final polynomial statement uses `checkerInputSize` below, not only
`modelSize`: product-family witness arrays are independent input data and must
be counted explicitly even though most models leave that table empty.

The single global fallback envelope is
`Stepped.globalStepEnvelope = (thingCount + 1)^8 * (worldCount + 1)^4`. The thing
exponent `8` dominates the largest direct thing scan currently exposed by the
checker, including the seven thing variables in distance triangle, with one
degree of slack for helper composition. The world exponent `4` is a deliberate
upper-bound allowance for modal/helper expansion. Product-family witness arrays
are accounted for separately by `checkerInputSize`.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

/--
Thing/world size component used in the one-variable polynomial statement.

This is an abstract finite-model size, not a byte size or wall-clock runtime
measurement: it counts generated thing/world positions with `+ 1` offsets and
is one summand of `checkerInputSize`.
-/
def modelSize (M : FiniteModel4) : Nat :=
  (M.thingCount + 1) * (M.worldCount + 1)

/--
Input footprint contributed by product-family witnesses.

Each witness contributes one slot plus both stored arrays. The arrays are
included because axiom 99 scans the product-family table and then scans witness
dimensions/types through `allProductFamilyIndices`/`anyProductFamilyIndices`.
-/
def productFamilyFootprint (M : FiniteModel4) : Nat :=
  M.productFamilies.foldl
    (fun size pf => size + 1 + pf.dimensionThings.size + pf.typeThings.size) 0

/--
Size measure for the checker input.

This extends `modelSize` with product-family witness data. It is still abstract:
primitive Boolean tables are treated extensionally through their indexed lookup
interfaces, while witness arrays are counted because their lengths are not
determined by `thingCount` and `worldCount`.
-/
def checkerInputSize (M : FiniteModel4) : Nat :=
  modelSize M + productFamilyFootprint M + 1

theorem modelSize_le_checkerInputSize (M : FiniteModel4) :
    modelSize M ≤ checkerInputSize M := by
  unfold checkerInputSize
  exact Nat.le_add_right (modelSize M) (productFamilyFootprint M + 1)

theorem checkAxioms4_S_value (M : FiniteModel4) :
    (checkAxioms4_S M).value = checkAxioms4 M := by
  rfl

theorem checkAxioms4_steps_bound (M : FiniteModel4) :
    (checkAxioms4_S M).steps ≤ 116 * Stepped.globalStepEnvelope M + 115 := by
  rfl

theorem globalStepEnvelope_le_modelSize_pow_twelve (M : FiniteModel4) :
    Stepped.globalStepEnvelope M ≤ modelSize M ^ 12 := by
  unfold Stepped.globalStepEnvelope Stepped.stepEnvelope modelSize
  have hThing :
      (M.thingCount + 1) ^ 8 ≤ (M.thingCount + 1) ^ 12 :=
    Nat.pow_le_pow_right (Nat.succ_pos M.thingCount) (by decide)
  have hWorld :
      (M.worldCount + 1) ^ 4 ≤ (M.worldCount + 1) ^ 12 :=
    Nat.pow_le_pow_right (Nat.succ_pos M.worldCount) (by decide)
  calc
    (M.thingCount + 1) ^ 8 * (M.worldCount + 1) ^ 4
        ≤ (M.thingCount + 1) ^ 12 * (M.worldCount + 1) ^ 12 :=
      Nat.mul_le_mul hThing hWorld
    _ = ((M.thingCount + 1) * (M.worldCount + 1)) ^ 12 := by
      rw [Nat.mul_pow]

theorem globalStepEnvelope_le_checkerInputSize_pow_twelve (M : FiniteModel4) :
    Stepped.globalStepEnvelope M ≤ checkerInputSize M ^ 12 := by
  calc
    Stepped.globalStepEnvelope M ≤ modelSize M ^ 12 :=
      globalStepEnvelope_le_modelSize_pow_twelve M
    _ ≤ checkerInputSize M ^ 12 :=
      Nat.pow_le_pow_left (modelSize_le_checkerInputSize M) 12

/--
One-variable polynomial step bound for the full reflective checker annotation.

This bound is stated over `checkerInputSize`, which includes product-family
witness data, and the deliberately conservative `globalStepEnvelope`.

The existential witnesses have the usual polynomial-bound meaning:
* `C` is the leading constant multiplying the size polynomial.
* `d` is the degree in the one-variable size measure `checkerInputSize`.
* `k` is an additive constant for fixed checker overhead.

For the current aggregate checker we instantiate these witnesses as `C = 116`,
`d = 12`, and `k = 115`. The degree `12` comes from bounding
`(thingCount + 1)^8 * (worldCount + 1)^4` by
`((thingCount + 1) * (worldCount + 1))^12`, then using
`modelSize ≤ checkerInputSize`. It is intentionally conservative and should not
be read as a tight syntactic loop-depth result.
-/
theorem checkAxioms4_steps_polynomial_in_checkerInputSize :
    ∃ C d k,
      ∀ M : FiniteModel4,
        (checkAxioms4_S M).steps ≤ C * (checkerInputSize M) ^ d + k := by
  refine ⟨116, 12, 115, ?_⟩
  intro M
  calc
    (checkAxioms4_S M).steps ≤ 116 * Stepped.globalStepEnvelope M + 115 :=
      checkAxioms4_steps_bound M
    _ ≤ 116 * (checkerInputSize M) ^ 12 + 115 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 116 (globalStepEnvelope_le_checkerInputSize_pow_twelve M)) 115

end Checker
end LeanUfo.UFO.DSL
