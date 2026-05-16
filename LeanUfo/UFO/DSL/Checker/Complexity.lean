import LeanUfo.UFO.DSL.Checker.Soundness

/-!
# Step bounds for reflective checkers

These bounds are deliberately conservative.  They are formal statements about
the abstract `Stepped` checker interface, not claims about wall-clock runtime or
Lean kernel checking.  Later phases can refine individual axiom step counts
without changing the public theorem shape.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

/--
Size measure used for one-variable polynomial statements about the reflective
checker.

This is an abstract finite-model size, not a byte size or runtime measurement:
it counts the product of the generated thing and world domains, with `+ 1`
offsets to keep the bound nonzero for degenerate finite domains. Primitive table
lookups and Boolean operations are accounted for by the separate `Stepped`
interface.
-/
def modelSize (M : FiniteModel4) : Nat :=
  (M.thingCount + 1) * (M.worldCount + 1)

theorem checkAx7_S_value (M : FiniteModel4) :
    (checkAx7_S M).value = checkAx7 M :=
  rfl

theorem checkAx1_S_value (M : FiniteModel4) :
    (checkAx1_S M).value = checkAx1 M :=
  rfl

theorem checkAx2_S_value (M : FiniteModel4) :
    (checkAx2_S M).value = checkAx2 M :=
  rfl

theorem checkAx3_S_value (M : FiniteModel4) :
    (checkAx3_S M).value = checkAx3 M :=
  rfl

theorem checkAx4_S_value (M : FiniteModel4) :
    (checkAx4_S M).value = checkAx4 M :=
  rfl

theorem checkAx5_S_value (M : FiniteModel4) :
    (checkAx5_S M).value = checkAx5 M :=
  rfl

theorem checkAx6_S_value (M : FiniteModel4) :
    (checkAx6_S M).value = checkAx6 M :=
  rfl

theorem checkAx13_S_value (M : FiniteModel4) :
    (checkAx13_S M).value = checkAx13 M :=
  rfl

theorem checkAx8_S_value (M : FiniteModel4) :
    (checkAx8_S M).value = checkAx8 M :=
  rfl

theorem checkAx9_S_value (M : FiniteModel4) :
    (checkAx9_S M).value = checkAx9 M :=
  rfl

theorem checkAx10_S_value (M : FiniteModel4) :
    (checkAx10_S M).value = checkAx10 M :=
  rfl

theorem checkAx11_S_value (M : FiniteModel4) :
    (checkAx11_S M).value = checkAx11 M :=
  rfl

theorem checkAx12_S_value (M : FiniteModel4) :
    (checkAx12_S M).value = checkAx12 M :=
  rfl

theorem checkAx14_S_value (M : FiniteModel4) :
    (checkAx14_S M).value = checkAx14 M :=
  rfl

theorem checkAx15_S_value (M : FiniteModel4) :
    (checkAx15_S M).value = checkAx15 M :=
  rfl

theorem checkAx16_S_value (M : FiniteModel4) :
    (checkAx16_S M).value = checkAx16 M :=
  rfl

theorem checkAx17_S_value (M : FiniteModel4) :
    (checkAx17_S M).value = checkAx17 M :=
  rfl

theorem checkAx18_S_value (M : FiniteModel4) :
    (checkAx18_S M).value = checkAx18 M :=
  rfl

theorem checkAx19_S_value (M : FiniteModel4) :
    (checkAx19_S M).value = checkAx19 M :=
  rfl

theorem checkAx20_S_value (M : FiniteModel4) :
    (checkAx20_S M).value = checkAx20 M :=
  rfl

theorem checkAx21_S_value (M : FiniteModel4) :
    (checkAx21_S M).value = checkAx21 M :=
  rfl

theorem checkAx22_S_value (M : FiniteModel4) :
    (checkAx22_S M).value = checkAx22 M :=
  rfl

theorem checkAx23_S_value (M : FiniteModel4) :
    (checkAx23_S M).value = checkAx23 M :=
  rfl

theorem checkAx34_S_value (M : FiniteModel4) :
    (checkAx34_S M).value = checkAx34 M :=
  rfl

theorem checkAx35_S_value (M : FiniteModel4) :
    (checkAx35_S M).value = checkAx35 M :=
  rfl

theorem checkAx36_S_value (M : FiniteModel4) :
    (checkAx36_S M).value = checkAx36 M :=
  rfl

theorem checkAx37_S_value (M : FiniteModel4) :
    (checkAx37_S M).value = checkAx37 M :=
  rfl

theorem checkAx38_S_value (M : FiniteModel4) :
    (checkAx38_S M).value = checkAx38 M :=
  rfl

theorem checkAx39_S_value (M : FiniteModel4) :
    (checkAx39_S M).value = checkAx39 M :=
  rfl

theorem checkAx40_S_value (M : FiniteModel4) :
    (checkAx40_S M).value = checkAx40 M :=
  rfl

theorem checkAx41_S_value (M : FiniteModel4) :
    (checkAx41_S M).value = checkAx41 M :=
  rfl

theorem checkAx42_S_value (M : FiniteModel4) :
    (checkAx42_S M).value = checkAx42 M :=
  rfl

theorem checkAx43_S_value (M : FiniteModel4) :
    (checkAx43_S M).value = checkAx43 M :=
  rfl

theorem checkAx44_S_value (M : FiniteModel4) :
    (checkAx44_S M).value = checkAx44 M :=
  rfl

theorem checkAx45_S_value (M : FiniteModel4) :
    (checkAx45_S M).value = checkAx45 M :=
  rfl

theorem checkAx46_S_value (M : FiniteModel4) :
    (checkAx46_S M).value = checkAx46 M :=
  rfl

theorem checkAx47_S_value (M : FiniteModel4) :
    (checkAx47_S M).value = checkAx47 M :=
  rfl

theorem checkAx48_S_value (M : FiniteModel4) :
    (checkAx48_S M).value = checkAx48 M :=
  rfl

theorem checkAx49_S_value (M : FiniteModel4) :
    (checkAx49_S M).value = checkAx49 M :=
  rfl

theorem checkAx50_S_value (M : FiniteModel4) :
    (checkAx50_S M).value = checkAx50 M :=
  rfl

theorem checkAx51_S_value (M : FiniteModel4) :
    (checkAx51_S M).value = checkAx51 M :=
  rfl

theorem checkAx52_S_value (M : FiniteModel4) :
    (checkAx52_S M).value = checkAx52 M :=
  rfl

theorem checkAx53_S_value (M : FiniteModel4) :
    (checkAx53_S M).value = checkAx53 M :=
  rfl

theorem checkAx54_S_value (M : FiniteModel4) :
    (checkAx54_S M).value = checkAx54 M :=
  rfl

theorem checkAx55_S_value (M : FiniteModel4) :
    (checkAx55_S M).value = checkAx55 M :=
  rfl

theorem checkAx56_S_value (M : FiniteModel4) :
    (checkAx56_S M).value = checkAx56 M :=
  rfl

theorem checkAx57_S_value (M : FiniteModel4) :
    (checkAx57_S M).value = checkAx57 M :=
  rfl

theorem checkAx58_S_value (M : FiniteModel4) :
    (checkAx58_S M).value = checkAx58 M :=
  rfl

theorem checkAx59_S_value (M : FiniteModel4) :
    (checkAx59_S M).value = checkAx59 M :=
  rfl

theorem checkAx60_S_value (M : FiniteModel4) :
    (checkAx60_S M).value = checkAx60 M :=
  rfl

theorem checkAx62_S_value (M : FiniteModel4) :
    (checkAx62_S M).value = checkAx62 M :=
  rfl

theorem checkAx63_S_value (M : FiniteModel4) :
    (checkAx63_S M).value = checkAx63 M :=
  rfl

theorem checkAx64_S_value (M : FiniteModel4) :
    (checkAx64_S M).value = checkAx64 M :=
  rfl

theorem checkAx65_S_value (M : FiniteModel4) :
    (checkAx65_S M).value = checkAx65 M :=
  rfl

theorem checkAx66_S_value (M : FiniteModel4) :
    (checkAx66_S M).value = checkAx66 M :=
  rfl

theorem checkAx67_S_value (M : FiniteModel4) :
    (checkAx67_S M).value = checkAx67 M :=
  rfl

theorem checkAx68_S_value (M : FiniteModel4) :
    (checkAx68_S M).value = checkAx68 M :=
  rfl

theorem checkAx69_S_value (M : FiniteModel4) :
    (checkAx69_S M).value = checkAx69 M :=
  rfl

theorem checkAx70_S_value (M : FiniteModel4) :
    (checkAx70_S M).value = checkAx70 M :=
  rfl

theorem checkAx61_S_value (M : FiniteModel4) :
    (checkAx61_S M).value = checkAx61 M :=
  rfl

theorem checkAx71_S_value (M : FiniteModel4) :
    (checkAx71_S M).value = checkAx71 M :=
  rfl

theorem checkAx72_S_value (M : FiniteModel4) :
    (checkAx72_S M).value = checkAx72 M :=
  rfl

theorem checkAx73_S_value (M : FiniteModel4) :
    (checkAx73_S M).value = checkAx73 M :=
  rfl

theorem checkAx74_S_value (M : FiniteModel4) :
    (checkAx74_S M).value = checkAx74 M :=
  rfl

theorem checkAx75_S_value (M : FiniteModel4) :
    (checkAx75_S M).value = checkAx75 M :=
  rfl

theorem checkAx76_S_value (M : FiniteModel4) :
    (checkAx76_S M).value = checkAx76 M :=
  rfl

theorem checkAx77_S_value (M : FiniteModel4) :
    (checkAx77_S M).value = checkAx77 M :=
  rfl

theorem checkAx78_S_value (M : FiniteModel4) :
    (checkAx78_S M).value = checkAx78 M :=
  rfl

theorem checkAx79_S_value (M : FiniteModel4) :
    (checkAx79_S M).value = checkAx79 M :=
  rfl

theorem checkAx80_S_value (M : FiniteModel4) :
    (checkAx80_S M).value = checkAx80 M :=
  rfl

theorem checkAxQuaIndividualOfEndurant_S_value (M : FiniteModel4) :
    (checkAxQuaIndividualOfEndurant_S M).value = checkAxQuaIndividualOfEndurant M :=
  rfl

theorem checkAx81_S_value (M : FiniteModel4) :
    (checkAx81_S M).value = checkAx81 M :=
  rfl

theorem checkAx82_S_value (M : FiniteModel4) :
    (checkAx82_S M).value = checkAx82 M :=
  rfl

theorem checkAx83_S_value (M : FiniteModel4) :
    (checkAx83_S M).value = checkAx83 M :=
  rfl

theorem checkAx84_S_value (M : FiniteModel4) :
    (checkAx84_S M).value = checkAx84 M :=
  rfl

theorem checkAx85_S_value (M : FiniteModel4) :
    (checkAx85_S M).value = checkAx85 M :=
  rfl

theorem checkAx86_S_value (M : FiniteModel4) :
    (checkAx86_S M).value = checkAx86 M :=
  rfl

theorem checkAx87_S_value (M : FiniteModel4) :
    (checkAx87_S M).value = checkAx87 M :=
  rfl

theorem checkAx88_S_value (M : FiniteModel4) :
    (checkAx88_S M).value = checkAx88 M :=
  rfl

theorem checkAx89_S_value (M : FiniteModel4) :
    (checkAx89_S M).value = checkAx89 M :=
  rfl

theorem checkAx90_S_value (M : FiniteModel4) :
    (checkAx90_S M).value = checkAx90 M :=
  rfl

theorem checkAx91_S_value (M : FiniteModel4) :
    (checkAx91_S M).value = checkAx91 M :=
  rfl

theorem checkAx92_S_value (M : FiniteModel4) :
    (checkAx92_S M).value = checkAx92 M :=
  rfl

theorem checkAx93_S_value (M : FiniteModel4) :
    (checkAx93_S M).value = checkAx93 M :=
  rfl

theorem checkAx94_S_value (M : FiniteModel4) :
    (checkAx94_S M).value = checkAx94 M :=
  rfl

theorem checkAx95_S_value (M : FiniteModel4) :
    (checkAx95_S M).value = checkAx95 M :=
  rfl

theorem checkAx96_S_value (M : FiniteModel4) :
    (checkAx96_S M).value = checkAx96 M :=
  rfl

theorem checkAx97_S_value (M : FiniteModel4) :
    (checkAx97_S M).value = checkAx97 M :=
  rfl

theorem checkAx98_S_value (M : FiniteModel4) :
    (checkAx98_S M).value = checkAx98 M :=
  rfl

theorem checkAx99_S_value (M : FiniteModel4) :
    (checkAx99_S M).value = checkAx99 M :=
  rfl

theorem checkAx100_S_value (M : FiniteModel4) :
    (checkAx100_S M).value = checkAx100 M :=
  rfl

theorem checkAx101_S_value (M : FiniteModel4) :
    (checkAx101_S M).value = checkAx101 M :=
  rfl

theorem checkAxDistanceIdentity_S_value (M : FiniteModel4) :
    (checkAxDistanceIdentity_S M).value = checkAxDistanceIdentity M :=
  rfl

theorem checkAxDistanceSymmetry_S_value (M : FiniteModel4) :
    (checkAxDistanceSymmetry_S M).value = checkAxDistanceSymmetry M :=
  rfl

theorem checkAxDistanceTriangle_S_value (M : FiniteModel4) :
    (checkAxDistanceTriangle_S M).value = checkAxDistanceTriangle M :=
  rfl

theorem checkAx102_S_value (M : FiniteModel4) :
    (checkAx102_S M).value = checkAx102 M :=
  rfl

theorem checkAx103_S_value (M : FiniteModel4) :
    (checkAx103_S M).value = checkAx103 M :=
  rfl

theorem checkAx104_S_value (M : FiniteModel4) :
    (checkAx104_S M).value = checkAx104 M :=
  rfl

theorem checkAx105_S_value (M : FiniteModel4) :
    (checkAx105_S M).value = checkAx105 M :=
  rfl

theorem checkAx106_S_value (M : FiniteModel4) :
    (checkAx106_S M).value = checkAx106 M :=
  rfl

theorem checkAx107_S_value (M : FiniteModel4) :
    (checkAx107_S M).value = checkAx107 M :=
  rfl

theorem checkAx108_S_value (M : FiniteModel4) :
    (checkAx108_S M).value = checkAx108 M :=
  rfl

theorem checkAx7_steps_bound (M : FiniteModel4) :
    (checkAx7_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx1_steps_bound (M : FiniteModel4) :
    (checkAx1_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx2_steps_bound (M : FiniteModel4) :
    (checkAx2_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx3_steps_bound (M : FiniteModel4) :
    (checkAx3_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx4_steps_bound (M : FiniteModel4) :
    (checkAx4_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx5_steps_bound (M : FiniteModel4) :
    (checkAx5_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx6_steps_bound (M : FiniteModel4) :
    (checkAx6_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx13_steps_bound (M : FiniteModel4) :
    (checkAx13_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx8_steps_bound (M : FiniteModel4) :
    (checkAx8_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx9_steps_bound (M : FiniteModel4) :
    (checkAx9_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx10_steps_bound (M : FiniteModel4) :
    (checkAx10_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx11_steps_bound (M : FiniteModel4) :
    (checkAx11_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx12_steps_bound (M : FiniteModel4) :
    (checkAx12_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx14_steps_bound (M : FiniteModel4) :
    (checkAx14_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx15_steps_bound (M : FiniteModel4) :
    (checkAx15_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx16_steps_bound (M : FiniteModel4) :
    (checkAx16_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx17_steps_bound (M : FiniteModel4) :
    (checkAx17_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx18_steps_bound (M : FiniteModel4) :
    (checkAx18_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx19_steps_bound (M : FiniteModel4) :
    (checkAx19_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx20_steps_bound (M : FiniteModel4) :
    (checkAx20_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx21_steps_bound (M : FiniteModel4) :
    (checkAx21_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx22_steps_bound (M : FiniteModel4) :
    (checkAx22_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx23_steps_bound (M : FiniteModel4) :
    (checkAx23_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx34_steps_bound (M : FiniteModel4) :
    (checkAx34_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx35_steps_bound (M : FiniteModel4) :
    (checkAx35_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx36_steps_bound (M : FiniteModel4) :
    (checkAx36_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx37_steps_bound (M : FiniteModel4) :
    (checkAx37_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx38_steps_bound (M : FiniteModel4) :
    (checkAx38_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx39_steps_bound (M : FiniteModel4) :
    (checkAx39_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx40_steps_bound (M : FiniteModel4) :
    (checkAx40_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx41_steps_bound (M : FiniteModel4) :
    (checkAx41_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx42_steps_bound (M : FiniteModel4) :
    (checkAx42_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx43_steps_bound (M : FiniteModel4) :
    (checkAx43_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx44_steps_bound (M : FiniteModel4) :
    (checkAx44_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx45_steps_bound (M : FiniteModel4) :
    (checkAx45_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx46_steps_bound (M : FiniteModel4) :
    (checkAx46_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx47_steps_bound (M : FiniteModel4) :
    (checkAx47_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx48_steps_bound (M : FiniteModel4) :
    (checkAx48_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx49_steps_bound (M : FiniteModel4) :
    (checkAx49_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx50_steps_bound (M : FiniteModel4) :
    (checkAx50_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx51_steps_bound (M : FiniteModel4) :
    (checkAx51_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx52_steps_bound (M : FiniteModel4) :
    (checkAx52_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx53_steps_bound (M : FiniteModel4) :
    (checkAx53_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx54_steps_bound (M : FiniteModel4) :
    (checkAx54_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx55_steps_bound (M : FiniteModel4) :
    (checkAx55_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx56_steps_bound (M : FiniteModel4) :
    (checkAx56_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx57_steps_bound (M : FiniteModel4) :
    (checkAx57_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx58_steps_bound (M : FiniteModel4) :
    (checkAx58_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx59_steps_bound (M : FiniteModel4) :
    (checkAx59_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx60_steps_bound (M : FiniteModel4) :
    (checkAx60_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx62_steps_bound (M : FiniteModel4) :
    (checkAx62_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx63_steps_bound (M : FiniteModel4) :
    (checkAx63_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx64_steps_bound (M : FiniteModel4) :
    (checkAx64_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx65_steps_bound (M : FiniteModel4) :
    (checkAx65_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx66_steps_bound (M : FiniteModel4) :
    (checkAx66_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx67_steps_bound (M : FiniteModel4) :
    (checkAx67_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx68_steps_bound (M : FiniteModel4) :
    (checkAx68_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx69_steps_bound (M : FiniteModel4) :
    (checkAx69_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx70_steps_bound (M : FiniteModel4) :
    (checkAx70_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx61_steps_bound (M : FiniteModel4) :
    (checkAx61_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx71_steps_bound (M : FiniteModel4) :
    (checkAx71_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx72_steps_bound (M : FiniteModel4) :
    (checkAx72_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx73_steps_bound (M : FiniteModel4) :
    (checkAx73_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx74_steps_bound (M : FiniteModel4) :
    (checkAx74_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx75_steps_bound (M : FiniteModel4) :
    (checkAx75_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx76_steps_bound (M : FiniteModel4) :
    (checkAx76_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx77_steps_bound (M : FiniteModel4) :
    (checkAx77_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx78_steps_bound (M : FiniteModel4) :
    (checkAx78_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx79_steps_bound (M : FiniteModel4) :
    (checkAx79_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx80_steps_bound (M : FiniteModel4) :
    (checkAx80_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAxQuaIndividualOfEndurant_steps_bound (M : FiniteModel4) :
    (checkAxQuaIndividualOfEndurant_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx81_steps_bound (M : FiniteModel4) :
    (checkAx81_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx82_steps_bound (M : FiniteModel4) :
    (checkAx82_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx83_steps_bound (M : FiniteModel4) :
    (checkAx83_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx84_steps_bound (M : FiniteModel4) :
    (checkAx84_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx85_steps_bound (M : FiniteModel4) :
    (checkAx85_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx86_steps_bound (M : FiniteModel4) :
    (checkAx86_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx87_steps_bound (M : FiniteModel4) :
    (checkAx87_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx88_steps_bound (M : FiniteModel4) :
    (checkAx88_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx89_steps_bound (M : FiniteModel4) :
    (checkAx89_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx90_steps_bound (M : FiniteModel4) :
    (checkAx90_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx91_steps_bound (M : FiniteModel4) :
    (checkAx91_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx92_steps_bound (M : FiniteModel4) :
    (checkAx92_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx93_steps_bound (M : FiniteModel4) :
    (checkAx93_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx94_steps_bound (M : FiniteModel4) :
    (checkAx94_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx95_steps_bound (M : FiniteModel4) :
    (checkAx95_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx96_steps_bound (M : FiniteModel4) :
    (checkAx96_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx97_steps_bound (M : FiniteModel4) :
    (checkAx97_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx98_steps_bound (M : FiniteModel4) :
    (checkAx98_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx99_steps_bound (M : FiniteModel4) :
    (checkAx99_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx100_steps_bound (M : FiniteModel4) :
    (checkAx100_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx101_steps_bound (M : FiniteModel4) :
    (checkAx101_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAxDistanceIdentity_steps_bound (M : FiniteModel4) :
    (checkAxDistanceIdentity_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAxDistanceSymmetry_steps_bound (M : FiniteModel4) :
    (checkAxDistanceSymmetry_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAxDistanceTriangle_steps_bound (M : FiniteModel4) :
    (checkAxDistanceTriangle_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx102_steps_bound (M : FiniteModel4) :
    (checkAx102_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx103_steps_bound (M : FiniteModel4) :
    (checkAx103_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx104_steps_bound (M : FiniteModel4) :
    (checkAx104_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx105_steps_bound (M : FiniteModel4) :
    (checkAx105_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx106_steps_bound (M : FiniteModel4) :
    (checkAx106_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx107_steps_bound (M : FiniteModel4) :
    (checkAx107_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAx108_steps_bound (M : FiniteModel4) :
    (checkAx108_S M).steps ≤ Stepped.polyEnvelope M :=
  Nat.le_refl _

theorem checkAxiomsPilot_S_value (M : FiniteModel4) :
    (checkAxiomsPilot_S M).value = checkAxiomsPilot M := by
  rfl

theorem checkAxiomsPilot_steps_bound (M : FiniteModel4) :
    (checkAxiomsPilot_S M).steps ≤ 89 * Stepped.polyEnvelope M + 88 := by
  rfl

theorem finite_checker_pilot_polynomial_bound :
    ∃ C a b,
      ∀ M : FiniteModel4,
        (checkAxiomsPilot_S M).steps ≤
          C * (M.thingCount + 1) ^ a * (M.worldCount + 1) ^ b + 88 := by
  refine ⟨89, 4, 2, ?_⟩
  intro M
  simpa [Stepped.polyEnvelope, Nat.mul_assoc] using checkAxiomsPilot_steps_bound M

theorem checkAxioms4_S_value (M : FiniteModel4) :
    (checkAxioms4_S M).value = checkAxioms4 M := by
  rfl

theorem checkAxioms4_steps_bound (M : FiniteModel4) :
    (checkAxioms4_S M).steps ≤ 116 * Stepped.polyEnvelope M + 115 := by
  rfl

theorem finite_checker_polynomial_bound :
    ∃ C a b,
      ∀ M : FiniteModel4,
        (checkAxioms4_S M).steps ≤
          C * (M.thingCount + 1) ^ a * (M.worldCount + 1) ^ b + 115 := by
  refine ⟨116, 4, 2, ?_⟩
  intro M
  simpa [Stepped.polyEnvelope, Nat.mul_assoc] using checkAxioms4_steps_bound M

theorem polyEnvelope_le_modelSize_pow_six (M : FiniteModel4) :
    Stepped.polyEnvelope M ≤ modelSize M ^ 6 := by
  unfold Stepped.polyEnvelope modelSize
  have hThing :
      (M.thingCount + 1) ^ 4 ≤ (M.thingCount + 1) ^ 6 :=
    Nat.pow_le_pow_right (Nat.succ_pos M.thingCount) (by decide)
  have hWorld :
      (M.worldCount + 1) ^ 2 ≤ (M.worldCount + 1) ^ 6 :=
    Nat.pow_le_pow_right (Nat.succ_pos M.worldCount) (by decide)
  calc
    (M.thingCount + 1) ^ 4 * (M.worldCount + 1) ^ 2
        ≤ (M.thingCount + 1) ^ 6 * (M.worldCount + 1) ^ 6 :=
      Nat.mul_le_mul hThing hWorld
    _ = ((M.thingCount + 1) * (M.worldCount + 1)) ^ 6 := by
      rw [Nat.mul_pow]

/--
One-variable polynomial step bound for the full reflective checker.

The theorem packages the two-dimensional bound in terms of `modelSize`, the
abstract number of generated thing/world positions. It is deliberately
conservative: it proves polynomial growth of checker-level `Stepped` work, not a
tight asymptotic bound and not a wall-clock runtime statement.
-/
theorem checkAxioms4_steps_polynomial_in_modelSize :
    ∃ C d k,
      ∀ M : FiniteModel4,
        (checkAxioms4_S M).steps ≤ C * (modelSize M) ^ d + k := by
  refine ⟨116, 6, 115, ?_⟩
  intro M
  calc
    (checkAxioms4_S M).steps ≤ 116 * Stepped.polyEnvelope M + 115 :=
      checkAxioms4_steps_bound M
    _ ≤ 116 * (modelSize M) ^ 6 + 115 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 116 (polyEnvelope_le_modelSize_pow_six M)) 115

end Checker
end LeanUfo.UFO.DSL
