import LeanUfo.UFO.DSL.Checker.Axioms

/-!
# Soundness and completeness for checker-backed axioms

These theorems are the reusable proof boundary used by generated DSL
certificates.  A concrete model only has to evaluate the Boolean checker; the
semantic axiom proof follows from the corresponding theorem here.
-/

namespace LeanUfo.UFO.DSL
namespace Checker

private theorem checkAx1_correct (M : FiniteModel4) :
    checkAx1 M = true ↔ ax_a1 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx1 ax_a1 typeB iffB allThings allWorlds anyWorlds anyThings
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem, FiniteModel4.toS5Frame,
    Frame.Dia]

theorem checkAx1_sound (M : FiniteModel4) :
    checkAx1 M = true → ax_a1 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx1_correct M).1

theorem checkAx1_complete (M : FiniteModel4) :
    ax_a1 M.toUFOSignature4.toUFOSignature3_1 → checkAx1 M = true :=
  (checkAx1_correct M).2

theorem checkAx1_iff (M : FiniteModel4) :
    checkAx1 M = true ↔ ax_a1 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx1_correct M

private theorem checkAx2_correct (M : FiniteModel4) :
    checkAx2 M = true ↔ ax_a2 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx2 ax_a2 individualB iffB allThings allWorlds anyWorlds anyThings
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.individualSem,
    FiniteModel4.toS5Frame, Frame.Box]
  grind

theorem checkAx2_sound (M : FiniteModel4) :
    checkAx2 M = true → ax_a2 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx2_correct M).1

theorem checkAx2_complete (M : FiniteModel4) :
    ax_a2 M.toUFOSignature4.toUFOSignature3_1 → checkAx2 M = true :=
  (checkAx2_correct M).2

theorem checkAx2_iff (M : FiniteModel4) :
    checkAx2 M = true ↔ ax_a2 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx2_correct M

private theorem checkAx3_correct (M : FiniteModel4) :
    checkAx3 M = true ↔ ax_a3 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx3 ax_a3 typeB individualB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem,
    FiniteModel4.individualSem]
  grind

theorem checkAx3_sound (M : FiniteModel4) :
    checkAx3 M = true → ax_a3 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx3_correct M).1

theorem checkAx3_complete (M : FiniteModel4) :
    ax_a3 M.toUFOSignature4.toUFOSignature3_1 → checkAx3 M = true :=
  (checkAx3_correct M).2

theorem checkAx3_iff (M : FiniteModel4) :
    checkAx3 M = true ↔ ax_a3 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx3_correct M

private theorem checkAx4_correct (M : FiniteModel4) :
    checkAx4 M = true ↔ ax_a4 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx4 ax_a4 typeB allThings allWorlds anyWorlds anyThings
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem]
  grind

theorem checkAx4_sound (M : FiniteModel4) :
    checkAx4 M = true → ax_a4 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx4_correct M).1

theorem checkAx4_complete (M : FiniteModel4) :
    ax_a4 M.toUFOSignature4.toUFOSignature3_1 → checkAx4 M = true :=
  (checkAx4_correct M).2

theorem checkAx4_iff (M : FiniteModel4) :
    checkAx4 M = true ↔ ax_a4 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx4_correct M

private theorem checkAx5_correct (M : FiniteModel4) :
    checkAx5 M = true ↔ ax_a5 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx5 ax_a5 subDefB typeB iffB allThings allWorlds anyWorlds anyThings
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem, FiniteModel4.toS5Frame,
    Frame.Box]
  grind

theorem checkAx5_sound (M : FiniteModel4) :
    checkAx5 M = true → ax_a5 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx5_correct M).1

theorem checkAx5_complete (M : FiniteModel4) :
    ax_a5 M.toUFOSignature4.toUFOSignature3_1 → checkAx5 M = true :=
  (checkAx5_correct M).2

theorem checkAx5_iff (M : FiniteModel4) :
    checkAx5 M = true ↔ ax_a5 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx5_correct M

private theorem checkAx6_correct (M : FiniteModel4) :
    checkAx6 M = true ↔ ax_a6 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx6 ax_a6 allThings allWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx6_sound (M : FiniteModel4) :
    checkAx6 M = true → ax_a6 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx6_correct M).1

theorem checkAx6_complete (M : FiniteModel4) :
    ax_a6 M.toUFOSignature4.toUFOSignature3_1 → checkAx6 M = true :=
  (checkAx6_correct M).2

theorem checkAx6_iff (M : FiniteModel4) :
    checkAx6 M = true ↔ ax_a6 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx6_correct M

private theorem checkAx7_correct (M : FiniteModel4) :
    checkAx7 M = true ↔ ax_a7 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx7 ax_a7 individualB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.individualSem]
  grind

theorem checkAx7_sound (M : FiniteModel4) :
    checkAx7 M = true → ax_a7 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx7_correct M).1

theorem checkAx7_complete (M : FiniteModel4) :
    ax_a7 M.toUFOSignature4.toUFOSignature3_1 → checkAx7 M = true :=
  (checkAx7_correct M).2

theorem checkAx7_iff (M : FiniteModel4) :
    checkAx7 M = true ↔ ax_a7 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx7_correct M

private theorem checkAx8_correct (M : FiniteModel4) :
    checkAx8 M = true ↔ ax_a8 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx8 ax_a8 individualB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.individualSem]
  grind

theorem checkAx8_sound (M : FiniteModel4) :
    checkAx8 M = true → ax_a8 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx8_correct M).1

theorem checkAx8_complete (M : FiniteModel4) :
    ax_a8 M.toUFOSignature4.toUFOSignature3_1 → checkAx8 M = true :=
  (checkAx8_correct M).2

theorem checkAx8_iff (M : FiniteModel4) :
    checkAx8 M = true ↔ ax_a8 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx8_correct M

private theorem checkAx9_correct (M : FiniteModel4) :
    checkAx9 M = true ↔ ax_a9 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx9 ax_a9 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx9_sound (M : FiniteModel4) :
    checkAx9 M = true → ax_a9 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx9_correct M).1

theorem checkAx9_complete (M : FiniteModel4) :
    ax_a9 M.toUFOSignature4.toUFOSignature3_1 → checkAx9 M = true :=
  (checkAx9_correct M).2

theorem checkAx9_iff (M : FiniteModel4) :
    checkAx9 M = true ↔ ax_a9 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx9_correct M

private theorem checkAx10_correct (M : FiniteModel4) :
    checkAx10 M = true ↔ ax_a10 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx10 ax_a10 individualB iffB allThings allWorlds anyWorlds anyThings
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.individualSem]
  grind

theorem checkAx10_sound (M : FiniteModel4) :
    checkAx10 M = true → ax_a10 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx10_correct M).1

theorem checkAx10_complete (M : FiniteModel4) :
    ax_a10 M.toUFOSignature4.toUFOSignature3_1 → checkAx10 M = true :=
  (checkAx10_correct M).2

theorem checkAx10_iff (M : FiniteModel4) :
    checkAx10 M = true ↔ ax_a10 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx10_correct M

private theorem checkAx11_correct (M : FiniteModel4) :
    checkAx11 M = true ↔ ax_a11 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx11 ax_a11 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx11_sound (M : FiniteModel4) :
    checkAx11 M = true → ax_a11 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx11_correct M).1

theorem checkAx11_complete (M : FiniteModel4) :
    ax_a11 M.toUFOSignature4.toUFOSignature3_1 → checkAx11 M = true :=
  (checkAx11_correct M).2

theorem checkAx11_iff (M : FiniteModel4) :
    checkAx11 M = true ↔ ax_a11 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx11_correct M

private theorem checkAx12_correct (M : FiniteModel4) :
    checkAx12 M = true ↔ ax_a12 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx12 ax_a12 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx12_sound (M : FiniteModel4) :
    checkAx12 M = true → ax_a12 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx12_correct M).1

theorem checkAx12_complete (M : FiniteModel4) :
    ax_a12 M.toUFOSignature4.toUFOSignature3_1 → checkAx12 M = true :=
  (checkAx12_correct M).2

theorem checkAx12_iff (M : FiniteModel4) :
    checkAx12 M = true ↔ ax_a12 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx12_correct M

private theorem checkAx13_correct (M : FiniteModel4) :
    checkAx13 M = true ↔ ax_a13 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx13 ax_a13 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx13_sound (M : FiniteModel4) :
    checkAx13 M = true → ax_a13 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx13_correct M).1

theorem checkAx13_complete (M : FiniteModel4) :
    ax_a13 M.toUFOSignature4.toUFOSignature3_1 → checkAx13 M = true :=
  (checkAx13_correct M).2

theorem checkAx13_iff (M : FiniteModel4) :
    checkAx13 M = true ↔ ax_a13 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx13_correct M

private theorem checkAx14_correct (M : FiniteModel4) :
    checkAx14 M = true ↔ ax_a14 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx14 ax_a14 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx14_sound (M : FiniteModel4) :
    checkAx14 M = true → ax_a14 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx14_correct M).1

theorem checkAx14_complete (M : FiniteModel4) :
    ax_a14 M.toUFOSignature4.toUFOSignature3_1 → checkAx14 M = true :=
  (checkAx14_correct M).2

theorem checkAx14_iff (M : FiniteModel4) :
    checkAx14 M = true ↔ ax_a14 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx14_correct M

private theorem checkAx15_correct (M : FiniteModel4) :
    checkAx15 M = true ↔ ax_a15 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx15 ax_a15 typeB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem]
  grind

theorem checkAx15_sound (M : FiniteModel4) :
    checkAx15 M = true → ax_a15 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx15_correct M).1

theorem checkAx15_complete (M : FiniteModel4) :
    ax_a15 M.toUFOSignature4.toUFOSignature3_1 → checkAx15 M = true :=
  (checkAx15_correct M).2

theorem checkAx15_iff (M : FiniteModel4) :
    checkAx15 M = true ↔ ax_a15 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx15_correct M

private theorem checkAx16_correct (M : FiniteModel4) :
    checkAx16 M = true ↔ ax_a16 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx16 ax_a16 typeB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem]
  grind

theorem checkAx16_sound (M : FiniteModel4) :
    checkAx16 M = true → ax_a16 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx16_correct M).1

theorem checkAx16_complete (M : FiniteModel4) :
    ax_a16 M.toUFOSignature4.toUFOSignature3_1 → checkAx16 M = true :=
  (checkAx16_correct M).2

theorem checkAx16_iff (M : FiniteModel4) :
    checkAx16 M = true ↔ ax_a16 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx16_correct M

private theorem checkAx17_correct (M : FiniteModel4) :
    checkAx17 M = true ↔ ax_a17 M.toUFOSignature4.toUFOSignature3_1 := by
  unfold checkAx17 ax_a17 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx17_sound (M : FiniteModel4) :
    checkAx17 M = true → ax_a17 M.toUFOSignature4.toUFOSignature3_1 :=
  (checkAx17_correct M).1

theorem checkAx17_complete (M : FiniteModel4) :
    ax_a17 M.toUFOSignature4.toUFOSignature3_1 → checkAx17 M = true :=
  (checkAx17_correct M).2

theorem checkAx17_iff (M : FiniteModel4) :
    checkAx17 M = true ↔ ax_a17 M.toUFOSignature4.toUFOSignature3_1 :=
  checkAx17_correct M

private theorem checkAx18_correct (M : FiniteModel4) :
    checkAx18 M = true ↔ ax_a18 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx18 ax_a18 iffB allThings allWorlds anyWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Dia, Frame.Box]
  grind

theorem checkAx18_sound (M : FiniteModel4) :
    checkAx18 M = true → ax_a18 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx18_correct M).1

theorem checkAx18_complete (M : FiniteModel4) :
    ax_a18 M.toUFOSignature4.toUFOSignature3_2 → checkAx18 M = true :=
  (checkAx18_correct M).2

theorem checkAx18_iff (M : FiniteModel4) :
    checkAx18 M = true ↔ ax_a18 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx18_correct M

private theorem checkAx19_correct (M : FiniteModel4) :
    checkAx19 M = true ↔ ax_a19 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx19 ax_a19 iffB allThings allWorlds anyWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Dia]
  grind

theorem checkAx19_sound (M : FiniteModel4) :
    checkAx19 M = true → ax_a19 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx19_correct M).1

theorem checkAx19_complete (M : FiniteModel4) :
    ax_a19 M.toUFOSignature4.toUFOSignature3_2 → checkAx19 M = true :=
  (checkAx19_correct M).2

theorem checkAx19_iff (M : FiniteModel4) :
    checkAx19 M = true ↔ ax_a19 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx19_correct M

private theorem checkAx20_correct (M : FiniteModel4) :
    checkAx20 M = true ↔ ax_a20 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx20 ax_a20 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx20_sound (M : FiniteModel4) :
    checkAx20 M = true → ax_a20 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx20_correct M).1

theorem checkAx20_complete (M : FiniteModel4) :
    ax_a20 M.toUFOSignature4.toUFOSignature3_2 → checkAx20 M = true :=
  (checkAx20_correct M).2

theorem checkAx20_iff (M : FiniteModel4) :
    checkAx20 M = true ↔ ax_a20 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx20_correct M

private theorem checkAx21_correct (M : FiniteModel4) :
    checkAx21 M = true ↔ ax_a21 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx21 ax_a21 allThings allWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]
  grind

theorem checkAx21_sound (M : FiniteModel4) :
    checkAx21 M = true → ax_a21 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx21_correct M).1

theorem checkAx21_complete (M : FiniteModel4) :
    ax_a21 M.toUFOSignature4.toUFOSignature3_2 → checkAx21 M = true :=
  (checkAx21_correct M).2

theorem checkAx21_iff (M : FiniteModel4) :
    checkAx21 M = true ↔ ax_a21 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx21_correct M

private theorem checkAx22_correct (M : FiniteModel4) :
    checkAx22 M = true ↔ ax_a22 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx22 ax_a22 allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Dia]
  grind

theorem checkAx22_sound (M : FiniteModel4) :
    checkAx22 M = true → ax_a22 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx22_correct M).1

theorem checkAx22_complete (M : FiniteModel4) :
    ax_a22 M.toUFOSignature4.toUFOSignature3_2 → checkAx22 M = true :=
  (checkAx22_correct M).2

theorem checkAx22_iff (M : FiniteModel4) :
    checkAx22 M = true ↔ ax_a22 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx22_correct M

private theorem checkAx23_correct (M : FiniteModel4) :
    checkAx23 M = true ↔ ax_a23 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx23 ax_a23 iffB allThings allWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]
  grind

theorem checkAx23_sound (M : FiniteModel4) :
    checkAx23 M = true → ax_a23 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx23_correct M).1

theorem checkAx23_complete (M : FiniteModel4) :
    ax_a23 M.toUFOSignature4.toUFOSignature3_2 → checkAx23 M = true :=
  (checkAx23_correct M).2

theorem checkAx23_iff (M : FiniteModel4) :
    checkAx23 M = true ↔ ax_a23 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx23_correct M

private theorem checkAx24_correct (M : FiniteModel4) :
    checkAx24 M = true ↔ ax_a24 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx24 ax_a24 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx24_sound (M : FiniteModel4) :
    checkAx24 M = true → ax_a24 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx24_correct M).1

theorem checkAx24_complete (M : FiniteModel4) :
    ax_a24 M.toUFOSignature4.toUFOSignature3_2 → checkAx24 M = true :=
  (checkAx24_correct M).2

theorem checkAx24_iff (M : FiniteModel4) :
    checkAx24 M = true ↔ ax_a24 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx24_correct M

private theorem checkAx25_correct (M : FiniteModel4) :
    checkAx25 M = true ↔ ax_a25 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx25 ax_a25 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx25_sound (M : FiniteModel4) :
    checkAx25 M = true → ax_a25 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx25_correct M).1

theorem checkAx25_complete (M : FiniteModel4) :
    ax_a25 M.toUFOSignature4.toUFOSignature3_2 → checkAx25 M = true :=
  (checkAx25_correct M).2

theorem checkAx25_iff (M : FiniteModel4) :
    checkAx25 M = true ↔ ax_a25 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx25_correct M

private theorem checkAx26_correct (M : FiniteModel4) :
    checkAx26 M = true ↔ ax_a26 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx26 ax_a26 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx26_sound (M : FiniteModel4) :
    checkAx26 M = true → ax_a26 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx26_correct M).1

theorem checkAx26_complete (M : FiniteModel4) :
    ax_a26 M.toUFOSignature4.toUFOSignature3_2 → checkAx26 M = true :=
  (checkAx26_correct M).2

theorem checkAx26_iff (M : FiniteModel4) :
    checkAx26 M = true ↔ ax_a26 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx26_correct M

private theorem checkAx27_correct (M : FiniteModel4) :
    checkAx27 M = true ↔ ax_a27 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx27 ax_a27 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx27_sound (M : FiniteModel4) :
    checkAx27 M = true → ax_a27 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx27_correct M).1

theorem checkAx27_complete (M : FiniteModel4) :
    ax_a27 M.toUFOSignature4.toUFOSignature3_2 → checkAx27 M = true :=
  (checkAx27_correct M).2

theorem checkAx27_iff (M : FiniteModel4) :
    checkAx27 M = true ↔ ax_a27 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx27_correct M

private theorem checkAx28_correct (M : FiniteModel4) :
    checkAx28 M = true ↔ ax_a28 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx28 ax_a28 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx28_sound (M : FiniteModel4) :
    checkAx28 M = true → ax_a28 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx28_correct M).1

theorem checkAx28_complete (M : FiniteModel4) :
    ax_a28 M.toUFOSignature4.toUFOSignature3_2 → checkAx28 M = true :=
  (checkAx28_correct M).2

theorem checkAx28_iff (M : FiniteModel4) :
    checkAx28 M = true ↔ ax_a28 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx28_correct M

private theorem checkAx29_correct (M : FiniteModel4) :
    checkAx29 M = true ↔ ax_a29 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx29 ax_a29 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx29_sound (M : FiniteModel4) :
    checkAx29 M = true → ax_a29 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx29_correct M).1

theorem checkAx29_complete (M : FiniteModel4) :
    ax_a29 M.toUFOSignature4.toUFOSignature3_2 → checkAx29 M = true :=
  (checkAx29_correct M).2

theorem checkAx29_iff (M : FiniteModel4) :
    checkAx29 M = true ↔ ax_a29 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx29_correct M

private theorem checkAx30_correct (M : FiniteModel4) :
    checkAx30 M = true ↔ ax_a30 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx30 ax_a30 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx30_sound (M : FiniteModel4) :
    checkAx30 M = true → ax_a30 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx30_correct M).1

theorem checkAx30_complete (M : FiniteModel4) :
    ax_a30 M.toUFOSignature4.toUFOSignature3_2 → checkAx30 M = true :=
  (checkAx30_correct M).2

theorem checkAx30_iff (M : FiniteModel4) :
    checkAx30 M = true ↔ ax_a30 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx30_correct M

private theorem checkAx31_correct (M : FiniteModel4) :
    checkAx31 M = true ↔ ax_a31 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx31 ax_a31 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx31_sound (M : FiniteModel4) :
    checkAx31 M = true → ax_a31 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx31_correct M).1

theorem checkAx31_complete (M : FiniteModel4) :
    ax_a31 M.toUFOSignature4.toUFOSignature3_2 → checkAx31 M = true :=
  (checkAx31_correct M).2

theorem checkAx31_iff (M : FiniteModel4) :
    checkAx31 M = true ↔ ax_a31 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx31_correct M

private theorem checkAx32_correct (M : FiniteModel4) :
    checkAx32 M = true ↔ ax_a32 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx32 ax_a32 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx32_sound (M : FiniteModel4) :
    checkAx32 M = true → ax_a32 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx32_correct M).1

theorem checkAx32_complete (M : FiniteModel4) :
    ax_a32 M.toUFOSignature4.toUFOSignature3_2 → checkAx32 M = true :=
  (checkAx32_correct M).2

theorem checkAx32_iff (M : FiniteModel4) :
    checkAx32 M = true ↔ ax_a32 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx32_correct M

private theorem checkAx33_correct (M : FiniteModel4) :
    checkAx33 M = true ↔ ax_a33 M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAx33 ax_a33 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx33_sound (M : FiniteModel4) :
    checkAx33 M = true → ax_a33 M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAx33_correct M).1

theorem checkAx33_complete (M : FiniteModel4) :
    ax_a33 M.toUFOSignature4.toUFOSignature3_2 → checkAx33 M = true :=
  (checkAx33_correct M).2

theorem checkAx33_iff (M : FiniteModel4) :
    checkAx33 M = true ↔ ax_a33 M.toUFOSignature4.toUFOSignature3_2 :=
  checkAx33_correct M

private theorem checkAxInstEndurant_correct (M : FiniteModel4) :
    checkAxInstEndurant M = true ↔
      ax_instEndurant_of_EndurantType (Sig := M.toUFOSignature4.toUFOSignature3_2) := by
  unfold checkAxInstEndurant ax_instEndurant_of_EndurantType allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxInstEndurant_sound (M : FiniteModel4) :
    checkAxInstEndurant M = true →
      ax_instEndurant_of_EndurantType (Sig := M.toUFOSignature4.toUFOSignature3_2) :=
  (checkAxInstEndurant_correct M).1

theorem checkAxInstEndurant_complete (M : FiniteModel4) :
    ax_instEndurant_of_EndurantType (Sig := M.toUFOSignature4.toUFOSignature3_2) →
      checkAxInstEndurant M = true :=
  (checkAxInstEndurant_correct M).2

private theorem checkAxSubKindSortal_correct (M : FiniteModel4) :
    checkAxSubKindSortal M = true ↔
      ax_sub_of_kind_is_sortal (Sig := M.toUFOSignature4.toUFOSignature3_2) := by
  unfold checkAxSubKindSortal ax_sub_of_kind_is_sortal allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxSubKindSortal_sound (M : FiniteModel4) :
    checkAxSubKindSortal M = true →
      ax_sub_of_kind_is_sortal (Sig := M.toUFOSignature4.toUFOSignature3_2) :=
  (checkAxSubKindSortal_correct M).1

theorem checkAxSubKindSortal_complete (M : FiniteModel4) :
    ax_sub_of_kind_is_sortal (Sig := M.toUFOSignature4.toUFOSignature3_2) →
      checkAxSubKindSortal M = true :=
  (checkAxSubKindSortal_correct M).2

private theorem checkAxNonSortalUp_correct (M : FiniteModel4) :
    checkAxNonSortalUp M = true ↔
      ax_nonSortal_upward (Sig := M.toUFOSignature4.toUFOSignature3_2) := by
  unfold checkAxNonSortalUp ax_nonSortal_upward allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxNonSortalUp_sound (M : FiniteModel4) :
    checkAxNonSortalUp M = true →
      ax_nonSortal_upward (Sig := M.toUFOSignature4.toUFOSignature3_2) :=
  (checkAxNonSortalUp_correct M).1

theorem checkAxNonSortalUp_complete (M : FiniteModel4) :
    ax_nonSortal_upward (Sig := M.toUFOSignature4.toUFOSignature3_2) →
      checkAxNonSortalUp M = true :=
  (checkAxNonSortalUp_correct M).2

private theorem checkAxKindStable_correct (M : FiniteModel4) :
    checkAxKindStable M = true ↔ ax_kindStable M.toUFOSignature4.toUFOSignature3_2 := by
  unfold checkAxKindStable ax_kindStable allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame]
  grind

theorem checkAxKindStable_sound (M : FiniteModel4) :
    checkAxKindStable M = true → ax_kindStable M.toUFOSignature4.toUFOSignature3_2 :=
  (checkAxKindStable_correct M).1

theorem checkAxKindStable_complete (M : FiniteModel4) :
    ax_kindStable M.toUFOSignature4.toUFOSignature3_2 → checkAxKindStable M = true :=
  (checkAxKindStable_correct M).2

private theorem qualityB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    qualityB M x w = true ↔ Quality M.toUFOSignature4.toUFOSignature3_3 x w := by
  unfold qualityB Quality
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]

private theorem checkAx34_correct (M : FiniteModel4) :
    checkAx34 M = true ↔ ax_a34 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx34 ax_a34 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx34_sound (M : FiniteModel4) :
    checkAx34 M = true → ax_a34 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx34_correct M).1

theorem checkAx34_complete (M : FiniteModel4) :
    ax_a34 M.toUFOSignature4.toUFOSignature3_3 → checkAx34 M = true :=
  (checkAx34_correct M).2

private theorem checkAx35_correct (M : FiniteModel4) :
    checkAx35 M = true ↔ ax_a35 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx35 ax_a35 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx35_sound (M : FiniteModel4) :
    checkAx35 M = true → ax_a35 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx35_correct M).1

theorem checkAx35_complete (M : FiniteModel4) :
    ax_a35 M.toUFOSignature4.toUFOSignature3_3 → checkAx35 M = true :=
  (checkAx35_correct M).2

private theorem checkAx36_correct (M : FiniteModel4) :
    checkAx36 M = true ↔ ax_a36 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx36 ax_a36 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx36_sound (M : FiniteModel4) :
    checkAx36 M = true → ax_a36 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx36_correct M).1

theorem checkAx36_complete (M : FiniteModel4) :
    ax_a36 M.toUFOSignature4.toUFOSignature3_3 → checkAx36 M = true :=
  (checkAx36_correct M).2

private theorem checkAx37_correct (M : FiniteModel4) :
    checkAx37 M = true ↔ ax_a37 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx37 ax_a37 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx37_sound (M : FiniteModel4) :
    checkAx37 M = true → ax_a37 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx37_correct M).1

theorem checkAx37_complete (M : FiniteModel4) :
    ax_a37 M.toUFOSignature4.toUFOSignature3_3 → checkAx37 M = true :=
  (checkAx37_correct M).2

private theorem checkAx38_correct (M : FiniteModel4) :
    checkAx38 M = true ↔ ax_a38 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx38 ax_a38 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx38_sound (M : FiniteModel4) :
    checkAx38 M = true → ax_a38 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx38_correct M).1

theorem checkAx38_complete (M : FiniteModel4) :
    ax_a38 M.toUFOSignature4.toUFOSignature3_3 → checkAx38 M = true :=
  (checkAx38_correct M).2

private theorem checkAx39_correct (M : FiniteModel4) :
    checkAx39 M = true ↔ ax_a39 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx39 ax_a39 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx39_sound (M : FiniteModel4) :
    checkAx39 M = true → ax_a39 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx39_correct M).1

theorem checkAx39_complete (M : FiniteModel4) :
    ax_a39 M.toUFOSignature4.toUFOSignature3_3 → checkAx39 M = true :=
  (checkAx39_correct M).2

private theorem checkAx40_correct (M : FiniteModel4) :
    checkAx40 M = true ↔ ax_a40 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx40 ax_a40 iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx40_sound (M : FiniteModel4) :
    checkAx40 M = true → ax_a40 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx40_correct M).1

theorem checkAx40_complete (M : FiniteModel4) :
    ax_a40 M.toUFOSignature4.toUFOSignature3_3 → checkAx40 M = true :=
  (checkAx40_correct M).2

private theorem checkAx41_correct (M : FiniteModel4) :
    checkAx41 M = true ↔ ax_a41 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx41 ax_a41 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx41_sound (M : FiniteModel4) :
    checkAx41 M = true → ax_a41 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx41_correct M).1

theorem checkAx41_complete (M : FiniteModel4) :
    ax_a41 M.toUFOSignature4.toUFOSignature3_3 → checkAx41 M = true :=
  (checkAx41_correct M).2

private theorem checkAx42_correct (M : FiniteModel4) :
    checkAx42 M = true ↔ ax_a42 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx42 ax_a42 iffB allThings allWorlds qualityB Quality
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]
  grind

theorem checkAx42_sound (M : FiniteModel4) :
    checkAx42 M = true → ax_a42 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx42_correct M).1

theorem checkAx42_complete (M : FiniteModel4) :
    ax_a42 M.toUFOSignature4.toUFOSignature3_3 → checkAx42 M = true :=
  (checkAx42_correct M).2

private theorem checkAx43_correct (M : FiniteModel4) :
    checkAx43 M = true ↔ ax_a43 M.toUFOSignature4.toUFOSignature3_3 := by
  unfold checkAx43 ax_a43 allThings allWorlds qualityB Quality
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]
  grind

theorem checkAx43_sound (M : FiniteModel4) :
    checkAx43 M = true → ax_a43 M.toUFOSignature4.toUFOSignature3_3 :=
  (checkAx43_correct M).1

theorem checkAx43_complete (M : FiniteModel4) :
    ax_a43 M.toUFOSignature4.toUFOSignature3_3 → checkAx43 M = true :=
  (checkAx43_correct M).2

private theorem typeByInstancesB_correct
    (M : FiniteModel4)
    (typePred leafPred : Fin M.thingCount → Fin M.worldCount → Bool) :
    typeByInstancesB M typePred leafPred = true ↔
      ∀ (t : Fin M.thingCount) (w : Fin M.worldCount),
        (typePred t w = true) ↔
          (M.toUFOSignature4.Type_ t w ∧
            Frame.Box (F := M.toUFOSignature4.F)
              (fun v => ∀ x : Fin M.thingCount,
                M.toUFOSignature4.Inst x t v → leafPred x v = true)
              w) := by
  unfold typeByInstancesB typeB iffB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem, FiniteModel4.toS5Frame,
    Frame.Box]
  grind

private theorem qualityTypeByInstancesB_correct (M : FiniteModel4) :
    typeByInstancesB M M.qualityType (qualityB M) = true ↔
      ax_a44_qualityType M.toUFOSignature4.toUFOSignature3_4 := by
  unfold typeByInstancesB ax_a44_qualityType typeB qualityB Quality iffB
    allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem, FiniteModel4.toS5Frame,
    Frame.Box, ExistsUnique]
  grind

private theorem checkAx44_correct (M : FiniteModel4) :
    checkAx44 M = true ↔ ax_a44 M.toUFOSignature4.toUFOSignature3_4 := by
  unfold checkAx44 ax_a44 ax_a44_endurantType ax_a44_perdurantType
    ax_a44_substantialType ax_a44_momentType ax_a44_objectType
    ax_a44_collectiveType ax_a44_quantityType ax_a44_relatorType
    ax_a44_modeType
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    exact
      ⟨(typeByInstancesB_correct M M.endurantType M.endurant).1 h.1.1.1.1.1.1.1.1.1,
       (typeByInstancesB_correct M M.perdurantType M.perdurant).1 h.1.1.1.1.1.1.1.1.2,
       (typeByInstancesB_correct M M.substantialType M.substantial).1 h.1.1.1.1.1.1.1.2,
       (typeByInstancesB_correct M M.momentType M.moment).1 h.1.1.1.1.1.1.2,
       (typeByInstancesB_correct M M.objectType M.object).1 h.1.1.1.1.1.2,
       (typeByInstancesB_correct M M.collectiveType M.collective).1 h.1.1.1.1.2,
       (typeByInstancesB_correct M M.quantityType M.quantity).1 h.1.1.1.2,
       (typeByInstancesB_correct M M.relatorType M.relator).1 h.1.1.2,
       (typeByInstancesB_correct M M.modeType M.mode).1 h.1.2,
       (qualityTypeByInstancesB_correct M).1 h.2⟩
  · intro h
    rcases h with
      ⟨hEnd, hPerd, hSub, hMom, hObj, hColl, hQuant, hRel, hMode, hQual⟩
    exact
      ⟨⟨⟨⟨⟨⟨⟨⟨⟨(typeByInstancesB_correct M M.endurantType M.endurant).2 hEnd,
        (typeByInstancesB_correct M M.perdurantType M.perdurant).2 hPerd⟩,
        (typeByInstancesB_correct M M.substantialType M.substantial).2 hSub⟩,
        (typeByInstancesB_correct M M.momentType M.moment).2 hMom⟩,
        (typeByInstancesB_correct M M.objectType M.object).2 hObj⟩,
        (typeByInstancesB_correct M M.collectiveType M.collective).2 hColl⟩,
        (typeByInstancesB_correct M M.quantityType M.quantity).2 hQuant⟩,
        (typeByInstancesB_correct M M.relatorType M.relator).2 hRel⟩,
        (typeByInstancesB_correct M M.modeType M.mode).2 hMode⟩,
        (qualityTypeByInstancesB_correct M).2 hQual⟩

theorem checkAx44_sound (M : FiniteModel4) :
    checkAx44 M = true → ax_a44 M.toUFOSignature4.toUFOSignature3_4 :=
  (checkAx44_correct M).1

theorem checkAx44_complete (M : FiniteModel4) :
    ax_a44 M.toUFOSignature4.toUFOSignature3_4 → checkAx44 M = true :=
  (checkAx44_correct M).2

private theorem checkAx45_correct (M : FiniteModel4) :
    checkAx45 M = true ↔ ax_a45 M.toUFOSignature4.toUFOSignature3_4 := by
  unfold checkAx45 ax_a45 ax_a45_objectKind ax_a45_collectiveKind
    ax_a45_quantityKind ax_a45_relatorKind ax_a45_modeKind ax_a45_qualityKind
    kindByTypeB iffB allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx45_sound (M : FiniteModel4) :
    checkAx45 M = true → ax_a45 M.toUFOSignature4.toUFOSignature3_4 :=
  (checkAx45_correct M).1

theorem checkAx45_complete (M : FiniteModel4) :
    ax_a45 M.toUFOSignature4.toUFOSignature3_4 → checkAx45 M = true :=
  (checkAx45_correct M).2

private theorem checkAx46_correct (M : FiniteModel4) :
    checkAx46 M = true ↔ ax_a46 M.toUFOSignature4.toUFOSignature3_4 := by
  unfold checkAx46 ax_a46 specificEndurantKindB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Dia]
  grind

theorem checkAx46_sound (M : FiniteModel4) :
    checkAx46 M = true → ax_a46 M.toUFOSignature4.toUFOSignature3_4 :=
  (checkAx46_correct M).1

theorem checkAx46_complete (M : FiniteModel4) :
    ax_a46 M.toUFOSignature4.toUFOSignature3_4 → checkAx46 M = true :=
  (checkAx46_correct M).2

private theorem checkAx47_correct (M : FiniteModel4) :
    checkAx47 M = true ↔ ax_a47 M.toUFOSignature4.toUFOSignature3_5 := by
  unfold checkAx47 ax_a47 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx47_sound (M : FiniteModel4) :
    checkAx47 M = true → ax_a47 M.toUFOSignature4.toUFOSignature3_5 :=
  (checkAx47_correct M).1

theorem checkAx47_complete (M : FiniteModel4) :
    ax_a47 M.toUFOSignature4.toUFOSignature3_5 → checkAx47 M = true :=
  (checkAx47_correct M).2

private theorem checkAx48_correct (M : FiniteModel4) :
    checkAx48 M = true ↔ ax_a48 M.toUFOSignature4.toUFOSignature3_5 := by
  unfold checkAx48 ax_a48 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx48_sound (M : FiniteModel4) :
    checkAx48 M = true → ax_a48 M.toUFOSignature4.toUFOSignature3_5 :=
  (checkAx48_correct M).1

theorem checkAx48_complete (M : FiniteModel4) :
    ax_a48 M.toUFOSignature4.toUFOSignature3_5 → checkAx48 M = true :=
  (checkAx48_correct M).2

private theorem checkAx49_correct (M : FiniteModel4) :
    checkAx49 M = true ↔ ax_a49 M.toUFOSignature4.toUFOSignature3_5 := by
  unfold checkAx49 ax_a49 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx49_sound (M : FiniteModel4) :
    checkAx49 M = true → ax_a49 M.toUFOSignature4.toUFOSignature3_5 :=
  (checkAx49_correct M).1

theorem checkAx49_complete (M : FiniteModel4) :
    ax_a49 M.toUFOSignature4.toUFOSignature3_5 → checkAx49 M = true :=
  (checkAx49_correct M).2

private theorem checkAx50_correct (M : FiniteModel4) :
    checkAx50 M = true ↔ ax_a50 M.toUFOSignature4.toUFOSignature3_5 := by
  unfold checkAx50 ax_a50 allThings allWorlds anyThings iffB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx50_sound (M : FiniteModel4) :
    checkAx50 M = true → ax_a50 M.toUFOSignature4.toUFOSignature3_5 :=
  (checkAx50_correct M).1

theorem checkAx50_complete (M : FiniteModel4) :
    ax_a50 M.toUFOSignature4.toUFOSignature3_5 → checkAx50 M = true :=
  (checkAx50_correct M).2

private theorem checkAx51_correct (M : FiniteModel4) :
    checkAx51 M = true ↔ ax_a51 M.toUFOSignature4.toUFOSignature3_5 := by
  unfold checkAx51 ax_a51 allThings allWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx51_sound (M : FiniteModel4) :
    checkAx51 M = true → ax_a51 M.toUFOSignature4.toUFOSignature3_5 :=
  (checkAx51_correct M).1

theorem checkAx51_complete (M : FiniteModel4) :
    ax_a51 M.toUFOSignature4.toUFOSignature3_5 → checkAx51 M = true :=
  (checkAx51_correct M).2

private theorem checkAx52_correct (M : FiniteModel4) :
    checkAx52 M = true ↔ ax_a52 M.toUFOSignature4.toUFOSignature3_5 := by
  unfold checkAx52 ax_a52 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx52_sound (M : FiniteModel4) :
    checkAx52 M = true → ax_a52 M.toUFOSignature4.toUFOSignature3_5 :=
  (checkAx52_correct M).1

theorem checkAx52_complete (M : FiniteModel4) :
    ax_a52 M.toUFOSignature4.toUFOSignature3_5 → checkAx52 M = true :=
  (checkAx52_correct M).2

private theorem genericFunctionalDependenceB_eq_true_iff
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    genericFunctionalDependenceB M x' y' w = true ↔
      M.toUFOSignature4.GenericFunctionalDependence x' y' w := by
  unfold genericFunctionalDependenceB
  simp [FiniteModel4.toUFOSignature4, allThings, anyThings, impliesB]
  grind

private theorem individualFunctionalDependenceB_eq_true_iff
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    individualFunctionalDependenceB M x x' y y' w = true ↔
      M.toUFOSignature4.IndividualFunctionalDependence x x' y y' w := by
  unfold individualFunctionalDependenceB
  simp [FiniteModel4.toUFOSignature4, genericFunctionalDependenceB_eq_true_iff, impliesB]
  grind

private theorem checkAx53_correct (M : FiniteModel4) :
    checkAx53 M = true ↔ ax_a53 M.toUFOSignature4.toUFOSignature3_6 := by
  unfold checkAx53 ax_a53 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx53_sound (M : FiniteModel4) :
    checkAx53 M = true → ax_a53 M.toUFOSignature4.toUFOSignature3_6 :=
  (checkAx53_correct M).1

theorem checkAx53_complete (M : FiniteModel4) :
    ax_a53 M.toUFOSignature4.toUFOSignature3_6 → checkAx53 M = true :=
  (checkAx53_correct M).2

private theorem checkAx54_correct (M : FiniteModel4) :
    checkAx54 M = true ↔ ax_a54 M.toUFOSignature4.toUFOSignature3_6 := by
  unfold checkAx54 ax_a54 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx54_sound (M : FiniteModel4) :
    checkAx54 M = true → ax_a54 M.toUFOSignature4.toUFOSignature3_6 :=
  (checkAx54_correct M).1

theorem checkAx54_complete (M : FiniteModel4) :
    ax_a54 M.toUFOSignature4.toUFOSignature3_6 → checkAx54 M = true :=
  (checkAx54_correct M).2

private theorem checkAx55_correct (M : FiniteModel4) :
    checkAx55 M = true ↔ ax_a55 M.toUFOSignature4.toUFOSignature3_6 := by
  unfold checkAx55 ax_a55 allThings allWorlds iffB individualFunctionalDependenceB
    genericFunctionalDependenceB anyThings impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx55_sound (M : FiniteModel4) :
    checkAx55 M = true → ax_a55 M.toUFOSignature4.toUFOSignature3_6 :=
  (checkAx55_correct M).1

theorem checkAx55_complete (M : FiniteModel4) :
    ax_a55 M.toUFOSignature4.toUFOSignature3_6 → checkAx55 M = true :=
  (checkAx55_correct M).2

private theorem checkAx56_correct (M : FiniteModel4) :
    checkAx56 M = true ↔ ax_a56 M.toUFOSignature4.toUFOSignature3_7 := by
  unfold checkAx56 ax_a56 allThings allWorlds iffB impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx56_sound (M : FiniteModel4) :
    checkAx56 M = true → ax_a56 M.toUFOSignature4.toUFOSignature3_7 :=
  (checkAx56_correct M).1

theorem checkAx56_complete (M : FiniteModel4) :
    ax_a56 M.toUFOSignature4.toUFOSignature3_7 → checkAx56 M = true :=
  (checkAx56_correct M).2

private theorem checkAx57_correct (M : FiniteModel4) :
    checkAx57 M = true ↔ ax_a57 M.toUFOSignature4.toUFOSignature3_7 := by
  unfold checkAx57 ax_a57 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx57_sound (M : FiniteModel4) :
    checkAx57 M = true → ax_a57 M.toUFOSignature4.toUFOSignature3_7 :=
  (checkAx57_correct M).1

theorem checkAx57_complete (M : FiniteModel4) :
    ax_a57 M.toUFOSignature4.toUFOSignature3_7 → checkAx57 M = true :=
  (checkAx57_correct M).2

private theorem genericConstitutionalDependenceB_eq_true_iff
    (M : FiniteModel4) (x' y' : Fin M.thingCount) (w : Fin M.worldCount) :
    genericConstitutionalDependenceB M x' y' w = true ↔
      M.toUFOSignature4.GenericConstitutionalDependence x' y' w := by
  unfold genericConstitutionalDependenceB
  simp [FiniteModel4.toUFOSignature4, allThings, anyThings, impliesB]
  grind

private theorem constitutionB_eq_true_iff
    (M : FiniteModel4)
    (x x' y y' : Fin M.thingCount) (w : Fin M.worldCount) :
    constitutionB M x x' y y' w = true ↔
      M.toUFOSignature4.Constitution x x' y y' w := by
  unfold constitutionB genericConstitutionalDependenceB
  simp [FiniteModel4.toUFOSignature4, allThings, anyThings, impliesB]
  grind

private theorem checkAx58_correct (M : FiniteModel4) :
    checkAx58 M = true ↔ ax_a58 M.toUFOSignature4.toUFOSignature3_7 := by
  unfold checkAx58 ax_a58 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx58_sound (M : FiniteModel4) :
    checkAx58 M = true → ax_a58 M.toUFOSignature4.toUFOSignature3_7 :=
  (checkAx58_correct M).1

theorem checkAx58_complete (M : FiniteModel4) :
    ax_a58 M.toUFOSignature4.toUFOSignature3_7 → checkAx58 M = true :=
  (checkAx58_correct M).2

private theorem checkAx59_correct (M : FiniteModel4) :
    checkAx59 M = true ↔ ax_a59 M.toUFOSignature4.toUFOSignature3_7 := by
  unfold checkAx59 ax_a59 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx59_sound (M : FiniteModel4) :
    checkAx59 M = true → ax_a59 M.toUFOSignature4.toUFOSignature3_7 :=
  (checkAx59_correct M).1

theorem checkAx59_complete (M : FiniteModel4) :
    ax_a59 M.toUFOSignature4.toUFOSignature3_7 → checkAx59 M = true :=
  (checkAx59_correct M).2

private theorem checkAx60_correct (M : FiniteModel4) :
    checkAx60 M = true ↔ ax_a60 M.toUFOSignature4.toUFOSignature3_7 := by
  unfold checkAx60 ax_a60 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]
  grind

theorem checkAx60_sound (M : FiniteModel4) :
    checkAx60 M = true → ax_a60 M.toUFOSignature4.toUFOSignature3_7 :=
  (checkAx60_correct M).1

theorem checkAx60_complete (M : FiniteModel4) :
    ax_a60 M.toUFOSignature4.toUFOSignature3_7 → checkAx60 M = true :=
  (checkAx60_correct M).2

private theorem checkAx61_correct (M : FiniteModel4) :
    checkAx61 M = true ↔ ax_a61 M.toUFOSignature4.toUFOSignature3_7 := by
  unfold checkAx61 ax_a61 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx61_sound (M : FiniteModel4) :
    checkAx61 M = true → ax_a61 M.toUFOSignature4.toUFOSignature3_7 :=
  (checkAx61_correct M).1

theorem checkAx61_complete (M : FiniteModel4) :
    ax_a61 M.toUFOSignature4.toUFOSignature3_7 → checkAx61 M = true :=
  (checkAx61_correct M).2

theorem checkAx61_iff (M : FiniteModel4) :
    checkAx61 M = true ↔ ax_a61 M.toUFOSignature4.toUFOSignature3_7 :=
  checkAx61_correct M

private theorem checkAx62_correct (M : FiniteModel4) :
    checkAx62 M = true ↔ ax_a62 M.toUFOSignature4.toUFOSignature3_8 := by
  unfold checkAx62 ax_a62 allThings allWorlds
  simp

theorem checkAx62_sound (M : FiniteModel4) :
    checkAx62 M = true → ax_a62 M.toUFOSignature4.toUFOSignature3_8 :=
  (checkAx62_correct M).1

theorem checkAx62_complete (M : FiniteModel4) :
    ax_a62 M.toUFOSignature4.toUFOSignature3_8 → checkAx62 M = true :=
  (checkAx62_correct M).2

private theorem checkAx63_correct (M : FiniteModel4) :
    checkAx63 M = true ↔ ax_a63 M.toUFOSignature4.toUFOSignature3_8 := by
  unfold checkAx63 ax_a63 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx63_sound (M : FiniteModel4) :
    checkAx63 M = true → ax_a63 M.toUFOSignature4.toUFOSignature3_8 :=
  (checkAx63_correct M).1

theorem checkAx63_complete (M : FiniteModel4) :
    ax_a63 M.toUFOSignature4.toUFOSignature3_8 → checkAx63 M = true :=
  (checkAx63_correct M).2

private theorem checkAx64_correct (M : FiniteModel4) :
    checkAx64 M = true ↔ ax_a64 M.toUFOSignature4.toUFOSignature3_8 := by
  unfold checkAx64 ax_a64 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx64_sound (M : FiniteModel4) :
    checkAx64 M = true → ax_a64 M.toUFOSignature4.toUFOSignature3_8 :=
  (checkAx64_correct M).1

theorem checkAx64_complete (M : FiniteModel4) :
    ax_a64 M.toUFOSignature4.toUFOSignature3_8 → checkAx64 M = true :=
  (checkAx64_correct M).2

private theorem existentialDependenceB_eq_true_iff
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    existentialDependenceB M x y w = true ↔
      M.toUFOSignature4.ExistentialDependence x y w := by
  unfold existentialDependenceB allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]
  grind

private theorem checkAx65_correct (M : FiniteModel4) :
    checkAx65 M = true ↔ ax_a65 M.toUFOSignature4.toUFOSignature3_9 := by
  unfold checkAx65 ax_a65 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, existentialDependenceB_eq_true_iff]
  grind

theorem checkAx65_sound (M : FiniteModel4) :
    checkAx65 M = true → ax_a65 M.toUFOSignature4.toUFOSignature3_9 :=
  (checkAx65_correct M).1

theorem checkAx65_complete (M : FiniteModel4) :
    ax_a65 M.toUFOSignature4.toUFOSignature3_9 → checkAx65 M = true :=
  (checkAx65_correct M).2

private theorem checkAx66_correct (M : FiniteModel4) :
    checkAx66 M = true ↔ ax_a66 M.toUFOSignature4.toUFOSignature3_9 := by
  unfold checkAx66 ax_a66 typeB allThings allWorlds anyWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.typeSem]
  grind

theorem checkAx66_sound (M : FiniteModel4) :
    checkAx66 M = true → ax_a66 M.toUFOSignature4.toUFOSignature3_9 :=
  (checkAx66_correct M).1

theorem checkAx66_complete (M : FiniteModel4) :
    ax_a66 M.toUFOSignature4.toUFOSignature3_9 → checkAx66 M = true :=
  (checkAx66_correct M).2

private theorem checkAx67_correct (M : FiniteModel4) :
    checkAx67 M = true ↔ ax_a67 M.toUFOSignature4.toUFOSignature3_9 := by
  unfold checkAx67 ax_a67 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx67_sound (M : FiniteModel4) :
    checkAx67 M = true → ax_a67 M.toUFOSignature4.toUFOSignature3_9 :=
  (checkAx67_correct M).1

theorem checkAx67_complete (M : FiniteModel4) :
    ax_a67 M.toUFOSignature4.toUFOSignature3_9 → checkAx67 M = true :=
  (checkAx67_correct M).2

private theorem terminalDirectBearerB_eq_true_iff
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    terminalDirectBearerB M m b w = true ↔
      M.toUFOSignature4.InheresIn m b w ∧
        ¬ M.toUFOSignature4.Moment b w ∧
        ∀ z : M.toUFOSignature4.Thing, ¬ M.toUFOSignature4.InheresIn b z w := by
  unfold terminalDirectBearerB
  simp [FiniteModel4.toUFOSignature4, allThings_eq_true_iff]
  grind

private theorem existsUniqueTerminalDirectBearerB_eq_true_iff
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueTerminalDirectBearerB M m w = true ↔
      ∃ b : M.toUFOSignature4.Thing,
        M.toUFOSignature4.InheresIn m b w ∧
          ¬ M.toUFOSignature4.Moment b w ∧
          (∀ z : M.toUFOSignature4.Thing, ¬ M.toUFOSignature4.InheresIn b z w) ∧
          ∀ z : M.toUFOSignature4.Thing, M.toUFOSignature4.InheresIn m z w → z = b := by
  unfold existsUniqueTerminalDirectBearerB
  simp [terminalDirectBearerB_eq_true_iff, FiniteModel4.toUFOSignature4]
  grind

private theorem reachableInheresInFuel_sound
    (M : FiniteModel4) (fuel : Nat)
    (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    reachableInheresInFuel M fuel m b w = true →
      MomentOf M.toUFOSignature4.toUFOSignature3_9 m b w := by
  induction fuel generalizing m with
  | zero =>
      intro h
      simp [reachableInheresInFuel] at h
  | succ fuel ih =>
      intro h
      unfold reachableInheresInFuel at h
      cases hDirect : M.inheresIn m b w
      · simp [hDirect] at h
        rcases (anyThings_eq_true_iff M _).1 h with ⟨y, hy⟩
        have hyPair :
            M.inheresIn m y w = true ∧ reachableInheresInFuel M fuel y b w = true := by
          simpa using hy
        rcases hyPair with ⟨hInh, hReach⟩
        exact MomentOf.step
          (by simpa [FiniteModel4.toUFOSignature4] using hInh)
          (ih y hReach)
      · exact MomentOf.direct (by simpa [FiniteModel4.toUFOSignature4] using hDirect)

private theorem momentOf_trans
    {Sig : UFOSignature3_9} {a b c : Sig.Thing} {w : Sig.F.World} :
    MomentOf Sig a b w → MomentOf Sig b c w → MomentOf Sig a c w := by
  intro hab hbc
  induction hab generalizing c with
  | direct hInh =>
      exact MomentOf.step hInh hbc
  | step hInh _ ih =>
      exact MomentOf.step hInh (ih hbc)

private theorem reachableInheresInVia_sound_of_ne
    (M : FiniteModel4) (pivots : List (Fin M.thingCount))
    (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    m ≠ b →
      reachableInheresInVia M pivots m b w = true →
        MomentOf M.toUFOSignature4.toUFOSignature3_9 m b w := by
  intro hne h
  induction pivots generalizing m b with
  | nil =>
      unfold reachableInheresInVia at h
      cases hEq : decide (m = b)
      · simp [hEq] at h
        exact MomentOf.direct (by simpa [FiniteModel4.toUFOSignature4] using h)
      · exact False.elim (hne (decide_eq_true_eq.mp hEq))
  | cons pivot pivots ih =>
      unfold reachableInheresInVia at h
      have hOr :
          reachableInheresInVia M pivots m b w = true ∨
            (reachableInheresInVia M pivots m pivot w = true ∧
              reachableInheresInVia M pivots pivot b w = true) := by
        cases hLeft : reachableInheresInVia M pivots m b w
        · simp [hLeft] at h
          exact Or.inr (by simpa using h)
        · exact Or.inl (by simp)
      rcases hOr with hDirect | hStep
      · exact ih m b hne hDirect
      · by_cases hmp : m = pivot
        · subst pivot
          exact ih m b hne hStep.2
        · by_cases hpb : pivot = b
          · subst b
            exact ih m pivot hmp hStep.1
          · exact momentOf_trans
              (ih m pivot hmp hStep.1)
              (ih pivot b hpb hStep.2)

private theorem reachableInheresInB_sound_of_ne
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    m ≠ b →
      reachableInheresInB M m b w = true →
        MomentOf M.toUFOSignature4.toUFOSignature3_9 m b w := by
  intro hne h
  exact reachableInheresInVia_sound_of_ne M (List.finRange M.thingCount) m b w hne h

private theorem reachableInheresInVia_direct
    (M : FiniteModel4) (pivots : List (Fin M.thingCount))
    (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    M.inheresIn m b w = true →
      reachableInheresInVia M pivots m b w = true := by
  intro h
  induction pivots with
  | nil =>
      simp [reachableInheresInVia, h]
  | cons pivot pivots ih =>
      unfold reachableInheresInVia
      simp [ih]

private theorem reachableInheresInVia_refl
    (M : FiniteModel4) (pivots : List (Fin M.thingCount))
    (x : Fin M.thingCount) (w : Fin M.worldCount) :
    reachableInheresInVia M pivots x x w = true := by
  induction pivots with
  | nil =>
      simp [reachableInheresInVia]
  | cons pivot pivots ih =>
      unfold reachableInheresInVia
      simp [ih]

private theorem reachableInheresInVia_comp_of_mem
    (M : FiniteModel4) {pivots : List (Fin M.thingCount)}
    {m pivot b : Fin M.thingCount} {w : Fin M.worldCount}
    (hp : pivot ∈ pivots) :
    reachableInheresInVia M pivots m pivot w = true →
      reachableInheresInVia M pivots pivot b w = true →
        reachableInheresInVia M pivots m b w = true := by
  induction pivots generalizing m b with
  | nil =>
      simp at hp
  | cons head pivots ih =>
      simp at hp
      intro hmp hpb
      unfold reachableInheresInVia at hmp hpb ⊢
      rcases hp with hp | hp
      · subst pivot
        have hmpTail : reachableInheresInVia M pivots m head w = true := by
          simpa [reachableInheresInVia, reachableInheresInVia_refl] using hmp
        have hpbTail : reachableInheresInVia M pivots head b w = true := by
          simpa [reachableInheresInVia, reachableInheresInVia_refl] using hpb
        simp [hmpTail, hpbTail]
      · have lift :
            ∀ {x y : Fin M.thingCount},
              reachableInheresInVia M pivots x y w = true →
                (reachableInheresInVia M pivots x y w ||
                  (reachableInheresInVia M pivots x head w &&
                    reachableInheresInVia M pivots head y w)) = true := by
            intro x y hxy
            simp [hxy]
        have compTail :
            ∀ {x y : Fin M.thingCount},
              reachableInheresInVia M pivots x pivot w = true →
                reachableInheresInVia M pivots pivot y w = true →
                  reachableInheresInVia M pivots x y w = true := by
            intro x y hx hy
            exact ih hp hx hy
        have parse :
            (reachableInheresInVia M pivots m pivot w = true ∨
              (reachableInheresInVia M pivots m head w = true ∧
                reachableInheresInVia M pivots head pivot w = true)) ∧
            (reachableInheresInVia M pivots pivot b w = true ∨
              (reachableInheresInVia M pivots pivot head w = true ∧
                reachableInheresInVia M pivots head b w = true)) := by
          constructor
          · cases hLeft : reachableInheresInVia M pivots m pivot w
            · simp [hLeft] at hmp
              exact Or.inr (by simpa using hmp)
            · exact Or.inl (by simp)
          · cases hLeft : reachableInheresInVia M pivots pivot b w
            · simp [hLeft] at hpb
              exact Or.inr (by simpa using hpb)
            · exact Or.inl (by simp)
        rcases parse with ⟨hm, hb⟩
        rcases hm with hmTail | ⟨hmHead, hHeadPivot⟩
        · rcases hb with hbTail | ⟨hPivotHead, hHeadB⟩
          · exact lift (compTail hmTail hbTail)
          · have hmHead' := compTail hmTail hPivotHead
            simp [hmHead', hHeadB]
        · rcases hb with hbTail | ⟨hPivotHead, hHeadB⟩
          · have hHeadB' := compTail hHeadPivot hbTail
            simp [hmHead, hHeadB']
          · simp [hmHead, hHeadB]

private theorem reachableInheresInB_direct
    (M : FiniteModel4) (m b : Fin M.thingCount) (w : Fin M.worldCount) :
    M.inheresIn m b w = true → reachableInheresInB M m b w = true := by
  intro h
  unfold reachableInheresInB
  exact reachableInheresInVia_direct M (List.finRange M.thingCount) m b w h

private theorem reachableInheresInB_comp
    (M : FiniteModel4) (m pivot b : Fin M.thingCount) (w : Fin M.worldCount) :
    reachableInheresInB M m pivot w = true →
      reachableInheresInB M pivot b w = true →
        reachableInheresInB M m b w = true := by
  unfold reachableInheresInB
  exact reachableInheresInVia_comp_of_mem M (List.mem_finRange pivot)

private theorem reachableInheresInB_complete
    (M : FiniteModel4) :
    ∀ {m b : Fin M.thingCount} {w : Fin M.worldCount},
      MomentOf M.toUFOSignature4.toUFOSignature3_9 m b w →
        reachableInheresInB M m b w = true
  | m, b, w, MomentOf.direct hInh =>
      reachableInheresInB_direct M m b w (by simpa [FiniteModel4.toUFOSignature4] using hInh)
  | m, b, w, @MomentOf.step _ _ y _ _ hInh hTail =>
      reachableInheresInB_comp M m y b w
        (reachableInheresInB_direct M m y w (by simpa [FiniteModel4.toUFOSignature4] using hInh))
        (reachableInheresInB_complete M hTail)

private theorem ultimateBearerOfB_sound
    (M : FiniteModel4) (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    M.moment m w = true →
    ultimateBearerOfB M b m w = true →
      UltimateBearerOf M.toUFOSignature4.toUFOSignature3_9 b m w := by
  unfold ultimateBearerOfB
  intro hm h
  have hpair : M.moment b w = false ∧ reachableInheresInB M m b w = true := by
    simpa using h
  rcases hpair with ⟨hNonMomentB, hReach⟩
  constructor
  · intro hm
    have hmB : M.moment b w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hm
    simp [hmB] at hNonMomentB
  · have hne : m ≠ b := by
      intro hEq
      subst hEq
      simp [hm] at hNonMomentB
    exact reachableInheresInB_sound_of_ne M m b w hne hReach

private theorem ultimateBearerOfB_complete
    (M : FiniteModel4) (b m : Fin M.thingCount) (w : Fin M.worldCount) :
    UltimateBearerOf M.toUFOSignature4.toUFOSignature3_9 b m w →
      ultimateBearerOfB M b m w = true := by
  intro h
  unfold ultimateBearerOfB
  have hbNonMoment : M.moment b w = false := by
    cases hb : M.moment b w
    · rfl
    · exact False.elim (h.1 (by simpa [FiniteModel4.toUFOSignature4] using hb))
  have hReach := reachableInheresInB_complete M h.2
  simp [hbNonMoment, hReach]

private theorem existsUniqueUltimateBearerB_eq_true_iff
    (M : FiniteModel4) (m : Fin M.thingCount) (w : Fin M.worldCount)
    (hm : M.moment m w = true) :
    existsUniqueUltimateBearerB M m w = true ↔
      ∃! b : M.toUFOSignature4.Thing,
        UltimateBearerOf M.toUFOSignature4.toUFOSignature3_9 b m w := by
  unfold existsUniqueUltimateBearerB
  rw [decide_eq_true_iff]
  constructor
  · intro h
    rcases h with ⟨b, hb, hUnique⟩
    refine ⟨b, ultimateBearerOfB_sound M b m w hm hb, ?_⟩
    intro y hy
    exact hUnique y (ultimateBearerOfB_complete M y m w hy)
  · intro h
    rcases h with ⟨b, hb, hUnique⟩
    refine ⟨b, ultimateBearerOfB_complete M b m w hb, ?_⟩
    intro y hy
    exact hUnique y (ultimateBearerOfB_sound M y m w hm hy)

theorem checkAx68_sound (M : FiniteModel4) :
    checkAx68 M = true → ax_a68 M.toUFOSignature4.toUFOSignature3_9 := by
  intro h m w hm
  unfold checkAx68 checkAx68Closure at h
  have hmAll := (allThings_eq_true_iff M _).1 h m
  have hw := (allWorlds_eq_true_iff M _).1 hmAll w
  unfold impliesB at hw
  have hmB : M.moment m w = true := by
    simpa [FiniteModel4.toUFOSignature4] using hm
  simp [hmB] at hw
  exact (existsUniqueUltimateBearerB_eq_true_iff M m w hmB).1 hw

theorem checkAx68_complete (M : FiniteModel4) :
    ax_a68 M.toUFOSignature4.toUFOSignature3_9 → checkAx68 M = true := by
  intro h
  unfold checkAx68 checkAx68Closure
  apply (allThings_eq_true_iff M _).2
  intro m
  apply (allWorlds_eq_true_iff M _).2
  intro w
  unfold impliesB
  cases hm : M.moment m w
  · simp
  · simp
    exact (existsUniqueUltimateBearerB_eq_true_iff M m w hm).2
      (h m w (by simpa [FiniteModel4.toUFOSignature4] using hm))

theorem checkAx68_correct (M : FiniteModel4) :
    checkAx68 M = true ↔ ax_a68 M.toUFOSignature4.toUFOSignature3_9 :=
  ⟨checkAx68_sound M, checkAx68_complete M⟩

private theorem externallyDependentModeB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    externallyDependentModeB M x w = true ↔
      M.toUFOSignature4.ExternallyDependentMode x w := by
  unfold externallyDependentModeB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]

private theorem externallyDependentB_eq_true_iff
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    externallyDependentB M x y w = true ↔
      M.toUFOSignature4.ExternallyDependent x y w := by
  unfold externallyDependentB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]

private theorem boxExImpB_eq_true_iff
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount) :
    boxExImpB M x y w = true ↔
      M.toUFOSignature4.ExistentialDependence x y w := by
  unfold boxExImpB
  simp [FiniteModel4.toUFOSignature4, FiniteModel4.toS5Frame, Frame.Box]

private theorem quaIndividualAny_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    (anyThings M fun y => M.quaIndividualOf x y w) = true ↔
      M.toUFOSignature4.QuaIndividual x w := by
  simp [FiniteModel4.toUFOSignature4, anyThings_eq_true_iff]

private theorem iffB_self_true (b : Bool) : iffB b b = true := by
  cases b <;> rfl

private theorem iffB_eq_true_iff (p q : Bool) :
    iffB p q = true ↔ (p = true ↔ q = true) := by
  cases p <;> cases q <;> simp [iffB]

private theorem existsUniqueFoundedByB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueFoundedByB M x w = true ↔
      ∃! y, M.toUFOSignature4.FoundedBy x y w := by
  unfold existsUniqueFoundedByB
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]

private theorem existsUniqueInstInheresB_eq_true_iff
    (M : FiniteModel4) (z t : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueInstInheresB M z t w = true ↔
      ∃! y, M.toUFOSignature4.Inst y t w ∧ M.toUFOSignature4.InheresIn z y w := by
  unfold existsUniqueInstInheresB
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]
  grind

private theorem sameFoundationB_eq_true_iff_of_unique
    (M : FiniteModel4) (x y : Fin M.thingCount) (w : Fin M.worldCount)
    (hx : ∃! u, M.toUFOSignature4.FoundedBy x u w)
    (hy : ∃! u, M.toUFOSignature4.FoundedBy y u w) :
    sameFoundationB M x y w = true ↔
      FoundationOf M.toUFOSignature4.toUFOSignature3_10 x w =
        FoundationOf M.toUFOSignature4.toUFOSignature3_10 y w := by
  constructor
  · intro h
    rcases (anyThings_eq_true_iff M _).1 h with ⟨u, hu⟩
    have hpair :
        M.foundedBy x u w = true ∧ M.foundedBy y u w = true := by
      simpa using hu
    rcases hpair with ⟨hxuB, hyuB⟩
    have hxu : M.toUFOSignature4.FoundedBy x u w := by
      simpa [FiniteModel4.toUFOSignature4] using hxuB
    have hyu : M.toUFOSignature4.FoundedBy y u w := by
      simpa [FiniteModel4.toUFOSignature4] using hyuB
    have hxEq :
        FoundationOf M.toUFOSignature4.toUFOSignature3_10 x w = u :=
      (foundationOf_eq_iff (Sig := M.toUFOSignature4.toUFOSignature3_10) hx).2 hxu
    have hyEq :
        FoundationOf M.toUFOSignature4.toUFOSignature3_10 y w = u :=
      (foundationOf_eq_iff (Sig := M.toUFOSignature4.toUFOSignature3_10) hy).2 hyu
    exact hxEq.trans hyEq.symm
  · intro hEq
    apply (anyThings_eq_true_iff M _).2
    refine ⟨FoundationOf M.toUFOSignature4.toUFOSignature3_10 x w, ?_⟩
    have hxFound :=
        (foundationOf_eq_iff (Sig := M.toUFOSignature4.toUFOSignature3_10) hx).1 rfl
    have hyFound :=
        (foundationOf_eq_iff (Sig := M.toUFOSignature4.toUFOSignature3_10) hy).1 hEq.symm
    have hxFoundB : M.foundedBy x (FoundationOf M.toUFOSignature4.toUFOSignature3_10 x w) w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hxFound
    have hyFoundB : M.foundedBy y (FoundationOf M.toUFOSignature4.toUFOSignature3_10 x w) w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hyFound
    simp [hxFoundB, hyFoundB]

private theorem checkAx69_correct (M : FiniteModel4) :
    checkAx69 M = true ↔ ax_a69 M.toUFOSignature4.toUFOSignature3_10 := by
  constructor
  · intro _ x y w
    simp [FiniteModel4.toUFOSignature4]
  · intro _
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allWorlds_eq_true_iff M _).2
    intro w
    exact iffB_self_true (externallyDependentB M x y w)

theorem checkAx69_sound (M : FiniteModel4) :
    checkAx69 M = true → ax_a69 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx69_correct M).1

theorem checkAx69_complete (M : FiniteModel4) :
    ax_a69 M.toUFOSignature4.toUFOSignature3_10 → checkAx69 M = true :=
  (checkAx69_correct M).2

theorem checkAx69_iff (M : FiniteModel4) :
    checkAx69 M = true ↔ ax_a69 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx69_correct M

private theorem checkAx70_correct (M : FiniteModel4) :
    checkAx70 M = true ↔ ax_a70 M.toUFOSignature4.toUFOSignature3_10 := by
  constructor
  · intro _ x w
    simp [FiniteModel4.toUFOSignature4]
  · intro _
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    exact iffB_self_true (externallyDependentModeB M x w)

theorem checkAx70_sound (M : FiniteModel4) :
    checkAx70 M = true → ax_a70 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx70_correct M).1

theorem checkAx70_complete (M : FiniteModel4) :
    ax_a70 M.toUFOSignature4.toUFOSignature3_10 → checkAx70 M = true :=
  (checkAx70_correct M).2

theorem checkAx70_iff (M : FiniteModel4) :
    checkAx70 M = true ↔ ax_a70 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx70_correct M

theorem checkAx71_sound (M : FiniteModel4) :
    checkAx71 M = true → ax_a71 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h x y w hf
  have hx := (allThings_eq_true_iff M _).1 h x
  have hy := (allThings_eq_true_iff M _).1 hx y
  have hw := (allWorlds_eq_true_iff M _).1 hy w
  unfold impliesB at hw
  have hfBool : M.foundedBy x y w = true := by
    simpa [FiniteModel4.toUFOSignature4] using hf
  simp [hfBool] at hw
  rcases hw with ⟨hLeft, hPerd⟩
  constructor
  · rcases hLeft with hEDM | hRelator
    · exact Or.inl ((externallyDependentModeB_eq_true_iff M x w).1 hEDM)
    · exact Or.inr (by simpa [FiniteModel4.toUFOSignature4] using hRelator)
  · simpa [FiniteModel4.toUFOSignature4] using hPerd

theorem checkAx71_complete (M : FiniteModel4) :
    ax_a71 M.toUFOSignature4.toUFOSignature3_10 → checkAx71 M = true := by
  intro h
  apply (allThings_eq_true_iff M _).2
  intro x
  apply (allThings_eq_true_iff M _).2
  intro y
  apply (allWorlds_eq_true_iff M _).2
  intro w
  unfold impliesB
  by_cases hf : M.foundedBy x y w = true
  · have hProp := h x y w (by simpa [FiniteModel4.toUFOSignature4] using hf)
    rcases hProp with ⟨hClass, hPerd⟩
    have hLeft : externallyDependentModeB M x w = true ∨ M.relator x w = true := by
      rcases hClass with hEDM | hRelator
      · exact Or.inl ((externallyDependentModeB_eq_true_iff M x w).2 hEDM)
      · have hRel : M.relator x w = true := by
          simpa [FiniteModel4.toUFOSignature4] using hRelator
        exact Or.inr hRel
    have hPerdBool : M.perdurant y w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hPerd
    cases hEDM : externallyDependentModeB M x w <;>
      cases hRel : M.relator x w <;>
      simp [hf, hEDM, hRel, hPerdBool] at hLeft ⊢
  · simp [hf]

theorem checkAx71_iff (M : FiniteModel4) :
    checkAx71 M = true ↔ ax_a71 M.toUFOSignature4.toUFOSignature3_10 :=
  ⟨checkAx71_sound M, checkAx71_complete M⟩

private theorem checkAx72_correct (M : FiniteModel4) :
    checkAx72 M = true ↔ ax_a72 M.toUFOSignature4.toUFOSignature3_10 := by
  constructor
  · intro h x w hEDM
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    unfold impliesB at hw
    have hEDMB := (externallyDependentModeB_eq_true_iff M x w).2 hEDM
    simp [hEDMB] at hw
    exact (existsUniqueFoundedByB_eq_true_iff M x w).1 hw
  · intro h
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hEDMB : externallyDependentModeB M x w = true
    · have hEDM := (externallyDependentModeB_eq_true_iff M x w).1 hEDMB
      have hUnique := (existsUniqueFoundedByB_eq_true_iff M x w).2 (h x w hEDM)
      simp [hEDMB, hUnique]
    · simp [hEDMB]

theorem checkAx72_sound (M : FiniteModel4) :
    checkAx72 M = true → ax_a72 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx72_correct M).1

theorem checkAx72_complete (M : FiniteModel4) :
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 → checkAx72 M = true :=
  (checkAx72_correct M).2

theorem checkAx72_iff (M : FiniteModel4) :
    checkAx72 M = true ↔ ax_a72 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx72_correct M

theorem checkAx73_sound_with_prereqs (M : FiniteModel4) :
    ax_a47 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a50 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 →
    checkAx73 M = true →
    ax_a73 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h47 h50 h72 h75 h x y w
  have hx := (allThings_eq_true_iff M _).1 h x
  have hy := (allThings_eq_true_iff M _).1 hx y
  have hw := (allWorlds_eq_true_iff M _).1 hy w
  have hQiff := (iffB_eq_true_iff _ _).1 hw
  constructor
  · intro hQ z
    have hAllZ := hQiff.1 (by simpa [FiniteModel4.toUFOSignature4] using hQ)
    have hz := (allThings_eq_true_iff M _).1 hAllZ z
    have hzIff := (iffB_eq_true_iff _ _).1 hz
    have hQI : M.toUFOSignature4.QuaIndividual x w := by
      exact ⟨y, hQ⟩
    have hEDMx := h75 x w hQI
    have hUniqueX := h72 x w hEDMx
    constructor
    · intro hOv
      have hOvB : M.overlap z x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hOv
      have rhsB := hzIff.1 hOvB
      have rhs :
          (externallyDependentModeB M z w = true ∧
            M.inheresIn z y w = true) ∧ sameFoundationB M z x w = true := by
        simpa using rhsB
      rcases rhs with ⟨⟨hEDMzB, hInhB⟩, hSameB⟩
      have hEDMz := (externallyDependentModeB_eq_true_iff M z w).1 hEDMzB
      have hUniqueZ := h72 z w hEDMz
      exact ⟨hEDMz, by simpa [FiniteModel4.toUFOSignature4] using hInhB,
        (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).1 hSameB⟩
    · intro rhs
      rcases rhs with ⟨hEDMz, hInh, hSame⟩
      have hUniqueZ := h72 z w hEDMz
      have hEDMzB := (externallyDependentModeB_eq_true_iff M z w).2 hEDMz
      have hInhB : M.inheresIn z y w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hInh
      have hSameB : sameFoundationB M z x w = true :=
        (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).2 hSame
      have rhsB :
          (externallyDependentModeB M z w && M.inheresIn z y w &&
              sameFoundationB M z x w) = true := by
        simp [hEDMzB, hInhB, hSameB]
      exact by
        have hOvB := hzIff.2 rhsB
        simpa [FiniteModel4.toUFOSignature4] using hOvB
  · intro hSem
    apply hQiff.2
    apply (allThings_eq_true_iff M _).2
    have hPartXX := h47 x w
    have hOvXX : M.toUFOSignature4.Overlap x x w :=
      (h50 x x w).2 ⟨x, hPartXX, hPartXX⟩
    have hEDMx := (hSem x).1 hOvXX |>.1
    have hUniqueX := h72 x w hEDMx
    intro z
    apply (iffB_eq_true_iff _ _).2
    constructor
    · intro hOvB
      have hOv : M.toUFOSignature4.Overlap z x w := by
        simpa [FiniteModel4.toUFOSignature4] using hOvB
      rcases (hSem z).1 hOv with ⟨hEDMz, hInh, hSame⟩
      have hUniqueZ := h72 z w hEDMz
      have hEDMzB := (externallyDependentModeB_eq_true_iff M z w).2 hEDMz
      have hInhB : M.inheresIn z y w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hInh
      have hSameB : sameFoundationB M z x w = true :=
        (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).2 hSame
      simp [hEDMzB, hInhB, hSameB]
    · intro rhsB
      have rhs :
          (externallyDependentModeB M z w = true ∧
            M.inheresIn z y w = true) ∧ sameFoundationB M z x w = true := by
        simpa using rhsB
      rcases rhs with ⟨⟨hEDMzB, hInhB⟩, hSameB⟩
      have hEDMz := (externallyDependentModeB_eq_true_iff M z w).1 hEDMzB
      have hUniqueZ := h72 z w hEDMz
      have hSame :=
        (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).1 hSameB
      have hOv := (hSem z).2
        ⟨hEDMz, by simpa [FiniteModel4.toUFOSignature4] using hInhB, hSame⟩
      simpa [FiniteModel4.toUFOSignature4] using hOv

private theorem checkAx74_correct (M : FiniteModel4) :
    checkAx74 M = true ↔ ax_a74 M.toUFOSignature4.toUFOSignature3_10 := by
  constructor
  · intro _ x w
    simp [FiniteModel4.toUFOSignature4]
  · intro _
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    exact iffB_self_true (anyThings M fun y => M.quaIndividualOf x y w)

theorem checkAx74_sound (M : FiniteModel4) :
    checkAx74 M = true → ax_a74 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx74_correct M).1

theorem checkAx74_complete (M : FiniteModel4) :
    ax_a74 M.toUFOSignature4.toUFOSignature3_10 → checkAx74 M = true :=
  (checkAx74_correct M).2

theorem checkAx74_iff (M : FiniteModel4) :
    checkAx74 M = true ↔ ax_a74 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx74_correct M

private theorem checkAx75_correct (M : FiniteModel4) :
    checkAx75 M = true ↔ ax_a75 M.toUFOSignature4.toUFOSignature3_10 := by
  constructor
  · intro h x w hq
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    unfold impliesB at hw
    have hAny : (anyThings M fun y => M.quaIndividualOf x y w) = true := by
      apply (anyThings_eq_true_iff M _).2
      simpa [FiniteModel4.toUFOSignature4] using hq
    simp [hAny] at hw
    exact (externallyDependentModeB_eq_true_iff M x w).1 hw
  · intro h
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hAny : (anyThings M fun y => M.quaIndividualOf x y w) = true
    · have hq : M.toUFOSignature4.QuaIndividual x w := by
        exact (anyThings_eq_true_iff M _).1 hAny
      have hEDM := (externallyDependentModeB_eq_true_iff M x w).2 (h x w hq)
      simp [hAny, hEDM]
    · simp [hAny]

theorem checkAx75_sound (M : FiniteModel4) :
    checkAx75 M = true → ax_a75 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx75_correct M).1

theorem checkAx75_complete (M : FiniteModel4) :
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 → checkAx75 M = true :=
  (checkAx75_correct M).2

theorem checkAx75_iff (M : FiniteModel4) :
    checkAx75 M = true ↔ ax_a75 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx75_correct M

theorem checkAx73_sound (M : FiniteModel4) :
    checkAx47 M = true →
    checkAx50 M = true →
    checkAx72 M = true →
    checkAx75 M = true →
    checkAx73 M = true →
    ax_a73 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h47 h50 h72 h75 h73
  exact checkAx73_sound_with_prereqs M
    (checkAx47_sound M h47)
    (checkAx50_sound M h50)
    (checkAx72_sound M h72)
    (checkAx75_sound M h75)
    h73

theorem checkAx73_complete_with_prereqs (M : FiniteModel4) :
    ax_a47 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a50 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a73 M.toUFOSignature4.toUFOSignature3_10 →
    checkAx73 M = true := by
  intro h47 h50 h72 h75 h73
  unfold checkAx73
  apply (allThings_eq_true_iff M _).2
  intro x
  apply (allThings_eq_true_iff M _).2
  intro y
  apply (allWorlds_eq_true_iff M _).2
  intro w
  apply (iffB_eq_true_iff _ _).2
  constructor
  · intro hQB
    apply (allThings_eq_true_iff M _).2
    intro z
    apply (iffB_eq_true_iff _ _).2
    constructor
    · intro hOvB
      have hQ : M.toUFOSignature4.QuaIndividualOf x y w := by
        simpa [FiniteModel4.toUFOSignature4] using hQB
      have hOv : M.toUFOSignature4.Overlap z x w := by
        simpa [FiniteModel4.toUFOSignature4] using hOvB
      rcases (h73 x y w).1 hQ z |>.1 hOv with ⟨hEDMz, hInh, hSame⟩
      have hQI : M.toUFOSignature4.QuaIndividual x w := ⟨y, hQ⟩
      have hEDMx := h75 x w hQI
      have hUniqueX := h72 x w hEDMx
      have hUniqueZ := h72 z w hEDMz
      have hEDMzB := (externallyDependentModeB_eq_true_iff M z w).2 hEDMz
      have hInhB : M.inheresIn z y w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hInh
      have hSameB :=
        (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).2 hSame
      simp [hEDMzB, hInhB, hSameB]
    · intro rhsB
      have hQ : M.toUFOSignature4.QuaIndividualOf x y w := by
        simpa [FiniteModel4.toUFOSignature4] using hQB
      have hQI : M.toUFOSignature4.QuaIndividual x w := ⟨y, hQ⟩
      have hEDMx := h75 x w hQI
      have hUniqueX := h72 x w hEDMx
      have rhs :
          (externallyDependentModeB M z w = true ∧
            M.inheresIn z y w = true) ∧ sameFoundationB M z x w = true := by
        simpa using rhsB
      rcases rhs with ⟨⟨hEDMzB, hInhB⟩, hSameB⟩
      have hEDMz := (externallyDependentModeB_eq_true_iff M z w).1 hEDMzB
      have hUniqueZ := h72 z w hEDMz
      have hSame :=
        (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).1 hSameB
      have hOv := (h73 x y w).1 hQ z |>.2
        ⟨hEDMz, by simpa [FiniteModel4.toUFOSignature4] using hInhB, hSame⟩
      simpa [FiniteModel4.toUFOSignature4] using hOv
  · intro hAllZ
    have hSem : M.toUFOSignature4.QuaIndividualOf x y w := by
      apply (h73 x y w).2
      intro z
      have hz := (allThings_eq_true_iff M _).1 hAllZ z
      have hzIff := (iffB_eq_true_iff _ _).1 hz
      constructor
      · intro hOv
        have hOvB : M.overlap z x w = true := by
          simpa [FiniteModel4.toUFOSignature4] using hOv
        have rhsB := hzIff.1 hOvB
        have rhs :
            (externallyDependentModeB M z w = true ∧
              M.inheresIn z y w = true) ∧ sameFoundationB M z x w = true := by
          simpa using rhsB
        rcases rhs with ⟨⟨hEDMzB, hInhB⟩, hSameB⟩
        have hEDMz := (externallyDependentModeB_eq_true_iff M z w).1 hEDMzB
        have hPartXX := h47 x w
        have hOvXX : M.toUFOSignature4.Overlap x x w :=
          (h50 x x w).2 ⟨x, hPartXX, hPartXX⟩
        have hx := (allThings_eq_true_iff M _).1 hAllZ x
        have hxIff := (iffB_eq_true_iff _ _).1 hx
        have hOvXXB : M.overlap x x w = true := by
          simpa [FiniteModel4.toUFOSignature4] using hOvXX
        have rhsBX := hxIff.1 hOvXXB
        have hEDMxB : externallyDependentModeB M x w = true := by
          have parsed :
              (externallyDependentModeB M x w = true ∧
                M.inheresIn x y w = true) ∧ sameFoundationB M x x w = true := by
            simpa using rhsBX
          exact parsed.1.1
        have hEDMx := (externallyDependentModeB_eq_true_iff M x w).1 hEDMxB
        have hUniqueX := h72 x w hEDMx
        have hUniqueZ := h72 z w hEDMz
        exact ⟨hEDMz, ⟨by simpa [FiniteModel4.toUFOSignature4] using hInhB,
          (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).1 hSameB⟩⟩
      · intro rhs
        rcases rhs with ⟨hEDMz, hInh, hSame⟩
        have hz := (allThings_eq_true_iff M _).1 hAllZ z
        have hzIff := (iffB_eq_true_iff _ _).1 hz
        have hEDMzB := (externallyDependentModeB_eq_true_iff M z w).2 hEDMz
        have hInhB : M.inheresIn z y w = true := by
          simpa [FiniteModel4.toUFOSignature4] using hInh
        have hPartXX := h47 x w
        have hOvXX : M.toUFOSignature4.Overlap x x w :=
          (h50 x x w).2 ⟨x, hPartXX, hPartXX⟩
        have hx := (allThings_eq_true_iff M _).1 hAllZ x
        have hxIff := (iffB_eq_true_iff _ _).1 hx
        have hOvXXB : M.overlap x x w = true := by
          simpa [FiniteModel4.toUFOSignature4] using hOvXX
        have rhsBX := hxIff.1 hOvXXB
        have hEDMxB : externallyDependentModeB M x w = true := by
          have parsed :
              (externallyDependentModeB M x w = true ∧
                M.inheresIn x y w = true) ∧ sameFoundationB M x x w = true := by
            simpa using rhsBX
          exact parsed.1.1
        have hUniqueZ := h72 z w hEDMz
        have hUniqueX := h72 x w ((externallyDependentModeB_eq_true_iff M x w).1 hEDMxB)
        have hSameB :=
          (sameFoundationB_eq_true_iff_of_unique M z x w hUniqueZ hUniqueX).2 hSame
        have rhsB :
            (externallyDependentModeB M z w && M.inheresIn z y w &&
                sameFoundationB M z x w) = true := by
          simp [hEDMzB, hInhB, hSameB]
        have hOvB := hzIff.2 rhsB
        simpa [FiniteModel4.toUFOSignature4] using hOvB
    simpa [FiniteModel4.toUFOSignature4] using hSem

private theorem checkAx76_correct (M : FiniteModel4) :
    checkAx76 M = true ↔ ax_a76 M.toUFOSignature4.toUFOSignature3_10 := by
  unfold checkAx76 ax_a76 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx76_sound (M : FiniteModel4) :
    checkAx76 M = true → ax_a76 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx76_correct M).1

theorem checkAx76_complete (M : FiniteModel4) :
    ax_a76 M.toUFOSignature4.toUFOSignature3_10 → checkAx76 M = true :=
  (checkAx76_correct M).2

theorem checkAx76_iff (M : FiniteModel4) :
    checkAx76 M = true ↔ ax_a76 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx76_correct M

private theorem checkAx77_correct (M : FiniteModel4) :
    checkAx77 M = true ↔ ax_a77 M.toUFOSignature4.toUFOSignature3_10 := by
  unfold checkAx77 ax_a77 existsUniqueFoundedByB allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]
  grind

theorem checkAx77_sound (M : FiniteModel4) :
    checkAx77 M = true → ax_a77 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx77_correct M).1

theorem checkAx77_complete (M : FiniteModel4) :
    ax_a77 M.toUFOSignature4.toUFOSignature3_10 → checkAx77 M = true :=
  (checkAx77_correct M).2

theorem checkAx77_iff (M : FiniteModel4) :
    checkAx77 M = true ↔ ax_a77 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx77_correct M

theorem checkAx79_sound_with_prereqs (M : FiniteModel4) :
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 →
    checkAx79 M = true →
    ax_a79 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h72 h75 h x w
  have hx := (allThings_eq_true_iff M _).1 h x
  have hw := (allWorlds_eq_true_iff M _).1 hx w
  have hIff := (iffB_eq_true_iff _ _).1 hw
  constructor
  · intro hRel
    have hRelB : M.relator x w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hRel
    have rhsB := hIff.1 hRelB
    have rhs :
        (((anyThings M fun y => M.properPart y x w) = true ∧
          (allThings M fun y =>
            allThings M fun z =>
              impliesB (M.properPart y x w && M.properPart z x w)
                ((anyThings M fun q => M.quaIndividualOf y q w) &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)) = true) ∧
          (allThings M fun y =>
            allThings M fun z =>
              impliesB
                (M.properPart y x w &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)
                (M.properPart z x w)) = true) := by
      simpa using rhsB
    rcases rhs with ⟨⟨hAnyPPB, hPairAllB⟩, hClosureAllB⟩
    have hExistsPP :
        ∃ y : M.toUFOSignature4.Thing, M.toUFOSignature4.ProperPart y x w := by
      rcases (anyThings_eq_true_iff M _).1 hAnyPPB with ⟨y, hy⟩
      exact ⟨y, by simpa [FiniteModel4.toUFOSignature4] using hy⟩
    have hPairwise :
        ∀ y z : M.toUFOSignature4.Thing,
          (M.toUFOSignature4.ProperPart y x w ∧
            M.toUFOSignature4.ProperPart z x w) →
            (M.toUFOSignature4.QuaIndividual y w ∧
              M.toUFOSignature4.QuaIndividual z w ∧
              FoundationOf M.toUFOSignature4.toUFOSignature3_10 y w =
                FoundationOf M.toUFOSignature4.toUFOSignature3_10 z w ∧
              M.toUFOSignature4.ExistentialDependence y z w ∧
              M.toUFOSignature4.ExistentialDependence z y w) := by
      intro y z hPPs
      rcases hPPs with ⟨hPPY, hPPZ⟩
      have hyAll := (allThings_eq_true_iff M _).1 hPairAllB y
      have hzAll := (allThings_eq_true_iff M _).1 hyAll z
      unfold impliesB at hzAll
      have hPPYB : M.properPart y x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hPPY
      have hPPZB : M.properPart z x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hPPZ
      simp [hPPYB, hPPZB] at hzAll
      have parsed :
          ((((anyThings M fun q => M.quaIndividualOf y q w) = true ∧
              (anyThings M fun q => M.quaIndividualOf z q w) = true) ∧
              sameFoundationB M y z w = true) ∧
              boxExImpB M y z w = true) ∧
              boxExImpB M z y w = true := by
        simpa using hzAll
      rcases parsed with ⟨⟨⟨⟨hQYB, hQZB⟩, hSameB⟩, hEDYZB⟩, hEDZYB⟩
      have hQY := (quaIndividualAny_eq_true_iff M y w).1 hQYB
      have hQZ := (quaIndividualAny_eq_true_iff M z w).1 hQZB
      have hUniqueY := h72 y w (h75 y w hQY)
      have hUniqueZ := h72 z w (h75 z w hQZ)
      exact ⟨hQY, hQZ,
        (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).1 hSameB,
        (boxExImpB_eq_true_iff M y z w).1 hEDYZB,
        (boxExImpB_eq_true_iff M z y w).1 hEDZYB⟩
    have hClosure :
        ∀ y z : M.toUFOSignature4.Thing,
          (M.toUFOSignature4.ProperPart y x w ∧
            M.toUFOSignature4.QuaIndividual z w ∧
            FoundationOf M.toUFOSignature4.toUFOSignature3_10 y w =
              FoundationOf M.toUFOSignature4.toUFOSignature3_10 z w ∧
            M.toUFOSignature4.ExistentialDependence y z w ∧
            M.toUFOSignature4.ExistentialDependence z y w) →
            M.toUFOSignature4.ProperPart z x w := by
      intro y z hPrem
      rcases hPrem with ⟨hPPY, hQZ, hSame, hEDYZ, hEDZY⟩
      have hyAll := (allThings_eq_true_iff M _).1 hClosureAllB y
      have hzAll := (allThings_eq_true_iff M _).1 hyAll z
      unfold impliesB at hzAll
      have hPPYB : M.properPart y x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hPPY
      have hQZB := (quaIndividualAny_eq_true_iff M z w).2 hQZ
      have hQY := (hPairwise y y ⟨hPPY, hPPY⟩).1
      have hUniqueY := h72 y w (h75 y w hQY)
      have hUniqueZ := h72 z w (h75 z w hQZ)
      have hSameB :=
        (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).2 hSame
      have hEDYZB := (boxExImpB_eq_true_iff M y z w).2 hEDYZ
      have hEDZYB := (boxExImpB_eq_true_iff M z y w).2 hEDZY
      have premB :
          (M.properPart y x w &&
            (anyThings M fun q => M.quaIndividualOf z q w) &&
            sameFoundationB M y z w &&
            boxExImpB M y z w &&
            boxExImpB M z y w) = true := by
        simp [hPPYB, hQZB, hSameB, hEDYZB, hEDZYB]
      simp [premB] at hzAll
      simpa [FiniteModel4.toUFOSignature4] using hzAll
    exact ⟨hExistsPP, hPairwise, hClosure⟩
  · intro hSem
    rcases hSem with ⟨hExistsPP, hPairwise, hClosure⟩
    have rhsB :
        ((anyThings M fun y => M.properPart y x w) &&
          (allThings M fun y =>
            allThings M fun z =>
              impliesB (M.properPart y x w && M.properPart z x w)
                ((anyThings M fun q => M.quaIndividualOf y q w) &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)) &&
          (allThings M fun y =>
            allThings M fun z =>
              impliesB
                (M.properPart y x w &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)
                (M.properPart z x w))) = true := by
      have hAnyPPB : (anyThings M fun y => M.properPart y x w) = true := by
        rcases hExistsPP with ⟨y, hy⟩
        apply (anyThings_eq_true_iff M _).2
        exact ⟨y, by simpa [FiniteModel4.toUFOSignature4] using hy⟩
      have hPairAllB :
          (allThings M fun y =>
            allThings M fun z =>
              impliesB (M.properPart y x w && M.properPart z x w)
                ((anyThings M fun q => M.quaIndividualOf y q w) &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)) = true := by
        apply (allThings_eq_true_iff M _).2
        intro y
        apply (allThings_eq_true_iff M _).2
        intro z
        unfold impliesB
        by_cases hPremB : (M.properPart y x w && M.properPart z x w) = true
        · have hPremPair :
              M.properPart y x w = true ∧ M.properPart z x w = true := by
            simpa using hPremB
          rcases hPremPair with ⟨hPPYB, hPPZB⟩
          have hPPY : M.toUFOSignature4.ProperPart y x w := by
            simpa [FiniteModel4.toUFOSignature4] using hPPYB
          have hPPZ : M.toUFOSignature4.ProperPart z x w := by
            simpa [FiniteModel4.toUFOSignature4] using hPPZB
          rcases hPairwise y z ⟨hPPY, hPPZ⟩ with ⟨hQY, hQZ, hSame, hEDYZ, hEDZY⟩
          have hQYB := (quaIndividualAny_eq_true_iff M y w).2 hQY
          have hQZB := (quaIndividualAny_eq_true_iff M z w).2 hQZ
          have hUniqueY := h72 y w (h75 y w hQY)
          have hUniqueZ := h72 z w (h75 z w hQZ)
          have hSameB :=
            (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).2 hSame
          have hEDYZB := (boxExImpB_eq_true_iff M y z w).2 hEDYZ
          have hEDZYB := (boxExImpB_eq_true_iff M z y w).2 hEDZY
          simp [hPremB, hQYB, hQZB, hSameB, hEDYZB, hEDZYB]
        · simp [hPremB]
      have hClosureAllB :
          (allThings M fun y =>
            allThings M fun z =>
              impliesB
                (M.properPart y x w &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)
                (M.properPart z x w)) = true := by
        apply (allThings_eq_true_iff M _).2
        intro y
        apply (allThings_eq_true_iff M _).2
        intro z
        unfold impliesB
        by_cases hPremB :
            (M.properPart y x w &&
              (anyThings M fun q => M.quaIndividualOf z q w) &&
              sameFoundationB M y z w &&
              boxExImpB M y z w &&
              boxExImpB M z y w) = true
        · have parsed :
              ((((M.properPart y x w = true ∧
                (anyThings M fun q => M.quaIndividualOf z q w) = true) ∧
                sameFoundationB M y z w = true) ∧
                boxExImpB M y z w = true) ∧
                boxExImpB M z y w = true) := by
            simpa using hPremB
          rcases parsed with ⟨⟨⟨⟨hPPYB, hQZB⟩, hSameB⟩, hEDYZB⟩, hEDZYB⟩
          have hPPY : M.toUFOSignature4.ProperPart y x w := by
            simpa [FiniteModel4.toUFOSignature4] using hPPYB
          have hQZ := (quaIndividualAny_eq_true_iff M z w).1 hQZB
          have hQY := (hPairwise y y ⟨hPPY, hPPY⟩).1
          have hUniqueY := h72 y w (h75 y w hQY)
          have hUniqueZ := h72 z w (h75 z w hQZ)
          have hSame :=
            (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).1 hSameB
          have hEDYZ := (boxExImpB_eq_true_iff M y z w).1 hEDYZB
          have hEDZY := (boxExImpB_eq_true_iff M z y w).1 hEDZYB
          have hPPZ := hClosure y z ⟨hPPY, hQZ, hSame, hEDYZ, hEDZY⟩
          have hPPZB : M.properPart z x w = true := by
            simpa [FiniteModel4.toUFOSignature4] using hPPZ
          simp [hPremB, hPPZB]
        · simp [hPremB]
      simp [hAnyPPB, hPairAllB, hClosureAllB]
    have hRelB := hIff.2 rhsB
    simpa [FiniteModel4.toUFOSignature4] using hRelB

theorem checkAx79_sound (M : FiniteModel4) :
    checkAx72 M = true →
    checkAx75 M = true →
    checkAx79 M = true →
    ax_a79 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h72 h75 h79
  exact checkAx79_sound_with_prereqs M
    (checkAx72_sound M h72)
    (checkAx75_sound M h75)
    h79

theorem checkAx79_complete_with_prereqs (M : FiniteModel4) :
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a79 M.toUFOSignature4.toUFOSignature3_10 →
    checkAx79 M = true := by
  intro h72 h75 h79
  unfold checkAx79
  apply (allThings_eq_true_iff M _).2
  intro x
  apply (allWorlds_eq_true_iff M _).2
  intro w
  apply (iffB_eq_true_iff _ _).2
  constructor
  · intro hRelB
    have hRel : M.toUFOSignature4.Relator x w := by
      simpa [FiniteModel4.toUFOSignature4] using hRelB
    rcases (h79 x w).1 hRel with ⟨hExistsPP, hPairwise, hClosure⟩
    have hAnyPPB : (anyThings M fun y => M.properPart y x w) = true := by
      rcases hExistsPP with ⟨y, hy⟩
      apply (anyThings_eq_true_iff M _).2
      exact ⟨y, by simpa [FiniteModel4.toUFOSignature4] using hy⟩
    have hPairAllB :
        (allThings M fun y =>
          allThings M fun z =>
            impliesB (M.properPart y x w && M.properPart z x w)
              ((anyThings M fun q => M.quaIndividualOf y q w) &&
                (anyThings M fun q => M.quaIndividualOf z q w) &&
                sameFoundationB M y z w &&
                boxExImpB M y z w &&
                boxExImpB M z y w)) = true := by
      apply (allThings_eq_true_iff M _).2
      intro y
      apply (allThings_eq_true_iff M _).2
      intro z
      unfold impliesB
      by_cases hPremB : (M.properPart y x w && M.properPart z x w) = true
      · have hPremPair :
            M.properPart y x w = true ∧ M.properPart z x w = true := by
          simpa using hPremB
        rcases hPremPair with ⟨hPPYB, hPPZB⟩
        have hPPY : M.toUFOSignature4.ProperPart y x w := by
          simpa [FiniteModel4.toUFOSignature4] using hPPYB
        have hPPZ : M.toUFOSignature4.ProperPart z x w := by
          simpa [FiniteModel4.toUFOSignature4] using hPPZB
        rcases hPairwise y z ⟨hPPY, hPPZ⟩ with ⟨hQY, hQZ, hSame, hEDYZ, hEDZY⟩
        have hQYB := (quaIndividualAny_eq_true_iff M y w).2 hQY
        have hQZB := (quaIndividualAny_eq_true_iff M z w).2 hQZ
        have hUniqueY := h72 y w (h75 y w hQY)
        have hUniqueZ := h72 z w (h75 z w hQZ)
        have hSameB :=
          (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).2 hSame
        have hEDYZB := (boxExImpB_eq_true_iff M y z w).2 hEDYZ
        have hEDZYB := (boxExImpB_eq_true_iff M z y w).2 hEDZY
        simp [hPremB, hQYB, hQZB, hSameB, hEDYZB, hEDZYB]
      · simp [hPremB]
    have hClosureAllB :
        (allThings M fun y =>
          allThings M fun z =>
            impliesB
              (M.properPart y x w &&
                (anyThings M fun q => M.quaIndividualOf z q w) &&
                sameFoundationB M y z w &&
                boxExImpB M y z w &&
                boxExImpB M z y w)
              (M.properPart z x w)) = true := by
      apply (allThings_eq_true_iff M _).2
      intro y
      apply (allThings_eq_true_iff M _).2
      intro z
      unfold impliesB
      by_cases hPremB :
          (M.properPart y x w &&
            (anyThings M fun q => M.quaIndividualOf z q w) &&
            sameFoundationB M y z w &&
            boxExImpB M y z w &&
            boxExImpB M z y w) = true
      · have parsed :
            ((((M.properPart y x w = true ∧
              (anyThings M fun q => M.quaIndividualOf z q w) = true) ∧
              sameFoundationB M y z w = true) ∧
              boxExImpB M y z w = true) ∧
              boxExImpB M z y w = true) := by
          simpa using hPremB
        rcases parsed with ⟨⟨⟨⟨hPPYB, hQZB⟩, hSameB⟩, hEDYZB⟩, hEDZYB⟩
        have hPPY : M.toUFOSignature4.ProperPart y x w := by
          simpa [FiniteModel4.toUFOSignature4] using hPPYB
        have hQZ := (quaIndividualAny_eq_true_iff M z w).1 hQZB
        have hSemRhs :=
          (h79 x w).1 hRel
        have hQY := hSemRhs.2.1 y y ⟨hPPY, hPPY⟩ |>.1
        have hUniqueY := h72 y w (h75 y w hQY)
        have hUniqueZ := h72 z w (h75 z w hQZ)
        have hSame :=
          (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).1 hSameB
        have hEDYZ := (boxExImpB_eq_true_iff M y z w).1 hEDYZB
        have hEDZY := (boxExImpB_eq_true_iff M z y w).1 hEDZYB
        have hPPZ := hClosure y z ⟨hPPY, hQZ, hSame, hEDYZ, hEDZY⟩
        have hPPZB : M.properPart z x w = true := by
          simpa [FiniteModel4.toUFOSignature4] using hPPZ
        simp [hPremB, hPPZB]
      · simp [hPremB]
    simp [hAnyPPB, hPairAllB, hClosureAllB]
  · intro rhsB
    have rhs :
        (((anyThings M fun y => M.properPart y x w) = true ∧
          (allThings M fun y =>
            allThings M fun z =>
              impliesB (M.properPart y x w && M.properPart z x w)
                ((anyThings M fun q => M.quaIndividualOf y q w) &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)) = true) ∧
          (allThings M fun y =>
            allThings M fun z =>
              impliesB
                (M.properPart y x w &&
                  (anyThings M fun q => M.quaIndividualOf z q w) &&
                  sameFoundationB M y z w &&
                  boxExImpB M y z w &&
                  boxExImpB M z y w)
                (M.properPart z x w)) = true) := by
      simpa using rhsB
    rcases rhs with ⟨⟨hAnyPPB, hPairAllB⟩, hClosureAllB⟩
    have hExistsPP :
        ∃ y : M.toUFOSignature4.Thing, M.toUFOSignature4.ProperPart y x w := by
      rcases (anyThings_eq_true_iff M _).1 hAnyPPB with ⟨y, hy⟩
      exact ⟨y, by simpa [FiniteModel4.toUFOSignature4] using hy⟩
    have hPairwise :
        ∀ y z : M.toUFOSignature4.Thing,
          M.toUFOSignature4.ProperPart y x w ∧
          M.toUFOSignature4.ProperPart z x w →
          M.toUFOSignature4.QuaIndividual y w ∧
          M.toUFOSignature4.QuaIndividual z w ∧
          FoundationOf M.toUFOSignature4.toUFOSignature3_10 y w =
            FoundationOf M.toUFOSignature4.toUFOSignature3_10 z w ∧
          M.toUFOSignature4.ExistentialDependence y z w ∧
          M.toUFOSignature4.ExistentialDependence z y w := by
      intro y z hPPs
      rcases hPPs with ⟨hPPY, hPPZ⟩
      have hyAll := (allThings_eq_true_iff M _).1 hPairAllB y
      have hzAll := (allThings_eq_true_iff M _).1 hyAll z
      unfold impliesB at hzAll
      have hPPYB : M.properPart y x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hPPY
      have hPPZB : M.properPart z x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hPPZ
      simp [hPPYB, hPPZB] at hzAll
      have parsed :
          ((((anyThings M fun q => M.quaIndividualOf y q w) = true ∧
            (anyThings M fun q => M.quaIndividualOf z q w) = true) ∧
            sameFoundationB M y z w = true) ∧
            boxExImpB M y z w = true) ∧
            boxExImpB M z y w = true := by
        simpa using hzAll
      rcases parsed with ⟨⟨⟨⟨hQYB, hQZB⟩, hSameB⟩, hEDYZB⟩, hEDZYB⟩
      have hQY := (quaIndividualAny_eq_true_iff M y w).1 hQYB
      have hQZ := (quaIndividualAny_eq_true_iff M z w).1 hQZB
      have hUniqueY := h72 y w (h75 y w hQY)
      have hUniqueZ := h72 z w (h75 z w hQZ)
      exact ⟨hQY, hQZ,
        (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).1 hSameB,
        (boxExImpB_eq_true_iff M y z w).1 hEDYZB,
        (boxExImpB_eq_true_iff M z y w).1 hEDZYB⟩
    have hClosure :
        ∀ y z : M.toUFOSignature4.Thing,
          M.toUFOSignature4.ProperPart y x w ∧
          M.toUFOSignature4.QuaIndividual z w ∧
          FoundationOf M.toUFOSignature4.toUFOSignature3_10 y w =
            FoundationOf M.toUFOSignature4.toUFOSignature3_10 z w ∧
          M.toUFOSignature4.ExistentialDependence y z w ∧
          M.toUFOSignature4.ExistentialDependence z y w →
          M.toUFOSignature4.ProperPart z x w := by
      intro y z hPrem
      rcases hPrem with ⟨hPPY, hQZ, hSame, hEDYZ, hEDZY⟩
      have hyAll := (allThings_eq_true_iff M _).1 hClosureAllB y
      have hzAll := (allThings_eq_true_iff M _).1 hyAll z
      unfold impliesB at hzAll
      have hPPYB : M.properPart y x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hPPY
      have hQZB := (quaIndividualAny_eq_true_iff M z w).2 hQZ
      have hQY := (hPairwise y y ⟨hPPY, hPPY⟩).1
      have hUniqueY := h72 y w (h75 y w hQY)
      have hUniqueZ := h72 z w (h75 z w hQZ)
      have hSameB :=
        (sameFoundationB_eq_true_iff_of_unique M y z w hUniqueY hUniqueZ).2 hSame
      have hEDYZB := (boxExImpB_eq_true_iff M y z w).2 hEDYZ
      have hEDZYB := (boxExImpB_eq_true_iff M z y w).2 hEDZY
      have premB :
          (M.properPart y x w &&
            (anyThings M fun q => M.quaIndividualOf z q w) &&
            sameFoundationB M y z w &&
            boxExImpB M y z w &&
            boxExImpB M z y w) = true := by
        simp [hPPYB, hQZB, hSameB, hEDYZB, hEDZYB]
      simp [premB] at hzAll
      simpa [FiniteModel4.toUFOSignature4] using hzAll
    have hRel := (h79 x w).2 ⟨hExistsPP, hPairwise, hClosure⟩
    simpa [FiniteModel4.toUFOSignature4] using hRel

theorem checkAx78_sound_with_prereqs (M : FiniteModel4) :
    ax_a48 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a52 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a77 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a79 M.toUFOSignature4.toUFOSignature3_10 →
    checkAx78 M = true →
    ax_a78 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h48 h52 h72 h75 h77 h79 h x y w hRelPart
  rcases hRelPart with ⟨hRel, hPartYX⟩
  have hx := (allThings_eq_true_iff M _).1 h x
  have hy := (allThings_eq_true_iff M _).1 hx y
  have hw := (allWorlds_eq_true_iff M _).1 hy w
  unfold impliesB at hw
  have hRelB : M.relator x w = true := by
    simpa [FiniteModel4.toUFOSignature4] using hRel
  have hPartB : M.part y x w = true := by
    simpa [FiniteModel4.toUFOSignature4] using hPartYX
  simp [hRelB, hPartB] at hw
  have hUniqueX := h77 x w hRel
  have hUniqueY : ∃! u, M.toUFOSignature4.FoundedBy y u w := by
    by_cases hPartXY : M.toUFOSignature4.Part x y w
    · have hEq : x = y := h48 x y w ⟨hPartXY, hPartYX⟩
      subst y
      exact hUniqueX
    · have hPP : M.toUFOSignature4.ProperPart y x w :=
        (h52 y x w).2 ⟨hPartYX, hPartXY⟩
      rcases (h79 x w).1 hRel with ⟨_, hPairwise, _⟩
      have hQIY := (hPairwise y y ⟨hPP, hPP⟩).1
      exact h72 y w (h75 y w hQIY)
  exact (sameFoundationB_eq_true_iff_of_unique M x y w hUniqueX hUniqueY).1 hw

theorem checkAx78_sound (M : FiniteModel4) :
    checkAx48 M = true →
    checkAx52 M = true →
    checkAx72 M = true →
    checkAx75 M = true →
    checkAx77 M = true →
    checkAx79 M = true →
    checkAx78 M = true →
    ax_a78 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h48 h52 h72 h75 h77 h79 h78
  have h72Sem := checkAx72_sound M h72
  have h75Sem := checkAx75_sound M h75
  exact checkAx78_sound_with_prereqs M
    (checkAx48_sound M h48)
    (checkAx52_sound M h52)
    h72Sem
    h75Sem
    (checkAx77_sound M h77)
    (checkAx79_sound_with_prereqs M h72Sem h75Sem h79)
    h78

theorem checkAx78_complete_with_prereqs (M : FiniteModel4) :
    ax_a48 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a52 M.toUFOSignature4.toUFOSignature3_5 →
    ax_a72 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a75 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a77 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a79 M.toUFOSignature4.toUFOSignature3_10 →
    ax_a78 M.toUFOSignature4.toUFOSignature3_10 →
    checkAx78 M = true := by
  intro h48 h52 h72 h75 h77 h79 h78
  unfold checkAx78
  apply (allThings_eq_true_iff M _).2
  intro x
  apply (allThings_eq_true_iff M _).2
  intro y
  apply (allWorlds_eq_true_iff M _).2
  intro w
  unfold impliesB
  by_cases hPremB : (M.relator x w && M.part y x w) = true
  · have hPrem :
        M.relator x w = true ∧ M.part y x w = true := by
      simpa using hPremB
    rcases hPrem with ⟨hRelB, hPartB⟩
    have hRel : M.toUFOSignature4.Relator x w := by
      simpa [FiniteModel4.toUFOSignature4] using hRelB
    have hPartYX : M.toUFOSignature4.Part y x w := by
      simpa [FiniteModel4.toUFOSignature4] using hPartB
    have hUniqueX := h77 x w hRel
    have hUniqueY : ∃! u, M.toUFOSignature4.FoundedBy y u w := by
      by_cases hPartXY : M.toUFOSignature4.Part x y w
      · have hEq : x = y := h48 x y w ⟨hPartXY, hPartYX⟩
        subst y
        exact hUniqueX
      · have hPP : M.toUFOSignature4.ProperPart y x w :=
          (h52 y x w).2 ⟨hPartYX, hPartXY⟩
        rcases (h79 x w).1 hRel with ⟨_, hPairwise, _⟩
        have hQIY := (hPairwise y y ⟨hPP, hPP⟩).1
        exact h72 y w (h75 y w hQIY)
    have hSameSem := h78 x y w ⟨hRel, hPartYX⟩
    have hSameB :=
      (sameFoundationB_eq_true_iff_of_unique M x y w hUniqueX hUniqueY).2 hSameSem
    simp [hPremB, hSameB]
  · simp [hPremB]

private theorem checkAx80_correct (M : FiniteModel4) :
    checkAx80 M = true ↔ ax_a80 M.toUFOSignature4.toUFOSignature3_10 := by
  unfold checkAx80 ax_a80 iffB allThings allWorlds anyThings
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx80_sound (M : FiniteModel4) :
    checkAx80 M = true → ax_a80 M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAx80_correct M).1

theorem checkAx80_complete (M : FiniteModel4) :
    ax_a80 M.toUFOSignature4.toUFOSignature3_10 → checkAx80 M = true :=
  (checkAx80_correct M).2

theorem checkAx80_iff (M : FiniteModel4) :
    checkAx80 M = true ↔ ax_a80 M.toUFOSignature4.toUFOSignature3_10 :=
  checkAx80_correct M

private theorem checkAxQuaIndividualOfEndurant_correct (M : FiniteModel4) :
    checkAxQuaIndividualOfEndurant M = true ↔
      ax_quaIndividualOf_endurant M.toUFOSignature4.toUFOSignature3_10 := by
  unfold checkAxQuaIndividualOfEndurant ax_quaIndividualOf_endurant allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxQuaIndividualOfEndurant_sound (M : FiniteModel4) :
    checkAxQuaIndividualOfEndurant M = true →
      ax_quaIndividualOf_endurant M.toUFOSignature4.toUFOSignature3_10 :=
  (checkAxQuaIndividualOfEndurant_correct M).1

theorem checkAxQuaIndividualOfEndurant_complete (M : FiniteModel4) :
    ax_quaIndividualOf_endurant M.toUFOSignature4.toUFOSignature3_10 →
      checkAxQuaIndividualOfEndurant M = true :=
  (checkAxQuaIndividualOfEndurant_correct M).2

theorem checkAxQuaIndividualOfEndurant_iff (M : FiniteModel4) :
    checkAxQuaIndividualOfEndurant M = true ↔
      ax_quaIndividualOf_endurant M.toUFOSignature4.toUFOSignature3_10 :=
  checkAxQuaIndividualOfEndurant_correct M

private theorem checkAx81_correct (M : FiniteModel4) :
    checkAx81 M = true ↔ ax_a81 M.toUFOSignature4.toUFOSignature3_11 := by
  unfold checkAx81 ax_a81 allThings allWorlds anyThings impliesB
  simp [FiniteModel4.toUFOSignature4, existsUniqueInstInheresB_eq_true_iff]
  grind

theorem checkAx81_sound (M : FiniteModel4) :
    checkAx81 M = true → ax_a81 M.toUFOSignature4.toUFOSignature3_11 :=
  (checkAx81_correct M).1

theorem checkAx81_complete (M : FiniteModel4) :
    ax_a81 M.toUFOSignature4.toUFOSignature3_11 → checkAx81 M = true :=
  (checkAx81_correct M).2

theorem checkAx81_iff (M : FiniteModel4) :
    checkAx81 M = true ↔ ax_a81 M.toUFOSignature4.toUFOSignature3_11 :=
  checkAx81_correct M

private theorem checkAx82_correct (M : FiniteModel4) :
    checkAx82 M = true ↔ ax_a82 M.toUFOSignature4.toUFOSignature3_11 := by
  unfold checkAx82 ax_a82 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, existsUniqueInstInheresB_eq_true_iff]
  grind

theorem checkAx82_sound (M : FiniteModel4) :
    checkAx82 M = true → ax_a82 M.toUFOSignature4.toUFOSignature3_11 :=
  (checkAx82_correct M).1

theorem checkAx82_complete (M : FiniteModel4) :
    ax_a82 M.toUFOSignature4.toUFOSignature3_11 → checkAx82 M = true :=
  (checkAx82_correct M).2

theorem checkAx82_iff (M : FiniteModel4) :
    checkAx82 M = true ↔ ax_a82 M.toUFOSignature4.toUFOSignature3_11 :=
  checkAx82_correct M

private theorem checkAx83_correct (M : FiniteModel4) :
    checkAx83 M = true ↔ ax_a83 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx83 ax_a83 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx83_sound (M : FiniteModel4) :
    checkAx83 M = true → ax_a83 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx83_correct M).1

theorem checkAx83_complete (M : FiniteModel4) :
    ax_a83 M.toUFOSignature4.toUFOSignature3_12 → checkAx83 M = true :=
  (checkAx83_correct M).2

private theorem checkAx84_correct (M : FiniteModel4) :
    checkAx84 M = true ↔ ax_a84 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx84 ax_a84 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx84_sound (M : FiniteModel4) :
    checkAx84 M = true → ax_a84 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx84_correct M).1

theorem checkAx84_complete (M : FiniteModel4) :
    ax_a84 M.toUFOSignature4.toUFOSignature3_12 → checkAx84 M = true :=
  (checkAx84_correct M).2

private theorem checkAx85_correct (M : FiniteModel4) :
    checkAx85 M = true ↔ ax_a85 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx85 ax_a85 allThings allWorlds
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx85_sound (M : FiniteModel4) :
    checkAx85 M = true → ax_a85 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx85_correct M).1

theorem checkAx85_complete (M : FiniteModel4) :
    ax_a85 M.toUFOSignature4.toUFOSignature3_12 → checkAx85 M = true :=
  (checkAx85_correct M).2

private theorem nonEmptySetB_eq_true_iff
    (M : FiniteModel4) (s : Fin M.thingCount) (w : Fin M.worldCount) :
    nonEmptySetB M s w = true ↔ NonEmptySet M.toUFOSignature4.toUFOSignature3_12 s w := by
  unfold nonEmptySetB NonEmptySet anyThings
  simp [FiniteModel4.toUFOSignature4, Set.Nonempty]

private theorem checkAx89_correct (M : FiniteModel4) :
    checkAx89 M = true ↔ ax_a89 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx89 ax_a89 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx89_sound (M : FiniteModel4) :
    checkAx89 M = true → ax_a89 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx89_correct M).1

theorem checkAx89_complete (M : FiniteModel4) :
    ax_a89 M.toUFOSignature4.toUFOSignature3_12 → checkAx89 M = true :=
  (checkAx89_correct M).2

private theorem properSubsetB_eq_true_iff
    (M : FiniteModel4) (s t : Fin M.thingCount) (w : Fin M.worldCount) :
    properSubsetB M s t w = true ↔
      ProperSubsetOf M.toUFOSignature4.toUFOSignature3_12 s t w := by
  constructor
  · intro h
    unfold properSubsetB at h
    simp [allThings_eq_true_iff, anyThings_eq_true_iff, impliesB] at h
    unfold ProperSubsetOf
    rw [Set.ssubset_def]
    constructor
    · intro x hx
      have hxB : M.memberOf x s w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hx
      have hxDisj := h.1 x
      simp [hxB] at hxDisj
      simpa [FiniteModel4.toUFOSignature4] using hxDisj
    · intro hReverse
      rcases h.2 with ⟨x, hxt, hxsFalse⟩
      have hxs : M.memberOf x s w = true := hReverse hxt
      simp [hxs] at hxsFalse
  · intro h
    unfold properSubsetB
    unfold ProperSubsetOf at h
    rw [Set.ssubset_def] at h
    have hForward :
        (allThings M fun x => impliesB (M.memberOf x s w) (M.memberOf x t w)) = true := by
      apply (allThings_eq_true_iff M _).2
      intro x
      unfold impliesB
      by_cases hxs : M.memberOf x s w = true
      · have hxt : M.memberOf x t w = true := h.1 hxs
        simp [hxs, hxt]
      · cases hsx : M.memberOf x s w
        · simp
        · exact False.elim (hxs hsx)
    have hWitness :
        (anyThings M fun x => M.memberOf x t w && !M.memberOf x s w) = true := by
      apply (anyThings_eq_true_iff M _).2
      by_contra hNoWitness
      have hReverse : {x | M.memberOf x t w = true} ⊆ {x | M.memberOf x s w = true} := by
        intro x hxt
        have hxtB : M.memberOf x t w = true := hxt
        by_cases hxs : M.memberOf x s w = true
        · exact hxs
        · have hExists : ∃ x, (M.memberOf x t w && (!(M.memberOf x s w))) = true := by
            refine ⟨x, ?_⟩
            cases hsx : M.memberOf x s w
            · simp [hxtB]
            · exact False.elim (hxs hsx)
          exact False.elim (hNoWitness hExists)
      exact h.2 hReverse
    simp [hForward, hWitness]

private theorem checkAx90_correct (M : FiniteModel4) :
    checkAx90 M = true ↔ ax_a90 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx90 ax_a90 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, ProperSub, properSubsetB_eq_true_iff]
  grind

theorem checkAx90_sound (M : FiniteModel4) :
    checkAx90 M = true → ax_a90 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx90_correct M).1

theorem checkAx90_complete (M : FiniteModel4) :
    ax_a90 M.toUFOSignature4.toUFOSignature3_12 → checkAx90 M = true :=
  (checkAx90_correct M).2

private theorem qualityStructureB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    qualityStructureB M x w = true ↔ QualityStructure M.toUFOSignature4.toUFOSignature3_12 x w := by
  unfold qualityStructureB QualityStructure
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]

private theorem existsUniqueQualityStructureMemberB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueQualityStructureMemberB M x w = true ↔
      ∃! s : M.toUFOSignature4.Thing,
        QualityStructure M.toUFOSignature4.toUFOSignature3_12 s w ∧
        MemberOf M.toUFOSignature4.toUFOSignature3_12 x s w := by
  unfold existsUniqueQualityStructureMemberB
  rw [decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨s, ⟨hQSb, hMemB⟩, hUnique⟩
    refine ⟨s, ?_, ?_⟩
    · exact ⟨(qualityStructureB_eq_true_iff M s w).1 hQSb, hMemB⟩
    · intro s' hs'
      exact hUnique s' ⟨(qualityStructureB_eq_true_iff M s' w).2 hs'.1, hs'.2⟩
  · intro h
    rcases h with ⟨s, ⟨hQS, hMem⟩, hUnique⟩
    refine ⟨s, ⟨?_, ?_⟩, ?_⟩
    · exact (qualityStructureB_eq_true_iff M s w).2 hQS
    · exact hMem
    · intro s' hs'
      exact hUnique s' ⟨(qualityStructureB_eq_true_iff M s' w).1 hs'.1, hs'.2⟩

private theorem existsUniqueHasValueB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    existsUniqueHasValueB M x w = true ↔
      ∃! y : M.toUFOSignature4.Thing, M.toUFOSignature4.HasValue x y w := by
  unfold existsUniqueHasValueB
  simp [FiniteModel4.toUFOSignature4, ExistsUnique]

private theorem checkAx91_correct (M : FiniteModel4) :
    checkAx91 M = true ↔ ax_a91 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx91 ax_a91 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4, qualityStructureB_eq_true_iff, ExistsUnique]
  grind

theorem checkAx91_sound (M : FiniteModel4) :
    checkAx91 M = true → ax_a91 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx91_correct M).1

theorem checkAx91_complete (M : FiniteModel4) :
    ax_a91 M.toUFOSignature4.toUFOSignature3_12 → checkAx91 M = true :=
  (checkAx91_correct M).2

private theorem checkAx88_correct (M : FiniteModel4) :
    checkAx88 M = true ↔ ax_a88 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x w
    unfold checkAx88 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    have hIff := (iffB_eq_true_iff _ _).1 hw
    exact ⟨
      fun hxQS =>
        by
          have hDomainOrDimensionB :=
            hIff.mp ((qualityStructureB_eq_true_iff M x w).2 hxQS)
          simpa [FiniteModel4.toUFOSignature4] using hDomainOrDimensionB,
      fun h =>
        (qualityStructureB_eq_true_iff M x w).1
          (hIff.mpr (by simpa [FiniteModel4.toUFOSignature4] using h))⟩
  · intro h
    unfold checkAx88
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    apply (iffB_eq_true_iff _ _).2
    exact ⟨
      fun hxQSB => by
        have hxQS := (qualityStructureB_eq_true_iff M x w).1 hxQSB
        simpa [FiniteModel4.toUFOSignature4] using (h x w).mp hxQS,
      fun hDomainOrDimensionB => by
        apply (qualityStructureB_eq_true_iff M x w).2
        apply (h x w).mpr
        cases hd : M.qualityDomain x w with
        | true => exact Or.inl (by simpa [FiniteModel4.toUFOSignature4])
        | false =>
            cases hm : M.qualityDimension x w with
            | true => exact Or.inr (by simpa [FiniteModel4.toUFOSignature4])
            | false =>
                simp [hd, hm] at hDomainOrDimensionB⟩

theorem checkAx88_sound (M : FiniteModel4) :
    checkAx88 M = true → ax_a88 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx88_correct M).1

theorem checkAx88_complete (M : FiniteModel4) :
    ax_a88 M.toUFOSignature4.toUFOSignature3_12 → checkAx88 M = true :=
  (checkAx88_correct M).2

private theorem checkAx92_correct (M : FiniteModel4) :
    checkAx92 M = true ↔ ax_a92 M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAx92 ax_a92 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4, qualityB_eq_true_iff]
  grind

theorem checkAx92_sound (M : FiniteModel4) :
    checkAx92 M = true → ax_a92 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx92_correct M).1

theorem checkAx92_complete (M : FiniteModel4) :
    ax_a92 M.toUFOSignature4.toUFOSignature3_12 → checkAx92 M = true :=
  (checkAx92_correct M).2

private theorem checkAx93_correct (M : FiniteModel4) :
    checkAx93 M = true ↔ ax_a93 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x w hxQual
    unfold checkAx93 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    unfold impliesB at hw
    have hxQualB := (qualityB_eq_true_iff M x w).2 hxQual
    simp [hxQualB] at hw
    exact (existsUniqueHasValueB_eq_true_iff M x w).1 hw
  · intro h
    unfold checkAx93
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hxQualB : qualityB M x w = true
    · have hxQual := (qualityB_eq_true_iff M x w).1 hxQualB
      have hUniqueB := (existsUniqueHasValueB_eq_true_iff M x w).2 (h x w hxQual)
      simp [hxQualB, hUniqueB]
    · have hxQualFalse : qualityB M x w = false := by
        cases hq : qualityB M x w
        · rfl
        · exact False.elim (hxQualB hq)
      simp [hxQualFalse]

theorem checkAx93_sound (M : FiniteModel4) :
    checkAx93 M = true → ax_a93 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx93_correct M).1

theorem checkAx93_complete (M : FiniteModel4) :
    ax_a93 M.toUFOSignature4.toUFOSignature3_12 → checkAx93 M = true :=
  (checkAx93_correct M).2

private theorem checkAx86_correct (M : FiniteModel4) :
    checkAx86 M = true ↔ ax_a86 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x w hxQS
    unfold checkAx86 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    have hxQSB := (qualityStructureB_eq_true_iff M x w).2 hxQS
    unfold impliesB at hw
    simp [hxQSB] at hw
    exact ⟨hw.1, (nonEmptySetB_eq_true_iff M x w).1 hw.2⟩
  · intro h
    unfold checkAx86
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hxQSB : qualityStructureB M x w = true
    · have hxQS := (qualityStructureB_eq_true_iff M x w).1 hxQSB
      have hx := h x w hxQS
      have hxSetB : M.set_ x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hx.1
      have hxNonEmptyB := (nonEmptySetB_eq_true_iff M x w).2 hx.2
      simp [hxQSB, hxSetB, hxNonEmptyB]
    · cases hq : qualityStructureB M x w
      · simp
      · exact False.elim (hxQSB hq)

theorem checkAx86_sound (M : FiniteModel4) :
    checkAx86 M = true → ax_a86 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx86_correct M).1

theorem checkAx86_complete (M : FiniteModel4) :
    ax_a86 M.toUFOSignature4.toUFOSignature3_12 → checkAx86 M = true :=
  (checkAx86_correct M).2

private theorem checkAx87_correct (M : FiniteModel4) :
    checkAx87 M = true ↔ ax_a87 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x w
    unfold checkAx87 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    have hIff := (iffB_eq_true_iff _ _).1 hw
    exact ⟨
      fun hxQual => (existsUniqueQualityStructureMemberB_eq_true_iff M x w).1
        (hIff.mp hxQual),
      fun hxUnique => hIff.mpr
        ((existsUniqueQualityStructureMemberB_eq_true_iff M x w).2 hxUnique)⟩
  · intro h
    unfold checkAx87
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    apply (iffB_eq_true_iff _ _).2
    exact ⟨
      fun hxQual => (existsUniqueQualityStructureMemberB_eq_true_iff M x w).2
        ((h x w).mp hxQual),
      fun hxUniqueB => (h x w).mpr
        ((existsUniqueQualityStructureMemberB_eq_true_iff M x w).1 hxUniqueB)⟩

theorem checkAx87_sound (M : FiniteModel4) :
    checkAx87 M = true → ax_a87 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx87_correct M).1

theorem checkAx87_complete (M : FiniteModel4) :
    ax_a87 M.toUFOSignature4.toUFOSignature3_12 → checkAx87 M = true :=
  (checkAx87_correct M).2

private theorem checkAx94_correct (M : FiniteModel4) :
    checkAx94 M = true ↔ ax_a94 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x y w hValue
    unfold checkAx94 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hy := (allThings_eq_true_iff M _).1 hx y
    have hw := (allWorlds_eq_true_iff M _).1 hy w
    have hValueB : M.hasValue x y w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hValue
    have hwSome :
        (anyThings M fun t =>
          anyThings M fun s =>
            M.inst x t w && M.associatedWith s t w && M.memberOf y s w) = true := by
      simpa [impliesB, hValueB] using hw
    rcases (anyThings_eq_true_iff M _).1 hwSome with ⟨t, ht⟩
    rcases (anyThings_eq_true_iff M _).1 ht with ⟨s, hs⟩
    simp at hs
    exact ⟨t, s,
      by simpa [FiniteModel4.toUFOSignature4] using hs.1.1,
      by simpa [FiniteModel4.toUFOSignature4] using hs.1.2,
      by simpa [FiniteModel4.toUFOSignature4, MemberOf] using hs.2⟩
  · intro h
    unfold checkAx94
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hValue : M.hasValue x y w = true
    · rcases h x y w hValue with ⟨t, s, ht, hs, hMem⟩
      have htB : M.inst x t w = true := by
        simpa [FiniteModel4.toUFOSignature4] using ht
      have hsB : M.associatedWith s t w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hs
      have hMemB : M.memberOf y s w = true := by
        simpa [FiniteModel4.toUFOSignature4, MemberOf] using hMem
      have hSome :
          (anyThings M fun t =>
            anyThings M fun s =>
              M.inst x t w && M.associatedWith s t w && M.memberOf y s w) = true := by
        apply (anyThings_eq_true_iff M _).2
        refine ⟨t, ?_⟩
        apply (anyThings_eq_true_iff M _).2
        refine ⟨s, ?_⟩
        simp [htB, hsB, hMemB]
      simp [hValue, hSome]
    · cases hv : M.hasValue x y w
      · simp
      · exact False.elim (hValue hv)

theorem checkAx94_sound (M : FiniteModel4) :
    checkAx94 M = true → ax_a94 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx94_correct M).1

theorem checkAx94_complete (M : FiniteModel4) :
    ax_a94 M.toUFOSignature4.toUFOSignature3_12 → checkAx94 M = true :=
  (checkAx94_correct M).2

private theorem simpleQualityB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    simpleQualityB M x w = true ↔ SimpleQuality M.toUFOSignature4.toUFOSignature3_12 x w := by
  constructor
  · intro h
    unfold simpleQualityB at h
    simp at h
    constructor
    · exact (qualityB_eq_true_iff M x w).1 h.1
    · intro hExist
      rcases hExist with ⟨y, hy⟩
      have hNoInheres := (allThings_eq_true_iff M _).1 h.2 y
      have hyB : M.inheresIn y x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hy
      simp [hyB] at hNoInheres
  · intro h
    unfold simpleQualityB
    have hQualityB := (qualityB_eq_true_iff M x w).2 h.1
    have hNoInheresB :
        (allThings M fun y => !(M.inheresIn y x w)) = true := by
      apply (allThings_eq_true_iff M _).2
      intro y
      by_cases hy : M.inheresIn y x w = true
      · exact False.elim (h.2 ⟨y, by simpa [FiniteModel4.toUFOSignature4] using hy⟩)
      · cases hiy : M.inheresIn y x w
        · rfl
        · exact False.elim (hy hiy)
    simp [hQualityB, hNoInheresB]

private theorem complexQualityB_eq_true_iff
    (M : FiniteModel4) (x : Fin M.thingCount) (w : Fin M.worldCount) :
    complexQualityB M x w = true ↔ ComplexQuality M.toUFOSignature4.toUFOSignature3_12 x w := by
  constructor
  · intro h
    unfold complexQualityB at h
    simp at h
    constructor
    · exact (qualityB_eq_true_iff M x w).1 h.1
    · intro hSimple
      have hSimpleB := (simpleQualityB_eq_true_iff M x w).2 hSimple
      simp [hSimpleB] at h
  · intro h
    unfold complexQualityB
    have hQualityB := (qualityB_eq_true_iff M x w).2 h.1
    have hSimpleFalse : simpleQualityB M x w = false := by
      cases hs : simpleQualityB M x w
      · rfl
      · exact False.elim (h.2 ((simpleQualityB_eq_true_iff M x w).1 hs))
    simp [hQualityB, hSimpleFalse]

private theorem simpleQualityTypeB_eq_true_iff
    (M : FiniteModel4) (t : Fin M.thingCount) (w : Fin M.worldCount) :
    simpleQualityTypeB M t w = true ↔
      SimpleQualityType M.toUFOSignature4.toUFOSignature3_12 t w := by
  constructor
  · intro h
    unfold simpleQualityTypeB at h
    simp at h
    constructor
    · simpa [FiniteModel4.toUFOSignature4] using h.1
    · intro x hxInst
      have hxInstB : M.inst x t w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hxInst
      have hx := (allThings_eq_true_iff M _).1 h.2 x
      unfold impliesB at hx
      simp [hxInstB] at hx
      exact (simpleQualityB_eq_true_iff M x w).1 hx
  · intro h
    unfold simpleQualityTypeB
    have hQualityTypeB : M.qualityType t w = true := by
      simpa [FiniteModel4.toUFOSignature4] using h.1
    have hInstancesB :
        (allThings M fun x => impliesB (M.inst x t w) (simpleQualityB M x w)) = true := by
      apply (allThings_eq_true_iff M _).2
      intro x
      unfold impliesB
      by_cases hxInstB : M.inst x t w = true
      · have hxInst : M.toUFOSignature4.Inst x t w := by
          simpa [FiniteModel4.toUFOSignature4] using hxInstB
        have hxSimpleB := (simpleQualityB_eq_true_iff M x w).2 (h.2 x hxInst)
        simp [hxInstB, hxSimpleB]
      · cases hx : M.inst x t w
        · simp
        · exact False.elim (hxInstB hx)
    simp [hQualityTypeB, hInstancesB]

private theorem complexQualityTypeB_eq_true_iff
    (M : FiniteModel4) (t : Fin M.thingCount) (w : Fin M.worldCount) :
    complexQualityTypeB M t w = true ↔
      ComplexQualityType M.toUFOSignature4.toUFOSignature3_12 t w := by
  constructor
  · intro h
    unfold complexQualityTypeB at h
    simp at h
    constructor
    · simpa [FiniteModel4.toUFOSignature4] using h.1
    · intro x hxInst
      have hxInstB : M.inst x t w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hxInst
      have hx := (allThings_eq_true_iff M _).1 h.2 x
      unfold impliesB at hx
      simp [hxInstB] at hx
      exact (complexQualityB_eq_true_iff M x w).1 hx
  · intro h
    unfold complexQualityTypeB
    have hQualityTypeB : M.qualityType t w = true := by
      simpa [FiniteModel4.toUFOSignature4] using h.1
    have hInstancesB :
        (allThings M fun x => impliesB (M.inst x t w) (complexQualityB M x w)) = true := by
      apply (allThings_eq_true_iff M _).2
      intro x
      unfold impliesB
      by_cases hxInstB : M.inst x t w = true
      · have hxInst : M.toUFOSignature4.Inst x t w := by
          simpa [FiniteModel4.toUFOSignature4] using hxInstB
        have hxComplexB := (complexQualityB_eq_true_iff M x w).2 (h.2 x hxInst)
        simp [hxInstB, hxComplexB]
      · cases hx : M.inst x t w
        · simp
        · exact False.elim (hxInstB hx)
    simp [hQualityTypeB, hInstancesB]

private theorem checkAx95_correct (M : FiniteModel4) :
    checkAx95 M = true ↔ ax_a95 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x y w hAssoc
    unfold checkAx95 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hy := (allThings_eq_true_iff M _).1 hx y
    have hw := (allWorlds_eq_true_iff M _).1 hy w
    have hAssocB : M.associatedWith x y w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hAssoc
    unfold impliesB at hw
    simp [hAssocB] at hw
    have hIff := (iffB_eq_true_iff _ _).1 hw
    exact ⟨
      fun hDim => (simpleQualityTypeB_eq_true_iff M y w).1
        (hIff.mp (by simpa [FiniteModel4.toUFOSignature4] using hDim)),
      fun hSimpleType => by
        have hDimB := hIff.mpr ((simpleQualityTypeB_eq_true_iff M y w).2 hSimpleType)
        simpa [FiniteModel4.toUFOSignature4] using hDimB⟩
  · intro h
    unfold checkAx95
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hAssocB : M.associatedWith x y w = true
    · have hAssoc : M.toUFOSignature4.AssociatedWith x y w := by
        simpa [FiniteModel4.toUFOSignature4] using hAssocB
      have hIff := h x y w hAssoc
      have hBoolIff :
          M.qualityDimension x w = true ↔ simpleQualityTypeB M y w = true := by
        exact ⟨
          fun hDimB => (simpleQualityTypeB_eq_true_iff M y w).2
            (hIff.mp (by simpa [FiniteModel4.toUFOSignature4] using hDimB)),
          fun hSimpleB => by
            have hDim := hIff.mpr ((simpleQualityTypeB_eq_true_iff M y w).1 hSimpleB)
            simpa [FiniteModel4.toUFOSignature4] using hDim⟩
      have hIffB := (iffB_eq_true_iff _ _).2 hBoolIff
      simp [hAssocB, hIffB]
    · cases ha : M.associatedWith x y w
      · simp
      · exact False.elim (hAssocB ha)

theorem checkAx95_sound (M : FiniteModel4) :
    checkAx95 M = true → ax_a95 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx95_correct M).1

theorem checkAx95_complete (M : FiniteModel4) :
    ax_a95 M.toUFOSignature4.toUFOSignature3_12 → checkAx95 M = true :=
  (checkAx95_correct M).2

private theorem checkAx96_correct (M : FiniteModel4) :
    checkAx96 M = true ↔ ax_a96 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x y w hAssoc
    unfold checkAx96 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hy := (allThings_eq_true_iff M _).1 hx y
    have hw := (allWorlds_eq_true_iff M _).1 hy w
    have hAssocB : M.associatedWith x y w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hAssoc
    unfold impliesB at hw
    simp [hAssocB] at hw
    have hIff := (iffB_eq_true_iff _ _).1 hw
    exact ⟨
      fun hDomain => (complexQualityTypeB_eq_true_iff M y w).1
        (hIff.mp (by simpa [FiniteModel4.toUFOSignature4] using hDomain)),
      fun hComplexType => by
        have hDomainB := hIff.mpr ((complexQualityTypeB_eq_true_iff M y w).2 hComplexType)
        simpa [FiniteModel4.toUFOSignature4] using hDomainB⟩
  · intro h
    unfold checkAx96
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hAssocB : M.associatedWith x y w = true
    · have hAssoc : M.toUFOSignature4.AssociatedWith x y w := by
        simpa [FiniteModel4.toUFOSignature4] using hAssocB
      have hIff := h x y w hAssoc
      have hBoolIff :
          M.qualityDomain x w = true ↔ complexQualityTypeB M y w = true := by
        exact ⟨
          fun hDomainB => (complexQualityTypeB_eq_true_iff M y w).2
            (hIff.mp (by simpa [FiniteModel4.toUFOSignature4] using hDomainB)),
          fun hComplexB => by
            have hDomain := hIff.mpr ((complexQualityTypeB_eq_true_iff M y w).1 hComplexB)
            simpa [FiniteModel4.toUFOSignature4] using hDomain⟩
      have hIffB := (iffB_eq_true_iff _ _).2 hBoolIff
      simp [hAssocB, hIffB]
    · cases ha : M.associatedWith x y w
      · simp
      · exact False.elim (hAssocB ha)

theorem checkAx96_sound (M : FiniteModel4) :
    checkAx96 M = true → ax_a96 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx96_correct M).1

theorem checkAx96_complete (M : FiniteModel4) :
    ax_a96 M.toUFOSignature4.toUFOSignature3_12 → checkAx96 M = true :=
  (checkAx96_correct M).2

private theorem checkAx97_correct (M : FiniteModel4) :
    checkAx97 M = true ↔ ax_a97 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x y z Y Z w hprem
    unfold checkAx97 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hy := (allThings_eq_true_iff M _).1 hx y
    have hz := (allThings_eq_true_iff M _).1 hy z
    have hY := (allThings_eq_true_iff M _).1 hz Y
    have hZ := (allThings_eq_true_iff M _).1 hY Z
    have hw := (allWorlds_eq_true_iff M _).1 hZ w
    have hxComplexB := (complexQualityB_eq_true_iff M x w).2 hprem.1
    have hyInstB : M.inst y Y w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hprem.2.1
    have hzInstB : M.inst z Z w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hprem.2.2.1
    have hyInheresB : M.inheresIn y x w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hprem.2.2.2.1
    have hzInheresB : M.inheresIn z x w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hprem.2.2.2.2.1
    cases hprem.2.2.2.2.2
    unfold impliesB at hw
    simp [hxComplexB, hyInstB, hzInstB, hyInheresB, hzInheresB] at hw
    exact hw
  · intro h
    unfold checkAx97
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allThings_eq_true_iff M _).2
    intro z
    apply (allThings_eq_true_iff M _).2
    intro Y
    apply (allThings_eq_true_iff M _).2
    intro Z
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hxComplexB : complexQualityB M x w = true
    · by_cases hyInstB : M.inst y Y w = true
      · by_cases hzInstB : M.inst z Z w = true
        · by_cases hyInheresB : M.inheresIn y x w = true
          · by_cases hzInheresB : M.inheresIn z x w = true
            · by_cases hEqYZ : Y = Z
              · have hxComplex := (complexQualityB_eq_true_iff M x w).1 hxComplexB
                have hyInst : M.toUFOSignature4.Inst y Y w := by
                  simpa [FiniteModel4.toUFOSignature4] using hyInstB
                have hzInst : M.toUFOSignature4.Inst z Z w := by
                  simpa [FiniteModel4.toUFOSignature4] using hzInstB
                have hyInheres : M.toUFOSignature4.InheresIn y x w := by
                  simpa [FiniteModel4.toUFOSignature4] using hyInheresB
                have hzInheres : M.toUFOSignature4.InheresIn z x w := by
                  simpa [FiniteModel4.toUFOSignature4] using hzInheresB
                have hyz := h x y z Y Z w
                  ⟨hxComplex, hyInst, hzInst, hyInheres, hzInheres, hEqYZ⟩
                have hyzB : decide (y = z) = true := decide_eq_true hyz
                have hEqYZB : decide (Y = Z) = true := decide_eq_true hEqYZ
                simp [hxComplexB, hyInstB, hzInstB, hyInheresB, hzInheresB, hEqYZB, hyzB]
              · have hEqYZB : decide (Y = Z) = false := by
                  simp [hEqYZ]
                simp [hxComplexB, hyInstB, hzInstB, hyInheresB, hzInheresB, hEqYZB]
            · cases hzInh : M.inheresIn z x w
              · simp [hxComplexB, hyInstB, hzInstB, hyInheresB]
              · exact False.elim (hzInheresB hzInh)
          · cases hyInh : M.inheresIn y x w
            · simp [hxComplexB, hyInstB, hzInstB]
            · exact False.elim (hyInheresB hyInh)
        · cases hzI : M.inst z Z w
          · simp [hxComplexB, hyInstB]
          · exact False.elim (hzInstB hzI)
      · cases hyI : M.inst y Y w
        · simp [hxComplexB]
        · exact False.elim (hyInstB hyI)
    · cases hxC : complexQualityB M x w
      · simp
      · exact False.elim (hxComplexB hxC)

theorem checkAx97_sound (M : FiniteModel4) :
    checkAx97 M = true → ax_a97 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx97_correct M).1

theorem checkAx97_complete (M : FiniteModel4) :
    ax_a97 M.toUFOSignature4.toUFOSignature3_12 → checkAx97 M = true :=
  (checkAx97_correct M).2

private theorem checkAx98_correct (M : FiniteModel4) :
    checkAx98 M = true ↔ ax_a98 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x w hxComplex y hyInheres
    unfold checkAx98 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hw := (allWorlds_eq_true_iff M _).1 hx w
    have hxComplexB := (complexQualityB_eq_true_iff M x w).2 hxComplex
    unfold impliesB at hw
    simp [hxComplexB] at hw
    have hy := (allThings_eq_true_iff M _).1 hw y
    have hyInheresB : M.inheresIn y x w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hyInheres
    unfold impliesB at hy
    simp [hyInheresB] at hy
    exact (simpleQualityB_eq_true_iff M y w).1 hy
  · intro h
    unfold checkAx98
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hxComplexB : complexQualityB M x w = true
    · have hxComplex := (complexQualityB_eq_true_iff M x w).1 hxComplexB
      have hAllY :
          (allThings M fun y => !M.inheresIn y x w || simpleQualityB M y w) = true := by
        apply (allThings_eq_true_iff M _).2
        intro y
        by_cases hyInheresB : M.inheresIn y x w = true
        · have hyInheres : M.toUFOSignature4.InheresIn y x w := by
            simpa [FiniteModel4.toUFOSignature4] using hyInheresB
          have hySimpleB := (simpleQualityB_eq_true_iff M y w).2 (h x w hxComplex y hyInheres)
          simp [hyInheresB, hySimpleB]
        · cases hyI : M.inheresIn y x w
          · simp
          · exact False.elim (hyInheresB hyI)
      simp [hxComplexB, hAllY]
    · cases hxC : complexQualityB M x w
      · simp
      · exact False.elim (hxComplexB hxC)

theorem checkAx98_sound (M : FiniteModel4) :
    checkAx98 M = true → ax_a98 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx98_correct M).1

theorem checkAx98_complete (M : FiniteModel4) :
    ax_a98 M.toUFOSignature4.toUFOSignature3_12 → checkAx98 M = true :=
  (checkAx98_correct M).2

private theorem allProductFamilyIndices_eq_true_iff
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount)
    (p : Fin pf.dimensionThings.size → Bool) :
    allProductFamilyIndices pf p = true ↔ ∀ i, p i = true := by
  unfold allProductFamilyIndices
  exact decide_eq_true_iff

private theorem anyProductFamilyIndices_eq_true_iff
    {thingCount worldCount : Nat} (pf : ProductFamilyWitness thingCount worldCount)
    (p : Fin pf.dimensionThings.size → Bool) :
    anyProductFamilyIndices pf p = true ↔ ∃ i, p i = true := by
  unfold anyProductFamilyIndices
  exact decide_eq_true_iff

private theorem anyProductFamilyWitness_eq_true_iff
    (M : FiniteModel4)
    (p : (pf : ProductFamilyWitness M.thingCount M.worldCount) → Bool) :
    anyProductFamilyWitness M p = true ↔
      ∃ i : Fin M.productFamilies.size, p (M.productFamilies[i]) = true := by
  unfold anyProductFamilyWitness
  exact decide_eq_true_iff

private theorem productFamilyWitnessB_sound
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    productFamilyWitnessB M pf x t w = true →
      productFamilyWitnessProp M pf x t w := by
  intro h
  unfold productFamilyWitnessB at h
  simp [allThings_eq_true_iff, allProductFamilyIndices_eq_true_iff,
    anyProductFamilyIndices_eq_true_iff, impliesB] at h
  rcases h with ⟨⟨⟨⟨hDomainType, hWorld⟩, hProduct⟩, hAssocChar⟩, hCover⟩
  rcases hDomainType with ⟨hDomain, hType⟩
  refine ⟨hDomain, hType, hWorld, ?_, hAssocChar, ?_⟩
  · intro p hp i
    exact ((hProduct p).resolve_left (by simp [hp])) i
  · intro u hu
    exact (hCover u).resolve_left (by simp [hu])

private theorem productFamilyWitnessB_complete
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    productFamilyWitnessProp M pf x t w →
      productFamilyWitnessB M pf x t w = true := by
  intro h
  rcases h with ⟨hDomain, hType, hWorld, hProduct, hAssocChar, hCover⟩
  unfold productFamilyWitnessB
  have hProductB :
      (allThings M fun p =>
        impliesB (M.memberOf p x w)
          (allProductFamilyIndices pf fun i =>
            M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w)) = true := by
    apply (allThings_eq_true_iff M _).2
    intro p
    unfold impliesB
    by_cases hp : M.memberOf p x w = true
    · have hAll :
          (allProductFamilyIndices pf fun i =>
            M.memberOf (M.tupleProjection p i w) (productFamilyDimensions pf i) w) = true := by
        apply (allProductFamilyIndices_eq_true_iff pf _).2
        intro i
        exact hProduct p hp i
      simp [hp, hAll]
    · cases hpm : M.memberOf p x w
      · simp
      · exact False.elim (hp hpm)
  have hAssocCharB :
      (allProductFamilyIndices pf fun i =>
        M.associatedWith (productFamilyDimensions pf i) (productFamilyTypes pf i) w &&
          M.characterization t (productFamilyTypes pf i) w) = true := by
    apply (allProductFamilyIndices_eq_true_iff pf _).2
    intro i
    simp [(hAssocChar i).1, (hAssocChar i).2]
  have hCoverB :
      (allThings M fun u =>
        impliesB (M.characterization t u w)
          (anyProductFamilyIndices pf fun i => decide (u = productFamilyTypes pf i))) = true := by
    apply (allThings_eq_true_iff M _).2
    intro u
    unfold impliesB
    by_cases hu : M.characterization t u w = true
    · rcases hCover u hu with ⟨i, hi⟩
      have hAny :
          (anyProductFamilyIndices pf fun i => decide (u = productFamilyTypes pf i)) = true := by
        apply (anyProductFamilyIndices_eq_true_iff pf _).2
        exact ⟨i, by simp [hi]⟩
      simp [hu, hAny]
    · cases hum : M.characterization t u w
      · simp
      · exact False.elim (hu hum)
  simp [hDomain, hType, hWorld, hProductB, hAssocCharB, hCoverB]

private theorem productFamilyWitnessB_correct
    (M : FiniteModel4) (pf : ProductFamilyWitness M.thingCount M.worldCount)
    (x t : Fin M.thingCount) (w : Fin M.worldCount) :
    productFamilyWitnessB M pf x t w = true ↔
      productFamilyWitnessProp M pf x t w :=
  ⟨productFamilyWitnessB_sound M pf x t w,
   productFamilyWitnessB_complete M pf x t w⟩

theorem checkAx99_correct_finite (M : FiniteModel4) :
    checkAx99 M = true ↔ ax99Finite M := by
  constructor
  · intro h x t w hprem
    unfold checkAx99 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have ht := (allThings_eq_true_iff M _).1 hx t
    have hw := (allWorlds_eq_true_iff M _).1 ht w
    unfold impliesB at hw
    simp [hprem.1, hprem.2] at hw
    rcases (anyProductFamilyWitness_eq_true_iff M _).1 hw with ⟨idx, hWitnessB⟩
    exact ⟨idx, (productFamilyWitnessB_correct M (M.productFamilies[idx]) x t w).1 hWitnessB⟩
  · intro h
    unfold checkAx99
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro t
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hDomainB : M.qualityDomain x w = true
    · by_cases hAssocB : M.associatedWith x t w = true
      · rcases h x t w ⟨hDomainB, hAssocB⟩ with ⟨idx, hWitness⟩
        have hWitnessB :=
          (productFamilyWitnessB_correct M (M.productFamilies[idx]) x t w).2 hWitness
        have hAny :
            anyProductFamilyWitness M (fun pf => productFamilyWitnessB M pf x t w) = true :=
          (anyProductFamilyWitness_eq_true_iff M _).2 ⟨idx, hWitnessB⟩
        simp [hDomainB, hAssocB, hAny]
      · cases ha : M.associatedWith x t w
        · simp [hDomainB]
        · exact False.elim (hAssocB ha)
    · cases hd : M.qualityDomain x w
      · simp
      · exact False.elim (hDomainB hd)

/--
Representation-completeness condition for ax99.

The core axiom `ax_a99` quantifies over arbitrary finite families
`ys zs : Fin n → Thing`. The reflective checker can only inspect the finite
`productFamilies` table stored in `FiniteModel4`. This condition states the
exact bridge needed for checker completeness: whenever the semantic axiom holds
for the compiled signature, the required witness can be represented by the
stored finite table checked by `checkAx99`.

This is stronger than merely having a `product_family` entry for each active
quality-domain association. Entry presence is useful diagnostic information;
this condition is the formal completeness contract.
-/
def ProductFamilyWitnessTableComplete (M : FiniteModel4) : Prop :=
  ax_a99 M.toUFOSignature4.toUFOSignature3_12 → ax99Finite M

theorem productFamilyWitnessTableComplete_of_finite
    (M : FiniteModel4) (h : ax99Finite M) :
    ProductFamilyWitnessTableComplete M := by
  intro _hAx99
  exact h

theorem checkAx99_complete_of_witness_table_complete
    (M : FiniteModel4) :
    ProductFamilyWitnessTableComplete M →
    ax_a99 M.toUFOSignature4.toUFOSignature3_12 →
    checkAx99 M = true := by
  intro hComplete hAx99
  exact (checkAx99_correct_finite M).2 (hComplete hAx99)

theorem not_ax99_of_checkAx99_false
    (M : FiniteModel4) :
    ProductFamilyWitnessTableComplete M →
    checkAx99 M = false →
    ¬ ax_a99 M.toUFOSignature4.toUFOSignature3_12 := by
  intro hComplete hFalse hAx99
  have hTrue := checkAx99_complete_of_witness_table_complete M hComplete hAx99
  rw [hFalse] at hTrue
  contradiction

theorem checkAx99_sound (M : FiniteModel4) :
    checkAx99 M = true → ax_a99 M.toUFOSignature4.toUFOSignature3_12 := by
  intro h x t w hprem
  unfold checkAx99 at h
  have hx := (allThings_eq_true_iff M _).1 h x
  have ht := (allThings_eq_true_iff M _).1 hx t
  have hw := (allWorlds_eq_true_iff M _).1 ht w
  have hDomainB : M.qualityDomain x w = true := by
    simpa [FiniteModel4.toUFOSignature4] using hprem.1
  have hAssocB : M.associatedWith x t w = true := by
    simpa [FiniteModel4.toUFOSignature4] using hprem.2
  unfold impliesB at hw
  simp [hDomainB, hAssocB] at hw
  rcases (anyProductFamilyWitness_eq_true_iff M _).1 hw with ⟨idx, hWitnessB⟩
  let pf := M.productFamilies[idx]
  have hWitness := productFamilyWitnessB_sound M pf x t w hWitnessB
  rcases hWitness with ⟨hDomain, hType, hWorld, hProduct, hAssocChar, hCover⟩
  subst hDomain
  subst hType
  subst hWorld
  refine ⟨pf.dimensionThings.size, productFamilyDimensions pf, productFamilyTypes pf, ?_, ?_, ?_⟩
  · intro p hp
    have hpB : M.memberOf p pf.domain pf.world = true := by
      simpa [FiniteModel4.toUFOSignature4] using hp
    intro i
    have hi := hProduct p hpB i
    simpa [FiniteModel4.toUFOSignature4] using hi
  · intro i
    exact ⟨by
      simpa [FiniteModel4.toUFOSignature4] using (hAssocChar i).1, by
      simpa [FiniteModel4.toUFOSignature4] using (hAssocChar i).2⟩
  · intro u hu
    have huB : M.characterization pf.qualityType u pf.world = true := by
      simpa [FiniteModel4.toUFOSignature4] using hu
    exact hCover u huB

theorem checkAx99_complete_of_product_family_witnesses (M : FiniteModel4) :
    (∀ (x t : Fin M.thingCount) (w : Fin M.worldCount),
      (M.qualityDomain x w = true ∧ M.associatedWith x t w = true) →
        ∃ i : Fin M.productFamilies.size,
          productFamilyWitnessB M (M.productFamilies[i]) x t w = true) →
      checkAx99 M = true := by
  intro h
  unfold checkAx99
  apply (allThings_eq_true_iff M _).2
  intro x
  apply (allThings_eq_true_iff M _).2
  intro t
  apply (allWorlds_eq_true_iff M _).2
  intro w
  unfold impliesB
  by_cases hDomainB : M.qualityDomain x w = true
  · by_cases hAssocB : M.associatedWith x t w = true
    · rcases h x t w ⟨hDomainB, hAssocB⟩ with ⟨idx, hWitnessB⟩
      have hAny : anyProductFamilyWitness M (fun pf => productFamilyWitnessB M pf x t w) = true :=
        (anyProductFamilyWitness_eq_true_iff M _).2 ⟨idx, hWitnessB⟩
      simp [hDomainB, hAssocB, hAny]
    · cases ha : M.associatedWith x t w
      · simp [hDomainB]
      · exact False.elim (hAssocB ha)
  · cases hd : M.qualityDomain x w
    · simp
    · exact False.elim (hDomainB hd)

private theorem checkAx100_correct (M : FiniteModel4) :
    checkAx100 M = true ↔ ax_a100 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x y r w hDistance
    unfold checkAx100 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hy := (allThings_eq_true_iff M _).1 hx y
    have hr := (allThings_eq_true_iff M _).1 hy r
    have hw := (allWorlds_eq_true_iff M _).1 hr w
    have hDistanceB : M.distance x y r w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hDistance
    have hw :
        (M.quale x w = true ∧ M.quale y w = true) ∧
          (anyThings M fun z => M.memberOf x z w && M.memberOf y z w) = true := by
      simpa [impliesB, hDistanceB] using hw
    rcases hw with ⟨⟨hxQual, hyQual⟩, hCommonB⟩
    rcases (anyThings_eq_true_iff M _).1 hCommonB with ⟨z, hz⟩
    simp at hz
    exact ⟨
      by simpa [FiniteModel4.toUFOSignature4] using hxQual,
      by simpa [FiniteModel4.toUFOSignature4] using hyQual,
      z,
      by simpa [FiniteModel4.toUFOSignature4, MemberOf] using hz.1,
      by simpa [FiniteModel4.toUFOSignature4, MemberOf] using hz.2⟩
  · intro h
    unfold checkAx100
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allThings_eq_true_iff M _).2
    intro r
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hDistance : M.distance x y r w = true
    · rcases h x y r w hDistance with ⟨hxQual, hyQual, z, hxMem, hyMem⟩
      have hxQualB : M.quale x w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hxQual
      have hyQualB : M.quale y w = true := by
        simpa [FiniteModel4.toUFOSignature4] using hyQual
      have hxMemB : M.memberOf x z w = true := by
        simpa [FiniteModel4.toUFOSignature4, MemberOf] using hxMem
      have hyMemB : M.memberOf y z w = true := by
        simpa [FiniteModel4.toUFOSignature4, MemberOf] using hyMem
      have hCommonB :
          (anyThings M fun z => M.memberOf x z w && M.memberOf y z w) = true := by
        apply (anyThings_eq_true_iff M _).2
        refine ⟨z, ?_⟩
        simp [hxMemB, hyMemB]
      simp [hDistance, hxQualB, hyQualB, hCommonB]
    · cases hd : M.distance x y r w
      · simp
      · exact False.elim (hDistance hd)

theorem checkAx100_sound (M : FiniteModel4) :
    checkAx100 M = true → ax_a100 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx100_correct M).1

theorem checkAx100_complete (M : FiniteModel4) :
    ax_a100 M.toUFOSignature4.toUFOSignature3_12 → checkAx100 M = true :=
  (checkAx100_correct M).2

private theorem checkAx101_correct (M : FiniteModel4) :
    checkAx101 M = true ↔ ax_a101 M.toUFOSignature4.toUFOSignature3_12 := by
  constructor
  · intro h x y w hQuals
    unfold checkAx101 at h
    have hx := (allThings_eq_true_iff M _).1 h x
    have hy := (allThings_eq_true_iff M _).1 hx y
    have hw := (allWorlds_eq_true_iff M _).1 hy w
    have hxQualB : M.quale x w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hQuals.1
    have hyQualB : M.quale y w = true := by
      simpa [FiniteModel4.toUFOSignature4] using hQuals.2
    have hwUnique :
        decide
          (∃ r : Fin M.thingCount,
            M.distance x y r w = true ∧
              ∀ r' : Fin M.thingCount, M.distance x y r' w = true → r' = r) = true := by
      simpa [impliesB, hxQualB, hyQualB] using hw
    simpa [FiniteModel4.toUFOSignature4, ExistsUnique] using
      (decide_eq_true_eq.mp hwUnique)
  · intro h
    unfold checkAx101
    apply (allThings_eq_true_iff M _).2
    intro x
    apply (allThings_eq_true_iff M _).2
    intro y
    apply (allWorlds_eq_true_iff M _).2
    intro w
    unfold impliesB
    by_cases hxQual : M.quale x w = true
    · by_cases hyQual : M.quale y w = true
      · have hUnique := h x y w ⟨hxQual, hyQual⟩
        have hUniqueTable :
            ∃ r : Fin M.thingCount,
              M.distance x y r w = true ∧
                ∀ r' : Fin M.thingCount, M.distance x y r' w = true → r' = r := by
          simpa [FiniteModel4.toUFOSignature4, ExistsUnique] using hUnique
        have hUniqueB :
            decide
              (∃ r : Fin M.thingCount,
                M.distance x y r w = true ∧
                  ∀ r' : Fin M.thingCount, M.distance x y r' w = true → r' = r) = true :=
          decide_eq_true hUniqueTable
        simp [hxQual, hyQual, hUniqueB]
      · cases hy : M.quale y w
        · simp [hxQual]
        · exact False.elim (hyQual hy)
    · cases hx : M.quale x w
      · simp
      · exact False.elim (hxQual hx)

theorem checkAx101_sound (M : FiniteModel4) :
    checkAx101 M = true → ax_a101 M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAx101_correct M).1

theorem checkAx101_complete (M : FiniteModel4) :
    ax_a101 M.toUFOSignature4.toUFOSignature3_12 → checkAx101 M = true :=
  (checkAx101_correct M).2

private theorem checkAxDistanceIdentity_correct (M : FiniteModel4) :
    checkAxDistanceIdentity M = true ↔ ax_distance_identity M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAxDistanceIdentity ax_distance_identity allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxDistanceIdentity_sound (M : FiniteModel4) :
    checkAxDistanceIdentity M = true → ax_distance_identity M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAxDistanceIdentity_correct M).1

theorem checkAxDistanceIdentity_complete (M : FiniteModel4) :
    ax_distance_identity M.toUFOSignature4.toUFOSignature3_12 → checkAxDistanceIdentity M = true :=
  (checkAxDistanceIdentity_correct M).2

private theorem checkAxDistanceSymmetry_correct (M : FiniteModel4) :
    checkAxDistanceSymmetry M = true ↔ ax_distance_symmetry M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAxDistanceSymmetry ax_distance_symmetry allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxDistanceSymmetry_sound (M : FiniteModel4) :
    checkAxDistanceSymmetry M = true → ax_distance_symmetry M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAxDistanceSymmetry_correct M).1

theorem checkAxDistanceSymmetry_complete (M : FiniteModel4) :
    ax_distance_symmetry M.toUFOSignature4.toUFOSignature3_12 → checkAxDistanceSymmetry M = true :=
  (checkAxDistanceSymmetry_correct M).2

private theorem checkAxDistanceTriangle_correct (M : FiniteModel4) :
    checkAxDistanceTriangle M = true ↔ ax_distance_triangle M.toUFOSignature4.toUFOSignature3_12 := by
  unfold checkAxDistanceTriangle ax_distance_triangle allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAxDistanceTriangle_sound (M : FiniteModel4) :
    checkAxDistanceTriangle M = true → ax_distance_triangle M.toUFOSignature4.toUFOSignature3_12 :=
  (checkAxDistanceTriangle_correct M).1

theorem checkAxDistanceTriangle_complete (M : FiniteModel4) :
    ax_distance_triangle M.toUFOSignature4.toUFOSignature3_12 → checkAxDistanceTriangle M = true :=
  (checkAxDistanceTriangle_correct M).2

private theorem checkAx102_correct (M : FiniteModel4) :
    checkAx102 M = true ↔ ax_a102 M.toUFOSignature4.toUFOSignature3_13 := by
  unfold checkAx102 ax_a102 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx102_sound (M : FiniteModel4) :
    checkAx102 M = true → ax_a102 M.toUFOSignature4.toUFOSignature3_13 :=
  (checkAx102_correct M).1

theorem checkAx102_complete (M : FiniteModel4) :
    ax_a102 M.toUFOSignature4.toUFOSignature3_13 → checkAx102 M = true :=
  (checkAx102_correct M).2

private theorem checkAx103_correct (M : FiniteModel4) :
    checkAx103 M = true ↔ ax_a103 M.toUFOSignature4.toUFOSignature3_13 := by
  unfold checkAx103 ax_a103 allThings allWorlds iffB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx103_sound (M : FiniteModel4) :
    checkAx103 M = true → ax_a103 M.toUFOSignature4.toUFOSignature3_13 :=
  (checkAx103_correct M).1

theorem checkAx103_complete (M : FiniteModel4) :
    ax_a103 M.toUFOSignature4.toUFOSignature3_13 → checkAx103 M = true :=
  (checkAx103_correct M).2

private theorem checkAx104_correct (M : FiniteModel4) :
    checkAx104 M = true ↔ ax_a104 M.toUFOSignature4.toUFOSignature3_13 := by
  unfold checkAx104 ax_a104 allThings allWorlds impliesB
  simp [FiniteModel4.toUFOSignature4]
  grind

theorem checkAx104_sound (M : FiniteModel4) :
    checkAx104 M = true → ax_a104 M.toUFOSignature4.toUFOSignature3_13 :=
  (checkAx104_correct M).1

theorem checkAx104_complete (M : FiniteModel4) :
    ax_a104 M.toUFOSignature4.toUFOSignature3_13 → checkAx104 M = true :=
  (checkAx104_correct M).2

private theorem checkAx105_correct (M : FiniteModel4) :
    checkAx105 M = true ↔ ax_a105 M.toUFOSignature4 := by
  unfold checkAx105 ax_a105
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx105_sound (M : FiniteModel4) :
    checkAx105 M = true → ax_a105 M.toUFOSignature4 :=
  (checkAx105_correct M).1

theorem checkAx105_complete (M : FiniteModel4) :
    ax_a105 M.toUFOSignature4 → checkAx105 M = true :=
  (checkAx105_correct M).2

private theorem checkAx106_correct (M : FiniteModel4) :
    checkAx106 M = true ↔ ax_a106 M.toUFOSignature4 := by
  unfold checkAx106 ax_a106
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx106_sound (M : FiniteModel4) :
    checkAx106 M = true → ax_a106 M.toUFOSignature4 :=
  (checkAx106_correct M).1

theorem checkAx106_complete (M : FiniteModel4) :
    ax_a106 M.toUFOSignature4 → checkAx106 M = true :=
  (checkAx106_correct M).2

private theorem checkAx107_correct (M : FiniteModel4) :
    checkAx107 M = true ↔ ax_a107 M.toUFOSignature4 := by
  unfold checkAx107 ax_a107
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx107_sound (M : FiniteModel4) :
    checkAx107 M = true → ax_a107 M.toUFOSignature4 :=
  (checkAx107_correct M).1

theorem checkAx107_complete (M : FiniteModel4) :
    ax_a107 M.toUFOSignature4 → checkAx107 M = true :=
  (checkAx107_correct M).2

private theorem checkAx108_correct (M : FiniteModel4) :
    checkAx108 M = true ↔ ax_a108 M.toUFOSignature4 := by
  unfold checkAx108 ax_a108
  simp [FiniteModel4.toUFOSignature4]

theorem checkAx108_sound (M : FiniteModel4) :
    checkAx108 M = true → ax_a108 M.toUFOSignature4 :=
  (checkAx108_correct M).1

theorem checkAx108_complete (M : FiniteModel4) :
    ax_a108 M.toUFOSignature4 → checkAx108 M = true :=
  (checkAx108_correct M).2

private theorem all_id_eq_true_of_mem {xs : List Bool} {b : Bool} :
    xs.all id = true → b ∈ xs → b = true := by
  intro hall hmem
  induction xs with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      cases hmem with
      | head =>
          exact hall.1
      | tail _ htail =>
          exact ih hall.2 htail

theorem checkAxioms4_sound (M : FiniteModel4) :
    checkAxioms4 M = true →
      UFOAxioms4 M.toUFOSignature4 := by
  intro h
  have hAll : (checkAxioms4Checks M).all id = true := by
    simpa [checkAxioms4] using h
  have hmem : ∀ b, b ∈ checkAxioms4Checks M → b = true :=
    fun b hb => all_id_eq_true_of_mem hAll hb
  have h1 : checkAx1 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h2 : checkAx2 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h3 : checkAx3 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h4 : checkAx4 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h5 : checkAx5 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h6 : checkAx6 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h7 : checkAx7 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h8 : checkAx8 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h9 : checkAx9 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h10 : checkAx10 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h11 : checkAx11 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h12 : checkAx12 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h13 : checkAx13 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h14 : checkAx14 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h15 : checkAx15 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h16 : checkAx16 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h17 : checkAx17 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h18 : checkAx18 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h19 : checkAx19 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h20 : checkAx20 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h21 : checkAx21 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h22 : checkAx22 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h23 : checkAx23 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h24 : checkAx24 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h25 : checkAx25 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h26 : checkAx26 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h27 : checkAx27 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h28 : checkAx28 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h29 : checkAx29 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h30 : checkAx30 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h31 : checkAx31 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h32 : checkAx32 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h33 : checkAx33 M = true := hmem _ (by simp [checkAxioms4Checks])
  have hInstEndurant : checkAxInstEndurant M = true := hmem _ (by simp [checkAxioms4Checks])
  have hSubKindSortal : checkAxSubKindSortal M = true := hmem _ (by simp [checkAxioms4Checks])
  have hNonSortalUp : checkAxNonSortalUp M = true := hmem _ (by simp [checkAxioms4Checks])
  have hKindStable : checkAxKindStable M = true := hmem _ (by simp [checkAxioms4Checks])
  have h34 : checkAx34 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h35 : checkAx35 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h36 : checkAx36 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h37 : checkAx37 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h38 : checkAx38 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h39 : checkAx39 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h40 : checkAx40 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h41 : checkAx41 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h42 : checkAx42 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h43 : checkAx43 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h44 : checkAx44 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h45 : checkAx45 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h46 : checkAx46 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h47 : checkAx47 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h48 : checkAx48 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h49 : checkAx49 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h50 : checkAx50 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h51 : checkAx51 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h52 : checkAx52 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h53 : checkAx53 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h54 : checkAx54 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h55 : checkAx55 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h56 : checkAx56 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h57 : checkAx57 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h58 : checkAx58 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h59 : checkAx59 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h60 : checkAx60 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h61 : checkAx61 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h62 : checkAx62 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h63 : checkAx63 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h64 : checkAx64 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h65 : checkAx65 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h66 : checkAx66 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h67 : checkAx67 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h68 : checkAx68 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h69 : checkAx69 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h70 : checkAx70 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h71 : checkAx71 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h72 : checkAx72 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h73 : checkAx73 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h74 : checkAx74 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h75 : checkAx75 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h76 : checkAx76 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h77 : checkAx77 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h78 : checkAx78 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h79 : checkAx79 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h80 : checkAx80 M = true := hmem _ (by simp [checkAxioms4Checks])
  have hQuaEnd : checkAxQuaIndividualOfEndurant M = true := hmem _ (by simp [checkAxioms4Checks])
  have h81 : checkAx81 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h82 : checkAx82 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h83 : checkAx83 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h84 : checkAx84 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h85 : checkAx85 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h86 : checkAx86 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h87 : checkAx87 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h88 : checkAx88 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h89 : checkAx89 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h90 : checkAx90 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h91 : checkAx91 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h92 : checkAx92 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h93 : checkAx93 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h94 : checkAx94 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h95 : checkAx95 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h96 : checkAx96 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h97 : checkAx97 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h98 : checkAx98 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h99 : checkAx99 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h100 : checkAx100 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h101 : checkAx101 M = true := hmem _ (by simp [checkAxioms4Checks])
  have hDistId : checkAxDistanceIdentity M = true := hmem _ (by simp [checkAxioms4Checks])
  have hDistSymm : checkAxDistanceSymmetry M = true := hmem _ (by simp [checkAxioms4Checks])
  have hDistTri : checkAxDistanceTriangle M = true := hmem _ (by simp [checkAxioms4Checks])
  have h102 : checkAx102 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h103 : checkAx103 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h104 : checkAx104 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h105 : checkAx105 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h106 : checkAx106 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h107 : checkAx107 M = true := hmem _ (by simp [checkAxioms4Checks])
  have h108 : checkAx108 M = true := hmem _ (by simp [checkAxioms4Checks])
  exact {
    ax1 := checkAx1_sound M h1
    ax2 := checkAx2_sound M h2
    ax3 := checkAx3_sound M h3
    ax4 := checkAx4_sound M h4
    ax5 := checkAx5_sound M h5
    ax6 := checkAx6_sound M h6
    ax7 := checkAx7_sound M h7
    ax8 := checkAx8_sound M h8
    ax9 := checkAx9_sound M h9
    ax10 := checkAx10_sound M h10
    ax11 := checkAx11_sound M h11
    ax12 := checkAx12_sound M h12
    ax13 := checkAx13_sound M h13
    ax14 := checkAx14_sound M h14
    ax15 := checkAx15_sound M h15
    ax16 := checkAx16_sound M h16
    ax17 := checkAx17_sound M h17
    ax18 := checkAx18_sound M h18
    ax19 := checkAx19_sound M h19
    ax20 := checkAx20_sound M h20
    ax21 := checkAx21_sound M h21
    ax22 := checkAx22_sound M h22
    ax23 := checkAx23_sound M h23
    ax24 := checkAx24_sound M h24
    ax25 := checkAx25_sound M h25
    ax26 := checkAx26_sound M h26
    ax27 := checkAx27_sound M h27
    ax28 := checkAx28_sound M h28
    ax29 := checkAx29_sound M h29
    ax30 := checkAx30_sound M h30
    ax31 := checkAx31_sound M h31
    ax32 := checkAx32_sound M h32
    ax33 := checkAx33_sound M h33
    ax_instEndurant := checkAxInstEndurant_sound M hInstEndurant
    ax_sub_kind_sortal := checkAxSubKindSortal_sound M hSubKindSortal
    ax_nonSortal_up := checkAxNonSortalUp_sound M hNonSortalUp
    ax_kindStable := checkAxKindStable_sound M hKindStable
    ax34 := checkAx34_sound M h34
    ax35 := checkAx35_sound M h35
    ax36 := checkAx36_sound M h36
    ax37 := checkAx37_sound M h37
    ax38 := checkAx38_sound M h38
    ax39 := checkAx39_sound M h39
    ax40 := checkAx40_sound M h40
    ax41 := checkAx41_sound M h41
    ax42 := checkAx42_sound M h42
    ax43 := checkAx43_sound M h43
    ax44 := checkAx44_sound M h44
    ax45 := checkAx45_sound M h45
    ax46 := checkAx46_sound M h46
    ax47 := checkAx47_sound M h47
    ax48 := checkAx48_sound M h48
    ax49 := checkAx49_sound M h49
    ax50 := checkAx50_sound M h50
    ax51 := checkAx51_sound M h51
    ax52 := checkAx52_sound M h52
    ax53 := checkAx53_sound M h53
    ax54 := checkAx54_sound M h54
    ax55 := checkAx55_sound M h55
    ax56 := checkAx56_sound M h56
    ax57 := checkAx57_sound M h57
    ax58 := checkAx58_sound M h58
    ax59 := checkAx59_sound M h59
    ax60 := checkAx60_sound M h60
    ax61 := checkAx61_sound M h61
    ax62 := checkAx62_sound M h62
    ax63 := checkAx63_sound M h63
    ax64 := checkAx64_sound M h64
    ax65 := checkAx65_sound M h65
    ax66 := checkAx66_sound M h66
    ax67 := checkAx67_sound M h67
    ax68 := checkAx68_sound M h68
    ax69 := checkAx69_sound M h69
    ax70 := checkAx70_sound M h70
    ax71 := checkAx71_sound M h71
    ax72 := checkAx72_sound M h72
    ax73 := checkAx73_sound M h47 h50 h72 h75 h73
    ax74 := checkAx74_sound M h74
    ax75 := checkAx75_sound M h75
    ax76 := checkAx76_sound M h76
    ax77 := checkAx77_sound M h77
    ax78 := checkAx78_sound M h48 h52 h72 h75 h77 h79 h78
    ax79 := checkAx79_sound M h72 h75 h79
    ax80 := checkAx80_sound M h80
    axQuaIndividualOfEndurant := checkAxQuaIndividualOfEndurant_sound M hQuaEnd
    ax81 := checkAx81_sound M h81
    ax82 := checkAx82_sound M h82
    ax83 := checkAx83_sound M h83
    ax84 := checkAx84_sound M h84
    ax85 := checkAx85_sound M h85
    ax86 := checkAx86_sound M h86
    ax87 := checkAx87_sound M h87
    ax88 := checkAx88_sound M h88
    ax89 := checkAx89_sound M h89
    ax90 := checkAx90_sound M h90
    ax91 := checkAx91_sound M h91
    ax92 := checkAx92_sound M h92
    ax93 := checkAx93_sound M h93
    ax94 := checkAx94_sound M h94
    ax95 := checkAx95_sound M h95
    ax96 := checkAx96_sound M h96
    ax97 := checkAx97_sound M h97
    ax98 := checkAx98_sound M h98
    ax99 := checkAx99_sound M h99
    ax100 := checkAx100_sound M h100
    ax101 := checkAx101_sound M h101
    axDistanceIdentity := checkAxDistanceIdentity_sound M hDistId
    axDistanceSymmetry := checkAxDistanceSymmetry_sound M hDistSymm
    axDistanceTriangle := checkAxDistanceTriangle_sound M hDistTri
    ax102 := checkAx102_sound M h102
    ax103 := checkAx103_sound M h103
    ax104 := checkAx104_sound M h104
    ax105 := checkAx105_sound M h105
    ax106 := checkAx106_sound M h106
    ax107 := checkAx107_sound M h107
    ax108 := checkAx108_sound M h108
  }

theorem checkAxiomsPilot_sound (M : FiniteModel4) :
    checkAxiomsPilot M = true →
      ax_a7 M.toUFOSignature4.toUFOSignature3_1 ∧
      ax_a13 M.toUFOSignature4.toUFOSignature3_1 ∧
      ax_a61 M.toUFOSignature4.toUFOSignature3_7 ∧
      ax_a71 M.toUFOSignature4.toUFOSignature3_10 ∧
      ax_a77 M.toUFOSignature4.toUFOSignature3_10 := by
  intro h
  simp only [checkAxiomsPilot, Bool.and_eq_true] at h
  exact ⟨checkAx7_sound M (by grind), checkAx13_sound M (by grind),
    checkAx61_sound M (by grind), checkAx71_sound M (by grind),
    checkAx77_sound M (by grind)⟩

end Checker
end LeanUfo.UFO.DSL
