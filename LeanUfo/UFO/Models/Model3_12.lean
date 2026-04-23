import LeanUfo.UFO.Core.Section3_12
import LeanUfo.UFO.Models.Model3_11

universe u

namespace Model3_12

/-
  A concrete model for UFO §3.12 (Qualities and quality structures).

  Design choice (minimal extension of Model3_11):
  we reuse the same tiny domain and single-world S5 frame from `Model3_11.sig3_11`
  and interpret the new quality-structure layer in the smallest way compatible
  with axioms (a83)–(a101).

  Intuition:
  - the inherited witness has no qualities, no quality types, no quality kinds,
    no moments, no inherence, and no characterization facts,
  - therefore quales, quality structures, quality domains, quality dimensions,
    quality values, simple/complex qualities, and distances can all be empty,
  - Lean-set extensions are empty for every entity,
  - tuple projections are irrelevant because there are no quality domains.
-/

/--
Signature interpretation for §3.12 extending the §3.11 concrete signature.

The witness still has the same two entities:
- `K`, the unique type/kind,
- `I`, the unique individual, with `I :: K` as the only instantiation fact.

All previous layers remain unchanged. For the new §3.12 layer we choose the
minimal compatible interpretation:
- `Quale`, `Set_`, `QualityStructure`, `QualityDomain`, `QualityDimension`,
  `AssociatedWith`, `IntrinsicMomentType`, `HasValue`, `SimpleQuality`,
  `ComplexQuality`, `SimpleQualityType`, `ComplexQualityType`, and `Distance`
  are empty,
- `SetExtension` is the empty Lean set for every UFO entity,
- `TupleProjection` is arbitrary, because no product-subset obligations arise,
- distance-zero, distance-sum, and distance-order relations are empty.

Since all antecedents requiring the new positive structure are false, the
§3.12 axioms hold vacuously or by the inherited emptiness of `Quality` and
`QualityType`.
-/
def sig3_12 : UFOSignature3_12.{0,0} :=
{ toUFOSignature3_11 := Model3_11.sig3_11

  Quale := fun _x _w => False
  Set_ := fun _x _w => False
  SetExtension := fun _x _w => ∅

  QualityStructure := fun _x _w => False
  QualityDomain := fun _x _w => False
  QualityDimension := fun _x _w => False
  AssociatedWith := fun _x _y _w => False

  IntrinsicMomentType := fun _x _w => False
  HasValue := fun _x _y _w => False

  SimpleQuality := fun _x _w => False
  ComplexQuality := fun _x _w => False
  SimpleQualityType := fun _x _w => False
  ComplexQualityType := fun _x _w => False

  TupleProjection := fun {_n} p _i _w => p

  Distance := fun _x _y _r _w => False
  DistanceZero := fun _r _w => False
  DistanceSum := fun _r0 _r1 _s _w => False
  DistanceGreaterEq := fun _s _r _w => False
}

attribute [simp] sig3_12

/-- Proof that `sig3_12` satisfies (a83). -/
theorem ax83_sig3_12 : ax_a83 sig3_12 := by
  unfold ax_a83
  intro x w h
  cases w
  cases x <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a84). -/
theorem ax84_sig3_12 : ax_a84 sig3_12 := by
  unfold ax_a84
  intro x w h
  cases w
  cases x <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a85). -/
theorem ax85_sig3_12 : ax_a85 sig3_12 := by
  unfold ax_a85
  intro w h
  cases w
  rcases h with ⟨x, hQuale, _hSet⟩
  cases x <;> simp [sig3_12] at hQuale

/-- Proof that `sig3_12` satisfies (a86). -/
theorem ax86_sig3_12 : ax_a86 sig3_12 := by
  unfold ax_a86
  intro x w h
  cases w
  cases x <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a87). -/
theorem ax87_sig3_12 : ax_a87 sig3_12 := by
  unfold ax_a87
  intro x w
  cases w
  cases x <;> simp [sig3_12]

/-- Proof that `sig3_12` satisfies (a88). -/
theorem ax88_sig3_12 : ax_a88 sig3_12 := by
  unfold ax_a88
  intro x w
  cases w
  cases x <;> simp [sig3_12]

/-- Proof that `sig3_12` satisfies (a89). -/
theorem ax89_sig3_12 : ax_a89 sig3_12 := by
  unfold ax_a89
  intro x w h
  cases w
  cases x <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a90). -/
theorem ax90_sig3_12 : ax_a90 sig3_12 := by
  unfold ax_a90
  intro s t s' t' w h
  cases w
  cases s <;> cases t <;> cases s' <;> cases t' <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a91). -/
theorem ax91_sig3_12 : ax_a91 sig3_12 := by
  unfold ax_a91
  intro t w
  cases w
  cases t <;> simp [sig3_12, Model3_11.sig3_11, Model3_10.sig3_10, Model3_9.sig3_9,
    Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5,
    Model3_4.sig3_4, Model3_3.sig3_3, Model3_2.sig3_2]

/-- Proof that `sig3_12` satisfies (a92). -/
theorem ax92_sig3_12 : ax_a92 sig3_12 := by
  unfold ax_a92
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a93). -/
theorem ax93_sig3_12 : ax_a93 sig3_12 := by
  unfold ax_a93
  intro x w h
  cases w
  cases x <;> simp [sig3_12, Model3_11.sig3_11, Model3_10.sig3_10, Model3_9.sig3_9,
    Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5,
    Model3_4.sig3_4, Model3_3.sig3_3, Model3_2.sig3_2] at h

/-- Proof that `sig3_12` satisfies (a94). -/
theorem ax94_sig3_12 : ax_a94 sig3_12 := by
  unfold ax_a94
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a95). -/
theorem ax95_sig3_12 : ax_a95 sig3_12 := by
  unfold ax_a95
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a96). -/
theorem ax96_sig3_12 : ax_a96 sig3_12 := by
  unfold ax_a96
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a97). -/
theorem ax97_sig3_12 : ax_a97 sig3_12 := by
  unfold ax_a97
  intro x y z Y Z w h
  cases w
  cases x <;> cases y <;> cases z <;> cases Y <;> cases Z <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a98). -/
theorem ax98_sig3_12 : ax_a98 sig3_12 := by
  unfold ax_a98
  intro x w h
  cases w
  cases x <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a99). -/
theorem ax99_sig3_12 : ax_a99 sig3_12 := by
  unfold ax_a99
  intro x t w h
  cases w
  cases x <;> cases t <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a100). -/
theorem ax100_sig3_12 : ax_a100 sig3_12 := by
  unfold ax_a100
  intro x y r w h
  cases w
  cases x <;> cases y <;> cases r <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies (a101). -/
theorem ax101_sig3_12 : ax_a101 sig3_12 := by
  unfold ax_a101
  intro x y w h
  cases w
  cases x <;> cases y <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies the distance identity constraint. -/
theorem ax_distance_identity_sig3_12 : ax_distance_identity sig3_12 := by
  unfold ax_distance_identity
  intro x y r w h
  cases w
  cases x <;> cases y <;> cases r <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies the distance symmetry constraint. -/
theorem ax_distance_symmetry_sig3_12 : ax_distance_symmetry sig3_12 := by
  unfold ax_distance_symmetry
  intro x y r w h
  cases w
  cases x <;> cases y <;> cases r <;> simp [sig3_12] at h

/-- Proof that `sig3_12` satisfies the distance triangle constraint. -/
theorem ax_distance_triangle_sig3_12 : ax_distance_triangle sig3_12 := by
  unfold ax_distance_triangle
  intro x y z r0 r1 r2 s w h
  cases w
  cases x <;> cases y <;> cases z <;> cases r0 <;> cases r1 <;> cases r2 <;> cases s <;>
    simp [sig3_12] at h

/-- Consistency witness: a concrete model of UFO subsection 3.12. -/
instance : UFOAxioms3_12 sig3_12 :=
by
  classical

  have h11 : UFOAxioms3_11 sig3_12.toUFOSignature3_11 := by
    simpa [sig3_12] using (inferInstance : UFOAxioms3_11 Model3_11.sig3_11)

  refine
  { toUFOAxioms3_11 := h11
    -- §3.12 axioms
    ax83 := ax83_sig3_12
    ax84 := ax84_sig3_12
    ax85 := ax85_sig3_12
    ax86 := ax86_sig3_12
    ax87 := ax87_sig3_12
    ax88 := ax88_sig3_12
    ax89 := ax89_sig3_12
    ax90 := ax90_sig3_12
    ax91 := ax91_sig3_12
    ax92 := ax92_sig3_12
    ax93 := ax93_sig3_12
    ax94 := ax94_sig3_12
    ax95 := ax95_sig3_12
    ax96 := ax96_sig3_12
    ax97 := ax97_sig3_12
    ax98 := ax98_sig3_12
    ax99 := ax99_sig3_12
    ax100 := ax100_sig3_12
    ax101 := ax101_sig3_12
    axDistanceIdentity := ax_distance_identity_sig3_12
    axDistanceSymmetry := ax_distance_symmetry_sig3_12
    axDistanceTriangle := ax_distance_triangle_sig3_12
  }

end Model3_12
