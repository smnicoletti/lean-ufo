import LeanUfo.UFO.Core.Section3_6
import LeanUfo.UFO.Models.Model3_5

universe u

namespace Model3_6

/-
  A concrete model for UFO §3.6 (Composition).

  Design choice (minimal extension of Model3_5):
  we reuse the same tiny domain and single-world S5 frame from `Model3_5.sig3_5`
  and interpret the new composition predicates in the smallest way compatible
  with axioms (a53)–(a55).

  Intuition:
  - nothing in the tiny witness `FunctionsAs` any type,
  - therefore the universal condition in (a53) is vacuously true for every pair
    of types, so `GenericFunctionalDependence` is total,
  - `IndividualFunctionalDependence` is then determined only by actual
    instantiation in the model,
  - `ComponentOf` is empty because `ProperPart` is already empty in `Model3_5`.
-/

/--
Signature interpretation for §3.6 extending the §3.5 concrete signature.

The witness again reuses the same two entities:
- `K`, the unique type/kind,
- `I`, the unique individual instantiating `K`.

The previously fixed structure remains unchanged:
- there is only one world,
- `I :: K` is the only instantiation fact,
- `I` is an endurant and there are no perdurants,
- mereology is still degenerate as in §3.5 (`Part` and `Overlap` are identity,
  `ProperPart` is empty).

For the new composition layer we interpret:
- `FunctionsAs` as empty, so nothing plays any functional role,
- `GenericFunctionalDependence` as universally true, since the universal clause
  in (a53) becomes vacuously satisfied,
- `IndividualFunctionalDependence` exactly by the right-hand side of (a54),
- `ComponentOf` as empty, because `ProperPart` is already empty.

So this witness validates the composition axioms in the most minimal way:
there are no actual components, and all generic functional dependence claims
hold only vacuously.
-/
def sig3_6 : UFOSignature3_6.{0,0} :=
{ toUFOSignature3_5 := Model3_5.sig3_5

  FunctionsAs := fun _x _t _w => False

  GenericFunctionalDependence := fun _x' _y' _w => True

  IndividualFunctionalDependence := fun x x' y y' w =>
    True ∧
    Model3_5.sig3_5.Inst x x' w ∧
    Model3_5.sig3_5.Inst y y' w ∧
    (False → False)

  ComponentOf := fun _x _x' _y _y' _w => False
}

attribute [simp] sig3_6

/-- Proof that `sig3_6` satisfies (a53). -/
theorem ax53_sig3_6 : ax_a53 sig3_6 := by
  unfold ax_a53
  intro x' y' w
  constructor
  · intro _ x hx
    simp [sig3_6] at hx
  · intro _
    trivial

/-- Proof that `sig3_6` satisfies (a54). -/
theorem ax54_sig3_6 : ax_a54 sig3_6 := by
  unfold ax_a54
  intro x x' y y' w
  simp [sig3_6]

/-- Proof that `sig3_6` satisfies (a55). -/
theorem ax55_sig3_6 : ax_a55 sig3_6 := by
  unfold ax_a55
  intro x x' y y' w
  cases w
  constructor
  · intro h
    cases h
  · intro h
    exact False.elim h.1

/-- Consistency witness: a concrete model of UFO subsection 3.6. -/
instance : UFOAxioms3_6 sig3_6 :=
by
  classical

  have h5 : UFOAxioms3_5 sig3_6.toUFOSignature3_5 := by
    change UFOAxioms3_5 Model3_5.sig3_5
    infer_instance

  refine
  { toUFOAxioms3_5 := h5
    -- §3.6 axioms
    ax53 := ax53_sig3_6
    ax54 := ax54_sig3_6
    ax55 := ax55_sig3_6
  }

end Model3_6
