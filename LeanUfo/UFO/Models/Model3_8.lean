import LeanUfo.UFO.Core.Section3_8
import LeanUfo.UFO.Models.Model3_7

universe u

namespace Model3_8

/-
  A concrete model for UFO §3.8 (Existence and existential dependence).

  Design choice (minimal extension of Model3_7):
  we reuse the same tiny domain and single-world S5 frame from `Model3_7.sig3_7`
  and interpret existential dependence exactly by the right-hand side of (a63).

  Intuition:
  - `Ex` is already total in `Model3_7`,
  - therefore `ExistentialDependence` becomes total as well,
  - and `ExistentialIndependence` is empty, since no ordered pair fails
    existential dependence in either direction.
-/

/--
Signature interpretation for §3.8 extending the §3.7 concrete signature.

The witness again has the same tiny domain inherited from the previous models:
- `K`, the unique type in the model; it is an `EndurantType`, a rigid `Sortal`,
  and in particular a `Kind`,
- `I`, the unique individual in the model; it is the unique instance of `K`,
  hence an `Endurant`.

The earlier structure is still the same:
- `I :: K` is the only instantiation fact,
- there are no perdurants,
- the mereological relations are still interpreted minimally (`Part` and
  `Overlap` collapse to identity, `ProperPart` is empty),
- the composition predicates are minimal as in §3.6 (`FunctionsAs` empty,
  `ComponentOf` empty),
- the constitution predicates are minimal as in §3.7 (`ConstitutedBy` empty,
  `Constitution` empty, and `GCD` true only vacuously for instance-empty
  arguments).

There is only one world, and `Ex` is total on both `K` and `I`. Therefore the
modal condition `□(Ex(x) → Ex(y))` is always true for every pair `x, y`, so:
- existential dependence is total,
- existential independence is empty.
-/
def sig3_8 : UFOSignature3_8.{0,0} :=
{ toUFOSignature3_7 := Model3_7.sig3_7

  /-
    We interpret existential dependence exactly by the defining modal clause
    from (a63): `x` depends on `y` iff, at every accessible world, existence
    of `x` implies existence of `y`.

    Since `Ex` is total in `sig3_7` and the frame has only one world, this box
    condition is always true in the present witness.
  -/
  ExistentialDependence := fun x y w =>
    Frame.Box (F := Model3_7.sig3_7.F)
      (fun w' => Model3_7.sig3_7.Ex x w' → Model3_7.sig3_7.Ex y w')
      w

  /-
    We interpret existential independence exactly as in (a64): neither `x`
    depends on `y` nor `y` depends on `x`.

    Because existential dependence is total in this witness, both negated box
    clauses are always false, so existential independence is empty.
  -/
  ExistentialIndependence := fun x y w =>
    ¬ Frame.Box (F := Model3_7.sig3_7.F)
        (fun w' => Model3_7.sig3_7.Ex x w' → Model3_7.sig3_7.Ex y w')
        w ∧
    ¬ Frame.Box (F := Model3_7.sig3_7.F)
        (fun w' => Model3_7.sig3_7.Ex y w' → Model3_7.sig3_7.Ex x w')
        w
}

attribute [simp] sig3_8

/-- Proof that `sig3_8` satisfies (a62). -/
theorem ax62_sig3_8 : ax_a62 sig3_8 := by
  unfold ax_a62
  intro x w hEx
  trivial

/-- Proof that `sig3_8` satisfies (a63). -/
theorem ax63_sig3_8 : ax_a63 sig3_8 := by
  unfold ax_a63
  intro x y w
  rfl

/-- Proof that `sig3_8` satisfies (a64). -/
theorem ax64_sig3_8 : ax_a64 sig3_8 := by
  unfold ax_a64
  intro x y w
  rfl

/-- Consistency witness: a concrete model of UFO subsection 3.8. -/
instance : UFOAxioms3_8 sig3_8 :=
by
  classical

  have h7 : UFOAxioms3_7 sig3_8.toUFOSignature3_7 := by
    change UFOAxioms3_7 Model3_7.sig3_7
    infer_instance

  refine
  { toUFOAxioms3_7 := h7
    -- §3.8 axioms
    ax62 := ax62_sig3_8
    ax63 := ax63_sig3_8
    ax64 := ax64_sig3_8
  }

end Model3_8
