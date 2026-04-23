import LeanUfo.UFO.Core.Section3_11
import LeanUfo.UFO.Models.Model3_10

universe u

namespace Model3_11

/-
  A concrete model for UFO §3.11 (Characterization).

  Design choice (minimal extension of Model3_10):
  we reuse the same tiny domain and single-world S5 frame from `Model3_10.sig3_10`
  and interpret characterization as empty.

  Intuition:
  - the inherited witness has no moments, no moment types beyond the empty
    interpretation, no quality types, and no inherence facts,
  - therefore the characterization relation can be taken empty,
  - axioms (a81) and (a82) then hold vacuously.
-/

/--
Signature interpretation for §3.11 extending the §3.10 concrete signature.

The witness still has the same two entities:
- `K`, the unique type/kind,
- `I`, the unique individual, with `I :: K` as the only instantiation fact.

All previous layers remain unchanged. For the new §3.11 layer we interpret
`Characterization` as empty.
-/
def sig3_11 : UFOSignature3_11.{0,0} :=
{ toUFOSignature3_10 := Model3_10.sig3_10

  Characterization := fun _t _m _w => False
}

attribute [simp] sig3_11

/-- Proof that `sig3_11` satisfies (a81). -/
theorem ax81_sig3_11 : ax_a81 sig3_11 := by
  unfold ax_a81
  intro t m w hChar
  cases hChar

/-- Proof that `sig3_11` satisfies (a82). -/
theorem ax82_sig3_11 : ax_a82 sig3_11 := by
  unfold ax_a82
  intro t q w h
  exact False.elim h.1

/-- Consistency witness: a concrete model of UFO subsection 3.11. -/
instance : UFOAxioms3_11 sig3_11 :=
by
  classical

  have h10 : UFOAxioms3_10 sig3_11.toUFOSignature3_10 := by
    change UFOAxioms3_10 Model3_10.sig3_10
    infer_instance

  refine
  { toUFOAxioms3_10 := h10
    -- §3.11 axioms
    ax81 := ax81_sig3_11
    ax82 := ax82_sig3_11
  }

end Model3_11
