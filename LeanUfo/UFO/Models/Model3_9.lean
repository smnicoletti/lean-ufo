import LeanUfo.UFO.Core.Section3_9
import LeanUfo.UFO.Models.Model3_8

universe u

namespace Model3_9

/-
  A concrete model for UFO §3.9 (Moments and inherence).

  Design choice (minimal extension of Model3_8):
  we reuse the same tiny domain and single-world S5 frame from `Model3_8.sig3_8`
  and interpret inherence as empty.

  Intuition:
  - there are still no moments in the inherited witness,
  - so the inherence relation can be taken empty,
  - consequently `MomentOf` has no instances and `UltimateBearerOf` is empty,
  - the axioms about inherence and ultimate bearers then hold vacuously.
-/

/--
Signature interpretation for §3.9 extending the §3.8 concrete signature.

The witness still has exactly the same tiny structure:
- `K`, the unique type/kind,
- `I`, the unique individual, with `I :: K` as the only instantiation fact.

All earlier layers remain unchanged:
- there is only one world,
- `I` is an endurant and there are no perdurants,
- there are no moments in the inherited witness,
- mereology, composition, constitution, and existential-dependence are
  interpreted exactly as in §§3.5–3.8.

For the new §3.9 layer we interpret `InheresIn` as empty. Since there are no
moments at all, this is the smallest possible witness:
- no entity directly inheres in any other,
- hence no `MomentOf` chains arise,
- and `UltimateBearerOf` is never instantiated.
-/
def sig3_9 : UFOSignature3_9.{0,0} :=
{ toUFOSignature3_8 := Model3_8.sig3_8

  InheresIn := fun _x _y _w => False
}

attribute [simp] sig3_9

/-- Proof that `sig3_9` satisfies (a65). -/
theorem ax65_sig3_9 : ax_a65 sig3_9 := by
  unfold ax_a65
  intro x y w h
  cases h

/-- Proof that `sig3_9` satisfies (a66). -/
theorem ax66_sig3_9 : ax_a66 sig3_9 := by
  unfold ax_a66
  intro x y w h
  cases h

/-- Proof that `sig3_9` satisfies (a67). -/
theorem ax67_sig3_9 : ax_a67 sig3_9 := by
  unfold ax_a67
  intro x y z w h
  exact False.elim h.1

/-- Proof that `sig3_9` satisfies (a68). -/
theorem ax68_sig3_9 : ax_a68 sig3_9 := by
  unfold ax_a68
  intro m w hMom
  cases w
  cases m <;> simp [sig3_9, Model3_8.sig3_8, Model3_7.sig3_7, Model3_6.sig3_6, Model3_5.sig3_5, Model3_4.sig3_4, Model3_3.sig3_3, Model3_2.sig3_2] at hMom

/-- Consistency witness: a concrete model of UFO subsection 3.9. -/
instance : UFOAxioms3_9 sig3_9 :=
by
  classical

  have h8 : UFOAxioms3_8 sig3_9.toUFOSignature3_8 := by
    change UFOAxioms3_8 Model3_8.sig3_8
    infer_instance

  refine
  { toUFOAxioms3_8 := h8
    -- §3.9 axioms
    ax65 := ax65_sig3_9
    ax66 := ax66_sig3_9
    ax67 := ax67_sig3_9
    ax68 := ax68_sig3_9
  }

end Model3_9
