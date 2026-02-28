import LeanUfo.UFO.Models.Model3_1
import LeanUfo.UFO.Models.Model3_2
/--
Consistency checkpoint for UFO subsection 3.1 (relative to Lean):
axioms (a1)–(a17) are jointly satisfiable.
-/
theorem consistent_3_1 :
  ∃ (Sig : UFOSignature3_1.{0,0}),
    UFOAxioms3_1 Sig :=
by
  refine ⟨Model3_1.sig3_1, ?_⟩
  infer_instance
/--
Consistency checkpoint for UFO subsection 3.2 (relative to Lean):
axioms (a18)-(a33) + structural assumptions for (t10), (t11), (t14), (t16)
are jointly satisfiable.
-/

theorem consistent_3_2 :
  ∃ (Sig : UFOSignature3_2.{0,0}),
    UFOAxioms3_2 Sig :=
by
  refine ⟨Model3_2.sig3_2, ?_⟩
  infer_instance
