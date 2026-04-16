import LeanUfo.UFO.Models.Model3_1
import LeanUfo.UFO.Models.Model3_2
import LeanUfo.UFO.Models.Model3_3
import LeanUfo.UFO.Models.Model3_4
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
axioms (a1)-(a33) + structural assumptions for (t10), (t11), (t14), (t16)
are jointly satisfiable.
-/

theorem consistent_3_2 :
  ∃ (Sig : UFOSignature3_2.{0,0}),
    UFOAxioms3_2 Sig :=
by
  refine ⟨Model3_2.sig3_2, ?_⟩
  infer_instance

/--
Consistency checkpoint for UFO subsection 3.3 (relative to Lean):
axioms (a1)-(a43) + structural assumptions for (t10), (t11), (t14), (t16)
are jointly satisfiable.
-/

theorem consistent_3_3 :
  ∃ (Sig : UFOSignature3_3.{0,0}),
    UFOAxioms3_3 Sig :=
by
  refine ⟨Model3_3.sig3_3, ?_⟩
  infer_instance

/--
Consistency checkpoint for UFO subsection 3.4 (relative to Lean):
axioms (a1)-(a46) + inherited structural assumptions from §3.2
are jointly satisfiable.
-/
theorem consistent_3_4 :
  ∃ (Sig : UFOSignature3_4.{0,0}),
    UFOAxioms3_4 Sig :=
by
  refine ⟨Model3_4.sig3_4, ?_⟩
  infer_instance
