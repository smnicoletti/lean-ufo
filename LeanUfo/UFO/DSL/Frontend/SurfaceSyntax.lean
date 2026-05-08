import Lean

/-!
# Surface syntax for the finite UFO DSL

This module owns only the parser-facing grammar for `ufo_model` commands.  It
does not interpret names, compile tables, derive relations, emit diagnostics, or
prove certificates.  Keeping the grammar separate makes it easier to inspect the
accepted user-facing language without reading the elaborator.
-/

namespace LeanUfo.UFO.DSL

declare_syntax_cat ufoFact
syntax (name := ufoInstFact) ident "::" ident : ufoFact
syntax (name := ufoSubFact) ident "⊑" ident : ufoFact
syntax (name := ufoUnaryFact) ident "(" ident ")" : ufoFact
syntax (name := ufoBinaryFact) ident "(" ident "," ident ")" : ufoFact
syntax (name := ufoTernaryFact) ident "(" ident "," ident "," ident ")" : ufoFact
syntax (name := ufoQuaternaryFact) ident "(" ident "," ident "," ident "," ident ")" : ufoFact
syntax (name := ufoTupleProjectionFact) "TupleProjection" "(" ident "," num "," ident ")" : ufoFact

declare_syntax_cat ufoFactBlock
syntax (name := ufoGivenAt) "given" ident ":" ppLine ufoFact* : ufoFactBlock

declare_syntax_cat ufoDeriveDirective
syntax (name := ufoDeriveRelations) "derive_relations" : ufoDeriveDirective

declare_syntax_cat ufoCertDirective
syntax (name := ufoCertify) "certify" : ufoCertDirective

syntax (name := ufoModelCmd)
  "ufo_model" ident ":" "UFO" "where"
  ppLine "worlds" ident+
  ppLine "things" ident+
  ppLine ufoFactBlock+
  ppLine ufoDeriveDirective
  ppLine ufoCertDirective : command

end LeanUfo.UFO.DSL
