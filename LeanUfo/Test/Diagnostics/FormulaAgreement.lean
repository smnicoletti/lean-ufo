import LeanUfo.UFO.DSL.Syntax

/-!
# Diagnostic formula agreement

Compare every registered generic diagnostic formula with its production
checker on 200 deterministic finite tables. Both true and false relations,
including tables that violate earlier axioms, occur in this regression.
Specialized diagnostic searches have separate witness fixtures.
-/
open LeanUfo.UFO.DSL
open private diagnosticFormula? diagnosticFormulaRegistry evalDiagFormula DiagAtom DiagFormula
  from LeanUfo.UFO.DSL.Diagnostic.AxiomAnalysis

/-- A registered axiom must never reach the assertion-string fallback. -/
private def usesComputedAtoms : DiagFormula → Bool
  | DiagFormula.atom (DiagAtom.derivedUnary field _ _) =>
      #["ExternallyDependentMode", "QuaIndividual"].contains field
  | DiagFormula.atom (DiagAtom.derivedBinary field _ _ _) =>
      #["ExistentialDependence", "ExistentialIndependence", "ExternallyDependent",
        "GenericFunctionalDependence", "GenericConstitutionalDependence"].contains field
  | DiagFormula.atom (DiagAtom.quaternary ..) => false
  | DiagFormula.atom _ | DiagFormula.eqThing .. | DiagFormula.eqWorld .. => true
  | DiagFormula.not p => usesComputedAtoms p
  | DiagFormula.and p q | DiagFormula.or p q | DiagFormula.imp p q | DiagFormula.iff p q =>
      usesComputedAtoms p && usesComputedAtoms q
  | DiagFormula.forallThing _ p | DiagFormula.forallWorld _ p |
      DiagFormula.existsThing _ p | DiagFormula.existsWorld _ p |
      DiagFormula.box _ _ p | DiagFormula.dia _ _ p => usesComputedAtoms p

private def sampleFacts (seed : Nat) : Array CompiledFact := Id.run do
  let mut state := seed + 1
  let mut facts := #[]
  for field in UnaryField.all do
    for x in [:2] do
      for w in [:2] do
        state := (1664525 * state + 1013904223) % 4294967296
        if state % 11 < seed % 10 then facts := facts.push (.unary field x w)
  for field in BinaryField.all do
    for x in [:2] do
      for y in [:2] do
        for w in [:2] do
          state := (1664525 * state + 1013904223) % 4294967296
          if state % 11 < seed % 10 then facts := facts.push (.binary field x y w)
  for field in TernaryField.all do
    for x in [:2] do
      for y in [:2] do
        for z in [:2] do
          for w in [:2] do
            state := (1664525 * state + 1013904223) % 4294967296
            if state % 11 < seed % 10 then facts := facts.push (.ternary field x y z w)
  return facts

#eval show IO Unit from do
  unless diagnosticFormulaRegistry.all (fun entry => usesComputedAtoms entry.2) do
    throw <| IO.userError "a registered diagnostic formula uses assertion presence as semantic truth"
  let mut mismatches : Array (String × Nat × Bool × Bool) := #[]
  let mut comparisons := 0
  for seed in [:200] do
    let tables := compileExplicitModelAST { worldCount := 2, thingCount := 2, facts := sampleFacts seed }
    let model := tables.toFiniteModel4 2 2 (by decide) (by decide)
    let answers := (Checker.checkAxioms4Checks model).toArray
    for h : i in [:certFields.size] do
      let field := CertField.field certFields[i]
      if let some formula := diagnosticFormula? field then
        let diagnostic := evalDiagFormula 2 2 tables #[] formula
        comparisons := comparisons + 1
        if diagnostic != answers[i]! && !(mismatches.any fun row => row.1 == field) then
          mismatches := mismatches.push (field, seed, answers[i]!, diagnostic)
  unless comparisons == 20800 && mismatches.isEmpty do
    throw <| IO.userError s!"Diagnostic/checker mismatch after {comparisons} comparisons: {mismatches}"
