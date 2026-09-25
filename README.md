# Lean UFO Core Mechanization

## Overview

This artifact contains the Lean 4 formal material for the paper *A Lean
Mechanization of the Unified Foundational Ontology*. It covers the modal
semantics, the cumulative UFO axioms through Section 3.13 and Section 4, the
derived theorems (t1)--(t33), concrete satisfiability witnesses and the formal
analyses reported in the paper.

## Results and source map

| Paper material | Lean source | What Lean checks |
| --- | --- | --- |
| Modal semantics | [`LeanUfo/UFO/Modal/`](LeanUfo/UFO/Modal/) | Kripke frames, semantic modal operators and S5 frame properties |
| UFO formalization | [`LeanUfo/UFO/Core/`](LeanUfo/UFO/Core/) | Signatures, numbered axioms and theorems (t1)--(t33) |
| Joint satisfiability | [`FormalAnalysis/Satisfiability/`](LeanUfo/UFO/FormalAnalysis/Satisfiability/) | Concrete models for the cumulative axiom packages |
| Axiom analysis | [`FormalAnalysis/AxiomaticAnalysis.lean`](LeanUfo/UFO/FormalAnalysis/AxiomaticAnalysis.lean) and [`StructuralAssumptions.lean`](LeanUfo/UFO/FormalAnalysis/StructuralAssumptions.lean) | Consequences, assumption dependencies and finite countermodels |
| Relator analysis | [`FormalAnalysis/Satisfiability/Relator/`](LeanUfo/UFO/FormalAnalysis/Satisfiability/Relator/) and [`Historical/`](LeanUfo/UFO/FormalAnalysis/Historical/) | Nonempty relator witnesses and comparison with earlier candidate repairs |
| Anti-vacuity checks | [`FormalAnalysis/AntiVacuity/`](LeanUfo/UFO/FormalAnalysis/AntiVacuity/) | Section-local models that inhabit the predicates examined in the paper |

The files preserve the cumulative organization of the source UFO
formalization. Each `Signature` file introduces a fragment's vocabulary. The
corresponding `Section` file states its axioms and theorems. Later sections
extend the earlier signatures and axiom packages.

## Requirements

The artifact fixes these dependencies:

- Lean `v4.34.0`, selected by [`lean-toolchain`](lean-toolchain)
- Mathlib `v4.34.0`, selected by [`lakefile.toml`](lakefile.toml)
- Git and the [Elan](https://github.com/leanprover/elan) Lean toolchain manager

The first build downloads Lean and Mathlib if they are not already installed.
It therefore requires network access and additional disk space for those
dependencies.

## Installation

Clone the repository and select the immutable artifact tag:

```bash
git clone https://github.com/smnicoletti/lean-ufo.git
cd lean-ufo
git switch --detach core-mechanization-v1.0.0
```

Elan reads `lean-toolchain` and selects the required Lean release. Lake obtains
the fixed Mathlib dependency during the first build.

## Verify the artifact

Run the complete build from the repository root:

```bash
lake build
```

A successful build means that Lean elaborated every imported declaration and
that its kernel accepted the resulting proof terms. The root module
[`LeanUfo.lean`](LeanUfo.lean) imports the complete artifact through
[`CoreMechanization.lean`](LeanUfo/UFO/CoreMechanization.lean).

You can also build a result group directly:

```bash
lake build LeanUfo.UFO.FormalAnalysis.Satisfiability.Consistency
lake build LeanUfo.UFO.FormalAnalysis.StructuralAssumptions
lake build LeanUfo.UFO.FormalAnalysis.AntiVacuity.AntiVacuity
```

These commands check smaller import closures. The complete `lake build` command
is the reproduction command for the artifact as a whole.

## Reading routes

To inspect the semantic basis, start with `Modal/Basics.lean`, `Modal/S5.lean`
and `Core/Signature3_1.lean`. To follow the UFO reconstruction, read the
numbered `Signature` and `Section` files in order, ending with `Section4.lean`.

For the evidence that each cumulative package has a model, read
`FormalAnalysis/Satisfiability/Consistency.lean` and then the referenced model
files. For the analysis of additional assumptions and the relator axioms, read
`AxiomaticAnalysis.lean`, `StructuralAssumptions.lean` and the `Relator`
directory. The `AntiVacuity` directory contains the section-local nonemptiness
witnesses.

## What the checks establish

The development represents UFO semantics directly in Lean. Worlds and things
are Lean types. Predicates and relations are fields of signatures, and modal
operators quantify over an explicit accessibility relation. The current UFO
signatures use constant-domain S5 frames.

The numbered axioms are propositions packaged as typeclasses. A concrete model
must provide a proof of every axiom in the relevant package. The satisfiability
results exhibit such models. The theorem files prove the stated consequences
from the named packages and any assumptions shown in their declarations.

These results are relative to the Lean encoding and Lean's logic. Kernel
checking does not establish that the encoding is the only possible reading of
the source formulas. The correspondence between the published formulas and
their Lean statements remains subject to scholarly inspection. The paper
documents the semantic choices and the justified corrections made during the
reconstruction.

## Trust and limitations

The trusted base includes Lean's kernel, the Lean toolchain and the imported
Mathlib definitions. Tactics can construct proof terms, but the kernel checks
those terms before accepting a theorem. Concrete finite models support the
satisfiability and countermodel results.

This archive does not provide a separate syntactic calculus for quantified S5,
a completeness proof for such a calculus or a proof that the Lean encoding is
textually identical to the source publication.

## Citation and preservation

The reserved archival DOI is
[`10.5281/zenodo.22961487`](https://doi.org/10.5281/zenodo.22961487). Citation
metadata is available in [`CITATION.cff`](CITATION.cff).

GitHub provides readable, tag-pinned source links for the paper. Zenodo stores
the deposited ZIP and its checksum. The archive tag is
`core-mechanization-v1.0.0`.

## License

The artifact is distributed under the [GNU Affero General Public License,
version 3](LICENSE).
