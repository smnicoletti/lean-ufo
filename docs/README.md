# Documentation

This directory is the canonical documentation home for Lean UFO.

Lean UFO's documentation is split by reading task: orientation, modeling,
diagnostics, tests, and implementation details.

## Guide Map

| Page | Use It For |
| --- | --- |
| [Project overview](overview.md) | What the project formalizes and how the DSL fits |
| [Theoretical notes](theory.md) | Modal choices, formal milestones, relator diagnosis and repair analysis, S5 consequences, and explicit bridge axioms |
| [DSL quickstart](dsl/quickstart.md) | Writing and certifying a first finite model |
| [DSL syntax reference](dsl/syntax.md) | Facts, scopes, derived assertions, and quality/distance primitives |
| [DSL architecture](dsl/architecture.md) | DSL directory ownership, import direction, syntax-to-certificate pipeline, checker, and diagnostics |
| [Concrete complexity](dsl/complexity.md) | Operational cost model, explicit encoding, verified-DSL theorem map, and literature |
| [Diagnostics guide](dsl/diagnostics.md) | Reading failure boxes, evidence, suggestions, and probe status |
| [Diagnostics internals](dsl/diagnostics-internals.md) | How failed certificates are turned into source-level explanations |
| [DSL developer guide](dsl/developer-guide.md) | File responsibilities, command pipeline, diagnostics, and generated certificates |
| [Testing guide](testing.md) | `lake test`, selected axiom checks, and witness coverage |
| [Current status](status.md) | Implemented features and current caveats |
| [Project architecture](architecture.md) | Core formalization, DSL layer, certificates, tests, and trust boundary |
| [Formal guarantees](guarantees.md) | The theorem-backed guarantees for core, DSL, checker, reuse, diagnostics, and complexity |
| [Roadmap and limitations](roadmap.md) | Known gaps and planned work |

## Reading Paths

### First Pass

1. [Project overview](overview.md)
2. [Theoretical notes](theory.md)
3. [DSL quickstart](dsl/quickstart.md)
4. [Diagnostics guide](dsl/diagnostics.md)
5. [Testing guide](testing.md)
6. [Current status](status.md)

### Implementation Pass

1. [Project architecture](architecture.md)
2. [Formal guarantees](guarantees.md)
3. [Theoretical notes](theory.md)
4. [DSL architecture](dsl/architecture.md)
5. [Concrete complexity](dsl/complexity.md)
6. [DSL developer guide](dsl/developer-guide.md)
7. [Diagnostics internals](dsl/diagnostics-internals.md)
8. [DSL syntax reference](dsl/syntax.md)
9. [Roadmap and limitations](roadmap.md)

## Core Commands

```bash
lake build
lake test
LEANUFO_AXIOMS=ax66 lake test
```

[Project README](../README.md)
