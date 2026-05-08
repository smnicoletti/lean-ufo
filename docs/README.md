# Documentation

This directory is the canonical documentation home for Lean UFO.

Lean UFO's documentation is split by reading task: orientation, modeling,
diagnostics, tests, and implementation details.

## Guide Map

| Page | Use It For |
| --- | --- |
| [Project overview](overview.md) | What the project formalizes and how the DSL fits |
| [Theoretical notes](theory.md) | Modal choices, formal milestones, S5 consequences, and explicit bridge axioms |
| [DSL quickstart](dsl/quickstart.md) | Writing and certifying a first finite model |
| [DSL syntax reference](dsl/syntax.md) | Facts, scopes, derived assertions, and quality/distance primitives |
| [Diagnostics guide](dsl/diagnostics.md) | Reading failure boxes, evidence, suggestions, and probe status |
| [Diagnostics internals](dsl/diagnostics-internals.md) | How failed certificates are turned into source-level explanations |
| [DSL developer guide](dsl/developer-guide.md) | File responsibilities, command pipeline, diagnostics, and generated certificates |
| [Testing guide](testing.md) | `lake test`, selected axiom checks, and witness coverage |
| [Current status](status.md) | Implemented features and current caveats |
| [Architecture and trust boundary](architecture.md) | Compiler pipeline and generated Lean declarations |
| [Formal guarantees](guarantees.md) | The theorem-backed parts of the DSL pipeline |
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

1. [Architecture and trust boundary](architecture.md)
2. [Formal guarantees](guarantees.md)
3. [Theoretical notes](theory.md)
4. [DSL developer guide](dsl/developer-guide.md)
5. [Diagnostics internals](dsl/diagnostics-internals.md)
6. [DSL syntax reference](dsl/syntax.md)
7. [Roadmap and limitations](roadmap.md)

## Core Commands

```bash
lake build
lake test
LEANUFO_AXIOMS=ax66 lake test
```

[Project README](../README.md)
