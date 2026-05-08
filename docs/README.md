# Documentation

This directory is the canonical documentation home for Lean UFO.

Lean UFO's documentation is split by reading task: orientation, modeling,
diagnostics, tests, and implementation details.

## Guide Map

| Page | Use It For |
| --- | --- |
| [Project overview](overview.md) | What the project formalizes and how the DSL fits |
| [DSL quickstart](dsl/quickstart.md) | Writing and certifying a first finite model |
| [DSL syntax reference](dsl/syntax.md) | Facts, scopes, derived assertions, and quality/distance primitives |
| [Diagnostics guide](dsl/diagnostics.md) | Reading failure boxes, evidence, suggestions, and probe status |
| [Testing guide](testing.md) | `lake test`, selected axiom checks, and witness coverage |
| [Current status](status.md) | Implemented features and current caveats |
| [Architecture and trust boundary](architecture.md) | Compiler pipeline and generated Lean declarations |
| [Formal guarantees](guarantees.md) | The theorem-backed parts of the DSL pipeline |
| [Roadmap and limitations](roadmap.md) | Known gaps and planned work |

## Reading Paths

### First Pass

1. [Project overview](overview.md)
2. [DSL quickstart](dsl/quickstart.md)
3. [Diagnostics guide](dsl/diagnostics.md)
4. [Testing guide](testing.md)
5. [Current status](status.md)

### Implementation Pass

1. [Architecture and trust boundary](architecture.md)
2. [Formal guarantees](guarantees.md)
3. [DSL syntax reference](dsl/syntax.md)
4. [Roadmap and limitations](roadmap.md)

## Core Commands

```bash
lake build
lake test
LEANUFO_AXIOMS=ax66 lake test
```

[Project README](../README.md)
