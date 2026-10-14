# Included software and licence notices

ALIEN's source is distributed under `AGPL-3.0-or-later`; the complete text is
in the repository's `LICENSE`. `COMMERCIAL-LICENSE.md` describes the separate
commercial licensing option. This notice does not change either licence.

The images retain the installed toolchain, dependency sources, and their
licence notices. `lake-manifest.json` records the exact Lean-library revisions.
In an unpacked image, their notices are under
`/workspace/alien/.lake/packages/PACKAGE/LICENSE`. The Zenodo source archive includes
the same dependency sources and notices in `artifact/dependency-sources.tar.gz`.

| Component | Licence notice location |
| --- | --- |
| ALIEN / Lean UFO | `/workspace/alien/LICENSE` |
| Mathlib, Batteries, Aesop, Qq, ProofWidgets, Plausible, ImportGraph, LeanSearchClient | Each package's `LICENSE` under `.lake/packages/` |
| Lean CLI library | `.lake/packages/Cli/LICENSE` |
| Lean toolchain and bundled components | The toolchain distribution under `/home/reviewer/.elan/toolchains/` |
| Ubuntu packages, including TeX and native compilation tools | `/usr/share/doc/PACKAGE/copyright` and `/usr/share/common-licenses/` |

`/opt/alien/system-packages.txt` records installed Ubuntu package versions.
Upstream software retains its own licence terms; ALIEN's licence does not
relicense it. Packaging removes download caches, not these source files or
notices.
