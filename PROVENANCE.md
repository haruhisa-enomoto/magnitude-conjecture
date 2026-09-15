# Provenance

The Lean source is synchronized from the magnitude-conjecture package of the
owner-directed `homological-conjectures` research repository, at canonical
commit `d0831ee92` (2026-09-15). That checkpoint completes the migration to the
frozen F1 proof route, removes the superseded endpoint modules, and passes the
canonical public, full-library, axiom, source, Challenge/Solution, and
independent-kernel checks.

The standalone repository was initially extracted from canonical commit
`20ebfbcf9f83e359425a89bf5b8980e3ad7054e6` on 2026-09-07. This synchronization
replaces its production Lean tree with the complete F1 checkpoint. The source
package path is `formalization/magnitude_conjecture`. No compiled Lean artifacts
or research checkout caches are part of the transferred source; the standalone
build downloads the pinned dependency cache and compiles its own project
modules.

The mathematical source is Haruhisa Enomoto's frozen September 10 manuscript
checkpoint. Its canonical repository commit is
`6d9095121c8cafac4b97e9dfabf1f6bc9b6519e5`, and the frozen proof source has Git
blob `c4d50a6257aab1c0368ccbc2ba618d1e389367fe`. The
[paper correspondence](docs/PAPER-CORRESPONDENCE.md) maps that proof route to
the synchronized Lean modules. Later exposition edits do not change which
proof checkpoint this release records.

The owner and responsible maintainer is Haruhisa Enomoto. The formalization was
developed using AI coding agents under his direction. The independent
statement, presentation equivalences, F1 migration, release interface, and
website were prepared by Codex using GPT-6. A complete model-by-model history
and total cost for the inherited development have not been reconstructed.

The proof package pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Its only external Lake dependency is
Mathlib. The [vendored-source record](VENDORED.md) identifies reused
equidistribution foundations, local adaptations, and their licence.

The mathematical website's CSS is adapted from the same owner's
quotient-submodule-equidistribution website. The remaining website pages and
build script were written for this project. The root Apache-2.0 licence covers
this repository; cited mathematical sources retain their own rights.

The metadata validator and verification shell scripts are adapted from
PalomarRegistry/PalomarTemplate commit
`128a6c5ce5f48622e69927ccd639cbff401022e8`, under Apache-2.0. The verifier uses
the project's exact Lean patch toolchain; the exporter qualification is
recorded in `docs/VERIFICATION.md`.

No public release, website deployment, or Palomar registration has been made.
