# Provenance

The Lean source was extracted from the magnitude-conjecture package of the
owner-directed `homological-conjectures` research repository, at commit
`20ebfbcf9f83e359425a89bf5b8980e3ad7054e6` (2026-09-07). That snapshot includes
the complete production proof, the direct simple/projective count connection,
and the independent Mathlib-only theorem statement.

The extraction includes the complete library, not just a theorem wrapper.
The source package path was `formalization/magnitude_conjecture`. No compiled
Lean artifacts or research checkout caches are part of the extracted source.
The standalone build downloads the pinned dependency cache and compiles its
own project modules.

The owner and responsible maintainer is Haruhisa Enomoto. The formalization
was developed using AI coding agents under his direction. The independent
statement, presentation equivalences, release interface, and website were
prepared by Codex using GPT-6. A complete model-by-model history and total
cost for the inherited development have not been reconstructed.

The proof package pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Its only external Lake dependency is
Mathlib. The [vendored-source record](VENDORED.md) identifies reused
equidistribution foundations, local adaptations, and their licence.

The mathematical website's CSS is adapted from the same owner's
quotient-submodule-equidistribution website. The remaining website pages and
build script were written for this project. The root Apache-2.0 licence
covers this repository; cited mathematical sources retain their own rights.

The [paper correspondence](docs/PAPER-CORRESPONDENCE.md) identifies the
read-only manuscript checkpoint and known differences. No manuscript revision
was performed as part of this extraction. No public release, website
deployment, or Palomar registration has been made.

The metadata validator and verification shell scripts are adapted from
PalomarRegistry/PalomarTemplate commit
`128a6c5ce5f48622e69927ccd639cbff401022e8`, under Apache-2.0. The verifier uses
the project's exact Lean patch toolchain; the exporter qualification is
recorded in `docs/VERIFICATION.md`.
