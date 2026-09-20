# Provenance

The Lean source is synchronized from `formalization/magnitude_conjecture`
in the owner-directed `homological-conjectures` research repository at commit
`62b5468c3` (2026-09-20). The complete graded-interval proof replaces the
previous F1 implementation, with 199 obsolete modules removed after dependency
checks. The canonical full library, source and axiom audits pass; the current
standalone build and independent replay results are recorded in
[verification](docs/VERIFICATION.md).

The standalone repository was initially extracted from research commit
`20ebfbcf9f83e359425a89bf5b8980e3ad7054e6` on 2026-09-07. Compiled artifacts
are not transferred as source; this checkout builds its own project modules.

The manuscript target is the September 20 snapshot at research commit
`4404dea52deec5a0dc20dddf1ac8204b620ecb6a`, TeX blob
`3f2273a3faf11d226ec2a131a902ff05664f9ebf`. Its SHA-256 is
`8941be673f965879cae99484353ce50f6a05a6b8f3649229570976eedab5e5b8`.
The [paper correspondence](docs/PAPER-CORRESPONDENCE.md) maps this fixed proof
to Lean and describes the final-map formulation of almost-split transfer.
Later exposition revisions do not change the recorded target.

The owner and responsible maintainer is Haruhisa Enomoto. The formalization was
developed using AI coding agents under his direction. The independent
statement, presentation equivalences, graded-interval migration, release interface, and
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
