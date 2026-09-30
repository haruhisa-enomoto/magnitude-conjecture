# Provenance

The Lean development is maintained by Haruhisa Enomoto and proves the main
theorem of *Magnitude of module categories and special biserial algebras*.
The [manuscript](docs/manuscript/README.md) is the September 30, 2026 revision,
from source commit `e327fbcf1b75a3f6986f4f29d5afe5089e384297`. Its manifest
records the exact TeX and PDF hashes; the
[correspondence](docs/PAPER-CORRESPONDENCE.md) describes formal coverage.

The proof sources originate in `formalization/magnitude_conjecture` in the
`homological-conjectures` research repository at commit `62b5468c3`.
The [source manifest](verification/2026-09-20/source-sync.json) records their
hashes. Complete builds, axiom checks and independent kernel replay are
documented in [Verification](docs/VERIFICATION.md).

## Contributions

The formalization was developed with AI coding agents under Haruhisa Enomoto's
direction. The independent statement, presentation equivalences, graded-interval
implementation, release interface and website have recorded contributions
from Codex using GPT-6. The manuscript contains the author's account of AI
contributions to the research and formalization. A complete model-by-model
history and total cost of the development have not been reconstructed.

## Dependencies and licences

The proof package pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib is its only external Lake
dependency. The [vendored-source record](VENDORED.md) identifies categorical
foundations adapted from quotient-submodule-equidistribution, their local
modifications and licence.

The website's CSS is adapted from Haruhisa Enomoto's
quotient-submodule-equidistribution website. The remaining pages and build
script were written for this project. The repository uses the Apache-2.0
licence; cited mathematical sources retain their own rights.

The metadata validator and verification shell scripts are adapted from
PalomarRegistry/PalomarTemplate commit
`128a6c5ce5f48622e69927ccd639cbff401022e8`, under Apache-2.0.
The verifier's toolchain and exporter qualification are recorded in
[Verification](docs/VERIFICATION.md).

The website records its documentation and API source revisions in
[build.json](https://haruhisa-enomoto.github.io/magnitude-conjecture/build.json).
