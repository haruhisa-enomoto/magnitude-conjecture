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

The manuscript target is *Magnitude of module categories and special biserial
algebras*, frozen September 29 from research commit
`e091a2d056470e49366a64650e1504d3d151df85`, manuscript commit
`ea7d79800044d5a007679ced5bf7115b62140631` and TeX blob
`7fa94a158b16b701cd1b315793ca6d56d85a9a3e`. Its SHA-256 is
`1e76449d38b7884215ff02d7b41c39227b670b469902013b5b97aadb3f27ae36`.
The [frozen manuscript](docs/manuscript/README.md) contains the exact TeX,
33-page PDF and manifest. The [paper correspondence](docs/PAPER-CORRESPONDENCE.md)
maps the main theorem's dependencies in six sections and Appendix A to Lean.
It explicitly limits generalized manuscript statements to the special cases
needed by the main theorem, including beta transfer to one control interval.
This target supersedes September 21; the Lean source and its historical build
and replay records are unchanged. Later live revisions do not move the target.

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

The owner made the repository public on September 21, 2026, and authorized
GitHub Pages publication. The [website](https://haruhisa-enomoto.github.io/magnitude-conjecture/)
is delivered by the Pages workflow from checked generated files on `gh-pages`.
The website records its source and API revisions. No Palomar registration has
been made.
