# The magnitude conjecture for module categories

Let A be a finite-dimensional representation-finite algebra over an
algebraically closed field k. Its rational Hom-dimension matrix on
indecomposable right-module representatives is invertible. The sum of its
inverse entries is at least the number of simple-module isomorphism classes,
with equality exactly when the basic algebra of A is special biserial.
There is no characteristic or basicness restriction on A.

This repository contains the complete Lean proof and a mathematical website.
The source theorem is the magnitude conjecture of Børve, Horiatakis, and Kalck,
as proved in Haruhisa Enomoto's manuscript *The magnitude conjecture for module
categories*. See [paper correspondence](docs/PAPER-CORRESPONDENCE.md) for the
recorded manuscript revision and known exposition discrepancies.

## Start reading

- [Independent definitions](MagnitudeConjecture/Statement.lean): Mathlib-only
  vocabulary for the full theorem.
- [Main theorem](MagnitudeConjecture/Algebra/StatementTheorem.lean):
  `MagnitudeConjecture.Statement.mainClaim` and the exact presentation equivalence.
- [Public entry point](MagnitudeConjecture/MainResults.lean): the theorem,
  direct simple count, and simple/projective bijection.
- [Proof guide](website/pages/proof.html) and [provenance](PROVENANCE.md).

The independent [Challenge](Challenge.lean) is generated from Statement.lean.
It has one deliberate theorem placeholder for Comparator. [Solution](Solution.lean)
supplies its proof and never imports the Challenge. All production definitions
and proofs are complete, with only `propext`, `Classical.choice`, and `Quot.sound`.

## Build and verify

Lean is pinned to 4.33.1; the committed manifest pins Mathlib. Mathlib is the
only external dependency of the proof package. Reused categorical source and
its licence are recorded in [VENDORED.md](VENDORED.md).

```sh
lake exe cache get
python3 scripts/build_lean_serial.py --package . --output .build-audit/public \
  --max-rss-kib 8388608 MagnitudeConjecture.MainResults \
  MagnitudeConjecture.PublicAxiomAudit
python3 scripts/build_lean_serial.py --package . --output .build-audit/full \
  --max-rss-kib 8388608 MagnitudeConjecture MagnitudeConjecture.AxiomAudit
python3 scripts/build_lean_serial.py --package . --output .build-audit/statement \
  --max-rss-kib 8388608 Challenge Solution
python3 scripts/generate_challenge.py --check
```

Run one build at a time. The helper compiles Lake's dependency frontier
serially and records memory and timing. A fresh full build is substantial;
subsequent builds reuse current artifacts. Do not commit `.lake/`.

[Comparator configuration](comparator.json) requests statement matching and
NanoDa replay, with only the three standard axioms permitted. The current
results and toolchain qualifications are recorded in [verification](docs/VERIFICATION.md).
A compiling Challenge/Solution pair alone is not an independent replay result.

## Website and API

```sh
python3 scripts/build_website.py
python3 -m http.server 8000 --directory _site --bind 127.0.0.1
```

The website reads the actual Challenge source and records the source commit.
Generate the API through the separate [docbuild project](docbuild/README.md),
then rebuild the site. The doc-gen4 dependency does not enter the proof package.

The repository remains private during preparation. Public release, website
deployment, and optional Palomar registration are separate later steps.
