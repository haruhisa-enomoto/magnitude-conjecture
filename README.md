# The magnitude conjecture for module categories

Let A be a finite-dimensional representation-finite algebra over an
algebraically closed field k. Its rational Hom-dimension matrix on
indecomposable right-module representatives is invertible. The sum of its
inverse entries is at least the number of simple-module isomorphism classes,
with equality exactly when the basic algebra of A is special biserial.
There is no characteristic or basicness restriction on A.

This repository contains the complete Lean proof and a mathematical website.
The result resolves the magnitude conjecture of
[Børve, Horiatakis, and Kalck](https://arxiv.org/abs/2607.07555v1),
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
- [Website instructions](website/README.md) and [provenance](PROVENANCE.md).

The independent [Challenge](Challenge.lean) is generated from Statement.lean.
It has one deliberate theorem placeholder for Comparator. [Solution](Solution.lean)
supplies its proof and never imports the Challenge. All production definitions
and proofs are complete, with only `propext`, `Classical.choice`, and `Quot.sound`.

The implementation follows the frozen September 10 F1 manuscript route. Its
central step is a finite-support incidence argument: local deletion changes are
averaged over deletion orders and transported through source-orbit
representatives. The F1 inequality and equality layers then connect this
positive average to the primitive quotient and special-biserial
characterization. The earlier algebra-level covering-average and
finite-convex equality modules have been removed; Git retains their history.

## Build and verify

Lean is pinned to 4.33.1; the committed manifest pins Mathlib. Mathlib is the
only external dependency of the proof package. Reused categorical source and
its licence are recorded in [VENDORED.md](VENDORED.md). The commands below
were tested on Linux/WSL2. The serial helper requires Python 3, GNU time, and
`ps`.

```sh
lake exe cache get
python3 scripts/build_lean_serial.py --package . --output .build-audit/public \
  --max-rss-kib 12582912 MagnitudeConjecture.MainResults \
  MagnitudeConjecture.PublicAxiomAudit
python3 scripts/build_lean_serial.py --package . --output .build-audit/full \
  --max-rss-kib 12582912 MagnitudeConjecture MagnitudeConjecture.AxiomAudit
python3 scripts/build_lean_serial.py --package . --output .build-audit/statement \
  --max-rss-kib 12582912 Challenge Solution
python3 scripts/generate_challenge.py --check
python3 scripts/audit_axioms.py
python3 scripts/audit_axioms.py --full
```

Run one build at a time. The helper compiles Lake's dependency frontier
serially and records memory and timing. A fresh full build is substantial;
subsequent builds reuse current artifacts. The 12 GiB process guard leaves
room above the largest measured F1 compilation while still detecting runaway
steps; use a machine with at least 16 GiB RAM. Do not commit `.lake/`.

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
