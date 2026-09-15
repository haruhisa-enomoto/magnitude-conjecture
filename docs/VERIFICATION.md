# Verification

This checkpoint verifies the standalone synchronization of the frozen F1 proof
route at source commit `317a6e27a5be03c720dc4238b92c74d1d6037e07`.
The Lean tree is byte-for-byte equal to the 995-file magnitude package at
canonical research commit `d0831ee92`; there are no missing, extra, mismatched,
or legacy-imported source modules. The frozen manuscript identifiers are in
[`PROVENANCE.md`](../PROVENANCE.md), and the proof map is in
[`PAPER-CORRESPONDENCE.md`](PAPER-CORRESPONDENCE.md).

The production main theorem and its independent presentation equivalence
compile using only `propext`, `Classical.choice`, and `Quot.sound`. The
independent Challenge contains one deliberate theorem placeholder. It is not
imported by the production proof or Solution.

## Current results

The fresh standalone build began after `lake clean` and passed all 4,501 serial
compilation steps. It built the complete `MagnitudeConjecture` library, the
full axiom-audit umbrella, Challenge, and Solution, then passed Lake's
`--no-build` validation. The largest process peak was 9,683,212 KiB (9.23 GiB),
and the largest sampled process-tree peak was 10,623,112 KiB (10.13 GiB), both
for `RightModuleF1CoveringPrimitive`. Only one Lean compiler process was active
at a time. These measurements come from one Linux/WSL2 run and are not memory
guarantees for other machines.

The public and full axiom audits checked 7 and 3,675 declarations respectively.
Every reported declaration used only the three standard axioms. The
Challenge generator check, selected import graph check, metadata validation,
six verification-helper regression tests, shell syntax checks, and Git
whitespace check also passed.

Comparator passed on 2026-09-15. Exact statement comparison, permitted-axiom
checking, NanoDa verification, and Lean's default kernel replay all succeeded
with exit code 0 and the final verdict `Your solution is okay!`. The
[`Comparator record`](../verification/2026-09-15/comparator.json) contains the
exact tool pins, Challenge and Solution hashes, and the checksum of the local
2,888,445-byte replay log. The exporter-version qualification below applies.

The searchable API covers 1,072 tracked modules: the 995-file production tree
and 77 vendored quotient-submodule modules. The generated site check examined
1,103 HTML pages; all local targets resolved, and the displayed statement
matched Challenge exactly. The API and site both identify source commit
`317a6e27a5be03c720dc4238b92c74d1d6037e07`.

Evidence: [source synchronization](../verification/2026-09-15/source-sync.json),
[fresh build summary](../verification/2026-09-15/fresh-build-summary.json),
[public axioms](../verification/2026-09-15/public-axioms.json),
[full axioms](../verification/2026-09-15/full-axioms.json), and
[website checks](../verification/2026-09-15/website-summary.json). The older
`verification/2026-09-07/` checkpoint remains as historical evidence for the
superseded proof route.

## Reproduce the checks

Use the serial build commands in the [README](../README.md). The public audit
is `MagnitudeConjecture.PublicAxiomAudit`; the full supporting-result audit is
`MagnitudeConjecture.AxiomAudit`.

```sh
python3 scripts/audit_axioms.py
python3 scripts/audit_axioms.py --full
python3 scripts/generate_challenge.py --check
python3 scripts/generate_import_graph.py --check
python3 -m unittest discover -s tests
```

After building Challenge and Solution, on Linux with Go and Rust installed:

```sh
./scripts/verify-comparator.sh
```

The script uses Comparator's Landrun sandbox, requires NanoDa replay, and
permits only the three standard axioms. It pins these tool sources:

| Tool | Source commit |
| --- | --- |
| Comparator | `68a064109f01c08f47c8edc9f51d6a2bbffaa188` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator and lean4export are compiled with the project's Lean 4.33.1.
The exporter source is its v4.33.0 release. Upstream has no v4.33.1 exporter
tag at this checkpoint. This local compatibility choice means that a
successful local replay does not establish that Palomar's release-tag resolver
accepts the project unchanged.

Build the generated documentation and website with:

```sh
cd docbuild
python3 ../scripts/build_lean_serial.py --package . \
  --output ../.build-audit/doc-tool --max-rss-kib 12582912 doc-gen4
cd ..
python3 scripts/build_api.py
python3 scripts/build_website.py
python3 scripts/check_website.py
```

## Palomar preparation

`Challenge.lean` is generated from the Mathlib-only `Statement.lean`, with one
target theorem appended. It contains the actual admissible-quiver
presentation, Morita condition, rational Hom matrix, and direct simple count.
Its connections to the production definitions are proved. The template
metadata validator checks required sections, version, licence, description,
and retained placeholders; this is not a mathematical review or a complete
registry acceptance test.

The repository remains private. No public release, website deployment, or
Palomar registration has been performed. Registration requires a public
GitHub repository and an exact commit.

## Continuous integration

Pushes and pull requests run source, metadata, helper, and website checks.
During private preparation, the workflow's manual dispatch performs the
substantial full proof build, with optional documentation and independent
replay. The workflow uploads evidence and website artifacts; it does not
deploy. Private standard Linux runners have less memory than public runners,
so the workflow adds swap on smaller machines. Independent replay has a larger
total memory footprint than an individual Lean compilation; use a machine with
at least 16 GiB RAM for that optional step.
