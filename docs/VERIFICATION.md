# Verification

The current manuscript target is the revised exposition frozen on September 21
in [docs/manuscript](manuscript/README.md). Its correspondence was checked
against the unchanged Lean source. The previous build and replay dates below
remain their actual dates; changing the manuscript target does not constitute
a new proof run. The [exposition migration record](../verification/2026-09-21/exposition-migration.json)
records the snapshot, source-identity and documentation checks separately.

The September 20 source checkpoint `2396fb9` synchronizes the frozen
graded-interval proof from research commit `62b5468c3`. The source has 1,106
owned development modules and 77 vendored modules. The complete canonical
library, Challenge/Solution, source and dependency audits pass. Its expanded
axiom audit checks 4,090 declarations; public checks cover seven declarations.
All use only `propext`, `Classical.choice`, `Quot.sound`, or no axioms.
The independent Challenge has one deliberate placeholder and is not imported
by the production proof.

The standalone full-library build and both axiom audits also pass. Independent
replay with the current Palomar Comparator passed on September 21: the statement
matches, only the permitted axioms occur, and both NanoDa and Lean's kernel
accept the exported proof. The run took 2,288.61 seconds (38.1 minutes), with a
reported peak process RSS of 4.21 GiB. Exact source hashes, tool pins and results
are in [the replay record](../verification/2026-09-20/comparator.json).
The complete API covers all 1,183 development modules. All 1,196 generated
pages pass local-target checks, and the displayed Challenge matches its source.
Browser checks pass for five public theorem links, theorem search and result
navigation, API return navigation, and all five main pages at desktop and mobile
widths. No JavaScript errors or mobile horizontal overflow were found. The 200
removed module pages are absent. Results are in [the documentation record](../verification/2026-09-20/documentation.json). The earlier `verification/2026-09-15/` evidence describes
the superseded F1 proof and is retained only as history.

Both full-library builds were incremental, not from an empty cache. The
standalone build rebuilt 356 targets in 4,529.65 seconds of summed step time;
its highest compiler memory was 8.29 GiB. Its concrete interval beta transfer
took 486.67 seconds and 4.69 GiB. The canonical interval biseriality bridge
took 116.39 seconds and 8.06 GiB. Cached checks
cannot be used to estimate a first source build. All project resource limits
and dependency pins are unchanged.

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
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator uses the toolchain pinned by its own source, Lean 4.34.0-rc1.
The exporter source is v4.33.0, rebuilt with the project's unchanged Lean
4.33.1. The current official verifier's resolver selects that exact exporter
commit and accepts this toolchain pair. The resolver check used
[PalomarSubmission commit 3561d237](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/scripts/verify_submission.py).
A local replay still does not claim execution of the full hosted profile,
editorial review or registry acceptance.

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
