# Verification

The production main theorem and its independent presentation equivalence have
compiled with only `propext`, `Classical.choice`, and `Quot.sound`. The
independent Challenge contains one deliberate theorem placeholder; it is not
imported by the production proof or Solution.

Comparator passed on 2026-09-07: the exact statement comparison, permitted
axiom check, NanoDa verification, and Lean default kernel replay all succeeded
with exit code 0. The [result and exact tool pins](../verification/2026-09-07/comparator.json)
and [complete compressed log](../verification/2026-09-07/comparator.log.gz)
record this check. The exporter-version qualification below still applies.

The fresh standalone build passed all 1,065 steps, including the entire
1,063-module production library, Challenge, and Solution. The fresh public
and full axiom audits checked 7 and 3,650 declarations respectively, with
only the three standard axioms. The axiom-report parser handles primed Lean
names; six verification-helper regression tests pass.

The complete API covers all 1,063 production modules. All 1,076 generated
pages passed local-target checks, and the displayed statement matches
Challenge exactly. Browser checks passed for the five public declaration
links, theorem search, API return navigation, and the five handwritten pages
on desktop and mobile.

Evidence: [fresh build summary](../verification/2026-09-07/fresh-build-summary.json),
[per-step metrics](../verification/2026-09-07/fresh-build-metrics.jsonl),
[public axioms](../verification/2026-09-07/public-axioms.json),
[full axioms](../verification/2026-09-07/full-axioms.json), and
[website checks](../verification/2026-09-07/website-summary.json).

The largest measured step used 7.99 GiB, leaving very little room under the
8 GiB compiler guard. The public proof's covering-average base used 7.88 GiB;
the largest step was a supplementary Ext² comparison. These measurements are
from one Linux/WSL2 run, not memory guarantees for other environments. Profile
those declarations before assuming the same tight limit is portable.

## Reproduce the checks

Use the serial build commands in the [README](../README.md). The public audit
is `MagnitudeConjecture.PublicAxiomAudit`; the full supporting-result audit
is `MagnitudeConjecture.AxiomAudit`. To print the current public axioms again:

```sh
python3 scripts/audit_axioms.py
python3 scripts/audit_axioms.py --full
```

After building Challenge and Solution, on Linux with Go and Rust installed:

```sh
./scripts/verify-comparator.sh
```

The script uses Comparator's Landrun sandbox, requests NanoDa replay, and
permits only the three standard axioms. It pins these tool sources:

| Tool | Source commit |
| --- | --- |
| Comparator | `68a064109f01c08f47c8edc9f51d6a2bbffaa188` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator and lean4export are compiled with the project's Lean 4.33.1.
The exporter source is its v4.33.0 release. Upstream has no v4.33.1 exporter
tag at the recorded checkpoint. This is an explicit local compatibility
choice: even a successful local replay does not establish that Palomar's
release-tag resolver accepts the project unchanged.

## Palomar preparation

The [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate)
and [policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
allow a website and a separate documentation project alongside a formalization.
Registration uses a public GitHub repository and an exact commit; this
repository remains private during preparation. No registration or deployment
has been performed.

`Challenge.lean` is generated from the Mathlib-only `Statement.lean`, with
one target theorem appended. It contains the actual admissible-quiver
presentation, Morita condition, rational Hom matrix, and direct simple count.
Its connections to the production definitions are proved. Run
`python3 scripts/generate_challenge.py --check` to detect drift.

The template metadata validator checks required sections, version, licence,
description, and retained placeholders. The metadata also passes the upstream
v0.4 JSON schema at commit `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`, checked
with `check-jsonschema` 0.38.0. Neither is a mathematical review or a complete
registry acceptance test. The provenance of inherited
AI-assisted development is disclosed without claiming an independent human
review.

## Continuous integration

Pushes and pull requests run source, metadata, helper, and website checks.
During private preparation, use the workflow's manual dispatch for the
substantial full proof build, with optional documentation and independent
replay. The full proof build also runs automatically once the repository is
public. The workflow uploads evidence and website artifacts; it does not deploy.

The local fresh build and independent replay are recorded separately from CI.
The source/site CI run passed at commit `7c481593c483baa791fc3f8434f5135d39cfa1f5`:
[workflow run](https://github.com/haruhisa-enomoto/magnitude-conjecture/actions/runs/34079715066).
The full remote build has not been run at this checkpoint. Private standard
Linux runners have less memory than public runners, so the workflow adds swap
on smaller machines. See [GitHub's runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).
Independent replay has a larger total memory footprint than an individual
Lean compilation: Comparator retains the exported environment while NanoDa
runs. Use a machine with at least 16 GB RAM for that optional step; manual
dispatch accepts a configured runner label. The default private runner is
intended for the serial proof build, with swap for its largest steps.
