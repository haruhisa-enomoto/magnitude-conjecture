# Verification

The production main theorem and its independent presentation equivalence have
compiled with only `propext`, `Classical.choice`, and `Quot.sound`. The
independent Challenge contains one deliberate theorem placeholder; it is not
imported by the production proof or Solution.

At this preparation checkpoint, Comparator has accepted the statement match
and axiom boundary. Its NanoDa replay and the fresh standalone build are still
running. They are not yet reported as successful. Final results will replace
this preparation status after the processes finish.

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
The first source/site CI run passed at commit `539a4c26ff68dd5266761f00f2781b8a61a190af`:
[workflow run](https://github.com/haruhisa-enomoto/magnitude-conjecture/actions/runs/34074150379).
The full remote build has not been run at this checkpoint. Private standard
Linux runners have less memory than public runners, so the workflow adds swap
on smaller machines. See [GitHub's runner specifications](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).
Independent replay has a larger total memory footprint than an individual
Lean compilation: Comparator retains the exported environment while NanoDa
runs. Use a machine with at least 16 GB RAM for that optional step; manual
dispatch accepts a configured runner label. The default private runner is
intended for the serial proof build, with swap for its largest steps.
