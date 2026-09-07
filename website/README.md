# Mathematical website

The site follows the quotient-submodule equidistribution project's
mathematical pages and separate doc-gen4 documentation build.

| Page | Content |
| --- | --- |
| Overview | Main theorem, definitions, context, and paper link |
| Formal statement | Mathematical statement beside the Lean statement generated from its source |
| Proof guide | Principal arguments, a curated dependency diagram, and links to Lean declarations |
| API | Generated searchable documentation |
| Verification and provenance | Build instructions, checks, source correspondence, contributions, and any registered Palomar version |

The documentation identifies its source revision. Stable LaTeX labels and
Lean declaration names will anchor the paper-to-code correspondence.

Run `python3 scripts/build_website.py` from the repository root, then
`python3 scripts/check_website.py`. Preview with
`python3 -m http.server 8000 --directory _site --bind 127.0.0.1`.
The statement page reads the actual Challenge file and checks its generator.
A separate [docbuild project](../docbuild/README.md) keeps documentation
tooling outside the proof library's dependency graph. Generate its API first
to include searchable declarations in the preview. No site has been deployed.
