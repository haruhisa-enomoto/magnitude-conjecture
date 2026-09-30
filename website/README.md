# Mathematical website

The site presents the main theorem, its proof and the searchable Lean API.
It also serves the manuscript PDF at `paper.pdf`.

| Page | Content |
| --- | --- |
| Overview | Main theorem, definitions, context, and paper link |
| Formal statement | Mathematical statement beside the Lean statement generated from its source |
| Proof guide | Principal arguments, a curated dependency diagram, and links to Lean declarations |
| API | Generated searchable documentation |
| Verification and provenance | Build instructions, checks, source correspondence, contributions and source revisions |

The documentation identifies its source revision. LaTeX labels and
Lean declaration names anchor the paper-to-code correspondence.

Run `python3 scripts/build_website.py` from the repository root, then
`python3 scripts/check_website.py`. Preview with
`python3 -m http.server 8000 --directory _site --bind 127.0.0.1`.
The statement page reads the actual Challenge file and checks its generator.
A separate [docbuild project](../docbuild/README.md) keeps documentation
tooling outside the proof library's dependency graph. Generate its API first
to include searchable declarations in the preview.

## Publish

The public URL is <https://haruhisa-enomoto.github.io/magnitude-conjecture/>.
Repository **Settings → Pages → Source** must be **GitHub Actions**.
The [Deploy Pages workflow](../.github/workflows/pages.yml) publishes the
complete checked website, including the API, from the `gh-pages` branch.
It runs when that branch is updated; it can also be run manually from Actions.

After committing and pushing source changes to `main`, run:

```sh
python3 scripts/publish_website.py
```

The publisher rebuilds and checks the website, requires a complete API matching
the current Lean source, and pushes the generated output and Pages workflow
from an isolated temporary checkout. It preserves the source working tree and
uses an ordinary fast-forward push. A push to `gh-pages` starts deployment;
check its result in Actions. No Lean compilation is performed during publication.

Handwritten-page changes reuse the checked API. If Lean source or pins change,
first rebuild the proof and regenerate the API as described in
[docbuild](../docbuild/README.md); the publisher rejects a stale API.
The site records both source revisions, so documentation can be refreshed
without attributing a new date to the earlier proof verification.
