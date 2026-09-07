# Website outline

The planned site follows the quotient-submodule equidistribution project's
mathematical pages and separate doc-gen4 documentation build.

| Page | Content |
| --- | --- |
| Overview | Main theorem, definitions, context, and paper link |
| Formal statement | Mathematical statement beside the Lean statement generated from its source |
| Proof guide | Principal arguments, a curated dependency diagram, and links to Lean declarations |
| API | Generated searchable documentation |
| Verification and provenance | Build instructions, checks, source correspondence, contributions, and any registered Palomar version |

The documentation will identify its source revision. Stable LaTeX labels and
Lean declaration names will anchor the paper-to-code correspondence.

The site has not yet been implemented or deployed. A separate `docbuild/`
Lake project is planned to keep documentation tooling outside the proof
library's dependency graph.
