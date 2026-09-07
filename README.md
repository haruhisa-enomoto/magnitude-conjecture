# The magnitude conjecture for module categories

This repository is being prepared as the standalone home of the Lean
formalization and its accompanying mathematical website.

Let A be a finite-dimensional representation-finite algebra over an
algebraically closed field k. Form the rational matrix whose entries are
the dimensions of Hom spaces between representatives of the indecomposable
finite-dimensional right A-modules. The magnitude is the sum of the entries
of the inverse matrix.

The main theorem states that magnitude is at least the number of
isomorphism classes of simple right A-modules, with equality exactly when
the basic algebra of A is special biserial. There is no characteristic
restriction.

## Preparation status

The existing Lean development has been compiled and audited in the research
repository. Its public theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`. The standalone extraction, independent statement interface,
and documentation build have not yet been added here. This repository does
not yet contain a buildable Lean package or a Palomar submission.

The next preparation steps are:

1. Export the equality between the direct simple-module count and the
   existing indecomposable-projective count.
2. Connect a readable, Mathlib-only statement to the completed proof.
3. Extract the Lean package with pinned dependencies and source attribution,
   and verify it in a standalone checkout.
4. Add the mathematical website, generated API documentation, and CI.
5. Record a release against a specific manuscript revision.

## Documentation

The [website outline](website/README.md) describes the intended mathematical
overview, formal statement, proof guide, API, and verification pages.

Each release will identify the Lean source commit and manuscript revision
it accompanies. Further paper revisions can lead to later releases without
changing earlier correspondence records. Palomar registration is optional
and would identify an exact public repository commit.
