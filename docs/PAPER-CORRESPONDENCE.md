# Paper-to-Lean correspondence

This record assumes familiarity with finite-dimensional algebras, almost-split
sequences, and the statement of the magnitude conjecture. It compares the
formalization with Haruhisa Enomoto's manuscript *The magnitude conjecture for
module categories*, at the source checkpoint recorded in `PROVENANCE.md`.
The manuscript is a read-only source for this work. Its Git blob is
`020b5907b2c78508ac3b91a3034f854aaa8e9a24` (recorded 2026-09-07).

The main statement has the same field, finiteness, and handedness hypotheses:
a finite-dimensional representation-finite algebra over an algebraically
closed field, with finitely generated right modules. There is no characteristic
restriction and no basicness hypothesis on the original algebra. Special
biseriality means an admissible special-biserial bound-quiver presentation in
the Morita class.

| Stable paper label | Lean module | Correspondence |
| --- | --- | --- |
| `thm:main` | `Algebra.StatementTheorem` | `MagnitudeConjecture.Statement.mainClaim`, including nonsingularity and the full equality case |
| `sec:magnitude` | `Algebra.StatementFiniteModules` | Exact Hom matrix, inverse-matrix magnitude, and direct simple count |
| `thm:directed-deletion` | `Algebra.RightModulePrimitiveDirectedDeletion` | Directed primitive deletion comparison |
| `thm:covering-average` | `Algebra.RightModuleStandardFormCoveringAverageInequality` | Covering-average comparison used by induction |
| `sec:completion` | `Algebra.RightModuleMagnitudeInequality` and `Algebra.RightModuleMagnitudeCharacterization` | Inequality and the two directions of equality |
| Equality characterization | `Algebra.RepresentationFiniteSpecialBiserialBeta` | Representation-finite special biseriality iff the relevant beta bound is at most two |
| Left/right beta comparison | `Algebra.RightModuleGabrielBetaComparison` | Direct proved comparison supporting the characterization |

Module names above are prefixed by `MagnitudeConjecture`. The public
`Statement.isSpecialBiserial_iff` proves that the independent presentation
means exactly the production predicate. The direct simple count is connected
to the old projective count by
`RightModule.simpleModuleCount_eq_numberOfSimpleModules`; the underlying
simple-top bijection holds over any field.

The Lean induction decreases the number of indecomposable labels; the
manuscript uses the number of simple modules. Both provide a decreasing
finite measure for the reduction. The formal proof also supplies the coherent
duality ingredient through Freyd categories and closure of defect subcategories
under subobjects and quotients. The additional full Ext² comparison development
is retained as supplementary library material.

## Known manuscript discrepancies

These are findings for the paper author, not paper edits.

1. The projective-stable and injective-stable Hom quotients in `eq:ar-duality`
   and subsequent applications are reversed. With the manuscript's stated
   conventions, `D Ext¹(X,Y)` is projective-stable `Hom(τ⁻Y,X)` and
   injective-stable `Hom(Y,τX)`. The formal proof uses these quotients correctly;
   the audited applications survive the correction.
2. The introduction to `app:multiplicity` incorrectly attributes
   indecomposability/directing to the whole middle term. The argument actually
   uses a sincere indecomposable summand of one of the three terms.
3. The inherited source account of the left/right Gabriel beta comparison
   depends on a private communication. The formalization contains a direct
   proof. An accessible account of that argument would make the paper's
   dependency clearer.

These differences do not weaken the stated formal theorem. The correspondence
audit and proofs are agent work; no independent human review is claimed.

## Later paper revisions

Wording and numbering changes require reference updates. Changes to a proof
route require checking and documenting the comparison. Changes to definitions,
hypotheses, or conclusions require a fresh statement comparison and affected
proof checks. Each release should retain its own source and manuscript
identifiers so later revisions do not change the meaning of an earlier record.
