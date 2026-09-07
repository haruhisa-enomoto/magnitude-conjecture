import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Initial dependency audit

Compilation checks for the finite-sum and matrix APIs used by the first
magnitude/mesh stratum.
-/

namespace MagnitudeConjecture.DependencyAudit

#check Finset.sum_add_distrib
#check Fintype.card
#check Matrix

end MagnitudeConjecture.DependencyAudit
