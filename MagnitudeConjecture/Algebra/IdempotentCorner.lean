import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Linear subspaces cut out by idempotents

For a family `e` in a `k`-algebra, the `(i,j)` corner is the subspace
`e i * A * e j`.  We keep the range presentation because it exposes a
literal ambient-algebra coordinate together with a witness.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture

universe u v

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- The vector subspace `e i * A * e j`. -/
def idempotentCorner {ι : Type*} (e : ι → A) (i j : ι) : Submodule k A :=
  LinearMap.range
    ((LinearMap.mulRight k (e j)).comp (LinearMap.mulLeft k (e i)))

theorem mem_idempotentCorner_iff {ι : Type*} (e : ι → A) (i j : ι) (x : A) :
    x ∈ idempotentCorner (k := k) e i j ↔
      ∃ a : A, e i * a * e j = x :=
  Iff.rfl

end MagnitudeConjecture
