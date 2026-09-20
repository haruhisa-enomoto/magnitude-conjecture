import MagnitudeConjecture.CategoryTheory.LinearPathKernelFiltration
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The free degree-one path space counts arrows -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.LinearPathCategory
universe u v w
variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]

/-- Restrict path coordinates to one fixed path length. -/
def lengthComponentPathEquiv (X Y : Category k Q) (n : ℕ) :
    lengthComponent X Y n ≃ₗ[k]
      ({p : Quiver.Path (vertex Y) (vertex X) // p.length = n} →₀ k) := by
  let E := homPathLinearEquiv X Y
  let P := GradedFinsupp.degreeComponent (k := k)
    (fun p : Quiver.Path (vertex Y) (vertex X) ↦ p.length) n
  have hmap : (lengthComponent X Y n).map E.toLinearMap = P := by
    change (P.comap E.toLinearMap).map E.toLinearMap = P
    exact Submodule.map_comap_eq_of_surjective E.surjective P
  exact (E.ofSubmodules _ P hmap).trans
    (Finsupp.supportedEquivFinsupp (R := k)
      {p : Quiver.Path (vertex Y) (vertex X) | p.length = n})

/-- Degree-one path coefficients are precisely coefficients indexed by arrows. -/
def lengthOneArrowEquiv (X Y : Category k Q) :
    lengthComponent X Y 1 ≃ₗ[k] ((vertex Y ⟶ vertex X) →₀ k) :=
  (lengthComponentPathEquiv X Y 1).trans
    (Finsupp.domLCongr (arrowEquivLengthOnePath (vertex Y) (vertex X)).symm)

/-- Variance is reversed: maps X to Y have the arrows from vertex Y to vertex X. -/
theorem lengthComponent_one_finrank (X Y : Category k Q)
    [Fintype (vertex Y ⟶ vertex X)] :
    Module.finrank k (lengthComponent X Y 1) = Fintype.card (vertex Y ⟶ vertex X) :=
  (lengthOneArrowEquiv X Y).finrank_eq.trans (Module.finrank_finsupp_self k)

end MagnitudeConjecture.LinearPathCategory
