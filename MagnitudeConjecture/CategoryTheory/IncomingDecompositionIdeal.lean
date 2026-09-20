import MagnitudeConjecture.CategoryTheory.IncomingDecompositionSum
import QuotientSubmoduleEquidistribution.CategoryTheory.HomIdeal

/-! # Ideal membership of the factors in an incoming-summand expansion -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal
namespace MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]
variable {X M Y : C} (d : FiniteIndecomposableDecomposition M)

/-- Projecting the first factor to a summand preserves membership in any
categorical ideal, in particular in the radical. -/
theorem outgoingComponent_mem (I : HomIdeal C) (a : X ⟶ M)
    (ha : a ∈ I.hom X M) (j : Fin d.n) :
    d.outgoingComponent a j ∈ I.hom X (d.summand j) :=
  I.postcomp (d.isoBiproduct.hom ≫ biproduct.π d.summand j) ha

/-- Restricting the second factor to a summand likewise preserves ideal
membership. Thus the reduced sum preserves both radical constraints. -/
theorem incomingComponent_mem (I : HomIdeal C) (b : M ⟶ Y)
    (hb : b ∈ I.hom M Y) (j : Fin d.n) :
    d.incomingComponent b j ∈ I.hom (d.summand j) Y := by
  have h := I.precomp (biproduct.ι d.summand j ≫ d.isoBiproduct.inv) hb
  simpa only [incomingComponent, Category.assoc] using h

end MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
