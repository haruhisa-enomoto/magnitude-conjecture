import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Pointwise exactness for module-valued functors

Exactness in a functor category is detected by evaluation.  This file records
the resulting concrete criterion for short complexes of module-valued
functors: equality of the image and kernel at every object implies categorical
exactness of the natural transformations.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CategoryTheory

universe u v w t

variable {R : Type w} [Ring R]
variable {C : Type u} [Category.{v} C]

/-- A short complex of module-valued functors is exact when its evaluated
linear maps have image equal to kernel at every object. -/
theorem moduleFunctor_exact_of_app_range_eq_ker
    (S : ShortComplex (C ⥤ ModuleCat.{t} R))
    (h : ∀ X : C,
      LinearMap.range (S.f.app X).hom = LinearMap.ker (S.g.app X).hom) :
    S.Exact := by
  let E : ∀ X : C,
      (C ⥤ ModuleCat.{t} R) ⥤ ModuleCat.{t} R :=
    fun X ↦ (evaluation C (ModuleCat.{t} R)).obj X
  let hE : JointlyReflectIsomorphisms E :=
    { isIso := by
        intro X Y f h
        rw [NatTrans.isIso_iff_isIso_app]
        intro Z
        change IsIso ((E Z).map f)
        infer_instance }
  rw [hE.exact_iff S]
  intro X
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h X

end MagnitudeConjecture.CategoryTheory
