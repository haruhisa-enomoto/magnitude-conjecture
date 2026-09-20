import MagnitudeConjecture.CategoryTheory.GradedAdditiveEnvelope
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-! # Fully faithful linear functors on finite matrix objects -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CategoryTheory
universe u u' v
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v} D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive]

instance matrixFunctor_additive : F.mapMat_.Additive where
  map_add {X Y} f g := by
    apply Mat_.hom_ext
    intro i j
    exact F.map_add

instance matrixFunctor_linear [F.Linear k] : F.mapMat_.Linear k where
  map_smul f c := by
    apply Mat_.hom_ext
    intro i j
    exact F.map_smul c (f i j)

instance matrixFunctor_faithful [F.Faithful] : F.mapMat_.Faithful where
  map_injective {X Y} f g hfg := by
    apply Mat_.hom_ext
    intro i j
    exact F.map_injective (congrArg (fun f ↦ f i j) hfg)

instance matrixFunctor_full [F.Full] : F.mapMat_.Full where
  map_surjective f := by
    refine ⟨fun i j ↦ F.preimage (f i j), ?_⟩
    apply Mat_.hom_ext
    intro i j
    exact F.map_preimage (f i j)

/-- Entrywise transport along a fully faithful linear functor preserves
the finite matrix object's endomorphism algebra. -/
def matrixFunctorEndAlgEquiv [F.Linear k] [F.Full] [F.Faithful] (X : Mat_ C) :
    End X ≃ₐ[k] End (F.mapMat_.obj X) :=
  Functor.endAlgEquivOfFullyFaithful F.mapMat_ X

end MagnitudeConjecture.CategoryTheory
