import MagnitudeConjecture.CategoryTheory.GradedAdditiveEnvelope
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-! # Fully faithful linear extension to finite direct sums -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CategoryTheory
universe u v w u' v'
variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable [HasFiniteBiproducts D]
variable (F : C ⥤ D) [F.Additive]

instance finiteMatrixLiftLinear [F.Linear k] : (CoveringHom.finiteMatrixLift F).Linear k where
  map_smul := by
    intro X Y f c
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    change (biproduct.ι _ i ≫ biproduct.matrix (fun i j ↦ F.map ((c • f) i j))) ≫ biproduct.π _ j = _
    change (biproduct.ι _ i ≫ biproduct.matrix (fun i j ↦ F.map (c • f i j))) ≫ biproduct.π _ j =
      (biproduct.ι _ i ≫ (c • biproduct.matrix (fun i j ↦ F.map (f i j)))) ≫ biproduct.π _ j
    rw [Linear.comp_smul, Linear.smul_comp]
    simp only [Category.assoc, biproduct.matrix_π, biproduct.ι_desc, F.map_smul]

/-- The endomorphism algebra is preserved under fully faithful realization
of the finite additive envelope. -/
def finiteMatrixLiftEndAlgEquiv [F.Full] [F.Faithful] [F.Linear k] (X : Mat_ C) :
    End X ≃ₐ[k] End ((CoveringHom.finiteMatrixLift F).obj X) :=
  Functor.endAlgEquivOfFullyFaithful (CoveringHom.finiteMatrixLift F) X

end MagnitudeConjecture.CategoryTheory
