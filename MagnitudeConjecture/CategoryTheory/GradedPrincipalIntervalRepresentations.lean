import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalDeletion
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit

/-! # Finite interval representations of actual graded modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)

/-- The deletion comparison preserves literal object support by a bijection. -/
theorem principalIntervalOpDeletion_obj_bijective (m : ℕ) :
    Function.Bijective (principalIntervalOpDeletionEquivalence R hmul e he0 he hneg m).functor.obj := by
  constructor
  · intro X Y hXY
    exact principalIntervalInclusion_op_injective R hmul e he0 m
      (congrArg (fun Z ↦ Z.obj.as) hXY)
  · intro Y
    have hy := Y.property
    change ¬ (Y.obj.as.unop.2 < 0 ∨ (m : ℤ) < Y.obj.as.unop.2) at hy
    let X : PrincipalIntervalCategory R hmul e he0 m :=
      (Y.obj.as.unop.1, ⟨Y.obj.as.unop.2.toNat, by omega⟩)
    refine ⟨op X, ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    apply Opposite.unop_injective
    apply Prod.ext
    · rfl
    · change (Y.obj.as.unop.2.toNat : ℤ) = Y.obj.as.unop.2
      omega

/-- Finite interval representations are precisely supported representations of all shifted projectives. -/
def principalIntervalSupportedRepresentationEquivalence (m : ℕ) :
    CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ) k ≌
    ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) := by
  let E := principalIntervalOpDeletionEquivalence R hmul e he0 he hneg m
  let eo := Equiv.ofBijective E.functor.obj
    (principalIntervalOpDeletion_obj_bijective R hmul e he0 he hneg m)
  exact (CoveringHom.finiteDimensionalModuleCongrEquivalence
    (k := k) E eo (fun _ ↦ rfl)).symm.trans
      (ObjectDeletion.finiteDimensionalModuleExtensionByZeroVanishingEquivalence
        (k := k) _ _)

/-- The finite projective interval represents actual supported graded modules. -/
def principalIntervalGradedModuleEquivalence
    (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
    (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ) :
    CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ) k ≌ SupportedCategory (R := R) m :=
  (principalIntervalSupportedRepresentationEquivalence R hmul e he0 he hneg m).trans
    (supportedProjectiveRepresentationEquivalence R hmul e he0 he hsum horth m hneg h1).symm

end MagnitudeConjecture.Graded.FiniteGradedModule
