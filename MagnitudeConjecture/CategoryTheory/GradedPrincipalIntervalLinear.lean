import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalAlgebra
import MagnitudeConjecture.CategoryTheory.ObjectDeletionVanishingLinear
import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGeneratorLinear

/-! # Linearity of the finite interval realization -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
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

instance principalIntervalSupportedRepresentationEquivalence_additive (m : ℕ) :
    (principalIntervalSupportedRepresentationEquivalence R hmul e he0 he hneg m).functor.Additive := by
  let E := principalIntervalOpDeletionEquivalence R hmul e he0 he hneg m
  let eo := Equiv.ofBijective E.functor.obj
    (principalIntervalOpDeletion_obj_bijective R hmul e he0 he hneg m)
  let F := CoveringHom.finiteDimensionalModuleCongrEquivalence
    (k := k) E eo (fun _ ↦ rfl)
  let V := ObjectDeletion.finiteDimensionalModuleExtensionByZeroVanishingEquivalence
    (k := k) (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m)
  change (F.inverse ⋙ V.functor).Additive
  infer_instance

instance principalIntervalSupportedRepresentationEquivalence_linear (m : ℕ) :
    (principalIntervalSupportedRepresentationEquivalence R hmul e he0 he hneg m).functor.Linear k := by
  let E := principalIntervalOpDeletionEquivalence R hmul e he0 he hneg m
  let eo := Equiv.ofBijective E.functor.obj
    (principalIntervalOpDeletion_obj_bijective R hmul e he0 he hneg m)
  let F := CoveringHom.finiteDimensionalModuleCongrEquivalence
    (k := k) E eo (fun _ ↦ rfl)
  let V := ObjectDeletion.finiteDimensionalModuleExtensionByZeroVanishingEquivalence
    (k := k) (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m)
  change (F.inverse ⋙ V.functor).Linear k
  infer_instance

variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)

instance principalIntervalGradedModuleEquivalence_additive (m : ℕ) :
    (principalIntervalGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m).functor.Additive := by
  change ((principalIntervalSupportedRepresentationEquivalence R hmul e he0 he hneg m).functor ⋙
    (supportedProjectiveRepresentationEquivalence R hmul e he0 he hsum horth m hneg h1).inverse).Additive
  infer_instance

instance principalIntervalGradedModuleEquivalence_linear (m : ℕ) :
    (principalIntervalGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m).functor.Linear k := by
  change ((principalIntervalSupportedRepresentationEquivalence R hmul e he0 he hneg m).functor ⋙
    (supportedProjectiveRepresentationEquivalence R hmul e he0 he hsum horth m hneg h1).inverse).Linear k
  infer_instance

local instance linearIntervalFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m) :=
  inferInstanceAs (Fintype (ι × Fin (m + 1)))
local instance linearIntervalOpFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

attribute [local irreducible] CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence

instance principalIntervalAlgebraGradedModuleEquivalence_additive (m : ℕ) :
    (principalIntervalAlgebraGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m).functor.Additive := by
  let :=  principalIntervalAlgebra_finiteDimensional R hmul e he0 he m
  let :=  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
  let G := CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
  change ((LeftModule.fgModuleEquivalenceOfAlgEquiv
    (AlgEquiv.op (principalIntervalAlgebraRepresentableEquiv R hmul e he0 he m))).functor ⋙
      (G.inverse ⋙ (principalIntervalGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m).functor)).Additive
  infer_instance

instance principalIntervalAlgebraGradedModuleEquivalence_linear (m : ℕ) :
    (principalIntervalAlgebraGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m).functor.Linear k := by
  let :=  principalIntervalAlgebra_finiteDimensional R hmul e he0 he m
  let :=  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
  let G := CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
  change ((LeftModule.fgModuleEquivalenceOfAlgEquiv
    (AlgEquiv.op (principalIntervalAlgebraRepresentableEquiv R hmul e he0 he m))).functor ⋙
      (G.inverse ⋙ (principalIntervalGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m).functor)).Linear k
  infer_instance

end MagnitudeConjecture.Graded.FiniteGradedModule
