import MagnitudeConjecture.CategoryTheory.GradedSupportedEvaluationIso

/-! # Recovery of supported representations by actual graded modules -/
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
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ)

/-- The recovered representation is isomorphic in the supported finite module category. -/
def supportedEvaluationReconstructionObjectIso
    (F : ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m)) :
    (supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m ⋙
      principalSupportedEvaluationFunctor R hmul e he0 he m).obj F ≅ F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (supportedEvaluationReconstructionIso R hmul e he0 he F.obj.obj.obj
      hneg h1 hsum horth F.obj.property.1 m F.property)))

/-- Reconstruction followed by evaluation is naturally isomorphic to the identity. -/
def supportedEvaluationReconstructionCounit :
    supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m ⋙
      principalSupportedEvaluationFunctor R hmul e he0 he m ≅ 𝟭 _ :=
  NatIso.ofComponents
    (supportedEvaluationReconstructionObjectIso R hmul e he0 he hneg h1 hsum horth m)
    (by
      intro F G α
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext p
      by_cases hp : p ∈ Set.range (principalIntervalInclusion R hmul e he0 m).op.obj
      · obtain ⟨q, rfl⟩ := hp
        change _ ≫ ((supportedEvaluationReconstructionIso R hmul e he0 he G.obj.obj.obj
          hneg h1 hsum horth G.obj.property.1 m G.property).app _).hom =
          ((supportedEvaluationReconstructionIso R hmul e he0 he F.obj.obj.obj
          hneg h1 hsum horth F.obj.property.1 m F.property).app _).hom ≫ _
        erw [supportedEvaluationReconstructionIso_app_interval R hmul e he0 he
          G.obj.obj.obj hneg h1 hsum horth G.obj.property.1 m G.property q.unop,
          supportedEvaluationReconstructionIso_app_interval R hmul e he0 he
          F.obj.obj.obj hneg h1 hsum horth F.obj.property.1 m F.property q.unop]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        rfl
      · exact (G.property p (principalIntervalInclusion_outside R hmul e he0 m p hp)).eq_of_tgt _ _)

include hneg h1 hsum horth in
/-- Every supported finite representation is the evaluation of an actual supported graded module. -/
theorem principalSupportedEvaluation_essSurj :
    (principalSupportedEvaluationFunctor R hmul e he0 he m).EssSurj where
  mem_essImage F := ⟨(supportedIntervalReconstructionFunctor R hmul e he0 he
    hneg h1 hsum horth m).obj F,
    ⟨supportedEvaluationReconstructionObjectIso R hmul e he0 he hneg h1 hsum horth m F⟩⟩

end MagnitudeConjecture.Graded.FiniteGradedModule
