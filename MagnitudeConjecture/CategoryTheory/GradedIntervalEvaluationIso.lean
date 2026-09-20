import MagnitudeConjecture.CategoryTheory.GradedIntervalCoordinateNaturality

/-! # Evaluation of reconstruction agrees with the representation throughout the interval -/
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

/-- The finite full category of selected projectives with degrees in [0,m]. -/
abbrev PrincipalIntervalCategory (m : ℕ) :=
  InducedCategory (PrincipalDegreeCategory R hmul e he0) (intervalProjectiveLabel R hmul e he0 m)

/-- Include the interval-labelled projectives in the whole degree category. -/
def principalIntervalInclusion (m : ℕ) : PrincipalIntervalCategory R hmul e he0 m ⥤
    PrincipalDegreeCategory R hmul e he0 := inducedFunctor (intervalProjectiveLabel R hmul e he0 m)

variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (hfinite : ∀ p, FiniteDimensional k (F.obj p)) (m : ℕ)

/-- The coordinate comparisons assemble into a natural isomorphism on the finite interval. -/
def intervalEvaluationReconstructionIso :
    (principalIntervalInclusion R hmul e he0 m).op ⋙
      CoveringHom.restrictedLinearYoneda (k := k) (principalDegreeInclusion R hmul e he0)
        (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj ≅
    (principalIntervalInclusion R hmul e he0 m).op ⋙ F :=
  NatIso.ofComponents
    (fun p ↦ (intervalEvaluationCoordinateEquiv R hmul e he0 he F hneg h1 hsum horth hfinite m p.unop).toModuleIso)
    (by
      intro p q f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      exact intervalEvaluationCoordinate_naturality R hmul e he0 he F hneg h1 hsum horth hfinite m
        q.unop p.unop f.unop.hom g)

end MagnitudeConjecture.Graded.FiniteGradedModule
