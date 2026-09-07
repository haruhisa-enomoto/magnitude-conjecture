import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity
import MagnitudeConjecture.Combinatorics.EulerSurplus

/-!
# Local density from a minimal right almost-split source

The manuscript's local density at an indecomposable is twice its
nonprojective indicator minus the total number of incoming arrow
occurrences.  In a finite tau-category, the second term is the arity of the
chosen right-mesh middle object.  This file records the exact numerical
bridge in a form that can also use any other minimal right almost-split
source decomposition.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ARCount

/-- Local density written using a supplied total incoming arity. -/
def localDensityOfIncomingArity
    (incomingArity : ℕ) (IsProjective : Prop) : ℤ := by
  classical
  exact 2 * (if IsProjective then 0 else 1) - incomingArity

end MagnitudeConjecture.ARCount

namespace MagnitudeConjecture.FiniteTauMatrix

open QuotientSubmoduleEquidistribution.Iyama

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

variable (T : FiniteRightTauCategoryData C Ind)

omit [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The first term of a right tau-sequence is zero exactly when its terminal
map is monic. -/
theorem rightTau_first_isZero_iff_mono_terminal
    {S : ShortComplex C} (hS : RightTauSequence S) :
    IsZero S.X₁ ↔ Mono S.g := by
  constructor
  · intro hzero
    apply Preadditive.mono_of_cancel_zero
    intro P a ha
    obtain ⟨l, hl⟩ :=
      (ShortComplex.isWeakKernel_iff S).mp hS.minimalWeakKernel.1 a ha
    rw [← hl, hzero.eq_of_tgt l 0, zero_comp]
  · intro hg
    letI : Mono S.g := hg
    have hf : S.f = 0 := zero_of_comp_mono S.g S.zero
    haveI : IsIso (0 : S.X₁ ⟶ S.X₁) :=
      hS.minimalWeakKernel.2 0 (by rw [zero_comp, hf])
    rw [IsZero.iff_id_eq_zero]
    rw [← cancel_epi (0 : S.X₁ ⟶ S.X₁)]
    simp

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasFiniteBiproducts A] [HasBinaryBiproducts A]
  [IsIdempotentComplete A]
variable {J : Type w} [Fintype J]

/-- In an abelian category with enough projectives, the finite tau
predicate defined by a zero left mesh term is exactly categorical
projectivity of the chosen indecomposable. -/
theorem isProjective_iff_projective_obj
    (U : FiniteRightTauCategoryData A J) [EnoughProjectives A] (Y : J) :
    U.IsProjective Y ↔ Projective (U.obj Y) := by
  rw [show U.IsProjective Y =
      IsZero (U.rightMesh (U.obj Y)).X₁ from rfl,
    rightTau_first_isZero_iff_mono_terminal
      (U.rightTau (U.obj Y))]
  let S := U.rightMesh (U.obj Y)
  let e : S.X₃ ≅ U.obj Y := U.rightTermIso (U.obj Y)
  let g : S.X₂ ⟶ U.obj Y := S.g ≫ e.hom
  have hgAlmost : IsRightAlmostSplit g :=
    rightMesh_terminal_isRightAlmostSplit U Y
  constructor
  · intro hmono
    letI : Mono S.g := hmono
    letI : Mono g := by
      dsimp only [g]
      infer_instance
    exact MagnitudeConjecture.CategoryTheory.projective_of_mono_rightAlmostSplit
      g hgAlmost
  · intro hprojective
    letI : Projective (U.obj Y) := hprojective
    have hgmono : Mono g :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
        g hgAlmost (rightMesh_terminal_isRightMinimal U Y)
    letI : Mono g := hgmono
    dsimp only [g] at hgmono
    exact mono_of_mono S.g e.hom

end Abelian

/-- The matrix local density is determined by the right-middle arity and the
projective predicate at the chosen label. -/
theorem localDensity_eq_localDensityOfIncomingArity
    [DecidablePred T.IsProjective]
    (Y : Ind) (incomingArity : ℕ)
    (hArity : rightMiddleArity T Y = incomingArity)
    (IsProjective : Prop)
    (hProjective : T.IsProjective Y ↔ IsProjective) :
    ARCount.localDensity (arrowMultiplicity T) T.IsProjective Y =
      ARCount.localDensityOfIncomingArity incomingArity IsProjective := by
  have hIndegree :
      ARCount.indegree (arrowMultiplicity T) Y =
        (rightMiddleArity T Y : ℤ) := by
    rw [ARCount.indegree, ← Nat.cast_sum]
    exact congrArg (fun n : ℕ ↦ (n : ℤ))
      (sum_arrowMultiplicity_source T Y)
  rw [ARCount.localDensity, hIndegree, hArity]
  by_cases h : T.IsProjective Y
  · simp [ARCount.localDensityOfIncomingArity, h, hProjective.mp h]
  · have h' : ¬ IsProjective := fun hI ↦ h (hProjective.mpr hI)
    simp [ARCount.localDensityOfIncomingArity, h, h']

/-- Equivalently, every finite decomposition of a minimal right
almost-split source computes the local density at its endpoint. -/
theorem localDensity_eq_of_minimalRightAlmostSplitDecomposition
    [DecidablePred T.IsProjective]
    (Y : Ind) {E : C} {f : E ⟶ T.obj Y}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E)
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f)
    (IsProjective : Prop)
    (hProjective : T.IsProjective Y ↔ IsProjective) :
    ARCount.localDensity (arrowMultiplicity T) T.IsProjective Y =
      ARCount.localDensityOfIncomingArity d.n IsProjective := by
  apply localDensity_eq_localDensityOfIncomingArity T Y d.n
  · exact rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T Y d hf hfmin
  · exact hProjective

end MagnitudeConjecture.FiniteTauMatrix
