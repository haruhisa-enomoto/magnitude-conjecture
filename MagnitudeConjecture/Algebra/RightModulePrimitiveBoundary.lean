import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModulePrimitivePosetRealization

/-!
# Primitive multiplicity on the projective boundary

This file formalizes the boundary reduction in the frozen manuscript.  A
tau-projective object of the literal primitive factor is either already
ambient projective or its ambient Auslander--Reiten translate was killed.
The manuscript's exact coordinate estimate then forces its primitive
multiplicity to be one.

`MultiplicityCoordinateEstimate` is an intermediate interface for the
manuscript's boundary-coordinate lemma.  The final theorem must construct it;
this file does not treat it as an unexplained headline hypothesis.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.Iyama
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The exact numerical coordinate estimate used by the manuscript.  It says
that the multiplicity of a simple in an indecomposable projective or
injective is at most one, and that multiplicities change by at most one under
ambient Auslander--Reiten translation. -/
structure MultiplicityCoordinateEstimate
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K) : Prop where
  projective_le_one : ∀ x : Fin S.n,
    Projective (S.fgObj x) → D.multiplicity x ≤ 1
  injective_le_one : ∀ x : Fin S.n,
    Injective (S.fgObj x) → D.multiplicity x ≤ 1
  translation_difference_le_one :
    ∀ z : {x : Fin S.n // ¬ Projective (S.fgObj x)},
      abs ((D.multiplicity z.1 : ℤ) -
        (D.multiplicity (S.rightTranslationLabel z) : ℤ)) ≤ 1

/-- The repaired Appendix A data constructs the numerical estimate for a
literal primitive idempotent.  The projective and injective clauses are the
schurian corner bounds, while the translation clause comes from the Cartan
form on the sequence-dependent middle-term support algebra. -/
theorem MultiplicityCoordinateEstimate.ofMiddleSupport [IsAlgClosed k]
    {e : A} (D : RightModule.PrimitiveIdempotentData e)
    (R : S.MiddleSupportCartanData D)
    (B : S.SchurianBoundaryData) :
    S.MultiplicityCoordinateEstimate (S.primitiveMultiplicityInput D) where
  projective_le_one := fun x hx =>
    SchurianBoundaryData.primitiveMultiplicity_projective_le_one
      (S := S) B D x hx
  injective_le_one := fun x hx =>
    SchurianBoundaryData.primitiveMultiplicity_injective_le_one
      (S := S) B D x hx
  translation_difference_le_one :=
    R.primitiveMultiplicity_translation_difference_le_one

/-- A tau-projective surviving label is either ambient projective or its
ambient right translate belongs to the killed set. -/
theorem PrimitiveMultiplicityInput.factorProjective_ambient_projective_or_translation_killed
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K)
    (hx : (S.factorFiniteTauCategoryData K).IsProjective x) :
    Projective (S.fgObj x.1) ∨
      ∃ hnp : ¬ Projective (S.fgObj x.1),
        S.rightTranslationLabel ⟨x.1, hnp⟩ ∈ K := by
  classical
  by_cases hprojective : Projective (S.fgObj x.1)
  · exact Or.inl hprojective
  · right
    refine ⟨hprojective, ?_⟩
    by_contra hsurvives
    apply S.factorRawRightMesh_X₁_not_isZero_of_translation_survives
      K x.1 hprojective hsurvives
    have hchosen : IsZero (S.factorLabelRightMesh K x).X₁ := by
      change IsZero
        (S.canonicalFactorRightMesh K (S.factorObject K x)).X₁ at hx
      rwa [S.canonicalFactorRightMesh_at_label K x] at hx
    by_cases hraw : IsZero (S.factorRawRightMesh K x.1).X₁ ∨
        (S.factorRawRightMesh K x.1).f = 0
    · rcases hraw with hsource | hf
      · exact hsource
      · letI : Mono (S.factorRawRightMesh K x.1).f :=
          S.factorRawRightMesh_f_mono D.noMapsFromKilled
            D.toPrimitiveTraceInput.toPrimitiveFactorInput.representableFaithful
            x.1
        exact IsZero.of_mono_eq_zero _ hf
    · rwa [show S.factorLabelRightMesh K x =
          S.factorRawRightMesh K x.1 by
        simp [factorLabelRightMesh, hraw]] at hchosen

/-- The manuscript's coordinate estimate forces multiplicity one on every
tau-projective surviving label of the literal primitive factor. -/
theorem PrimitiveMultiplicityInput.factorProjective_multiplicity_eq_one
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (E : S.MultiplicityCoordinateEstimate D)
    (p : S.FactorProjectiveLabel K) :
    D.multiplicity p.1.1 = 1 := by
  rcases PrimitiveMultiplicityInput.factorProjective_ambient_projective_or_translation_killed
      (S := S) D p.1 p.2 with hprojective | ⟨hnp, hkilled⟩
  · have hle := E.projective_le_one p.1.1 hprojective
    have hpos := PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) D p.1
    omega
  · let z : {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
      ⟨p.1.1, hnp⟩
    have hzero : D.multiplicity (S.rightTranslationLabel z) = 0 :=
      (D.killed_iff_multiplicity_zero _).1 (by simpa [z] using hkilled)
    have hdiff := E.translation_difference_le_one z
    have hsub :
        (D.multiplicity z.1 : ℤ) -
            (D.multiplicity (S.rightTranslationLabel z) : ℤ) ≤ 1 :=
      le_trans (le_abs_self _) hdiff
    have hleInt : (D.multiplicity p.1.1 : ℤ) ≤ 1 := by
      simpa [z, hzero] using hsub
    have hle : D.multiplicity p.1.1 ≤ 1 := by exact_mod_cast hleInt
    have hpos := PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) D p.1
    omega

/-- A tau-injective surviving label is either ambient injective or its
ambient inverse right translate belongs to the killed set. -/
theorem PrimitiveMultiplicityInput.factorInjective_ambient_injective_or_inverse_translation_killed
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (x : S.SurvivingLabel K)
    (hx : (S.factorFiniteTauCategoryData K).IsInjective x) :
    Injective (S.fgObj x.1) ∨
      ∃ hni : ¬ Injective (S.fgObj x.1),
        ((S.rightTranslationEquiv).symm
          (⟨x.1, hni⟩ : {y : Fin S.n // ¬ Injective (S.fgObj y)})).1 ∈ K := by
  classical
  by_cases hinjective : Injective (S.fgObj x.1)
  · exact Or.inl hinjective
  · right
    refine ⟨hinjective, ?_⟩
    by_contra hsurvives
    apply S.factorRawLeftMesh_X₃_not_isZero_of_inverse_translation_survives
      K x.1 hinjective hsurvives
    have hchosen : IsZero (S.factorLabelLeftMesh K x).X₃ := by
      change IsZero
        (S.canonicalFactorLeftMesh K (S.factorObject K x)).X₃ at hx
      rwa [S.canonicalFactorLeftMesh_at_label K x] at hx
    by_cases hraw : IsZero (S.factorRawLeftMesh K x.1).X₃ ∨
        (S.factorRawLeftMesh K x.1).g = 0
    · rcases hraw with htarget | hg
      · exact htarget
      · letI : Epi (S.factorRawLeftMesh K x.1).g :=
          S.factorRawLeftMesh_g_epi D.noMapsToKilled
            D.toPrimitiveTraceInput.toPrimitiveFactorInput.corepresentableFaithful
            x.1
        exact IsZero.of_epi_eq_zero _ hg
    · rwa [show S.factorLabelLeftMesh K x =
          S.factorRawLeftMesh K x.1 by
        simp [factorLabelLeftMesh, hraw]] at hchosen

/-- The manuscript's dual coordinate estimate forces multiplicity one on
every tau-injective surviving label of the literal primitive factor. -/
theorem PrimitiveMultiplicityInput.factorInjective_multiplicity_eq_one
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (E : S.MultiplicityCoordinateEstimate D)
    (i : S.FactorInjectiveLabel K) :
    D.multiplicity i.1.1 = 1 := by
  rcases
      PrimitiveMultiplicityInput.factorInjective_ambient_injective_or_inverse_translation_killed
        (S := S) D i.1 i.2 with hinjective | ⟨hni, hkilled⟩
  · have hle := E.injective_le_one i.1.1 hinjective
    have hpos := PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) D i.1
    omega
  · let y : {y : Fin S.n // ¬ Injective (S.fgObj y)} :=
      ⟨i.1.1, hni⟩
    let z : {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
      (S.rightTranslationEquiv).symm y
    have htranslate : S.rightTranslationLabel z = i.1.1 := by
      exact congrArg Subtype.val (S.rightTranslationEquiv.apply_symm_apply y)
    have hzero : D.multiplicity z.1 = 0 :=
      (D.killed_iff_multiplicity_zero _).1 (by simpa [z, y] using hkilled)
    have hdiff := E.translation_difference_le_one z
    have hsub :
        -((D.multiplicity z.1 : ℤ) -
            (D.multiplicity (S.rightTranslationLabel z) : ℤ)) ≤ 1 :=
      le_trans (neg_le_abs _) hdiff
    have hleInt : (D.multiplicity i.1.1 : ℤ) ≤ 1 := by
      simpa [hzero, htranslate] using hsub
    have hle : D.multiplicity i.1.1 ≤ 1 := by exact_mod_cast hleInt
    have hpos := PrimitiveMultiplicityInput.multiplicity_pos
      (S := S) D i.1
    omega

/-- Ambient directedness and the coordinate estimate construct the complete
boundary data required by the primitive projective-poset realization. -/
theorem PrimitiveDirectedBoundaryData.ofCoordinateEstimate
    {K : Set (Fin S.n)} (D : S.PrimitiveMultiplicityInput K)
    (hacyclic : S.HasAcyclicNonzeroNonisomorphisms)
    (E : S.MultiplicityCoordinateEstimate D) :
    S.PrimitiveDirectedBoundaryData D where
  acyclic := hacyclic
  projective_multiplicity_eq_one :=
    PrimitiveMultiplicityInput.factorProjective_multiplicity_eq_one
      (S := S) D E
  injective_multiplicity_eq_one :=
    PrimitiveMultiplicityInput.factorInjective_multiplicity_eq_one
      (S := S) D E

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
