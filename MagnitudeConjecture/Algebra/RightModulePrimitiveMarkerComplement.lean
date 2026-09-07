import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundaryCorrespondence
import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletedSocle
import MagnitudeConjecture.CategoryTheory.InjectivePresentationExt

/-!
# Complementarity of primitive new-mesh markers

For a primitive new right mesh, this file proves that the deleted simple is
a quotient of the ambient left marker exactly when it is not a subobject of
the ambient right marker.  The proof uses the Hoshino torsion sequence and
stable Auslander--Reiten duality directly.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {e : A} {D : RightModule.PrimitiveIdempotentData e}

noncomputable local instance markerPositiveHasExt :
    HasExt.{u} (RightModule.FinitelyGeneratedCategory A) := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  exact CategoryTheory.hasExt_of_enoughProjectives _

namespace PrimitiveNewRightMeshEndpoint

/-- The manuscript's marker-complement statement for a new quotient mesh:
the deleted simple is a quotient of the left marker `p_M` exactly when it is
not a subobject of the right marker `q_N`. -/
def HasComplementaryMarkers
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) : Prop :=
  (∃ f : S.fgObj (N.leftMarker H he).1 ⟶
      S.primitiveDeletedSimple D, f ≠ 0) ↔ N.IsPositive

/-- No map from the left marker can point back to the distinguished
primitive projective. -/
theorem hom_leftMarker_to_primitiveSource_eq_zero
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (f : S.fgObj (N.leftMarker H he).1 ⟶
      S.fgObj (S.primitiveSourceLabel D)) :
    f = 0 := by
  by_contra hf
  have hfinrank : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶
        S.fgObj (N.leftMarker H he).1) = 1 := by
    rw [← S.primitiveMultiplicity_eq_sourceHom D]
    exact N.leftMarker_primitiveMultiplicity_eq_one B H he
  obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by
    rw [hfinrank]
    exact Nat.zero_lt_one)
  let O := S.directedLinearOrder H
  have hforward : O.le (S.primitiveSourceLabel D)
      (N.leftMarker H he).1 :=
    S.directedLinearOrder_le_of_hom_ne_zero H g hg
  have hback : O.le (N.leftMarker H he).1
      (S.primitiveSourceLabel D) :=
    S.directedLinearOrder_le_of_hom_ne_zero H f hf
  have hlabel : (N.leftMarker H he).1 =
      S.primitiveSourceLabel D := O.le_antisymm _ _ hback hforward
  apply N.leftMarker_ambient_not_projective H he
  rw [hlabel]
  exact S.primitiveSource_projective D

/-- A nonzero map from the left marker to the deleted simple remains
nonzero in projective-stable Hom. -/
theorem projectiveStableClass_leftMarker_to_deletedSimple_ne_zero
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (f : S.fgObj (N.leftMarker H he).1 ⟶
      S.primitiveDeletedSimple D)
    (hf : f ≠ 0) :
    RightModule.projectiveStableClass (k := k) f ≠ 0 := by
  intro hstable
  obtain ⟨F⟩ :=
    (Submodule.Quotient.mk_eq_zero
      (RightModule.projectiveFactorSubmodule (k := k)
        (S.fgObj (N.leftMarker H he).1)
        (S.primitiveDeletedSimple D))).mp hstable
  letI : Projective F.middle := F.projective
  let p := S.primitiveDeletedSimpleProjection D
  letI : Epi p :=
    S.projectiveSimpleTopProjection_epi
      (S.primitiveSourceProjectiveLabel D)
  let lift : F.middle ⟶ S.fgObj (S.primitiveSourceLabel D) :=
    Projective.factorThru F.right p
  have hlift : lift ≫ p = F.right :=
    Projective.factorThru_comp F.right p
  have hleft : F.left ≫ lift = 0 :=
    N.hom_leftMarker_to_primitiveSource_eq_zero B H he (F.left ≫ lift)
  apply hf
  calc
    f = F.left ≫ F.right := F.fac.symm
    _ = (F.left ≫ lift) ≫ p := by rw [Category.assoc, hlift]
    _ = 0 := by rw [hleft, zero_comp]

/-- The torsion sequence of the right marker `q_N`. -/
def rightMarkerTorsionShortComplex
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
  ShortComplex.mk
    (RightModule.primitiveTorsionInclusion e (S.fgObj N.rightMarker.1))
    (RightModule.primitiveTorsionQuotientMk e (S.fgObj N.rightMarker.1))
    (RightModule.primitiveTorsionInclusion_comp_quotientMk e
      (S.fgObj N.rightMarker.1))

theorem rightMarkerTorsionShortComplex_shortExact
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.rightMarkerTorsionShortComplex.ShortExact :=
  RightModule.primitiveTorsionQuotient_fg_shortExact e
    (S.fgObj N.rightMarker.1)

theorem rightMarkerTorsionQuotient_nontrivial
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Nontrivial
      (RightModule.primitiveTorsionQuotientFGObj e
        (S.fgObj N.rightMarker.1)) := by
  apply primitiveTorsionQuotient_nontrivial_of_sourceHom_finrank_eq_one
    (S := S) (D := D)
  rw [← S.primitiveMultiplicity_eq_sourceHom D]
  exact N.rightMarker_primitiveMultiplicity_eq_one B

def rightMarkerPositiveConnectingLinear
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.primitiveDeletedSimple D ⟶
        RightModule.primitiveTorsionQuotientFGObj e
          (S.fgObj N.rightMarker.1)) →ₗ[k]
      Ext.{u} (S.primitiveDeletedSimple D) N.sourceModule 1 :=
  MagnitudeConjecture.InjectivePresentationExt.connectingLinear
    (k := k) N.rightMarkerTorsionShortComplex_shortExact
      (S.primitiveDeletedSimple D)

theorem rightMarkerPositiveConnectingLinear_injective
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    Function.Injective N.rightMarkerPositiveConnectingLinear := by
  letI : Subsingleton
      (S.primitiveDeletedSimple D ⟶
        (N.rightMarkerTorsionShortComplex).X₂) :=
    ⟨fun f g ↦ by rw [hpositive f, hpositive g]⟩
  exact MagnitudeConjecture.InjectivePresentationExt.connectingLinear_injective_of_subsingleton_hom_middle
    (k := k) N.rightMarkerTorsionShortComplex_shortExact
      (S.primitiveDeletedSimple D)

/-- Degree-one extensions from the deleted simple into the ambient right
marker vanish. -/
theorem extOne_deletedSimple_rightMarker_subsingleton
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Subsingleton
      (Ext.{u} (S.primitiveDeletedSimple D)
        (S.fgObj (S.rightTranslationLabel N.ambientLabel)) 1) := by
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} := N.ambientLabel
  change Subsingleton
    (Ext.{u} (S.primitiveDeletedSimple D)
      (S.fgObj (S.rightTranslationLabel z)) 1)
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (S.fgObj z.1)
  obtain ⟨eNak⟩ :=
    S.rightTranslationIso_nakayamaKernel H z P
  have hzero : ∀ xi : Ext.{u} (S.primitiveDeletedSimple D)
      (S.fgObj (S.rightTranslationLabel z)) 1, xi = 0 := by
    intro xi
    let xi' : Ext.{u} (S.primitiveDeletedSimple D)
        (P.nakayamaKernel (k := k)) 1 :=
      xi.comp (Ext.mk₀ eNak.hom) (add_zero 1)
    have hstable : ∀ a : RightModule.projectiveStableHom
        (k := k) (S.fgObj z.1) (S.primitiveDeletedSimple D),
        a = 0 := by
      intro a
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have hf : f = 0 :=
        S.hom_to_primitiveDeletedSimple_eq_zero_of_inAdd H
          (S.fgObj z.1)
          (S.almostSplitSkeleton.inAdd_obj (by
            change N.label.1 ∈ S.primitiveKilledLabels D
            exact N.label.2)) f
      rw [hf]
      simp
    have hxi' : xi' = 0 := by
      apply (P.stableHomExtLinearEquiv (k := k)
        (S.primitiveDeletedSimple D)).injective
      apply LinearMap.ext
      intro a
      rw [hstable a]
      simp
    have hrecover := congrArg
      (fun eta : Ext.{u} (S.primitiveDeletedSimple D)
          (P.nakayamaKernel (k := k)) 1 ↦
        eta.comp (Ext.mk₀ eNak.inv) (add_zero 1)) hxi'
    simpa [xi', Ext.comp_assoc_of_second_deg_zero] using hrecover
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

theorem rightMarkerPositiveConnectingLinear_surjective
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Function.Surjective N.rightMarkerPositiveConnectingLinear := by
  letI : Subsingleton
      (Ext.{u} (S.primitiveDeletedSimple D)
        (N.rightMarkerTorsionShortComplex).X₂ 1) :=
    N.extOne_deletedSimple_rightMarker_subsingleton H
  exact MagnitudeConjecture.InjectivePresentationExt.connectingLinear_surjective_of_ext_subsingleton_middle
    (k := k) N.rightMarkerTorsionShortComplex_shortExact
      (S.primitiveDeletedSimple D)

/-- The deleted-simple socle of the torsion-free quotient of `q_N` is
one-dimensional. -/
theorem deletedSimple_rightMarkerTorsionQuotient_finrank_eq_one
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Module.finrank k
      (S.primitiveDeletedSimple D ⟶
        RightModule.primitiveTorsionQuotientFGObj e
          (S.fgObj N.rightMarker.1)) = 1 := by
  let T := N.rightMarkerTorsionShortComplex
  have hsum := congrFun
    (S.projectiveHomVectorFGObj_middle_eq_add
      N.rightMarkerTorsionShortComplex_shortExact)
      (S.primitiveSourceProjectiveLabel D)
  have hq : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶
        S.fgObj N.rightMarker.1) = 1 := by
    rw [← S.primitiveMultiplicity_eq_sourceHom D]
    exact N.rightMarker_primitiveMultiplicity_eq_one B
  have hsource : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶ N.sourceModule) = 0 := by
    rw [Module.finrank_zero_iff]
    exact ⟨fun f g ↦
      (hom_primitiveSource_to_eq_zero (S := S) (D := D) N.sourceModule
        (RightModule.primitiveTorsionFGObj_isAnnihilatedBy e
          (S.fgObj N.rightMarker.1)) f).trans
      (hom_primitiveSource_to_eq_zero (S := S) (D := D) N.sourceModule
        (RightModule.primitiveTorsionFGObj_isAnnihilatedBy e
          (S.fgObj N.rightMarker.1)) g).symm⟩
  have hquotient : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶
        RightModule.primitiveTorsionQuotientFGObj e
          (S.fgObj N.rightMarker.1)) = 1 := by
    change (Module.finrank k
        (S.fgObj (S.primitiveSourceLabel D) ⟶
          S.fgObj N.rightMarker.1) : ℤ) =
      (Module.finrank k
        (S.fgObj (S.primitiveSourceLabel D) ⟶ N.sourceModule) : ℤ) +
      (Module.finrank k
        (S.fgObj (S.primitiveSourceLabel D) ⟶
          RightModule.primitiveTorsionQuotientFGObj e
            (S.fgObj N.rightMarker.1)) : ℤ) at hsum
    rw [hq, hsource] at hsum
    norm_num at hsum
    exact_mod_cast hsum.symm
  let p := S.primitiveDeletedSimpleProjection D
  letI : Epi p :=
    S.projectiveSimpleTopProjection_epi
      (S.primitiveSourceProjectiveLabel D)
  let precomp := CategoryTheory.Linear.leftComp k
    (RightModule.primitiveTorsionQuotientFGObj e
      (S.fgObj N.rightMarker.1)) p
  have hprecomp : Function.Injective precomp := by
    intro f g hfg
    exact (cancel_epi p).1 hfg
  have hle : Module.finrank k
      (S.primitiveDeletedSimple D ⟶
        RightModule.primitiveTorsionQuotientFGObj e
          (S.fgObj N.rightMarker.1)) ≤ 1 := by
    rw [← hquotient]
    exact LinearMap.finrank_le_finrank_of_injective hprecomp
  have hpos : 0 < Module.finrank k
      (S.primitiveDeletedSimple D ⟶
        RightModule.primitiveTorsionQuotientFGObj e
          (S.fgObj N.rightMarker.1)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      (exists_nonzero_hom_primitiveDeletedSimple_to_torsionQuotient
        (S := S) (D := D) (S.fgObj N.rightMarker.1)
          (N.rightMarkerTorsionQuotient_nontrivial B))
  omega

def rightMarkerPrimitiveDeletedSocleMap
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.primitiveDeletedSimple D ⟶
      RightModule.primitiveTorsionQuotientFGObj e
        (S.fgObj N.rightMarker.1) :=
  Classical.choose
    (exists_nonzero_hom_primitiveDeletedSimple_to_torsionQuotient
      (S := S) (D := D) (S.fgObj N.rightMarker.1)
        (N.rightMarkerTorsionQuotient_nontrivial B))

theorem rightMarkerPrimitiveDeletedSocleMap_ne_zero
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.rightMarkerPrimitiveDeletedSocleMap B ≠ 0 :=
  Classical.choose_spec
    (exists_nonzero_hom_primitiveDeletedSimple_to_torsionQuotient
      (S := S) (D := D) (S.fgObj N.rightMarker.1)
        (N.rightMarkerTorsionQuotient_nontrivial B))

def rightMarkerPositiveConnectingClass
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Ext.{u} (S.primitiveDeletedSimple D) N.sourceModule 1 :=
  N.rightMarkerPositiveConnectingLinear
    (N.rightMarkerPrimitiveDeletedSocleMap B)

theorem rightMarkerPositiveConnectingClass_ne_zero
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    N.rightMarkerPositiveConnectingClass B ≠ 0 := by
  intro hzero
  apply N.rightMarkerPrimitiveDeletedSocleMap_ne_zero B
  apply N.rightMarkerPositiveConnectingLinear_injective hpositive
  rw [map_zero]
  exact hzero

theorem exists_leftMarker_to_deletedSimple_of_isPositive
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    ∃ f : S.fgObj (N.leftMarker H he).1 ⟶
        S.primitiveDeletedSimple D,
      f ≠ 0 := by
  let xi : Ext.{u} (S.primitiveDeletedSimple D)
      (S.fgObj (N.sourceAmbientLabel H he)) 1 :=
    (N.rightMarkerPositiveConnectingClass B).comp
      (Ext.mk₀ (N.sourceIso H he).hom) (add_zero 1)
  have hxi : xi ≠ 0 := by
    intro hzero
    apply N.rightMarkerPositiveConnectingClass_ne_zero B hpositive
    have hrecover := congrArg
      (fun eta : Ext.{u} (S.primitiveDeletedSimple D)
          (S.fgObj (N.sourceAmbientLabel H he)) 1 ↦
        eta.comp (Ext.mk₀ (N.sourceIso H he).inv) (add_zero 1)) hzero
    simpa [xi, Ext.comp_assoc_of_second_deg_zero] using hrecover
  exact S.exists_nonzero_hom_inverseTranslation_of_extOne_ne_zero
    H (N.sourceNoninjectiveLabel H he)
      (S.primitiveDeletedSimple D) xi hxi

/-- A nonzero left-marker map supplies a nonzero extension of the deleted
simple by the source of the relative mesh. -/
theorem exists_nonzero_extOne_deletedSimple_sourceModule_of_leftMarker
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (f : S.fgObj (N.leftMarker H he).1 ⟶
      S.primitiveDeletedSimple D)
    (hf : f ≠ 0) :
    ∃ xi : Ext.{u} (S.primitiveDeletedSimple D) N.sourceModule 1,
      xi ≠ 0 := by
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    N.sourceNoninjectiveLabel H he
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    (S.rightTranslationEquiv).symm x
  change S.fgObj z.1 ⟶ S.primitiveDeletedSimple D at f
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (S.fgObj z.1)
  obtain ⟨eNak⟩ := S.rightTranslationIso_nakayamaKernel H z P
  let eSource : N.sourceModule ≅
      S.fgObj (S.rightTranslationLabel z) :=
    (N.sourceIso H he).trans (S.noninjectiveLeftSourceIso x)
  let e : N.sourceModule ≅ P.nakayamaKernel (k := k) :=
    eSource.trans eNak
  let a : RightModule.projectiveStableHom
      (k := k) (S.fgObj z.1) (S.primitiveDeletedSimple D) :=
    RightModule.projectiveStableClass (k := k) f
  have ha : a ≠ 0 :=
    N.projectiveStableClass_leftMarker_to_deletedSimple_ne_zero
      B H he f hf
  obtain ⟨lambda, hlambda⟩ :=
    Module.Projective.exists_dual_ne_zero k ha
  let eta : Ext.{u} (S.primitiveDeletedSimple D)
      (P.nakayamaKernel (k := k)) 1 :=
    (P.stableHomExtLinearEquiv (k := k)
      (S.primitiveDeletedSimple D)).symm lambda
  have heta : eta ≠ 0 := by
    intro hzero
    have hvalue := congrArg
      (fun xi : Ext.{u} (S.primitiveDeletedSimple D)
          (P.nakayamaKernel (k := k)) 1 ↦
        P.stableHomExtLinearEquiv (k := k)
          (S.primitiveDeletedSimple D) xi a) hzero
    apply hlambda
    simpa [eta] using hvalue
  let xi : Ext.{u} (S.primitiveDeletedSimple D) N.sourceModule 1 :=
    eta.comp (Ext.mk₀ e.inv) (add_zero 1)
  refine ⟨xi, ?_⟩
  intro hzero
  apply heta
  have hrecover := congrArg
    (fun theta : Ext.{u} (S.primitiveDeletedSimple D) N.sourceModule 1 ↦
      theta.comp (Ext.mk₀ e.hom) (add_zero 1)) hzero
  simpa [xi, Ext.comp_assoc_of_second_deg_zero] using hrecover

/-- A nonzero map from the deleted simple into the right marker remains
nonzero after passage to the torsion-free quotient. -/
theorem comp_rightMarkerTorsionQuotientMk_ne_zero
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (g : S.primitiveDeletedSimple D ⟶ S.fgObj N.rightMarker.1)
    (hg : g ≠ 0) :
    g ≫ RightModule.primitiveTorsionQuotientMk e
      (S.fgObj N.rightMarker.1) ≠ 0 := by
  intro hcomp
  let T := N.rightMarkerTorsionShortComplex
  have hT : T.ShortExact := N.rightMarkerTorsionShortComplex_shortExact
  letI : Mono T.f := hT.mono_f
  let lift : S.primitiveDeletedSimple D ⟶ N.sourceModule :=
    hT.exact.lift g hcomp
  have hlift : lift = 0 :=
    S.hom_primitiveDeletedSimple_eq_zero_of_inAdd N.sourceModule
      (S.primitiveTorsionFGObj_inAdd_primitiveKilledLabels D
        (S.fgObj N.rightMarker.1)) lift
  apply hg
  calc
    g = lift ≫ T.f := (hT.exact.lift_f g hcomp).symm
    _ = 0 := by rw [hlift, zero_comp]

/-- The two manuscript marker tests are complementary. -/
theorem hasComplementaryMarkers
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.HasComplementaryMarkers H he := by
  constructor
  · rintro ⟨f, hf⟩
    intro g
    by_contra hg
    obtain ⟨xi, hxi⟩ :=
      N.exists_nonzero_extOne_deletedSimple_sourceModule_of_leftMarker
        B H he f hf
    obtain ⟨h, hh⟩ :=
      N.rightMarkerPositiveConnectingLinear_surjective H xi
    let q : S.fgObj N.rightMarker.1 ⟶
        RightModule.primitiveTorsionQuotientFGObj e
          (S.fgObj N.rightMarker.1) :=
      RightModule.primitiveTorsionQuotientMk e
        (S.fgObj N.rightMarker.1)
    have hgq : g ≫ q ≠ 0 :=
      N.comp_rightMarkerTorsionQuotientMk_ne_zero g hg
    have hfinrank :=
      N.deletedSimple_rightMarkerTorsionQuotient_finrank_eq_one B
    obtain ⟨c, hc⟩ :=
      exists_smul_eq_of_finrank_eq_one hfinrank hgq h
    have hgqRange : g ≫ q ∈
        MagnitudeConjecture.InjectivePresentationExt.presentationRange
          (k := k) N.rightMarkerTorsionShortComplex
            (S.primitiveDeletedSimple D) := by
      exact ⟨g, rfl⟩
    have hgqKer : g ≫ q ∈
        N.rightMarkerPositiveConnectingLinear.ker := by
      change g ≫ q ∈
        (MagnitudeConjecture.InjectivePresentationExt.connectingLinear
          (k := k) N.rightMarkerTorsionShortComplex_shortExact
            (S.primitiveDeletedSimple D)).ker
      rw [← MagnitudeConjecture.InjectivePresentationExt.presentationRange_eq_connectingLinear_ker
        (k := k) N.rightMarkerTorsionShortComplex_shortExact
          (S.primitiveDeletedSimple D)]
      exact hgqRange
    have hgqZero : N.rightMarkerPositiveConnectingLinear (g ≫ q) = 0 :=
      LinearMap.mem_ker.mp hgqKer
    have hhzero : N.rightMarkerPositiveConnectingLinear h = 0 := by
      rw [← hc, map_smul, hgqZero, smul_zero]
    exact hxi (hh.symm.trans hhzero)
  · exact N.exists_leftMarker_to_deletedSimple_of_isPositive B H he

end PrimitiveNewRightMeshEndpoint

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
