import MagnitudeConjecture.Algebra.RightModuleIyamaSimpleResolution
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import Mathlib.RingTheory.FiniteLength

/-!
# The global-dimension bound for the factor Auslander algebra

The strict right meshes resolve the simple tops of all indecomposable
represented projectives.  This file identifies those tops with all simple
modules over the factor Auslander algebra and then propagates the resulting
projective-dimension bound through finite-length modules.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MagnitudeConjecture.CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

omit [IsAlgClosed k] in
/-- A represented surviving indecomposable has local module-endomorphism
ring over the factor Auslander algebra. -/
theorem factorAuslanderRepresentable_end_isLocalRing
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    IsLocalRing
      (Module.End (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ S.factorObject K x)) := by
  let G := S.factorAdditiveGenerator K
  let X : (finiteAddClosure G).FullSubcategory :=
    ⟨S.factorObject K x,
      S.factorAdditiveGenerator_isFiniteAddGenerator K
        (S.factorObject K x)⟩
  let U := (finiteAddClosure G).ι
  letI : IsLocalRing (End (U.obj X)) := by
    change IsLocalRing (End (S.factorObject K x))
    exact S.factorObject_end_isLocalRing K x
  letI : IsLocalRing (End X) :=
    RingEquiv.isLocalRing_noncomm
      (Functor.endRingEquivOfFullyFaithful U X).symm
  letI : (homFromGenerator G).Additive := ⟨by
    intro X Y f g
    apply ModuleCat.hom_ext
    ext h
    change G ⟶ X.obj at h
    change h ≫ (f.hom + g.hom) = h ≫ f.hom + h ≫ g.hom
    rw [Preadditive.comp_add]⟩
  letI : IsLocalRing (End ((homFromGenerator G).obj X)) :=
    RingEquiv.isLocalRing_noncomm
      (Functor.endRingEquivOfFullyFaithful (homFromGenerator G) X)
  have hmodule : IsLocalRing
      (Module.End (S.factorAuslanderRing K)
        ((homFromGenerator G).obj X)) :=
    RingEquiv.isLocalRing_noncomm
      (ModuleCat.endRingEquiv ((homFromGenerator G).obj X))
  exact hmodule

/-- The categorical radical is the unique maximal submodule of the
represented indecomposable. -/
theorem factorRepresentableRadical_eq_jacobson
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorRepresentableRadical K x =
      Module.jacobson (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ S.factorObject K x) := by
  let Γ := S.factorAuslanderRing K
  let P := S.factorAdditiveGenerator K ⟶ S.factorObject K x
  letI : Module.Finite Γ P :=
    (S.factorAuslanderRepresentable_finiteProjective K
      (S.factorObject K x)).1
  letI : Module.Projective Γ P := by
    apply (IsProjective.iff_projective P).2
    exact (S.factorAuslanderRepresentable_finiteProjective K
      (S.factorObject K x)).2
  letI : Nontrivial P := by
    refine ⟨biproduct.π
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x, 0, ?_⟩
    intro hzero
    have h := congrArg
      (fun f ↦ biproduct.ι
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x ≫ f)
      hzero
    have hid : 𝟙 (S.factorObject K x) = 0 := by
      calc
        𝟙 (S.factorObject K x) =
            biproduct.ι
                (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x ≫
              (0 : S.factorAdditiveGenerator K ⟶
                S.factorObject K x) := by
                  simpa only [biproduct.ι_π_self] using h
        _ = 0 := comp_zero
    exact S.factorObject_not_isZero K x
      ((IsZero.iff_id_eq_zero _).2 hid)
  letI : IsLocalRing (Module.End Γ P) :=
    S.factorAuslanderRepresentable_end_isLocalRing K x
  have hjac : IsCoatom (Module.jacobson Γ P) :=
    jacobson_isCoatom_of_projective_local_end
  have hrad : IsCoatom (S.factorRepresentableRadical K x) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (simple_iff_isSimpleModule' _).1
      (S.factorAuslanderSimple_simple H K x)
  exact (hjac.le_iff_eq hrad.ne_top).mp (sInf_le hrad)

/-- A vector in an arbitrary Auslander module induces a map from each
indecomposable represented projective. -/
def factorRepresentableToModule
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorAuslanderRing K) M] (m : M) :
    (S.factorAdditiveGenerator K ⟶ S.factorObject K x) →ₗ[
      S.factorAuslanderRing K] M :=
  (LinearMap.toSpanSingleton (S.factorAuslanderRing K) M m).comp
    ((regularLinearEquiv (S.factorAdditiveGenerator K)).symm.toLinearMap.comp
      ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map
        (biproduct.ι
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)).hom)

omit [IsAlgClosed k] in
/-- The represented indecomposable projectives generate the module category:
some coordinate map induced by a nonzero vector is nonzero. -/
theorem exists_factorRepresentableToModule_ne_zero
    (K : Set (Fin S.n))
    {M : Type u} [AddCommGroup M]
    [Module (S.factorAuslanderRing K) M]
    (m : M) (hm : m ≠ 0) :
    ∃ x : S.SurvivingLabel K,
      S.factorRepresentableToModule K x m ≠ 0 := by
  classical
  let G := S.factorAdditiveGenerator K
  let q : (G ⟶ G) →ₗ[S.factorAuslanderRing K] M :=
    (LinearMap.toSpanSingleton (S.factorAuslanderRing K) M m).comp
      (regularLinearEquiv G).symm.toLinearMap
  let term : S.SurvivingLabel K → (G ⟶ G) := fun x ↦
    (biproduct.π
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x :
      G ⟶ S.factorObject K x) ≫
    (biproduct.ι
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x :
      S.factorObject K x ⟶ G)
  by_contra h
  push Not at h
  have hx (x : S.SurvivingLabel K) : q (term x) = 0 := by
    have hxzero := DFunLike.congr_fun (h x)
      (biproduct.π
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)
    change q (term x) = 0 at hxzero
    exact hxzero
  have hqid : q (𝟙 G) = m := by
    change (1 : S.factorAuslanderRing K) • m = m
    exact one_smul _ _
  have htotal : (∑ x : S.SurvivingLabel K, term x) = 𝟙 G := by
    change
      (∑ x : S.SurvivingLabel K,
        biproduct.π
            (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x ≫
          biproduct.ι
            (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x) =
        𝟙 (⨁ fun a : S.SurvivingLabel K ↦ S.factorObject K a)
    exact biproduct.total
  apply hm
  rw [← hqid, ← htotal]
  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ ↦ hx x

/-- Every simple module over the factor Auslander algebra is one of the
radical quotients attached to a surviving indecomposable. -/
theorem exists_factorAuslanderSimple_linearEquiv
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n))
    {M : Type u} [AddCommGroup M]
    [Module (S.factorAuslanderRing K) M]
    [IsSimpleModule (S.factorAuslanderRing K) M] :
    ∃ x : S.SurvivingLabel K,
      Nonempty (S.factorAuslanderSimple K x ≃ₗ[
        S.factorAuslanderRing K] M) := by
  letI : Nontrivial M :=
    (inferInstance : IsSimpleModule (S.factorAuslanderRing K) M).nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ :=
    S.exists_factorRepresentableToModule_ne_zero K m hm
  let φ := S.factorRepresentableToModule K x m
  have hφ : Function.Surjective φ :=
    LinearMap.surjective_of_ne_zero hx
  have hker : IsCoatom (LinearMap.ker φ) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (φ.quotKerEquivOfSurjective hφ).isSimpleModule_iff.mpr
      (inferInstance : IsSimpleModule (S.factorAuslanderRing K) M)
  have hrad : IsCoatom (S.factorRepresentableRadical K x) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (simple_iff_isSimpleModule' _).1
      (S.factorAuslanderSimple_simple H K x)
  have hle : S.factorRepresentableRadical K x ≤
      LinearMap.ker φ := by
    rw [S.factorRepresentableRadical_eq_jacobson H K x,
      Module.jacobson]
    exact sInf_le hker
  have hkerEq : LinearMap.ker φ =
      S.factorRepresentableRadical K x :=
    (hrad.le_iff_eq hker.ne_top).mp hle
  refine ⟨x, ⟨?_⟩⟩
  let eKer := Submodule.Quotient.equiv
    (S.factorRepresentableRadical K x) (LinearMap.ker φ)
    (LinearEquiv.refl (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ S.factorObject K x)) (by
        simpa using hkerEq.symm)
  exact eKer.trans (φ.quotKerEquivOfSurjective hφ)

/-- Consequently every simple factor-Auslander module has projective
dimension at most two. -/
theorem simpleModule_hasProjectiveDimensionLE_two
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorAuslanderRing K) M]
    [IsSimpleModule (S.factorAuslanderRing K) M] :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K) M) 2 := by
  obtain ⟨x, ⟨e⟩⟩ :=
    S.exists_factorAuslanderSimple_linearEquiv H K (M := M)
  letI : HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAuslanderSimple K x)) 2 :=
    S.factorAuslanderSimple_hasProjectiveDimensionLE_two D x
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso 3

/-- The simple-module bound is stable under finite extensions. -/
theorem finiteLengthModule_hasProjectiveDimensionLE_two
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorAuslanderRing K) M]
    (hM : IsFiniteLength (S.factorAuslanderRing K) M) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K) M) 2 := by
  induction hM with
  | @of_subsingleton M _ _ hsub =>
      letI : Subsingleton M := hsub
      have hzero : IsZero
          (ModuleCat.of (S.factorAuslanderRing K) M) :=
        ModuleCat.isZero_iff_subsingleton.mpr (by
          change Subsingleton M
          infer_instance)
      letI : HasProjectiveDimensionLT
          (ModuleCat.of (S.factorAuslanderRing K) M) 0 :=
        hzero.hasProjectiveDimensionLT_zero
      infer_instance
  | @of_simple_quotient M _ _ N _ hN ih =>
      let C : ShortComplex
          (ModuleCat.{u} (S.factorAuslanderRing K)) :=
        ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by
          ext y
          simp)
      have hC : C.ShortExact := by
        apply ModuleCat.shortComplex_shortExact
        · exact LinearMap.exact_subtype_mkQ N
        · exact N.injective_subtype
        · exact N.mkQ_surjective
      have hleft : HasProjectiveDimensionLE C.X₁ 2 := by
        change HasProjectiveDimensionLE
          (ModuleCat.of (S.factorAuslanderRing K) N) 2
        exact ih
      have hright : HasProjectiveDimensionLE C.X₃ 2 := by
        change HasProjectiveDimensionLE
          (ModuleCat.of (S.factorAuslanderRing K) (M ⧸ N)) 2
        exact S.simpleModule_hasProjectiveDimensionLE_two D H
      exact hC.hasProjectiveDimensionLT_X₂ 3 hleft hright

/-- Every finite module over the finite-dimensional factor Auslander
algebra has projective dimension at most two. -/
theorem finiteModule_hasProjectiveDimensionLE_two
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorAuslanderRing K) M]
    [Module.Finite (S.factorAuslanderRing K) M] :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K) M) 2 := by
  letI : Module.Finite k
      (End (S.factorAdditiveGenerator K)) :=
    S.factorCategoryHomFinite K _ _
  letI : Module.Finite k (S.factorAuslanderRing K) := inferInstance
  letI : IsNoetherianRing (S.factorAuslanderRing K) :=
    IsNoetherianRing.of_finite k _
  letI : IsArtinianRing (S.factorAuslanderRing K) :=
    IsArtinianRing.of_finite k _
  have hfinite : IsFiniteLength (S.factorAuslanderRing K) M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩
  exact S.finiteLengthModule_hasProjectiveDimensionLE_two D H hfinite

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
