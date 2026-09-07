import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectedDeletion

/-!
# A finite right-module skeleton of the primitive quotient

The intrinsic primitive-quotient skeleton already uses the surviving ambient
labels.  Reindex it once by a finite type of the form `Fin n`, so it can feed
the official finite-tau construction, and compare that construction directly
with the intrinsic irreducible-Hom multiplicities used by directed deletion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : PrimitiveIdempotentData e)
variable [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]

/-- The single reindexing from the literal surviving-label type to the
`Fin n` shape required by `FiniteIndecomposableSkeleton`. -/
def primitiveQuotientFiniteLabelEquiv :
    Fin (Nat.card (S.PrimitiveQuotientLabel D)) ≃
      S.PrimitiveQuotientLabel D :=
  (Finite.equivFin (S.PrimitiveQuotientLabel D)).symm

/-- The complete duplicate-free primitive-quotient skeleton, retaining the
literal surviving labels through `primitiveQuotientFiniteLabelEquiv`. -/
def primitiveQuotientFiniteIndecomposableSkeleton :
    RightModule.FiniteIndecomposableSkeleton k
      (RightModule.primitiveQuotientAlgebra e) := by
  let sigma := S.primitiveQuotientAlmostSplitSkeleton D
  let q := S.primitiveQuotientFiniteLabelEquiv D
  refine
    { n := Nat.card (S.PrimitiveQuotientLabel D)
      obj := fun i ↦ (sigma.obj (q i)).obj
      obj_finite := ?_
      obj_indecomposable := ?_
      eq_of_iso := ?_
      complete := ?_ }
  · intro i
    exact RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.primitiveQuotientAlgebra e) (sigma.obj (q i))
  · intro i
    exact (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := RightModule.primitiveQuotientAlgebra e)
        (sigma.obj (q i))).1
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := RightModule.primitiveQuotientAlgebra e)
          (sigma.obj (q i))).1 (sigma.indecomposable (q i)))
  · intro i j hij
    apply q.injective
    apply sigma.eq_of_iso
    exact hij.map fun h ↦ ObjectProperty.isoMk _ h
  · intro M hM
    let Mfg : RightModule.FinitelyGeneratedCategory
        (RightModule.primitiveQuotientAlgebra e) :=
      @RightModule.finitelyGeneratedOfFiniteDimensional k _
        (RightModule.primitiveQuotientAlgebra e) _ _ M hM.1
    have hMfg : Indecomposable Mfg :=
      (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := RightModule.primitiveQuotientAlgebra e) Mfg).2 hM.2
    have hMmodule : Foundation.IsIndecomposableModule
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ Mfg :=
      (fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := RightModule.primitiveQuotientAlgebra e) Mfg).2 hMfg
    obtain ⟨x, ⟨hx⟩⟩ := sigma.complete Mfg hMmodule
    refine ⟨q.symm x, ?_⟩
    rw [q.apply_symm_apply]
    exact ⟨(forget₂
      (RightModule.FinitelyGeneratedCategory
        (RightModule.primitiveQuotientAlgebra e))
      (RightModule.Category
        (RightModule.primitiveQuotientAlgebra e))).mapIso hx⟩

/-- The reindexed finite skeleton has literally the same finitely generated
objects as the intrinsic primitive-quotient skeleton. -/
def primitiveQuotientFiniteFGObjIso
    (i : Fin (S.primitiveQuotientFiniteIndecomposableSkeleton D).n) :
    (S.primitiveQuotientFiniteIndecomposableSkeleton D).fgObj i ≅
      (S.primitiveQuotientAlmostSplitSkeleton D).obj
        (S.primitiveQuotientFiniteLabelEquiv D i) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- After the single finite reindexing, the official finite-tau arrow
multiplicity is exactly the intrinsic primitive-quotient `Irr` dimension.
-/
theorem primitiveQuotientFinite_arrowMultiplicity_eq
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (source target :
      Fin (S.primitiveQuotientFiniteIndecomposableSkeleton D).n) :
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        ((S.primitiveQuotientFiniteIndecomposableSkeleton D)
          |>.finiteTauCategoryData.toFiniteRightTauCategoryData)
        source target =
      S.primitiveQuotientIrreducibleArrowMultiplicity D
        (S.primitiveQuotientFiniteLabelEquiv D source)
        (S.primitiveQuotientFiniteLabelEquiv D target) := by
  let Q := S.primitiveQuotientFiniteIndecomposableSkeleton D
  let q := S.primitiveQuotientFiniteLabelEquiv D
  have hscalar : ∀ f : Q.fgObj source ⟶ Q.fgObj source,
      ∃ a : k, a • 𝟙 (Q.fgObj source) = f := by
    intro f
    let α := S.primitiveQuotientFiniteFGObjIso D source
    let g := α.inv ≫ f ≫ α.hom
    obtain ⟨a, ha⟩ :=
      S.primitiveQuotient_endomorphism_eq_smul_id D H (q source) g
    refine ⟨a, ?_⟩
    apply (cancel_mono α.hom).1
    calc
      (a • 𝟙 (Q.fgObj source)) ≫ α.hom = a • α.hom := by
        rw [Linear.smul_comp, Category.id_comp]
      _ = α.hom ≫
          (a • 𝟙 ((S.primitiveQuotientAlmostSplitSkeleton D).obj
            (q source))) := by
        rw [Linear.comp_smul, Category.comp_id]
      _ = α.hom ≫ g := congrArg (fun h ↦ α.hom ≫ h) ha
      _ = f ≫ α.hom := by simp only [g, Iso.hom_inv_id_assoc]
  exact (Q.finrank_irreducibleHomSpace_eq_arrowMultiplicity_of_scalarEndomorphisms
    source target hscalar).symm

/-- The official finite-tau surplus of the reindexed quotient skeleton is
the literal intrinsic primitive-quotient surplus used by directed deletion.
-/
theorem primitiveQuotientFinite_ambientARSurplus_eq
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    (S.primitiveQuotientFiniteIndecomposableSkeleton D).ambientARSurplus =
      S.primitiveQuotientARSurplus D := by
  classical
  let Q := S.primitiveQuotientFiniteIndecomposableSkeleton D
  let q := S.primitiveQuotientFiniteLabelEquiv D
  let L := S.PrimitiveQuotientLabel D
  letI : Fintype L := Fintype.ofFinite L
  let arrowQ := MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
    Q.finiteTauCategoryData.toFiniteRightTauCategoryData
  let arrowL := S.primitiveQuotientIrreducibleArrowMultiplicity D
  let projectiveQ : Fin Q.n → Prop := fun i ↦ Projective (Q.fgObj i)
  let projectiveL : L → Prop := fun x ↦
    Projective (S.primitiveQuotientLabelObj D x)
  have harrow (source target : Fin Q.n) :
      arrowQ source target = arrowL (q source) (q target) :=
    S.primitiveQuotientFinite_arrowMultiplicity_eq D H source target
  have hprojective (i : Fin Q.n) :
      projectiveQ i ↔ projectiveL (q i) := by
    let E := RightModule.primitiveQuotientEquivalence (k := k) e
    let α := S.primitiveQuotientFiniteFGObjIso D i
    constructor
    · intro hi
      exact (E.map_projective_iff
        (S.primitiveQuotientLabelObj D (q i))).1
        (Projective.of_iso α hi)
    · intro hi
      exact Projective.of_iso α.symm
        ((E.map_projective_iff
          (S.primitiveQuotientLabelObj D (q i))).2 hi)
  have hindegree (target : Fin Q.n) :
      ARCount.indegree arrowQ target =
        ARCount.indegree arrowL (q target) := by
    unfold ARCount.indegree
    exact Fintype.sum_bijective q q.bijective
      (fun source ↦ (arrowQ source target : ℤ))
      (fun source ↦ (arrowL source (q target) : ℤ))
      (fun source ↦ congrArg (fun n : ℕ ↦ (n : ℤ))
        (harrow source target))
  have hlocal (i : Fin Q.n) :
      @ARCount.localDensity (Fin Q.n) inferInstance arrowQ projectiveQ
          (Classical.decPred _) i =
        @ARCount.localDensity L inferInstance arrowL projectiveL
          (Classical.decPred _) (q i) := by
    rw [ARCount.localDensity, ARCount.localDensity, hindegree]
    by_cases hi : projectiveQ i
    · have hi' : projectiveL (q i) := (hprojective i).1 hi
      rw [if_pos hi, if_pos hi']
    · have hi' : ¬ projectiveL (q i) :=
        fun h ↦ hi ((hprojective i).2 h)
      rw [if_neg hi, if_neg hi']
  rw [show Q.ambientARSurplus =
      @ARCount.surplus (Fin Q.n) inferInstance arrowQ projectiveQ
        (Classical.decPred _) by rfl,
    show S.primitiveQuotientARSurplus D =
      @ARCount.surplus L inferInstance arrowL projectiveL
        (Classical.decPred _) by rfl,
    ← ARCount.sum_localDensity_eq_surplus,
    ← ARCount.sum_localDensity_eq_surplus]
  exact Fintype.sum_bijective q q.bijective
    (fun i ↦ @ARCount.localDensity (Fin Q.n) inferInstance
      arrowQ projectiveQ (Classical.decPred _) i)
    (fun x ↦ @ARCount.localDensity L inferInstance
      arrowL projectiveL (Classical.decPred _) x)
    hlocal

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
