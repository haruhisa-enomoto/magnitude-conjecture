import MagnitudeConjecture.Algebra.RepresentationFiniteQuotient
import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectedDeletion
import MagnitudeConjecture.CategoryTheory.FiniteTauSurplusEquivalence
import Mathlib.RingTheory.Congruence.Hom

/-!
# Right-module invariants under algebra equivalence

An algebra equivalence transports complete finite indecomposable right-module
skeletons, their Auslander--Reiten surplus, primitive idempotents, and literal
primitive quotients.  These facts let the standard-covering calculation be
performed in its strict orbit algebra and stated in the manuscript's literal
standard-form algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u

variable {k A B : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]

/-- Restriction of scalars along the opposite algebra equivalence, regarded
as an equivalence of finitely generated right-module categories. -/
noncomputable abbrev fgModuleEquivalenceOfAlgEquiv (f : A ≃ₐ[k] B) :
    FinitelyGeneratedCategory A ≌ FinitelyGeneratedCategory B :=
  LeftModule.fgModuleEquivalenceOfAlgEquiv (AlgEquiv.op f)

/-- Applying an algebra equivalence coefficientwise identifies the image of
the principal right ideal `eA` with the principal right ideal `f(e)B`. -/
def rightIdealMapAlgEquivLinearEquiv (f : A ≃ₐ[k] B) (e : A) :
    (fgModuleEquivalenceOfAlgEquiv f).functor.obj (rightIdealFGObj e) ≃ₗ[Bᵐᵒᵖ]
      rightIdealFGObj (f e) where
  toFun x := by
    let x' : rightIdeal e := x
    refine ⟨f x'.1, ?_⟩
    obtain ⟨a, ha⟩ := x'.2
    refine ⟨f a, ?_⟩
    change f e * f a = f x'.1
    change e * a = x'.1 at ha
    exact (f.map_mul e a).symm.trans (congrArg f ha)
  invFun y := by
    refine ⟨f.symm y.1, ?_⟩
    obtain ⟨b, hb⟩ := y.2
    refine ⟨f.symm b, ?_⟩
    change f e * b = y.1 at hb
    change e * f.symm b = f.symm y.1
    calc
      _ = f.symm (f e) * f.symm b := by rw [f.symm_apply_apply]
      _ = f.symm (f e * b) := (f.symm.map_mul (f e) b).symm
      _ = _ := congrArg f.symm hb
  left_inv x := by
    apply Subtype.ext
    let x' : rightIdeal e := x
    exact f.symm_apply_apply x'.1
  right_inv y := by
    apply Subtype.ext
    exact f.apply_symm_apply y.1
  map_add' x y := by
    apply Subtype.ext
    let x' : rightIdeal e := x
    let y' : rightIdeal e := y
    exact f.map_add x'.1 y'.1
  map_smul' r x := by
    apply Subtype.ext
    let x' : rightIdeal e := x
    change f (x'.1 * f.symm r.unop) = f x'.1 * r.unop
    exact (f.map_mul x'.1 (f.symm r.unop)).trans
      (congrArg (fun b ↦ f x'.1 * b) (f.apply_symm_apply r.unop))

/-- The categorical form of the coefficientwise principal-right-ideal
equivalence. -/
def rightIdealFGObjMapAlgEquivIso (f : A ≃ₐ[k] B) (e : A) :
    (fgModuleEquivalenceOfAlgEquiv f).functor.obj (rightIdealFGObj e) ≅
      rightIdealFGObj (f e) :=
  QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
    Bᵐᵒᵖ (rightIdealMapAlgEquivLinearEquiv f e)

/-- Transport a complete duplicate-free right-module skeleton along an
algebra equivalence. -/
noncomputable def FiniteIndecomposableSkeleton.mapAlgEquiv
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B) :
    FiniteIndecomposableSkeleton k B := by
  let E := fgModuleEquivalenceOfAlgEquiv f
  letI : E.functor.Additive := inferInstance
  letI : E.inverse.Additive := inferInstance
  refine
    { n := S.n
      obj := fun i ↦ (E.functor.obj (S.fgObj i)).obj
      obj_finite := fun i ↦
        finite_over_field_of_finitelyGenerated k B
          (E.functor.obj (S.fgObj i))
      obj_indecomposable := ?_
      eq_of_iso := ?_
      complete := ?_ }
  · intro i
    apply (FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := B) (E.functor.obj (S.fgObj i))).1
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor (S.fgObj i)).2 (S.fgObj_indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    apply S.fgObj_skeletal
    exact ⟨E.functor.preimageIso (ObjectProperty.isoMk _ hij)⟩
  · intro M hM
    let Mfg : FinitelyGeneratedCategory B :=
      @finitelyGeneratedOfFiniteDimensional k _ B _ _ M hM.1
    have hMfg : Indecomposable Mfg :=
      (FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := B) Mfg).2 hM.2
    have hInv : Indecomposable (E.inverse.obj Mfg) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse Mfg).2 hMfg
    obtain ⟨i, ⟨hi⟩⟩ := S.fgObj_complete (E.inverse.obj Mfg) hInv
    let efg : Mfg ≅ E.functor.obj (S.fgObj i) :=
      (E.counitIso.app Mfg).symm ≪≫ E.functor.mapIso hi
    exact ⟨i, ⟨(forget₂ (FinitelyGeneratedCategory B)
      (Category B)).mapIso efg⟩⟩

/-- The transported skeleton object is the functorial image of the original
one. -/
noncomputable def FiniteIndecomposableSkeleton.mapAlgEquivObjIso
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B)
    (i : Fin S.n) :
    (fgModuleEquivalenceOfAlgEquiv f).functor.obj (S.fgObj i) ≅
      (S.mapAlgEquiv f).fgObj i :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Algebra equivalence preserves the ambient Auslander--Reiten surplus. -/
theorem FiniteIndecomposableSkeleton.ambientARSurplus_mapAlgEquiv
    (S : FiniteIndecomposableSkeleton k A) (f : A ≃ₐ[k] B) :
    (S.mapAlgEquiv f).ambientARSurplus = S.ambientARSurplus := by
  let E := fgModuleEquivalenceOfAlgEquiv f
  letI : E.functor.Additive := inferInstance
  letI : EnoughProjectives (FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives (FinitelyGeneratedCategory B) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let U := (S.mapAlgEquiv f).finiteTauCategoryData.toFiniteRightTauCategoryData
  have h := FiniteTauMatrix.surplus_eq_of_equivalence
    T U E (Equiv.refl (Fin S.n)) (S.mapAlgEquivObjIso f)
  have hT : T.IsProjective = fun i ↦ Projective (S.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj T i
  have hU : U.IsProjective =
      fun i ↦ Projective ((S.mapAlgEquiv f).fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj U i
  rw [hT, hU] at h
  exact h.symm

/-- The label of `T` representing the finitely generated module at a label
of `S`. -/
noncomputable def FiniteIndecomposableSkeleton.relabel
    (S T : FiniteIndecomposableSkeleton k A) (i : Fin S.n) : Fin T.n :=
  Classical.choose (T.fgObj_complete (S.fgObj i) (S.fgObj_indecomposable i))

/-- The chosen module isomorphism underlying relabelling. -/
noncomputable def FiniteIndecomposableSkeleton.relabelIso
    (S T : FiniteIndecomposableSkeleton k A) (i : Fin S.n) :
    S.fgObj i ≅ T.fgObj (S.relabel T i) :=
  Classical.choice
    (Classical.choose_spec
      (T.fgObj_complete (S.fgObj i) (S.fgObj_indecomposable i)))

theorem FiniteIndecomposableSkeleton.relabel_injective
    (S T : FiniteIndecomposableSkeleton k A) :
    Function.Injective (S.relabel T) := by
  intro i j hij
  apply S.fgObj_skeletal
  exact ⟨S.relabelIso T i ≪≫
    eqToIso (congrArg T.fgObj hij) ≪≫ (S.relabelIso T j).symm⟩

theorem FiniteIndecomposableSkeleton.relabel_surjective
    (S T : FiniteIndecomposableSkeleton k A) :
    Function.Surjective (S.relabel T) := by
  intro j
  obtain ⟨i, ⟨e⟩⟩ :=
    S.fgObj_complete (T.fgObj j) (T.fgObj_indecomposable j)
  refine ⟨i, ?_⟩
  apply T.fgObj_skeletal
  exact ⟨(S.relabelIso T i).symm ≪≫ e.symm⟩

/-- Any two complete duplicate-free right-module skeletons for the same
algebra have equivalent label types. -/
noncomputable def FiniteIndecomposableSkeleton.relabelEquiv
    (S T : FiniteIndecomposableSkeleton k A) : Fin S.n ≃ Fin T.n :=
  Equiv.ofBijective (S.relabel T)
    ⟨S.relabel_injective T, S.relabel_surjective T⟩

/-- The ambient Auslander--Reiten surplus does not depend on the chosen
complete duplicate-free right-module skeleton. -/
theorem FiniteIndecomposableSkeleton.ambientARSurplus_eq
    (S T : FiniteIndecomposableSkeleton k A) :
    S.ambientARSurplus = T.ambientARSurplus := by
  letI : EnoughProjectives (FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let TS := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TT := T.finiteTauCategoryData.toFiniteRightTauCategoryData
  let E : FinitelyGeneratedCategory A ≌ FinitelyGeneratedCategory A :=
    CategoryTheory.Equivalence.refl
  letI : E.functor.Additive := ⟨by intros; rfl⟩
  have h := FiniteTauMatrix.surplus_eq_of_equivalence
    TS TT E (S.relabelEquiv T) (S.relabelIso T)
  have hS : TS.IsProjective = fun i ↦ Projective (S.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj TS i
  have hT : TT.IsProjective = fun i ↦ Projective (T.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj TT i
  rw [hS, hT] at h
  exact h

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
    [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
/-- An algebra equivalence carries the generated ideal `AeA` to the ideal
generated by the image of `e`. -/
theorem primitiveIdeal_eq_comap_algEquiv (f : A ≃ₐ[k] B) (e : A) :
    primitiveIdeal e = (primitiveIdeal (f e)).comap f := by
  apply le_antisymm
  · rw [primitiveIdeal, TwoSidedIdeal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (TwoSidedIdeal.mem_comap f).mpr
      (TwoSidedIdeal.subset_span (Set.mem_singleton (f e)))
  · intro x hx
    rw [TwoSidedIdeal.mem_comap] at hx
    have hle : primitiveIdeal (f e) ≤
        (primitiveIdeal e).comap f.symm := by
      rw [primitiveIdeal, TwoSidedIdeal.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (TwoSidedIdeal.mem_comap f.symm).mpr (by
        rw [f.symm_apply_apply]
        exact TwoSidedIdeal.subset_span (Set.mem_singleton e))
    have hx' := hle hx
    simpa only [TwoSidedIdeal.mem_comap, f.symm_apply_apply] using hx'

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
    [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
theorem primitiveIdeal_ringCon_eq_comap_algEquiv
    (f : A ≃ₐ[k] B) (e : A) :
    (primitiveIdeal e).ringCon =
      (primitiveIdeal (f e)).ringCon.comap f := by
  change (primitiveIdeal e).ringCon =
    ((primitiveIdeal (f e)).comap f).ringCon
  rw [primitiveIdeal_eq_comap_algEquiv (k := k) f e]

/-- Algebra equivalence transports the literal primitive quotient. -/
noncomputable def primitiveQuotientAlgEquiv
    (f : A ≃ₐ[k] B) (e : A) :
    primitiveQuotientAlgebra e ≃ₐ[k]
      primitiveQuotientAlgebra (f e) :=
  RingCon.congrₐ k f
    (primitiveIdeal_ringCon_eq_comap_algEquiv (k := k) f e)

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
    [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem primitiveQuotientAlgEquiv_mk
    (f : A ≃ₐ[k] B) (e a : A) :
    primitiveQuotientAlgEquiv (k := k) f e (primitiveQuotientMap e a) =
      primitiveQuotientMap (f e) (f a) :=
  rfl

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
/-- Algebra equivalence transports primitive idempotents. -/
theorem PrimitiveIdempotentData.mapAlgEquiv
    {e : A} (D : PrimitiveIdempotentData e) (f : A ≃ₐ[k] B) :
    PrimitiveIdempotentData (f e) :=
  D.map_of_surjective (k := k) f.toRingEquiv.toRingHom f.surjective
    (fun h ↦ D.nonzero (f.injective (h.trans f.map_zero.symm)))

end MagnitudeConjecture.RightModule
