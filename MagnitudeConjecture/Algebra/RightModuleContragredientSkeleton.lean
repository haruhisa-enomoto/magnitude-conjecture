import MagnitudeConjecture.Algebra.RightModuleAlmostSplit
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality

/-!
# The label-aligned contragredient finite skeleton

Finite-dimensional contragredient duality sends the chosen right-module
skeleton of `A` to a complete duplicate-free right-module skeleton of
`Aᵐᵒᵖ`.  We retain the same finite label type, so later dualization of a new
mesh reverses its endpoints without introducing a second arbitrary relabeling.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A module is killed by `AeA` exactly when its contragredient dual is
killed by the opposite primitive ideal. -/
theorem isAnnihilatedBy_primitiveIdeal_contragredient_iff
    (e : A) (M : RightModule.FinitelyGeneratedCategory A) :
    IsAnnihilatedBy (primitiveIdeal (MulOpposite.op e))
        ((Contragredient.dualFunctor k Aᵐᵒᵖ).obj
          (Opposite.op M)) ↔
      IsAnnihilatedBy (primitiveIdeal e) M := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Module k M := Module.restrictScalars k Aᵐᵒᵖ M
  letI : IsScalarTower k Aᵐᵒᵖ M :=
    IsScalarTower.restrictScalars k Aᵐᵒᵖ M
  rw [isAnnihilatedBy_primitiveIdeal_iff,
    isAnnihilatedBy_primitiveIdeal_iff]
  constructor
  · intro hdual x
    apply Module.eval_apply_injective k
    apply LinearMap.ext
    intro f
    have h := congrArg
      (fun q : Module.Dual k M ↦ q x) (hdual f)
    change f ((MulOpposite.op e) • x) = 0 at h
    simpa [Module.Dual.eval_apply] using h
  · intro hM f
    apply LinearMap.ext
    intro x
    change (show Module.Dual k M from f)
      ((MulOpposite.op e) • x) = 0
    rw [hM x]
    simp

/-- The contragredient dual of one selected right `A`-module, regarded as a
right `Aᵐᵒᵖ`-module. -/
def contragredientFGObj (i : Fin S.n) :
    RightModule.FinitelyGeneratedCategory Aᵐᵒᵖ :=
  (Contragredient.dualFunctor k Aᵐᵒᵖ).obj
    (Opposite.op (S.fgObj i))

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Contragredient duality preserves the indecomposability of every selected
skeleton object. -/
theorem contragredientFGObj_indecomposable (i : Fin S.n) :
    Indecomposable (S.contragredientFGObj i).obj := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hM : Foundation.IsIndecomposableModule (Aᵐᵒᵖ)ᵐᵒᵖ
      (S.contragredientFGObj i) :=
    Contragredient.dualFunctor_indec k Aᵐᵒᵖ
      (S.fgObj_isIndecomposableModule i)
  exact (indecomposable_iff_obj
    (k := k) (A := Aᵐᵒᵖ) (S.contragredientFGObj i)).1
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := Aᵐᵒᵖ) (S.contragredientFGObj i)).1 hM)

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The label-aligned dual family has no repeated isomorphism classes. -/
theorem contragredientFGObj_skeletal {i j : Fin S.n}
    (h : Nonempty (S.contragredientFGObj i ≅
      S.contragredientFGObj j)) :
    i = j := by
  obtain ⟨e⟩ := h
  let eback : S.fgObj i ≅ S.fgObj j :=
    (Contragredient.forwardBidualIso k Aᵐᵒᵖ (S.fgObj i)).trans
      (((Contragredient.reverseDualFunctor k Aᵐᵒᵖ).mapIso e.op).symm.trans
        (Contragredient.forwardBidualIso k Aᵐᵒᵖ (S.fgObj j)).symm)
  exact S.fgObj_skeletal ⟨eback⟩

/-- Every finite-dimensional indecomposable right `Aᵐᵒᵖ`-module is the
dual of a uniquely labelled object of the original skeleton. -/
theorem contragredientFGObj_complete
    (M : RightModule.Category Aᵐᵒᵖ)
    (hM : RightModule.IsFiniteIndecomposable k Aᵐᵒᵖ M) :
    ∃ i : Fin S.n, Nonempty (M ≅ (S.contragredientFGObj i).obj) := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Mfg : RightModule.FinitelyGeneratedCategory Aᵐᵒᵖ :=
    @RightModule.finitelyGeneratedOfFiniteDimensional
      k _ Aᵐᵒᵖ _ _ M hM.1
  have hMfoundation :
      Foundation.IsIndecomposableModule (Aᵐᵒᵖ)ᵐᵒᵖ Mfg :=
    (fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := Aᵐᵒᵖ) Mfg).2
        ((indecomposable_iff_obj
          (k := k) (A := Aᵐᵒᵖ) Mfg).2 hM.2)
  let N : RightModule.FinitelyGeneratedCategory A :=
    (Contragredient.reverseDualFunctor k Aᵐᵒᵖ).obj
      (Opposite.op Mfg)
  have hNfoundation : Foundation.IsIndecomposableModule Aᵐᵒᵖ N :=
    Contragredient.reverseDualFunctor_indec k Aᵐᵒᵖ hMfoundation
  have hNindec : Indecomposable N.obj :=
    (indecomposable_iff_obj (k := k) (A := A) N).1
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := A) N).1 hNfoundation)
  obtain ⟨i, ⟨eObj⟩⟩ := S.complete N.obj
    ⟨RightModule.finite_over_field_of_finitelyGenerated k A N,
      hNindec⟩
  let eFG : N ≅ S.fgObj i := ObjectProperty.isoMk _ eObj
  let eTarget : Mfg ≅ S.contragredientFGObj i :=
    (Contragredient.reverseBidualIso k Aᵐᵒᵖ Mfg).trans
      ((Contragredient.dualFunctor k Aᵐᵒᵖ).mapIso eFG.op).symm
  exact ⟨i, ⟨(forget₂
    (RightModule.FinitelyGeneratedCategory Aᵐᵒᵖ)
      (RightModule.Category Aᵐᵒᵖ)).mapIso eTarget⟩⟩

/-- The complete opposite-algebra skeleton obtained by dualizing `S`, with
the same literal finite label type. -/
def contragredientSkeleton :
    RightModule.FiniteIndecomposableSkeleton k Aᵐᵒᵖ where
  n := S.n
  obj i := (S.contragredientFGObj i).obj
  obj_finite i :=
    RightModule.finite_over_field_of_finitelyGenerated k Aᵐᵒᵖ
      (S.contragredientFGObj i)
  obj_indecomposable := S.contragredientFGObj_indecomposable
  eq_of_iso := by
    intro i j h
    obtain ⟨e⟩ := h
    exact S.contragredientFGObj_skeletal
      ⟨ObjectProperty.isoMk _ e⟩
  complete := S.contragredientFGObj_complete

@[simp]
theorem contragredientSkeleton_n :
    S.contragredientSkeleton.n = S.n := rfl

/-- The finitely generated object produced by the new skeleton is the
concrete contragredient object at the same label. -/
def contragredientSkeleton_fgObjIso (i : Fin S.n) :
    S.contragredientSkeleton.fgObj i ≅ S.contragredientFGObj i :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- A label is removed by primitive deletion in the opposite skeleton exactly
when the same label is removed in the original skeleton. -/
theorem mem_contragredient_primitiveKilledLabels_iff
    {e : A} (D : PrimitiveIdempotentData e) (i : Fin S.n) :
    i ∈ S.contragredientSkeleton.primitiveKilledLabels D.opposite ↔
      i ∈ S.primitiveKilledLabels D := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  change (∀ f : S.contragredientFGObj i,
      (MulOpposite.op (MulOpposite.op e)) • f = 0) ↔
    ∀ x : S.fgObj i, (MulOpposite.op e) • x = 0
  rw [← isAnnihilatedBy_primitiveIdeal_iff,
    ← isAnnihilatedBy_primitiveIdeal_iff]
  exact isAnnihilatedBy_primitiveIdeal_contragredient_iff
    e (S.fgObj i)

/-- Primitive deletion selects literally the same finite label set after
passing to the label-aligned contragredient skeleton. -/
theorem contragredient_primitiveKilledLabels
    {e : A} (D : PrimitiveIdempotentData e) :
    S.contragredientSkeleton.primitiveKilledLabels D.opposite =
      S.primitiveKilledLabels D := by
  ext i
  exact S.mem_contragredient_primitiveKilledLabels_iff D i

section AlmostSplitAlignment

variable [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]

/-- The opposite finite skeleton in the exact interface used for
finite-type almost-split sequences. -/
def contragredientAlmostSplitSkeleton :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton
      (Aᵐᵒᵖ)ᵐᵒᵖ (Fin S.n) :=
  S.contragredientSkeleton.almostSplitSkeleton

/-- Contragredient duality aligned with the original and opposite finite
skeletons. Both directions use the identity equivalence on labels. -/
def contragredientAlignedBiduality :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality
      S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton := by
  let forward :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedAntiEquivalence
        S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton :=
    { categoryEquiv := Contragredient.dualityEquivalence k Aᵐᵒᵖ
      labelEquiv := Equiv.refl _
      objIso := fun i ↦ (S.contragredientSkeleton_fgObjIso i).symm }
  let backward :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedAntiEquivalence
        S.contragredientAlmostSplitSkeleton S.almostSplitSkeleton :=
    { categoryEquiv := Contragredient.reverseDualityEquivalence k Aᵐᵒᵖ
      labelEquiv := Equiv.refl _
      objIso := fun i ↦
        ((Contragredient.reverseDualFunctor k Aᵐᵒᵖ).mapIso
          (S.contragredientSkeleton_fgObjIso i).op).symm.trans
            (Contragredient.forwardBidualIso k Aᵐᵒᵖ
              (S.fgObj i)).symm }
  exact { forward := forward, backward := backward, backward_label := rfl }

@[simp]
theorem contragredientAlignedBiduality_forward_label
    (i : Fin S.n) :
    S.contragredientAlignedBiduality.forward.labelEquiv i = i := rfl

@[simp]
theorem contragredientAlignedBiduality_backward_label
    (i : Fin S.n) :
    S.contragredientAlignedBiduality.backward.labelEquiv i = i := rfl

end AlmostSplitAlignment

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
