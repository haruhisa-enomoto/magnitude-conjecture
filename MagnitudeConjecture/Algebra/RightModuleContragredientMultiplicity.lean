import MagnitudeConjecture.Algebra.RightModulePrimitiveContragredient
import MagnitudeConjecture.Algebra.RightModuleStandardMesh
import MagnitudeConjecture.Algebra.RightModuleTranslationMultiplicity

/-!
# Multiplicities under contragredient duality

A label-aligned anti-equivalence preserves finite Krull--Schmidt
multiplicities.  For module skeletons, the two-sided tau-category identity
then rewrites an arrow leaving a noninjective module as an arrow entering its
inverse Auslander--Reiten translate.  These are the two numerical transports
used by the manuscript's negative new-mesh construction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A C : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable [Ring C] [Algebra k C] [FiniteDimensional k C]
  [IsNoetherianRing Cᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable (T : RightModule.FiniteIndecomposableSkeleton k C)

/-- A label-aligned anti-equivalence preserves the multiplicity of every
selected indecomposable in every finitely generated module. -/
theorem indecomposableMultiplicity_map_alignedAntiEquivalence
    (D : IndecomposableSkeleton.AlignedAntiEquivalence
      S.almostSplitSkeleton T.almostSplitSkeleton)
    (p : Fin S.n) (M : RightModule.FinitelyGeneratedCategory A) :
    T.indecomposableMultiplicity (D.labelEquiv p)
        (D.categoryEquiv.functor.obj (Opposite.op M)) =
      S.indecomposableMultiplicity p M := by
  let c := S.chosenLabelDecomposition M
  let d : D.categoryEquiv.functor.obj (Opposite.op M) ≅
      ⨁ fun i : Fin c.n ↦ T.fgObj (D.labelEquiv (c.label i)) :=
    (D.categoryEquiv.functor.mapIso c.iso.op).symm.trans
      (D.sumIso S.almostSplitSkeleton T.almostSplitSkeleton
        (FintypeCat.of (Fin c.n)) c.label)
  rw [T.indecomposableMultiplicity_eq_of_decomposition
    (D.labelEquiv p) _ d]
  rw [S.indecomposableMultiplicity_eq_of_decomposition p M c.iso]
  congr 1
  funext i
  simp only [D.labelEquiv.injective.eq_iff]

/-- An ambient arrow between selected modules reverses under contragredient
duality.  The proof compares the dual right almost-split middle with the
original left almost-split middle and then uses translation invariance of
arrow multiplicities. -/
theorem contragredient_arrowMultiplicity_eq_reverse [IsAlgClosed k]
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)})
    (y : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity
        S.contragredientSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
        y (S.contragredientNonprojectiveLabel x).1 =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x.1 y := by
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  let q := S.contragredientNonprojectiveLabel x
  let AopAR := Sop.minimalRightAlmostSplitAt q.1
  let g : S.fgObj x.1 ⟶
      B.backward.categoryEquiv.functor.obj
        (Opposite.op AopAR.middle) :=
    (B.backward.objIso q.1).inv ≫
      B.backward.categoryEquiv.functor.map AopAR.map.op
  have hgAS : IsLeftAlmostSplit g :=
    (AopAR.rightAlmostSplit.map_op_equivalence
      B.backward.categoryEquiv).precomp_iso
        (B.backward.objIso q.1).symm
  have hgMin : IsLeftMinimal g :=
    (AopAR.rightMinimal.map_op_equivalence
      B.backward.categoryEquiv).precomp_iso
        (B.backward.objIso q.1).symm
  let z := (S.rightTranslationEquiv).symm x
  let AAR := S.minimalRightAlmostSplitAt z.1
  let f : S.fgObj x.1 ⟶ AAR.middle :=
    (S.noninjectiveLeftSourceIso x).hom ≫ S.rightKernelMap z
  have hfAS : IsLeftAlmostSplit f :=
    (S.rightKernelMap_leftAlmostSplit z).precomp_iso
      (S.noninjectiveLeftSourceIso x)
  have hfMin : IsLeftMinimal f :=
    (S.rightKernelMap_leftMinimal z).precomp_iso
      (S.noninjectiveLeftSourceIso x)
  obtain ⟨eMiddle, _heMiddle⟩ :=
    exists_leftAlmostSplit_middleIso hgAS hgMin hfAS hfMin
  calc
    FiniteTauMatrix.arrowMultiplicity
          Sop.finiteTauCategoryData.toFiniteRightTauCategoryData y q.1 =
        Sop.indecomposableMultiplicity y AopAR.middle :=
      by
        simpa only [AopAR,
          Sop.meshRightAlmostSplitAt_eq_of_not_projective q.1 q.2] using
          (Sop.indecomposableMultiplicity_meshRightMiddle y q.1).symm
    _ = S.indecomposableMultiplicity y
          (B.backward.categoryEquiv.functor.obj
            (Opposite.op AopAR.middle)) :=
      (Sop.indecomposableMultiplicity_map_alignedAntiEquivalence
        S B.backward y AopAR.middle).symm
    _ = S.indecomposableMultiplicity y AAR.middle :=
      S.indecomposableMultiplicity_iso_invariant y eMiddle
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData y z.1 :=
      by
        simpa only [AAR,
          S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2] using
          S.indecomposableMultiplicity_meshRightMiddle y z.1
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData x.1 y :=
      (S.arrowMultiplicity_eq_inverseTranslation x y).symm

/-- Cycle-freeness of nonzero nonisomorphisms is preserved by the
label-aligned contragredient skeleton.  An opposite arrow is carried back to
an original arrow with its direction reversed, so an opposite cycle would
give an original cycle. -/
theorem contragredientSkeleton_hasAcyclicNonzeroNonisomorphisms
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.contragredientSkeleton.HasAcyclicNonzeroNonisomorphisms := by
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  have hedge : ∀ {i j : Fin S.n}, Sop.NonzeroNonisomorphism i j →
      S.NonzeroNonisomorphism j i := by
    intro i j h
    change ∃ f : S.contragredientAlmostSplitSkeleton.obj i ⟶
      S.contragredientAlmostSplitSkeleton.obj j,
        f ≠ 0 ∧ ¬ IsIso f at h
    obtain ⟨f, hfzero, hfiso⟩ := h
    let g : S.fgObj j ⟶ S.fgObj i :=
      (B.backward.objIso j).inv ≫
        B.backward.categoryEquiv.functor.map f.op ≫
          (B.backward.objIso i).hom
    refine ⟨g, ?_, ?_⟩
    · intro hgzero
      have hmapzero : B.backward.categoryEquiv.functor.map f.op = 0 := by
        simpa [g] using hgzero
      have hfopzero : f.op = 0 :=
        (B.backward.categoryEquiv.functor.map_eq_zero_iff).mp hmapzero
      exact hfzero (Quiver.Hom.op_inj (by simpa using hfopzero))
    · intro hgiso
      letI : IsIso g := hgiso
      haveI : IsIso
          ((B.backward.objIso j).inv ≫
            (B.backward.categoryEquiv.functor.map f.op ≫
              (B.backward.objIso i).hom)) := by
        change IsIso g
        infer_instance
      haveI : IsIso
          (B.backward.categoryEquiv.functor.map f.op ≫
            (B.backward.objIso i).hom) :=
        IsIso.of_isIso_comp_left (B.backward.objIso j).inv _
      haveI : IsIso (B.backward.categoryEquiv.functor.map f.op) :=
        IsIso.of_isIso_comp_right _ (B.backward.objIso i).hom
      haveI : IsIso f.op :=
        isIso_of_fully_faithful
          B.backward.categoryEquiv.functor f.op
      exact hfiso ((isIso_op_iff f).mp inferInstance)
  intro i hcycle
  apply H i
  have hreverse : Relation.TransGen
      (fun a b ↦ S.NonzeroNonisomorphism b a) i i :=
    hcycle.lift id (by
      intro a b hab
      exact hedge hab)
  exact (Relation.transGen_swap (r := S.NonzeroNonisomorphism)).mp hreverse

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
