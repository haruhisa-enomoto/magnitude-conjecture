import MagnitudeConjecture.Algebra.CornerQuotient
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientSkeleton
import MagnitudeConjecture.Algebra.RightModuleRegularDecomposition
import MagnitudeConjecture.Algebra.RightModuleSimpleTop
import MagnitudeConjecture.Algebra.RightModuleSupportQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.AdditiveSubcategory

/-!
# Projective count under primitive deletion

For a complete primitive-projective presentation of a directed basic algebra,
the images of all primitive idempotents except the deleted one form a complete
primitive family in `A / AeA`.  This file identifies that family with the
indecomposable projectives in the literal primitive-quotient skeleton and
deduces the one-projective drop used by the manuscript's direct mesh count.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

noncomputable local instance primitiveQuotientNoetherian
    (p : S.ProjectiveLabel) :
    IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra (P.idempotent p))ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The primitive-projective labels other than the deleted label. -/
abbrev PrimitiveSurvivingProjectiveLabel
    (_P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :=
  {q : S.ProjectiveLabel // q ≠ p}

/-- The image of a surviving primitive idempotent in `A / Ae_p A`. -/
def primitiveQuotientIdempotent
    (p : S.ProjectiveLabel)
    (q : P.PrimitiveSurvivingProjectiveLabel p) :
    RightModule.primitiveQuotientAlgebra (P.idempotent p) :=
  RightModule.primitiveQuotientMap (P.idempotent p) (P.idempotent q.1)

/-- A primitive idempotent distinct from the deleted one has nonzero image in
the primitive quotient. -/
theorem primitiveQuotientIdempotent_ne_zero
    (p : S.ProjectiveLabel)
    (q : P.PrimitiveSurvivingProjectiveLabel p) :
    P.primitiveQuotientIdempotent p q ≠ 0 := by
  intro hzero
  have hmem : P.idempotent q.1 ∈
      RightModule.primitiveIdeal (P.idempotent p) :=
    RightModule.mem_primitiveIdeal_iff_quotient_eq_zero.mpr hzero
  have hpNot : p ∉ S.projectiveSupport (S.projectiveSimpleTop q.1) := by
    rintro ⟨f, hf⟩
    exact hf (S.hom_projectiveSimpleTop_eq_zero
      q.1 p (Ne.symm q.2) f)
  have hpAction : ∀ x : S.projectiveSimpleTop q.1,
      (MulOpposite.op (P.idempotent p)) • x = 0 :=
    (P.not_mem_projectiveSupport_iff_idempotent_smul_eq_zero
      p (S.projectiveSimpleTop q.1)).mp hpNot
  have hann : RightModule.IsAnnihilatedBy
      (RightModule.primitiveIdeal (P.idempotent p))
      (S.projectiveSimpleTop q.1) :=
    (RightModule.isAnnihilatedBy_primitiveIdeal_iff
      (P.idempotent p) (S.projectiveSimpleTop q.1)).mpr hpAction
  have hqAction : ∀ x : S.projectiveSimpleTop q.1,
      (MulOpposite.op (P.idempotent q.1)) • x = 0 :=
    fun x ↦ hann x (P.idempotent q.1) hmem
  have hqNot : q.1 ∉ S.projectiveSupport (S.projectiveSimpleTop q.1) :=
    (P.not_mem_projectiveSupport_iff_idempotent_smul_eq_zero
      q.1 (S.projectiveSimpleTop q.1)).mpr hqAction
  exact hqNot ⟨S.projectiveSimpleTopProjection q.1,
    S.projectiveSimpleTopProjection_ne_zero q.1⟩

/-- The surviving quotient idempotents are complete and orthogonal. -/
theorem primitiveQuotientIdempotents_complete
    (p : S.ProjectiveLabel) :
    CompleteOrthogonalIdempotents
      (P.primitiveQuotientIdempotent p) := by
  classical
  let f := RightModule.primitiveQuotientMap (P.idempotent p)
  have hall : CompleteOrthogonalIdempotents
      (fun q : S.ProjectiveLabel ↦ f (P.idempotent q)) :=
    P.complete.map f
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro q
    exact hall.idem q.1
  · intro q r hqr
    exact hall.ortho (fun h ↦ hqr (Subtype.ext h))
  · have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun q : S.ProjectiveLabel ↦ q ≠ p)
        (fun q ↦ f (P.idempotent q))
    have hzero : ∑ q : {q : S.ProjectiveLabel // ¬ q ≠ p},
        f (P.idempotent q.1) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      have hqp : q.1 = p := not_ne_iff.mp q.2
      rw [hqp]
      exact RightModule.primitiveQuotientMap_generator (P.idempotent p)
    change ∑ q : P.PrimitiveSurvivingProjectiveLabel p,
      f (P.idempotent q.1) = 1
    calc
      ∑ q : P.PrimitiveSurvivingProjectiveLabel p,
          f (P.idempotent q.1) =
          (∑ q : P.PrimitiveSurvivingProjectiveLabel p,
            f (P.idempotent q.1)) +
            ∑ q : {q : S.ProjectiveLabel // ¬ q ≠ p},
              f (P.idempotent q.1) := by rw [hzero, add_zero]
      _ = ∑ q : S.ProjectiveLabel, f (P.idempotent q) := hsplit
      _ = 1 := hall.complete

/-- Every surviving quotient idempotent is primitive. -/
theorem primitiveQuotientPrimitiveIdempotentData
    (p : S.ProjectiveLabel)
    (q : P.PrimitiveSurvivingProjectiveLabel p) :
    RightModule.PrimitiveIdempotentData
      (P.primitiveQuotientIdempotent p q) :=
  (P.primitive q.1).map_of_surjective (k := k)
    (RightModule.primitiveQuotientMap (P.idempotent p))
    (RightModule.primitiveIdeal (P.idempotent p)).ringCon.mk'_surjective
    (P.primitiveQuotientIdempotent_ne_zero p q)

/-- Projective labels in the quotient-module realization of the literal
surviving ambient skeleton. -/
abbrev PrimitiveQuotientFGProjectiveLabel
    (P₀ : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :=
  {x : S.PrimitiveQuotientLabel (P₀.primitive p) //
    Projective (S.primitiveQuotientFGObj (P₀.primitive p) x)}

/-- The quotient-skeleton label representing a surviving primitive right
ideal. -/
def primitiveQuotientProjectiveCoordinateLabel
    (p : S.ProjectiveLabel)
    (q : P.PrimitiveSurvivingProjectiveLabel p) :
    S.PrimitiveQuotientLabel (P.primitive p) :=
  Classical.choose
    ((S.primitiveQuotientAlmostSplitSkeleton (P.primitive p)).complete
      (RightModule.rightIdealFGObj
        (P.primitiveQuotientIdempotent p q))
      (RightModule.rightIdeal_isIndecomposableModule
        (P.primitiveQuotientPrimitiveIdempotentData p q)))

/-- The chosen quotient coordinate represents the corresponding primitive
right ideal. -/
def primitiveQuotientProjectiveCoordinateIso
    (p : S.ProjectiveLabel)
    (q : P.PrimitiveSurvivingProjectiveLabel p) :
    RightModule.rightIdealFGObj (P.primitiveQuotientIdempotent p q) ≅
      S.primitiveQuotientFGObj (P.primitive p)
        (P.primitiveQuotientProjectiveCoordinateLabel p q) :=
  Classical.choice
    (Classical.choose_spec
      ((S.primitiveQuotientAlmostSplitSkeleton (P.primitive p)).complete
        (RightModule.rightIdealFGObj
          (P.primitiveQuotientIdempotent p q))
        (RightModule.rightIdeal_isIndecomposableModule
          (P.primitiveQuotientPrimitiveIdempotentData p q))))

/-- A surviving primitive idempotent determines an indecomposable projective
label of the primitive quotient. -/
def primitiveQuotientProjectiveCoordinate
    (p : S.ProjectiveLabel)
    (q : P.PrimitiveSurvivingProjectiveLabel p) :
    P.PrimitiveQuotientFGProjectiveLabel p :=
  ⟨P.primitiveQuotientProjectiveCoordinateLabel p q,
    Projective.of_iso
      (P.primitiveQuotientProjectiveCoordinateIso p q)
      (RightModule.rightIdealFGObj_projective
        (P.primitiveQuotientPrimitiveIdempotentData p q).idempotent)⟩

/-- The surviving primitive idempotents exhaust all indecomposable
projectives in the quotient skeleton. -/
theorem primitiveQuotientProjectiveCoordinate_surjective
    (p : S.ProjectiveLabel) :
    Function.Surjective (P.primitiveQuotientProjectiveCoordinate p) := by
  classical
  let D := P.primitive p
  let B := RightModule.primitiveQuotientAlgebra (P.idempotent p)
  let σ := S.primitiveQuotientAlmostSplitSkeleton D
  let R : Set (S.PrimitiveQuotientLabel D) :=
    Set.range (P.primitiveQuotientProjectiveCoordinateLabel p)
  have hright : ∀ q : P.PrimitiveSurvivingProjectiveLabel p,
      σ.InAdd R
        (RightModule.rightIdealFGObj
          (P.primitiveQuotientIdempotent p q)) := by
    intro q
    apply (σ.inAdd_iff_of_iso
      (P.primitiveQuotientProjectiveCoordinateIso p q)).2
    exact σ.inAdd_obj ⟨q, rfl⟩
  have hbiproduct : σ.InAdd R
      (⨁ fun q : P.PrimitiveSurvivingProjectiveLabel p ↦
        RightModule.rightIdealFGObj
          (P.primitiveQuotientIdempotent p q)) :=
    σ.inAdd_biproduct
      (FintypeCat.of (P.PrimitiveSurvivingProjectiveLabel p))
      (fun q ↦ RightModule.rightIdealFGObj
        (P.primitiveQuotientIdempotent p q)) hright
  have hregular : σ.InAdd R
      (RightModule.rightRegularFGObj (B := B)) := by
    apply (σ.inAdd_iff_of_iso
      (RightModule.regularDecompositionIso
        (P.primitiveQuotientIdempotent p)
        (P.primitiveQuotientIdempotents_complete p))).2
    exact hbiproduct
  rintro ⟨x, hx⟩
  obtain ⟨n, qmap, hqmap⟩ :=
    RightModule.exists_fin_free_epimorphism
      (S.primitiveQuotientFGObj D x)
  let Free : FGModuleCat.{u}
      (RightModule.primitiveQuotientAlgebra (P.idempotent p))ᵐᵒᵖ :=
    FGModuleCat.of
      (RightModule.primitiveQuotientAlgebra (P.idempotent p))ᵐᵒᵖ
      (Fin n →
        (RightModule.primitiveQuotientAlgebra (P.idempotent p))ᵐᵒᵖ)
  letI : Epi qmap := hqmap
  obtain ⟨s, hs⟩ := hx.factors
    (𝟙 (S.primitiveQuotientFGObj D x)) qmap
  let retract : CategoryTheory.Retract
      (S.primitiveQuotientFGObj D x) Free :=
    { i := s
      r := qmap
      retract := by simpa using hs }
  let U := forget₂ (FGModuleCat.{u} Bᵐᵒᵖ) (ModuleCat.{u} Bᵐᵒᵖ)
  let regularUnderlyingIso : ModuleCat.of Bᵐᵒᵖ Bᵐᵒᵖ ≅
      (RightModule.rightRegularFGObj (B := B)).obj :=
    LinearEquiv.toModuleIso (RightModule.rightRegularLinearEquiv (A := B))
  letI : PreservesBiproduct
      (fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B)) U :=
    preservesBiproduct_of_preservesProduct U
  let freeIso : Free ≅
      ⨁ fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B) :=
    ObjectProperty.isoMk _ <|
      (ModuleCat.biproductIsoPi
        (fun _ : Fin n ↦ ModuleCat.of Bᵐᵒᵖ Bᵐᵒᵖ)).symm |>.trans <|
        (biproduct.mapIso fun _ : Fin n ↦ regularUnderlyingIso) |>.trans <|
          (U.mapBiproduct
            (fun _ : Fin n ↦
              RightModule.rightRegularFGObj (B := B))).symm
  have hfreeBiproduct : σ.InAdd R
      (⨁ fun _ : Fin n ↦ RightModule.rightRegularFGObj (B := B)) :=
    σ.inAdd_biproduct (FintypeCat.of (Fin n))
      (fun _ ↦ RightModule.rightRegularFGObj (B := B))
      (fun _ ↦ hregular)
  have hfree : σ.InAdd R Free :=
    (σ.inAdd_iff_of_iso freeIso).2 hfreeBiproduct
  have hxR : x ∈ R := σ.index_mem_of_retract_inAdd retract hfree
  obtain ⟨q, hq⟩ := hxR
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact hq

/-- A nonzero map between surviving primitive right ideals after quotienting
lifts to a nonzero map between the corresponding ambient projectives. -/
theorem exists_ambient_projective_hom_of_primitiveQuotient_hom_ne_zero
    (p : S.ProjectiveLabel)
    (q r : P.PrimitiveSurvivingProjectiveLabel p)
    (f : RightModule.rightIdealFGObj
          (P.primitiveQuotientIdempotent p q) ⟶
        RightModule.rightIdealFGObj
          (P.primitiveQuotientIdempotent p r))
    (hf : f ≠ 0) :
    ∃ g : S.fgObj q.1.label ⟶ S.fgObj r.1.label, g ≠ 0 := by
  let qmap := RightModule.primitiveQuotientMap (P.idempotent p)
  let Dq := P.primitive q.1
  let Dr := P.primitive r.1
  let DqB := P.primitiveQuotientPrimitiveIdempotentData p q
  let DrB := P.primitiveQuotientPrimitiveIdempotentData p r
  let EB := RightModule.rightIdealHomCoordinateEquiv (k := k)
    DqB.idempotent
    (RightModule.rightIdealFGObj
      (P.primitiveQuotientIdempotent p r))
  let y := EB f
  have hy : y ≠ 0 := by
    intro hzero
    apply hf
    exact EB.injective (by rw [map_zero]; exact hzero)
  obtain ⟨a, ha⟩ :=
    (RightModule.primitiveIdeal (P.idempotent p)).ringCon.mk'_surjective y.1.1
  let yr : RightModule.rightIdeal (P.idempotent r.1) :=
    ⟨P.idempotent r.1 * a * P.idempotent q.1,
      ⟨a * P.idempotent q.1, by
        change P.idempotent r.1 * (a * P.idempotent q.1) =
          P.idempotent r.1 * a * P.idempotent q.1
        rw [mul_assoc]⟩⟩
  let z : RightModule.idempotentCoordinate (k := k)
      (P.idempotent q.1)
      (RightModule.rightIdealFGObj (P.idempotent r.1)) :=
    ⟨yr, ⟨yr, by
      apply Subtype.ext
      change (P.idempotent r.1 * a * P.idempotent q.1) *
          P.idempotent q.1 =
        P.idempotent r.1 * a * P.idempotent q.1
      rw [mul_assoc, Dq.idempotent.eq]⟩⟩
  have hzmap : qmap z.1.1 = y.1.1 := by
    have hleft : P.primitiveQuotientIdempotent p r * y.1.1 = y.1.1 :=
      RightModule.rightIdeal_fixed DrB.idempotent y.1
    have hright : y.1.1 * P.primitiveQuotientIdempotent p q = y.1.1 :=
      congrArg Subtype.val
        (RightModule.idempotentCoordinate_fixed DqB.idempotent _ y)
    change qmap a = y.1.1 at ha
    change qmap (P.idempotent r.1 * a * P.idempotent q.1) = y.1.1
    rw [map_mul, map_mul, ha]
    change P.primitiveQuotientIdempotent p r * y.1.1 *
      P.primitiveQuotientIdempotent p q = y.1.1
    rw [hleft, hright]
  have hz : z ≠ 0 := by
    intro hzero
    apply hy
    apply Subtype.ext
    apply Subtype.ext
    change y.1.1 = 0
    rw [← hzmap]
    have hzval := congrArg (fun w ↦ qmap w.1.1) hzero
    change qmap z.1.1 = qmap (0 : A) at hzval
    exact hzval.trans (map_zero qmap)
  let EA := RightModule.rightIdealHomCoordinateEquiv (k := k)
    Dq.idempotent (RightModule.rightIdealFGObj (P.idempotent r.1))
  let g₀ := EA.symm z
  have hg₀ : g₀ ≠ 0 := by
    change EA.symm z ≠ 0
    intro hzero
    apply hz
    apply EA.symm.injective
    simpa using hzero
  let iq := P.primitiveProjectiveIso q.1
  let ir := P.primitiveProjectiveIso r.1
  let g := iq.inv ≫ g₀ ≫ ir.hom
  have hg : g ≠ 0 := by
    intro hzero
    apply hg₀
    have h := congrArg
      (fun w ↦ iq.hom ≫ w ≫ ir.inv) hzero
    simpa [g, Category.assoc] using h
  exact ⟨g, hg⟩

/-- Directedness prevents two distinct surviving primitive projectives from
becoming isomorphic in the primitive quotient. -/
theorem primitiveQuotientProjectiveCoordinate_injective
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.ProjectiveLabel) :
    Function.Injective (P.primitiveQuotientProjectiveCoordinate p) := by
  intro q r hqr
  have hlabel :
      P.primitiveQuotientProjectiveCoordinateLabel p q =
        P.primitiveQuotientProjectiveCoordinateLabel p r :=
    congrArg Subtype.val hqr
  let e : RightModule.rightIdealFGObj
        (P.primitiveQuotientIdempotent p q) ≅
      RightModule.rightIdealFGObj
        (P.primitiveQuotientIdempotent p r) :=
    (P.primitiveQuotientProjectiveCoordinateIso p q).trans <|
      (eqToIso (congrArg
        (fun x ↦ S.primitiveQuotientFGObj (P.primitive p) x)
        hlabel)).trans <|
        (P.primitiveQuotientProjectiveCoordinateIso p r).symm
  have ehom_ne : e.hom ≠ 0 := by
    intro hzero
    have hid : 𝟙 (RightModule.rightIdealFGObj
        (P.primitiveQuotientIdempotent p q)) = 0 := by
      rw [← e.hom_inv_id, hzero, zero_comp]
    exact (RightModule.rightIdealFGObj_indecomposable
      (P.primitiveQuotientPrimitiveIdempotentData p q)).1
        ((CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hid)
  have einv_ne : e.inv ≠ 0 := by
    intro hzero
    have hid : 𝟙 (RightModule.rightIdealFGObj
        (P.primitiveQuotientIdempotent p r)) = 0 := by
      rw [← e.inv_hom_id, hzero, zero_comp]
    exact (RightModule.rightIdealFGObj_indecomposable
      (P.primitiveQuotientPrimitiveIdempotentData p r)).1
        ((CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hid)
  obtain ⟨f, hf⟩ :=
    P.exists_ambient_projective_hom_of_primitiveQuotient_hom_ne_zero
      p q r e.hom ehom_ne
  obtain ⟨g, hg⟩ :=
    P.exists_ambient_projective_hom_of_primitiveQuotient_hom_ne_zero
      p r q e.inv einv_ne
  let O := S.directedLinearOrder H
  have hqrLe : O.le q.1.label r.1.label :=
    S.directedLinearOrder_le_of_hom_ne_zero H f hf
  have hrqLe : O.le r.1.label q.1.label :=
    S.directedLinearOrder_le_of_hom_ne_zero H g hg
  have hlabels : q.1.label = r.1.label := O.le_antisymm _ _ hqrLe hrqLe
  apply Subtype.ext
  apply S.projectiveLabelEquivSubtype.injective
  exact Subtype.ext hlabels

/-- Surviving ambient primitive labels are exactly the indecomposable
projectives of the quotient-module skeleton. -/
def primitiveQuotientProjectiveEquiv
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.ProjectiveLabel) :
    P.PrimitiveSurvivingProjectiveLabel p ≃
      P.PrimitiveQuotientFGProjectiveLabel p :=
  Equiv.ofBijective (P.primitiveQuotientProjectiveCoordinate p)
    ⟨P.primitiveQuotientProjectiveCoordinate_injective H p,
      P.primitiveQuotientProjectiveCoordinate_surjective p⟩

/-- Projectivity in the quotient-module realization is equivalent to
projectivity in the annihilated full subcategory. -/
def primitiveQuotientFGProjectiveEquivSubcategory
    (p : S.ProjectiveLabel) :
    P.PrimitiveQuotientFGProjectiveLabel p ≃
      {x : S.PrimitiveQuotientLabel (P.primitive p) //
        Projective (S.primitiveQuotientLabelObj (P.primitive p) x)} where
  toFun x := ⟨x.1,
    ((RightModule.primitiveQuotientEquivalence
      (k := k) (P.idempotent p)).map_projective_iff
        (S.primitiveQuotientLabelObj (P.primitive p) x.1)).1 x.2⟩
  invFun x := ⟨x.1,
    ((RightModule.primitiveQuotientEquivalence
      (k := k) (P.idempotent p)).map_projective_iff
        (S.primitiveQuotientLabelObj (P.primitive p) x.1)).2 x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Deleting one chosen primitive idempotent removes exactly one
indecomposable projective from the quotient. -/
theorem card_ambientProjective_eq_primitiveQuotientProjective_add_one
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.ProjectiveLabel) :
    Nat.card {x : Fin S.n // Projective (S.fgObj x)} =
      Nat.card {x : S.PrimitiveQuotientLabel (P.primitive p) //
        Projective (S.primitiveQuotientLabelObj (P.primitive p) x)} + 1 := by
  classical
  have hdelete : Nat.card S.ProjectiveLabel =
      Nat.card (P.PrimitiveSurvivingProjectiveLabel p) + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hcard := Fintype.card_congr (Equiv.optionSubtypeNe p)
    simpa using hcard.symm
  calc
    Nat.card {x : Fin S.n // Projective (S.fgObj x)} =
        Nat.card S.ProjectiveLabel :=
      (Nat.card_congr S.projectiveLabelEquivSubtype).symm
    _ = Nat.card (P.PrimitiveSurvivingProjectiveLabel p) + 1 := hdelete
    _ = Nat.card {x : S.PrimitiveQuotientLabel (P.primitive p) //
          Projective (S.primitiveQuotientLabelObj (P.primitive p) x)} + 1 := by
      rw [Nat.card_congr ((P.primitiveQuotientProjectiveEquiv H p).trans
        (P.primitiveQuotientFGProjectiveEquivSubcategory p))]

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
