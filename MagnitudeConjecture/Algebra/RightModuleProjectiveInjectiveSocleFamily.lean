import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleRejection

/-!
# Simultaneous socle rejection for a basic projective-injective family

This file packages the sum of the embedded socle ideals belonging to a finite
basic family of indecomposable projective-injective right modules.  Its first
layer identifies the modules surviving the simultaneous quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The two-sided annihilator in `A` of a right `A`-module represented as a
left `Aᵐᵒᵖ`-module. -/
def rightModuleAnnihilator
    (X : FinitelyGeneratedCategory A) : TwoSidedIdeal A :=
  ((Module.annihilator Aᵐᵒᵖ X).toTwoSided).unop

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- An ideal annihilates a right module exactly when it is contained in the
module's two-sided annihilator. -/
theorem isAnnihilatedBy_iff_le_rightModuleAnnihilator
    (I : TwoSidedIdeal A) (X : FinitelyGeneratedCategory A) :
    IsAnnihilatedBy I X ↔ I ≤ rightModuleAnnihilator X := by
  constructor
  · intro h a ha
    rw [rightModuleAnnihilator, TwoSidedIdeal.mem_unop_iff,
      Ideal.mem_toTwoSided, Module.mem_annihilator]
    exact fun x ↦ h x a ha
  · intro h x a ha
    have ha' := h ha
    rw [rightModuleAnnihilator, TwoSidedIdeal.mem_unop_iff,
      Ideal.mem_toTwoSided, Module.mem_annihilator] at ha'
    exact ha' x

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- A supremum of two-sided ideals annihilates a module exactly when every
member of the family does. -/
theorem isAnnihilatedBy_iSup
    {ι : Type*} (I : ι → TwoSidedIdeal A)
    (X : FinitelyGeneratedCategory A) :
    IsAnnihilatedBy (⨆ i, I i) X ↔ ∀ i, IsAnnihilatedBy (I i) X := by
  constructor
  · intro h i
    rw [isAnnihilatedBy_iff_le_rightModuleAnnihilator] at h ⊢
    exact (le_iSup I i).trans h
  · intro h
    rw [isAnnihilatedBy_iff_le_rightModuleAnnihilator]
    exact iSup_le fun i ↦
      (isAnnihilatedBy_iff_le_rightModuleAnnihilator (I i) X).1 (h i)

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Annihilation is contravariant in the ideal. -/
theorem isAnnihilatedBy_of_le
    {I J : TwoSidedIdeal A} (hIJ : I ≤ J)
    {X : FinitelyGeneratedCategory A} (hX : IsAnnihilatedBy J X) :
    IsAnnihilatedBy I X :=
  fun x a ha ↦ hX x a (hIJ ha)

/-- A projective object in the category annihilated by `I` remains
projective in the smaller full subcategory annihilated by a larger ideal
`J`. -/
theorem idealQuotientSubcategory_projective_of_le
    {I J : TwoSidedIdeal A} (hIJ : I ≤ J)
    (M : FinitelyGeneratedCategory A) (hMJ : IsAnnihilatedBy J M)
    (hMI : Projective
      (⟨M, isAnnihilatedBy_of_le hIJ hMJ⟩ :
        IdealQuotientSubcategory I)) :
    Projective (⟨M, hMJ⟩ : IdealQuotientSubcategory J) := by
  let MI : IdealQuotientSubcategory I :=
    ⟨M, isAnnihilatedBy_of_le hIJ hMJ⟩
  letI : Projective MI := hMI
  constructor
  intro E X f e _
  let EI : IdealQuotientSubcategory I :=
    ⟨E.obj, isAnnihilatedBy_of_le hIJ E.property⟩
  let XI : IdealQuotientSubcategory I :=
    ⟨X.obj, isAnnihilatedBy_of_le hIJ X.property⟩
  let fI : MI ⟶ XI := ObjectProperty.homMk f.hom
  let eI : EI ⟶ XI := ObjectProperty.homMk e.hom
  letI : Epi e.hom := idealQuotientSubcategory_epi_ambient J e
  letI : Epi eI := by
    constructor
    intro Z g h hgh
    apply ObjectProperty.hom_ext
    apply (cancel_epi e.hom).1
    simpa [eI] using congrArg InducedCategory.Hom.hom hgh
  obtain ⟨g, hg⟩ := Projective.factors fI eI
  refine ⟨ObjectProperty.homMk g.hom, ?_⟩
  apply ObjectProperty.hom_ext
  simpa [fI, eI] using congrArg InducedCategory.Hom.hom hg

/-- An injective object in the category annihilated by `I` remains
injective in the smaller full subcategory annihilated by a larger ideal
`J`. -/
theorem idealQuotientSubcategory_injective_of_le
    {I J : TwoSidedIdeal A} (hIJ : I ≤ J)
    (M : FinitelyGeneratedCategory A) (hMJ : IsAnnihilatedBy J M)
    (hMI : Injective
      (⟨M, isAnnihilatedBy_of_le hIJ hMJ⟩ :
        IdealQuotientSubcategory I)) :
    Injective (⟨M, hMJ⟩ : IdealQuotientSubcategory J) := by
  let MI : IdealQuotientSubcategory I :=
    ⟨M, isAnnihilatedBy_of_le hIJ hMJ⟩
  letI : Injective MI := hMI
  constructor
  intro X E g f _
  let XI : IdealQuotientSubcategory I :=
    ⟨X.obj, isAnnihilatedBy_of_le hIJ X.property⟩
  let EI : IdealQuotientSubcategory I :=
    ⟨E.obj, isAnnihilatedBy_of_le hIJ E.property⟩
  let gI : XI ⟶ MI := ObjectProperty.homMk g.hom
  let fI : XI ⟶ EI := ObjectProperty.homMk f.hom
  let Q := IdealQuotientProperty J
  let U := Q.ι
  letI : Q.Nonempty := ObjectProperty.nonempty_of_prop E.property
  letI : U.PreservesMonomorphisms :=
    Q.preservesMonomorphisms_ι_of_isNormalEpiCategory
  letI : Mono (U.map f) := U.map_mono f
  letI : Mono f.hom := by
    change Mono (U.map f)
    infer_instance
  letI : Mono fI := by
    constructor
    intro Z a b hab
    apply ObjectProperty.hom_ext
    apply (cancel_mono f.hom).1
    simpa [fI] using congrArg InducedCategory.Hom.hom hab
  obtain ⟨h, hh⟩ := Injective.factors gI fI
  refine ⟨ObjectProperty.homMk h.hom, ?_⟩
  apply ObjectProperty.hom_ext
  simpa [gI, fI] using congrArg InducedCategory.Hom.hom hh

namespace FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable (P : S.PrimitiveProjectivePresentation)

/-- The projection from a selected indecomposable projective to its quotient
by the socle, written with the skeletal projective as source, is its minimal
projective presentation. -/
def primitiveProjectiveSocleQuotientMinimalProjectivePresentation
    (p : S.ProjectiveLabel)
    (hNotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    MinimalProjectivePresentation
      (P.primitiveProjectiveSocleQuotientFGObj p) := by
  let q : S.fgObj p.label ⟶
      P.primitiveProjectiveSocleQuotientFGObj p :=
    (P.primitiveProjectiveIso p).inv ≫
      P.primitiveProjectiveSocleQuotientProjection p
  letI : Epi (P.primitiveProjectiveSocleQuotientProjection p) :=
    P.primitiveProjectiveSocleQuotientProjection_epi p
  letI : Epi q := epi_comp _ _
  have hq : q ≠ 0 := by
    intro hzero
    have hQIndecomposable : Indecomposable
        (P.primitiveProjectiveSocleQuotientFGObj p) :=
      (fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := A)
        (P.primitiveProjectiveSocleQuotientFGObj p)).1
          (P.primitiveProjectiveSocleQuotient_isIndecomposableModule
            p hNotSimple)
    apply hQIndecomposable.1
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi q).1
    rw [Category.comp_id, hzero, zero_comp]
  letI : IsLocalRing (End (S.fgObj p.label)) :=
    S.fgObj_end_isLocalRing p.label
  exact {
    p := S.fgObj p.label
    projective := p.projective
    f := q
    epi := inferInstance
    rightMinimal := isRightMinimal_of_localEnd_of_ne_zero q hq }

include P in
/-- Distinct selected projectives have distinct ambient socle-quotient
replacement labels. -/
theorem socleQuotientReplacementLabel_injective
    (p q : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hqInjective : Injective (S.fgObj q.label))
    (hpNotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (hqNotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj q.label))
    (hlabel :
      (P.socleQuotientReplacementLabel
        p hpInjective hpNotSimple).1 =
      (P.socleQuotientReplacementLabel
        q hqInjective hqNotSimple).1) :
    p = q := by
  let rp := P.socleQuotientReplacementLabel
    p hpInjective hpNotSimple
  let rq := P.socleQuotientReplacementLabel
    q hqInjective hqNotSimple
  let ep := P.primitiveProjectiveSocleQuotientAmbientIso
    p hpInjective hpNotSimple
  let eq := P.primitiveProjectiveSocleQuotientAmbientIso
    q hqInjective hqNotSimple
  let etarget : P.primitiveProjectiveSocleQuotientFGObj p ≅
      P.primitiveProjectiveSocleQuotientFGObj q :=
    ep.trans <| (eqToIso (congrArg S.fgObj hlabel)).trans eq.symm
  let Cp := P.primitiveProjectiveSocleQuotientMinimalProjectivePresentation
    p hpNotSimple
  let Cq := P.primitiveProjectiveSocleQuotientMinimalProjectivePresentation
    q hqNotSimple
  have hpq : p.label = q.label :=
    S.fgObj_skeletal ⟨Cp.objectIsoOfTargetIso Cq etarget⟩
  cases p with
  | mk p hp =>
      cases q with
      | mk q hq =>
          dsimp at hpq
          subst q
          rfl

/-- The sum of the embedded socle ideals belonging to a finite basic family
of indecomposable projective-injective labels. -/
def primitiveProjectiveSocleFamilyIdeal
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    TwoSidedIdeal A :=
  ⨆ p : {p // p ∈ T},
    P.primitiveProjectiveSocleIdeal p.1 (hInjective p.1 p.2)

/-- The socle ideal of each selected summand is contained in the simultaneous
family ideal. -/
theorem primitiveProjectiveSocleIdeal_le_familyIdeal
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    P.primitiveProjectiveSocleIdeal p (hInjective p hp) ≤
      P.primitiveProjectiveSocleFamilyIdeal T hInjective := by
  exact le_iSup
    (fun q : {q // q ∈ T} ↦
      P.primitiveProjectiveSocleIdeal q.1 (hInjective q.1 q.2))
    ⟨p, hp⟩

/-- The ambient finite labels removed by the simultaneous quotient. -/
def primitiveProjectiveSocleFamilySelectedLabels
    (T : Finset S.ProjectiveLabel) : Finset (Fin S.n) :=
  T.image fun p ↦ p.label

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem mem_primitiveProjectiveSocleFamilySelectedLabels_iff
    (T : Finset S.ProjectiveLabel) (x : Fin S.n) :
    x ∈ primitiveProjectiveSocleFamilySelectedLabels T ↔
      ∃ p, p ∈ T ∧ p.label = x := by
  classical
  simp [primitiveProjectiveSocleFamilySelectedLabels]

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- Because the selected family is basic, passing to ambient labels does not
change its cardinality. -/
theorem card_primitiveProjectiveSocleFamilySelectedLabels
    (T : Finset S.ProjectiveLabel) :
    (primitiveProjectiveSocleFamilySelectedLabels T).card = T.card := by
  classical
  rw [primitiveProjectiveSocleFamilySelectedLabels,
    Finset.card_image_of_injective]
  intro p q hpq
  cases p with
  | mk p hp =>
      cases q with
      | mk q hq =>
          dsimp at hpq
          subst q
          rfl

/-- The selected structured projectives are equivalent to their ambient
finite labels. -/
def primitiveProjectiveSocleFamilySelectedEquiv
    (T : Finset S.ProjectiveLabel) :
    {p : S.ProjectiveLabel // p ∈ T} ≃
      {x : Fin S.n //
        x ∈ primitiveProjectiveSocleFamilySelectedLabels T} := by
  classical
  let f : {p : S.ProjectiveLabel // p ∈ T} →
      {x : Fin S.n //
        x ∈ primitiveProjectiveSocleFamilySelectedLabels T} :=
    fun p ↦ ⟨p.1.label,
      (mem_primitiveProjectiveSocleFamilySelectedLabels_iff
        T p.1.label).2 ⟨p.1, p.2, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    cases p with
    | mk p hp =>
        cases q with
        | mk q hq =>
            cases p with
            | mk p hpProjective =>
                cases q with
                | mk q hqProjective =>
                    congr
                    exact congrArg Subtype.val hpq
  · intro x
    obtain ⟨p, hp, hpx⟩ :=
      (mem_primitiveProjectiveSocleFamilySelectedLabels_iff T x.1).1 x.2
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hpx

include P in
/-- An indecomposable ambient module survives the simultaneous family
quotient exactly when its label is not one of the selected projectives. -/
theorem fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (x : Fin S.n) :
    IsAnnihilatedBy (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (S.fgObj x) ↔
      ∀ p, p ∈ T → x ≠ p.label := by
  rw [primitiveProjectiveSocleFamilyIdeal, isAnnihilatedBy_iSup]
  constructor
  · intro h p hp
    exact (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p (hInjective p hp) x).1 (h ⟨p, hp⟩)
  · intro h p
    exact (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p.1 (hInjective p.1 p.2) x).2 (h p.1 p.2)

/-- Intrinsic labels of the simultaneous quotient are exactly the ambient
labels outside the selected projective family. -/
def primitiveProjectiveSocleFamilySurvivingEquiv
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    S.IdealQuotientLabel
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective) ≃
      {x : Fin S.n // ∀ p, p ∈ T → x ≠ p.label} where
  toFun x := ⟨x.1,
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective x.1).1 x.2⟩
  invFun x := ⟨x.1,
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective x.1).2 x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- The same surviving-label equivalence, stated as the complement of the
finite set of selected ambient labels. -/
def primitiveProjectiveSocleFamilySurvivingLabelsEquiv
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    S.IdealQuotientLabel
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective) ≃
      {x : Fin S.n //
        x ∉ primitiveProjectiveSocleFamilySelectedLabels T} where
  toFun x := ⟨x.1, by
    intro hx
    obtain ⟨p, hp, hpx⟩ :=
      (mem_primitiveProjectiveSocleFamilySelectedLabels_iff T x.1).1 hx
    exact (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective x.1).1 x.2 p hp hpx.symm⟩
  invFun x := ⟨x.1,
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective x.1).2 (by
        intro p hp hxp
        exact x.2 <|
          (mem_primitiveProjectiveSocleFamilySelectedLabels_iff T x.1).2
            ⟨p, hp, hxp.symm⟩)⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- The finite-ordinal quotient labels are equivalent to the complement of
the selected ambient projective family. -/
def primitiveProjectiveSocleFamilyFiniteSurvivingEquiv
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ] :
    Fin (S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).n ≃
      {x : Fin S.n //
        x ∉ primitiveProjectiveSocleFamilySelectedLabels T} :=
  (S.idealQuotientFiniteLabelEquiv
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).trans
    (P.primitiveProjectiveSocleFamilySurvivingLabelsEquiv T hInjective)

/-- Simultaneous rejection removes exactly the selected basic family of
indecomposable labels. -/
theorem card_primitiveProjectiveSocleFamilyLabel_add_card
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label)) :
    Fintype.card
        (S.IdealQuotientLabel
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)) +
      T.card = S.n := by
  classical
  rw [Fintype.card_congr
      (P.primitiveProjectiveSocleFamilySurvivingLabelsEquiv T hInjective),
    Fintype.card_subtype_compl
      (fun x : Fin S.n ↦
        x ∈ primitiveProjectiveSocleFamilySelectedLabels T),
    Fintype.card_fin]
  rw [Fintype.card_coe,
    card_primitiveProjectiveSocleFamilySelectedLabels]
  exact Nat.sub_add_cancel <| by
    rw [← card_primitiveProjectiveSocleFamilySelectedLabels]
    simpa using Finset.card_le_univ
      (primitiveProjectiveSocleFamilySelectedLabels T)

include P in
/-- The socle-quotient replacement belonging to a selected summand is not
the label of any selected projective. -/
theorem socleQuotientReplacementLabel_ne_familySelected
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    ∀ q, q ∈ T →
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1 ≠ q.label := by
  intro q hq hpq
  apply P.socleQuotientReplacementLabel_not_projective
    p (hInjective p hp) (hNotSimple p hp)
  rw [hpq]
  exact q.projective

/-- The intrinsic simultaneous-quotient label represented by
`P / soc(P)` for one selected summand `P`. -/
def primitiveProjectiveSocleFamilyReplacementLabel
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    S.IdealQuotientLabel
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective) :=
  ⟨(P.socleQuotientReplacementLabel
      p (hInjective p hp) (hNotSimple p hp)).1,
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective _).2
        (P.socleQuotientReplacementLabel_ne_familySelected
          T hInjective hNotSimple p hp)⟩

include P in
/-- Every selected replacement `P / soc(P)` is projective already in the
full subcategory annihilated by the entire family ideal. -/
theorem primitiveProjectiveSocleFamilyReplacementLabel_projective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    Projective
      (S.idealQuotientLabelObj
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (P.primitiveProjectiveSocleFamilyReplacementLabel
          T hInjective hNotSimple p hp)) := by
  let hpInjective := hInjective p hp
  let hpNotSimple := hNotSimple p hp
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let r := P.socleQuotientReplacementLabel
    p hpInjective hpNotSimple
  let hJ : RightModule.IsAnnihilatedBy J (S.fgObj r.1) :=
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective r.1).2
        (P.socleQuotientReplacementLabel_ne_familySelected
          T hInjective hNotSimple p hp)
  have hIJ : I ≤ J :=
    P.primitiveProjectiveSocleIdeal_le_familyIdeal T hInjective p hp
  let E := RightModule.idealQuotientEquivalence (k := k) I
  have hIProjective : Projective (S.idealQuotientLabelObj I r) :=
    (E.map_projective_iff (S.idealQuotientLabelObj I r)).1
      (P.socleQuotientReplacementLabel_projective
        p hpInjective hpNotSimple)
  change Projective
    (⟨S.fgObj r.1, hJ⟩ : RightModule.IdealQuotientSubcategory J)
  exact RightModule.idealQuotientSubcategory_projective_of_le
    hIJ (S.fgObj r.1) hJ hIProjective

include P in
/-- The selected summands inject into the intrinsic replacement labels of
the simultaneous quotient. -/
theorem primitiveProjectiveSocleFamilyReplacementLabel_injective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Function.Injective (fun p : {p // p ∈ T} ↦
      P.primitiveProjectiveSocleFamilyReplacementLabel
        T hInjective hNotSimple p.1 p.2) := by
  intro p q hpq
  apply Subtype.ext
  apply P.socleQuotientReplacementLabel_injective
    p.1 q.1 (hInjective p.1 p.2) (hInjective q.1 q.2)
      (hNotSimple p.1 p.2) (hNotSimple q.1 q.2)
  exact congrArg Subtype.val hpq

include P in
/-- Each selected replacement is projective over the literal simultaneous
quotient algebra. -/
theorem primitiveProjectiveSocleFamilyReplacementFGObj_projective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    Projective
      (S.idealQuotientFGObj
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (P.primitiveProjectiveSocleFamilyReplacementLabel
          T hInjective hNotSimple p hp)) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let x := P.primitiveProjectiveSocleFamilyReplacementLabel
    T hInjective hNotSimple p hp
  exact (RightModule.idealQuotientEquivalence
    (k := k) J).map_projective_iff (S.idealQuotientLabelObj J x) |>.2
      (P.primitiveProjectiveSocleFamilyReplacementLabel_projective
        T hInjective hNotSimple p hp)

/-- The finite-ordinal quotient-skeleton replacement belonging to a selected
summand. -/
def primitiveProjectiveSocleFamilyFiniteReplacementLabel
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).n :=
  (S.idealQuotientFiniteLabelEquiv
    (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).symm
      (P.primitiveProjectiveSocleFamilyReplacementLabel
        T hInjective hNotSimple p hp)

@[simp]
theorem idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
          T hInjective hNotSimple p hp) =
      P.primitiveProjectiveSocleFamilyReplacementLabel
        T hInjective hNotSimple p hp :=
  Equiv.apply_symm_apply _ _

/-- The finite quotient representative of a selected replacement is
canonically isomorphic to its intrinsic quotient representative. -/
def primitiveProjectiveSocleFamilyFiniteReplacementIso
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).fgObj
        (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
          T hInjective hNotSimple p hp) ≅
      S.idealQuotientFGObj
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (P.primitiveProjectiveSocleFamilyReplacementLabel
          T hInjective hNotSimple p hp) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let j := P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
    T hInjective hNotSimple p hp
  let x := P.primitiveProjectiveSocleFamilyReplacementLabel
    T hInjective hNotSimple p hp
  have hj : S.idealQuotientFiniteLabelEquiv J j = x :=
    P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
      T hInjective hNotSimple p hp
  exact (S.idealQuotientFiniteFGObjIso J j).trans
    ((RightModule.idealQuotientEquivalence (k := k) J).functor.mapIso
      (eqToIso (congrArg (S.idealQuotientLabelObj J) hj)))

include P in
/-- Every finite-ordinal replacement label is projective in the simultaneous
quotient skeleton. -/
theorem primitiveProjectiveSocleFamilyFiniteReplacement_projective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    Projective
      ((S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).fgObj
          (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p hp)) :=
  Projective.of_iso
    (P.primitiveProjectiveSocleFamilyFiniteReplacementIso
      T hInjective hNotSimple p hp).symm
      (P.primitiveProjectiveSocleFamilyReplacementFGObj_projective
        T hInjective hNotSimple p hp)

include P in
/-- The finite-ordinal replacement labels belonging to distinct selected
projectives are distinct. -/
theorem primitiveProjectiveSocleFamilyFiniteReplacementLabel_injective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ] :
    Function.Injective (fun p : {p // p ∈ T} ↦
      P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
        T hInjective hNotSimple p.1 p.2) := by
  intro p q hpq
  apply P.primitiveProjectiveSocleFamilyReplacementLabel_injective
    T hInjective hNotSimple
  simpa using congrArg
    (S.idealQuotientFiniteLabelEquiv
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)) hpq

include P in
/-- A finite-ordinal replacement label is nonprojective in the ambient
finite-tau category. -/
theorem primitiveProjectiveSocleFamilyFiniteReplacement_ambient_not_projective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    ¬ S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
      (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
          T hInjective hNotSimple p hp)).1 := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  rw [congrArg Subtype.val
    (P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
      T hInjective hNotSimple p hp)]
  exact P.socleQuotientReplacementLabel_not_projective
    p (hInjective p hp) (hNotSimple p hp)

include P in
/-- A selected projective is not annihilated by the simultaneous family
ideal containing its embedded socle ideal. -/
theorem fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    ¬ RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
      (S.fgObj p.label) := by
  intro hP
  exact P.fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
    p (hInjective p hp) <|
      RightModule.isAnnihilatedBy_of_le
        (P.primitiveProjectiveSocleIdeal_le_familyIdeal
          T hInjective p hp) hP

include P in
/-- The radical boundary of every selected projective is annihilated by
the entire simultaneous family ideal. -/
theorem projectiveInjectiveBoundaryRadical_isAnnihilatedBy_family
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
      (S.projectiveBoundaryRadical p.label) := by
  rw [primitiveProjectiveSocleFamilyIdeal,
    RightModule.isAnnihilatedBy_iSup]
  intro q
  apply P.isAnnihilatedBy_primitiveProjectiveSocleIdeal_of_not_iso
    q.1 (hInjective q.1 q.2)
      (S.projectiveBoundaryRadical p.label)
      (projectiveInjectiveBoundaryRadical_indecomposable
        p (hInjective p hp) (hNotSimple p hp))
  rintro ⟨e⟩
  apply P.projectiveInjectiveBoundaryRadical_not_injective
    p (hInjective p hp) (hNotSimple p hp)
  exact Injective.of_iso e.symm (hInjective q.1 q.2)

include P in
/-- Under simultaneous rejection, the maximal annihilated submodule of a
selected projective is still its Jacobson radical. -/
def idealTorsionFGObj_familyProjectiveInjectiveIsoRadical
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    RightModule.idealTorsionFGObj
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
        (S.fgObj p.label) ≅
      S.projectiveBoundaryRadical p.label := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let R := S.projectiveBoundaryRadical p.label
  let ti := RightModule.idealTorsionInclusion J (S.fgObj p.label)
  let j := S.projectiveBoundaryRadicalInclusion p.label
  have hR : RightModule.IsAnnihilatedBy J R :=
    P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy_family
      T hInjective hNotSimple p hp
  have htiNotSplit : ¬ IsSplitEpi ti := by
    intro hs
    obtain ⟨s⟩ := hs.exists_splitEpi
    let r : Retract (S.fgObj p.label)
        (RightModule.idealTorsionFGObj J (S.fgObj p.label)) :=
      { i := s.section_
        r := ti
        retract := s.id }
    exact P.fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal
      T hInjective p hp <|
        (RightModule.IdealQuotientProperty J).prop_of_retract r
          (RightModule.idealTorsionFGObj_isAnnihilatedBy
            J (S.fgObj p.label))
  let hex :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      p.label p.projective).factors ti htiNotSplit
  let h := Classical.choose hex
  have hh : h ≫ j = ti := Classical.choose_spec hex
  let l : R ⟶ RightModule.idealTorsionFGObj J (S.fgObj p.label) :=
    RightModule.idealTorsionLift J hR j
  have hl : l ≫ ti = j :=
    RightModule.idealTorsionLift_comp_inclusion J hR j
  letI : Mono ti := by
    dsimp only [ti]
    infer_instance
  letI : Mono j := by
    apply (IndecomposableSkeleton.fg_mono_iff_injective j).2
    exact (Module.jacobson Aᵐᵒᵖ (S.fgObj p.label)).subtype_injective
  exact {
    hom := h
    inv := l
    hom_inv_id := by
      apply (cancel_mono ti).1
      rw [Category.assoc, hl, hh, Category.id_comp]
    inv_hom_id := by
      apply (cancel_mono j).1
      rw [Category.assoc, hh, hl, Category.id_comp] }

/-- The radical boundary of a selected summand, bundled in the full
subcategory annihilated by the simultaneous family ideal. -/
def projectiveInjectiveBoundaryRadicalFamilyObj
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    RightModule.IdealQuotientSubcategory
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective) :=
  ⟨S.projectiveBoundaryRadical p.label,
    P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy_family
      T hInjective hNotSimple p hp⟩

include P in
/-- After simultaneous socle rejection, the radical of every selected
projective is injective in the annihilated ambient full subcategory. -/
theorem projectiveInjectiveBoundaryRadicalFamilyObj_injective
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    Injective
      (P.projectiveInjectiveBoundaryRadicalFamilyObj
        T hInjective hNotSimple p hp) := by
  let I := P.primitiveProjectiveSocleIdeal p (hInjective p hp)
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let R := S.projectiveBoundaryRadical p.label
  let hRJ : RightModule.IsAnnihilatedBy J R :=
    P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy_family
      T hInjective hNotSimple p hp
  have hIJ : I ≤ J :=
    P.primitiveProjectiveSocleIdeal_le_familyIdeal T hInjective p hp
  apply RightModule.idealQuotientSubcategory_injective_of_le
    hIJ R hRJ
  simpa only [projectiveInjectiveBoundaryRadicalObj,
    RightModule.isAnnihilatedBy_of_le] using
      (P.projectiveInjectiveBoundaryRadicalObj_injective
        p (hInjective p hp) (hNotSimple p hp))

include P in
/-- At the replacement endpoint belonging to `p`, any selected
projective-injective occurring in the ambient right middle term is `p`
itself. -/
theorem minimalRightAlmostSplitAt_replacement_familySelected_eq
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (p : S.ProjectiveLabel) (hp : p ∈ T)
    (q : S.ProjectiveLabel) (hq : q ∈ T)
    (t : (S.minimalRightAlmostSplitAt
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1).index)
    (ht : (S.minimalRightAlmostSplitAt
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1).label t = q.label) :
    q = p := by
  let rp := P.socleQuotientReplacementLabel
    p (hInjective p hp) (hNotSimple p hp)
  let B := S.minimalRightAlmostSplitAt rp.1
  have hirr : HasIrreducibleMorphism
      (S.fgObj q.label) (S.fgObj rp.1) :=
    (B.summandIrreducibleCorrespondence q.label).1 ⟨t, ht⟩
  have hr : rp.1 =
      (P.socleQuotientReplacementLabel
        q (hInjective q hq) (hNotSimple q hq)).1 :=
    (P.hasIrreducibleMorphism_from_projectiveInjective_iff
      q (hInjective q hq) (hNotSimple q hq) rp.1).1 hirr
  exact (P.socleQuotientReplacementLabel_injective
    p q (hInjective p hp) (hInjective q hq)
      (hNotSimple p hp) (hNotSimple q hq) hr).symm

include P in
/-- For each selected replacement, restricting its ambient right
almost-split source by the simultaneous family ideal preserves the number
of indecomposable summands.  The unique selected projective summand becomes
its radical and every other summand is unchanged. -/
def primitiveProjectiveSocleFamilyExceptionalSourceDecomposition
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      ((RightModule.idealQuotientEquivalence
          (k := k)
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).functor.obj
        (RightModule.idealTorsionSubcategoryObj
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
          (S.minimalRightAlmostSplitAt
            (P.socleQuotientReplacementNonprojectiveLabel
              p (hInjective p hp) (hNotSimple p hp)).1).middle)) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p (hInjective p hp) (hNotSimple p hp)
  let B := S.minimalRightAlmostSplitAt z.1
  let dA := S.minimalRightAlmostSplitAtDecomposition z.1
  have hIndec (i : Fin dA.n) : Indecomposable
      ((RightModule.idealTorsionFunctor J).obj (dA.summand i)) := by
    let t := (Fintype.equivFin B.index).symm i
    change Indecomposable
      (RightModule.idealTorsionFGObj J (S.fgObj (B.label t)))
    by_cases hi : B.label t = p.label
    · rw [hi]
      exact
        (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
          (P.idealTorsionFGObj_familyProjectiveInjectiveIsoRadical
            T hInjective hNotSimple p hp)).2
          (projectiveInjectiveBoundaryRadical_indecomposable
            p (hInjective p hp) (hNotSimple p hp))
    · let hAnn : RightModule.IsAnnihilatedBy J
          (S.fgObj (B.label t)) :=
        (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
          T hInjective (B.label t)).2 (by
            intro q hq htq
            apply hi
            have hqp : q = p :=
              P.minimalRightAlmostSplitAt_replacement_familySelected_eq
                T hInjective hNotSimple p hp q hq t htq
            simpa [hqp] using htq)
      exact
        (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
          (RightModule.idealTorsionIsoOfIsAnnihilated
            J (S.fgObj (B.label t)) hAnn)).2
          (S.fgObj_indecomposable (B.label t))
  let dT := dA.mapOfIndecomposable
    (RightModule.idealTorsionFunctor J) hIndec
  exact RightModule.idealTorsionSourceDecomposition
    (k := k) J B.middle dT
      (fun i ↦ RightModule.idealTorsionFGObj_isAnnihilatedBy
        J (dA.summand i))

include P in
/-- At each selected replacement endpoint, simultaneous socle rejection
removes exactly one indecomposable occurrence from the incoming right mesh. -/
theorem primitiveProjectiveSocleFamily_replacement_rightMiddleArity_add_one_eq_ambient
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (p : S.ProjectiveLabel) (hp : p ∈ T) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
            ).toFiniteRightTauCategoryData
        (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
          T hInjective hNotSimple p hp) + 1 =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
          (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p hp)).1 := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let r := P.primitiveProjectiveSocleFamilyReplacementLabel
    T hInjective hNotSimple p hp
  let j := P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
    T hInjective hNotSimple p hp
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p (hInjective p hp) (hNotSimple p hp)
  let B := S.minimalRightAlmostSplitAt z.1
  let dA := S.minimalRightAlmostSplitAtDecomposition z.1
  let Eq := RightModule.idealQuotientEquivalence (k := k) J
  let C := RightModule.IdealQuotientSubcategory J
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      Eq.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence Eq.functor
  let restricted := RightModule.idealTorsionTargetMap J r.2 B.map
  let mapped := Eq.functor.map restricted
  let dSource :=
    P.primitiveProjectiveSocleFamilyExceptionalSourceDecomposition
      T hInjective hNotSimple p hp
  let R := P.projectiveInjectiveBoundaryRadicalFamilyObj
    T hInjective hNotSimple p hp
  have hKernelAnnihilated : RightModule.IsAnnihilatedBy J (kernel B.map) :=
    (RightModule.IdealQuotientProperty J).prop_of_iso
      (P.socleQuotientReplacementKernelIso
        p (hInjective p hp) (hNotSimple p hp)).symm
      (P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy_family
        T hInjective hNotSimple p hp)
  let eRestrictedKernel : kernel restricted ≅ R :=
    (RightModule.idealTorsionTargetKernelIso
      J r.2 B.map hKernelAnnihilated).trans
        (ObjectProperty.isoMk _
          (P.socleQuotientReplacementKernelIso
            p (hInjective p hp) (hNotSimple p hp)))
  let eMappedKernel : kernel mapped ≅ Eq.functor.obj R :=
    (PreservesKernel.iso Eq.functor restricted).symm.trans
      (Eq.functor.mapIso eRestrictedKernel)
  have hRIndec : Indecomposable R :=
    (idealQuotientSubcategory_indecomposable_iff_ambient
      (I := J) R).2
      (projectiveInjectiveBoundaryRadical_indecomposable
        p (hInjective p hp) (hNotSimple p hp))
  have hEqRIndec : Indecomposable (Eq.functor.obj R) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      Eq.functor R).2 hRIndec
  have hKernelIndec : Indecomposable (kernel mapped) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
      eMappedKernel).2 hEqRIndec
  have hEqRInjective : Injective (Eq.functor.obj R) :=
    (Eq.map_injective_iff R).2
      (P.projectiveInjectiveBoundaryRadicalFamilyObj_injective
        T hInjective hNotSimple p hp)
  have hKernelInjective : Injective (kernel mapped) :=
    Injective.of_iso eMappedKernel.symm hEqRInjective
  letI : Injective (kernel mapped) := hKernelInjective
  have hmappedAS : IsRightAlmostSplit mapped :=
    (RightModule.idealTorsionTargetMap_isRightAlmostSplit
      J r.2 B.map B.rightAlmostSplit).map_equivalence Eq
  obtain ⟨E', g, hgMono, hgAS, hgMin, hSplit⟩ :=
    MagnitudeConjecture.CategoryTheory.exists_mono_rightAlmostSplit_complement_of_injective_kernel
      mapped hmappedAS
  letI : Mono g := hgMono
  letI : Module k E' := Module.restrictScalars k
    (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ E'
  letI : IsScalarTower k
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ E' :=
    IsScalarTower.restrictScalars k
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ E'
  letI : Module.Finite k E' :=
    RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.idealQuotientAlgebra J) E'
  obtain ⟨dE⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) E'
  let dK :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (kernel mapped) hKernelIndec
  let dSum := dK.biprod dE
  have hlocal (i : Fin dSource.n) :
      IsLocalRing (End (dSource.summand i)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := RightModule.idealQuotientAlgebra J)
        (dSource.summand i) (dSource.indecomposable i)
  have hcount := dSource.n_eq_of_iso dSum hlocal (Classical.choice hSplit)
  change dA.n = 1 + dE.n at hcount
  let q := S.idealQuotientFiniteLabelEquiv J
  have hj : q j = r := by
    exact P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
      T hInjective hNotSimple p hp
  let TQ :=
    (idealQuotientFiniteTauCategoryData S J).toFiniteRightTauCategoryData
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let eTarget : Eq.functor.obj (S.idealQuotientLabelObj J r) ≅ TQ.obj j :=
    Eq.functor.mapIso
      (eqToIso (congrArg (S.idealQuotientLabelObj J) hj.symm))
  let g' : E' ⟶ TQ.obj j := g ≫ eTarget.hom
  have hg'AS : IsRightAlmostSplit g' :=
    IsRightAlmostSplit.postcomp_iso eTarget hgAS
  have hg'Min : IsRightMinimal g' :=
    IsRightMinimal.postcomp_iso eTarget hgMin
  have hQ : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      TQ j = dE.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TQ j dE hg'AS hg'Min
  have hA : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      TA z.1 = dA.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TA z.1 dA B.rightAlmostSplit B.rightMinimal
  change MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TQ j + 1 =
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TA (q j).1
  have hz : (q j).1 = z.1 := congrArg Subtype.val hj
  rw [hQ, hz, hA]
  omega

include P in
/-- Away from all selected replacements, an ambient minimal right
almost-split middle term contains no selected projective-injective summand. -/
theorem minimalRightAlmostSplitAt_label_ne_familySelected_of_endpoint_ne
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : Fin S.n)
    (hx : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T), x ≠
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1)
    (t : (S.minimalRightAlmostSplitAt x).index) :
    ∀ p, p ∈ T →
      (S.minimalRightAlmostSplitAt x).label t ≠ p.label := by
  intro p hp
  exact P.minimalRightAlmostSplitAt_label_ne_projectiveInjective_of_endpoint_ne
    p (hInjective p hp) (hNotSimple p hp) x (hx p hp) t

include P in
/-- Away from all selected replacements, the entire ambient minimal right
almost-split middle term is annihilated by the simultaneous family ideal. -/
theorem minimalRightAlmostSplitAt_middle_isAnnihilatedBy_family_of_endpoint_ne
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : Fin S.n)
    (hx : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T), x ≠
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
      (S.minimalRightAlmostSplitAt x).middle := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let B := S.minimalRightAlmostSplitAt x
  have hsummand (t : B.index) :
      RightModule.IsAnnihilatedBy J (S.fgObj (B.label t)) :=
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective (B.label t)).2
        (P.minimalRightAlmostSplitAt_label_ne_familySelected_of_endpoint_ne
          T hInjective hNotSimple x hx t)
  have hsum : RightModule.IsAnnihilatedBy J
      (⨁ fun t : B.index ↦ S.fgObj (B.label t)) :=
    RightModule.isAnnihilatedBy_biproduct J
      (fun t : B.index ↦ S.fgObj (B.label t)) hsummand
  exact (RightModule.IdealQuotientProperty J).prop_of_iso
    B.decomposition.symm hsum

include P in
/-- At an ordinary surviving endpoint, projectivity in the simultaneous
annihilated subcategory is equivalent to ambient projectivity. -/
theorem primitiveProjectiveSocleFamilyLabelObj_projective_iff_ambient
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : S.IdealQuotientLabel
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective))
    (hx : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T), x.1 ≠
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1) :
    Projective
        (S.idealQuotientLabelObj
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective) x) ↔
      Projective (S.fgObj x.1) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let B := S.minimalRightAlmostSplitAt x.1
  exact RightModule.idealQuotient_projective_iff_of_minimal_sink_source_isAnnihilatedBy
    (k := k) (A := A) J
    (P.minimalRightAlmostSplitAt_middle_isAnnihilatedBy_family_of_endpoint_ne
      T hInjective hNotSimple x.1 hx)
    x.2 B.map B.rightAlmostSplit B.rightMinimal

include P in
/-- The same ordinary-endpoint projectivity comparison over the literal
simultaneous quotient algebra. -/
theorem primitiveProjectiveSocleFamilyFGObj_projective_iff_ambient
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : S.IdealQuotientLabel
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective))
    (hx : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T), x.1 ≠
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1) :
    Projective
        (S.idealQuotientFGObj
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective) x) ↔
      Projective (S.fgObj x.1) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let Eq := RightModule.idealQuotientEquivalence (k := k) J
  exact (Eq.map_projective_iff
    (S.idealQuotientLabelObj J x)).trans
      (P.primitiveProjectiveSocleFamilyLabelObj_projective_iff_ambient
        T hInjective hNotSimple x hx)

include P in
/-- In the finite-tau presentations, projectivity is unchanged at every
ordinary surviving endpoint of simultaneous rejection. -/
theorem primitiveProjectiveSocleFamily_isProjective_iff_ambient
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).n)
    (hj : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
      (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective) j).1 ≠
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1) :
    S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective) j).1 ↔
      (idealQuotientFiniteTauCategoryData S
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
          ).toFiniteRightTauCategoryData.IsProjective j := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let q := S.idealQuotientFiniteLabelEquiv J
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra J)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj,
    MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  change Projective (S.fgObj (q j).1) ↔
    Projective (S.idealQuotientFGObj J (q j))
  exact (P.primitiveProjectiveSocleFamilyFGObj_projective_iff_ambient
    T hInjective hNotSimple (q j) hj).symm

include P in
/-- Every ordinary surviving endpoint has the same incoming right-mesh
arity before and after simultaneous socle rejection. -/
theorem primitiveProjectiveSocleFamily_rightMiddleArity_eq_ambient
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ]
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).n)
    (hj : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
      (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective) j).1 ≠
      (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective) j).1 =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
            ).toFiniteRightTauCategoryData j := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let q := S.idealQuotientFiniteLabelEquiv J
  let x := q j
  let B := S.minimalRightAlmostSplitAt x.1
  let dA := S.minimalRightAlmostSplitAtDecomposition x.1
  have hE : RightModule.IsAnnihilatedBy J B.middle :=
    P.minimalRightAlmostSplitAt_middle_isAnnihilatedBy_family_of_endpoint_ne
      T hInjective hNotSimple x.1 hj
  have hsummand (i : Fin dA.n) :
      RightModule.IsAnnihilatedBy J (dA.summand i) := by
    change RightModule.IsAnnihilatedBy J
      (S.fgObj (B.label ((Fintype.equivFin B.index).symm i)))
    exact
      (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
        T hInjective _).2
          (P.minimalRightAlmostSplitAt_label_ne_familySelected_of_endpoint_ne
            T hInjective hNotSimple x.1 hj
              ((Fintype.equivFin B.index).symm i))
  let dQ := RightModule.idealTorsionTargetSourceDecomposition
    (k := k) J B.middle hE dA hsummand
  let Eq := RightModule.idealQuotientEquivalence (k := k) J
  let restricted := RightModule.idealTorsionTargetMap J x.2 B.map
  let mapped := Eq.functor.map restricted
  have hmappedAS : IsRightAlmostSplit mapped :=
    (RightModule.idealTorsionTargetMap_isRightAlmostSplit
      J x.2 B.map B.rightAlmostSplit).map_equivalence Eq
  have hmappedMin : IsRightMinimal mapped :=
    (RightModule.idealTorsionTargetMap_isRightMinimal_of_source_isAnnihilatedBy
      J hE x.2 B.map B.rightMinimal).map_equivalence Eq
  let TQ := (idealQuotientFiniteTauCategoryData S J).toFiniteRightTauCategoryData
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  have hQ : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TQ j = dQ.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TQ j dQ hmappedAS hmappedMin
  have hA : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TA x.1 = dA.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TA x.1 dA B.rightAlmostSplit B.rightMinimal
  exact hA.trans (hQ.trans (by rfl)).symm

/-- The complete finite-tau rejection profile produced by simultaneously
removing the socles of a finite basic family of non-simple indecomposable
projective-injective modules. -/
def primitiveProjectiveSocleFamilyRejectionProfile
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ] :
    MagnitudeConjecture.FiniteTauMatrix.FamilyRejectionProfile
      S.finiteTauCategoryData.toFiniteRightTauCategoryData
      (idealQuotientFiniteTauCategoryData S
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
          ).toFiniteRightTauCategoryData := by
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let q := S.idealQuotientFiniteLabelEquiv J
  let selected := primitiveProjectiveSocleFamilySelectedEquiv (S := S) T
  let surviving :=
    P.primitiveProjectiveSocleFamilyFiniteSurvivingEquiv T hInjective
  let replacement :
      {i : Fin S.n //
        i ∈ primitiveProjectiveSocleFamilySelectedLabels T} →
        Fin (S.idealQuotientFiniteIndecomposableSkeleton J).n :=
    fun d ↦ P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
      T hInjective hNotSimple (selected.symm d).1 (selected.symm d).2
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra J)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
  refine {
    deleted := primitiveProjectiveSocleFamilySelectedLabels T
    replacement := replacement
    replacement_injective := ?_
    surviving := surviving
    deleted_projective := ?_
    deleted_arity := ?_
    replacement_ambient_nonprojective := ?_
    replacement_rejected_projective := ?_
    projective_iff_of_not_replacement := ?_
    replacement_arity := ?_
    arity_eq_of_not_replacement := ?_ }
  · exact (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel_injective
      T hInjective hNotSimple).comp selected.symm.injective
  · intro i hi
    let p := selected.symm ⟨i, hi⟩
    have hpLabel : p.1.label = i :=
      congrArg Subtype.val (selected.apply_symm_apply ⟨i, hi⟩)
    rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
    change Projective (S.fgObj i)
    rw [← hpLabel]
    exact p.1.projective
  · intro i hi
    let p := selected.symm ⟨i, hi⟩
    have hpLabel : p.1.label = i :=
      congrArg Subtype.val (selected.apply_symm_apply ⟨i, hi⟩)
    simpa [hpLabel] using
      (S.projectiveInjective_rightMiddleArity_eq_one
        p.1 (hInjective p.1 p.2) (hNotSimple p.1 p.2))
  · intro d
    let p := selected.symm d
    change ¬ S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
      (q (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
        T hInjective hNotSimple p.1 p.2)).1
    exact
      P.primitiveProjectiveSocleFamilyFiniteReplacement_ambient_not_projective
        T hInjective hNotSimple p.1 p.2
  · intro d
    let p := selected.symm d
    rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
    exact P.primitiveProjectiveSocleFamilyFiniteReplacement_projective
      T hInjective hNotSimple p.1 p.2
  · intro j hj
    have hj' : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
        (q j).1 ≠
          (P.socleQuotientReplacementLabel
            p (hInjective p hp) (hNotSimple p hp)).1 := by
      intro p hp heq
      apply hj (selected ⟨p, hp⟩)
      change P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
        T hInjective hNotSimple
          (selected.symm (selected ⟨p, hp⟩)).1
          (selected.symm (selected ⟨p, hp⟩)).2 = j
      rw [selected.symm_apply_apply]
      apply q.injective
      apply Subtype.ext
      exact (congrArg Subtype.val
        (P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
          T hInjective hNotSimple p hp)).trans heq.symm
    exact P.primitiveProjectiveSocleFamily_isProjective_iff_ambient
      T hInjective hNotSimple j hj'
  · intro d
    let p := selected.symm d
    change
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          (idealQuotientFiniteTauCategoryData S J
            ).toFiniteRightTauCategoryData
          (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p.1 p.2) + 1 =
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData
          (q (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p.1 p.2)).1
    exact
      P.primitiveProjectiveSocleFamily_replacement_rightMiddleArity_add_one_eq_ambient
        T hInjective hNotSimple p.1 p.2
  · intro j hj
    have hj' : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
        (q j).1 ≠
          (P.socleQuotientReplacementLabel
            p (hInjective p hp) (hNotSimple p hp)).1 := by
      intro p hp heq
      apply hj (selected ⟨p, hp⟩)
      change P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
        T hInjective hNotSimple
          (selected.symm (selected ⟨p, hp⟩)).1
          (selected.symm (selected ⟨p, hp⟩)).2 = j
      rw [selected.symm_apply_apply]
      apply q.injective
      apply Subtype.ext
      exact (congrArg Subtype.val
        (P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
          T hInjective hNotSimple p hp)).trans heq.symm
    change
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData (q j).1 =
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          (idealQuotientFiniteTauCategoryData S J
            ).toFiniteRightTauCategoryData j
    exact P.primitiveProjectiveSocleFamily_rightMiddleArity_eq_ambient
      T hInjective hNotSimple j hj'

include P in
/-- Simultaneous rejection replaces the selected projectives by the same
number of projective quotient modules. -/
theorem primitiveProjectiveSocleFamily_projectiveCount_eq
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ] :
    @MagnitudeConjecture.ARCount.projectiveCount (Fin S.n) inferInstance
        S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) =
      @MagnitudeConjecture.ARCount.projectiveCount
        (Fin (S.idealQuotientFiniteIndecomposableSkeleton
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)).n)
        inferInstance
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
            ).toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) :=
  (P.primitiveProjectiveSocleFamilyRejectionProfile
    T hInjective hNotSimple).projectiveCount_eq

include P in
/-- Simultaneous rejection of a finite family of non-simple indecomposable
projective-injectives preserves the Auslander--Reiten Euler magnitude. -/
theorem primitiveProjectiveSocleFamily_eulerMagnitude_eq
    (T : Finset S.ProjectiveLabel)
    (hInjective : ∀ p, p ∈ T → Injective (S.fgObj p.label))
    (hNotSimple : ∀ p, p ∈ T →
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal T hInjective))ᵐᵒᵖ] :
    @MagnitudeConjecture.ARCount.eulerMagnitude _ _
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData)
        S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) =
      @MagnitudeConjecture.ARCount.eulerMagnitude _ _
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (idealQuotientFiniteTauCategoryData S
            (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
              ).toFiniteRightTauCategoryData)
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal T hInjective)
            ).toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) :=
  (P.primitiveProjectiveSocleFamilyRejectionProfile
    T hInjective hNotSimple).eulerMagnitude_eq

end FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule
