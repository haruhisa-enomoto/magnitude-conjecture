import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.UniserialObject
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Radical subobjects from projective covers

A monic right almost-split morphism represents the unique maximal subobject
of its target.  If such a subobject is mapped through a minimal projective
cover, its image contains every proper subobject of the cover target and is
itself proper.  This is the intrinsic projective-cover description of the
module radical used in the covering argument.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
/-- A monic right almost-split morphism represents a subobject containing
every proper subobject of its target. -/
theorem isRadicalSubobject_mk_of_mono_rightAlmostSplit
    {R P : C} (r : R ⟶ P) [Mono r] (hr : IsRightAlmostSplit r) :
    IsUniserialObject.IsRadicalSubobject (Subobject.mk r) := by
  intro Q hQ
  have hnot : ¬ IsSplitEpi Q.arrow := by
    intro hsplit
    letI : IsSplitEpi Q.arrow := hsplit
    haveI : IsIso Q.arrow := isIso_of_mono_of_isSplitEpi Q.arrow
    apply hQ
    simpa using
      (Subobject.isIso_iff_mk_eq_top Q.arrow).mp (inferInstance : IsIso Q.arrow)
  obtain ⟨l, hl⟩ := hr.factors Q.arrow hnot
  exact Subobject.le_mk_of_comm l hl

omit [Abelian C] in
/-- The subobject represented by a monic right almost-split morphism is
proper. -/
theorem mk_ne_top_of_mono_rightAlmostSplit
    {R P : C} (r : R ⟶ P) [Mono r] (hr : IsRightAlmostSplit r) :
    Subobject.mk r ≠ ⊤ := by
  intro htop
  haveI : IsIso r :=
    (Subobject.isIso_iff_mk_eq_top r).mpr htop
  exact hr.not_isSplitEpi (inferInstance : IsSplitEpi r)

omit [Abelian C] in
/-- A monic right almost-split morphism represents a maximal proper
subobject. -/
theorem isCoatom_mk_of_mono_rightAlmostSplit
    {R P : C} (r : R ⟶ P) [Mono r] (hr : IsRightAlmostSplit r) :
    IsCoatom (Subobject.mk r) := by
  rw [isCoatom_iff_ge_of_le]
  refine ⟨mk_ne_top_of_mono_rightAlmostSplit r hr, ?_⟩
  intro Q hQ _
  exact isRadicalSubobject_mk_of_mono_rightAlmostSplit r hr Q hQ

/-- A proper radical subobject has simple quotient.  Indeed, it is a coatom
in the subobject lattice, hence its quotient is an atom under the abelian
subobject--quotient order duality. -/
theorem simple_cokernel_of_isRadicalSubobject
    {R X : C} (r : R ⟶ X) [Mono r]
    (hr : IsUniserialObject.IsRadicalSubobject (Subobject.mk r))
    (hproper : Subobject.mk r ≠ ⊤) :
    Simple (cokernel r) := by
  have hcoatom : IsCoatom (Subobject.mk r) := by
    rw [isCoatom_iff_ge_of_le]
    exact ⟨hproper, fun P hP _ ↦ hr P hP⟩
  let E := CategoryTheory.Abelian.subobjectIsoSubobjectOp X
  have hcoatom' : IsCoatom (E (Subobject.mk r)) :=
    (E.isCoatom_iff (Subobject.mk r)).2 hcoatom
  let Q : Subobject (Opposite.op X) :=
    OrderDual.ofDual (E (Subobject.mk r))
  have hatom : IsAtom Q := hcoatom'.dual
  have hs : Simple (Q : Cᵒᵖ) :=
    (subobject_simple_iff_isAtom _).2 hatom
  have hQ : Q = Subobject.mk (cokernel.π r).op := by
    rfl
  subst Q
  have hs' : Simple (Opposite.op (cokernel r)) := by
    letI : Simple
        ((Subobject.mk (cokernel.π r).op :
          Subobject (Opposite.op X)) : Cᵒᵖ) := hs
    exact Simple.of_iso
      ((Subobject.underlyingIso (cokernel.π r).op).symm)
  letI : Simple (Opposite.op (cokernel r)) := hs'
  simpa using
    (CategoryTheory.simple_unop_of_simple
      (X := Opposite.op (cokernel r)))

/-- The image of the inverse image of a subobject along an epimorphism is
the original subobject. -/
theorem imageSubobject_pullback_arrow_comp_eq_of_epi
    {P M : C} (p : P ⟶ M) [Epi p] (S : Subobject M) :
    imageSubobject (((Subobject.pullback p).obj S).arrow ≫ p) = S := by
  let T := (Subobject.pullback p).obj S
  let a := Subobject.pullbackπ p S
  have ha : a ≫ S.arrow = T.arrow ≫ p :=
    (Subobject.isPullback p S).w
  haveI : Epi a := by
    change Epi (Subobject.pullbackπ p S)
    rw [← (Subobject.isPullback p S).isoPullback_hom_fst]
    infer_instance
  let I := imageSubobject (a ≫ S.arrow)
  let S' := imageSubobject S.arrow
  have hle : I ≤ S' := imageSubobject_comp_le a S.arrow
  haveI : Epi (Subobject.ofLE I S' hle) := by
    exact imageSubobject_comp_le_epi_of_epi a S.arrow
  haveI : IsIso (Subobject.ofLE I S' hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE I S' hle)
  have heq : I = S' :=
    Subobject.eq_of_comm (asIso (Subobject.ofLE I S' hle))
      (Subobject.ofLE_arrow hle)
  rw [← ha]
  simpa only [I, S', imageSubobject_mono, Subobject.mk_arrow] using heq

/-- If a subobject contains every proper subobject of the source of an
epimorphism, then its image contains every proper subobject of the target. -/
theorem isRadicalSubobject_imageSubobject_comp_of_epi
    {R P M : C} (r : R ⟶ P) [Mono r]
    (p : P ⟶ M) [Epi p]
    (hr : IsUniserialObject.IsRadicalSubobject (Subobject.mk r)) :
    IsUniserialObject.IsRadicalSubobject (imageSubobject (r ≫ p)) := by
  intro S hS
  let T := (Subobject.pullback p).obj S
  have hT : T ≠ ⊤ := by
    intro htop
    haveI : IsIso T.arrow :=
      (Subobject.isIso_iff_mk_eq_top T.arrow).mpr (by simpa using htop)
    let a : P ⟶ (S : C) := inv T.arrow ≫ Subobject.pullbackπ p S
    have ha : a ≫ S.arrow = p := by
      dsimp only [a]
      rw [Category.assoc, (Subobject.isPullback p S).w,
        ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    haveI : Epi S.arrow := epi_of_epi_fac ha
    haveI : IsIso S.arrow := isIso_of_mono_of_epi S.arrow
    apply hS
    simpa using
      (Subobject.isIso_iff_mk_eq_top S.arrow).mp
        (inferInstance : IsIso S.arrow)
  have hTR : T ≤ Subobject.mk r := hr T hT
  let t : (T : C) ⟶ R := Subobject.ofLEMk T r hTR
  have ht : t ≫ r = T.arrow := Subobject.ofLEMk_comp hTR
  have himage :
      imageSubobject (T.arrow ≫ p) ≤ imageSubobject (r ≫ p) := by
    rw [← ht]
    simpa only [Category.assoc] using
      (imageSubobject_comp_le t (r ≫ p))
  rw [imageSubobject_pullback_arrow_comp_eq_of_epi p S] at himage
  exact himage

/-- Under an essential epimorphism, the image of a proper subobject remains
proper. -/
theorem imageSubobject_comp_ne_top_of_isEssentialEpi
    {R P M : C} (r : R ⟶ P) [Mono r]
    (p : P ⟶ M) [Epi p] (hp : IsEssentialEpi p)
    (hr : Subobject.mk r ≠ ⊤) :
    imageSubobject (r ≫ p) ≠ ⊤ := by
  intro htop
  let I := imageSubobject (r ≫ p)
  haveI : IsIso I.arrow :=
    (Subobject.isIso_iff_mk_eq_top I.arrow).mpr (by simpa [I] using htop)
  haveI : Epi (r ≫ p) := by
    rw [← imageSubobject_arrow_comp (r ≫ p)]
    infer_instance
  haveI : Epi r := hp.2 r (inferInstance : Epi (r ≫ p))
  haveI : IsIso r := isIso_of_mono_of_epi r
  apply hr
  exact (Subobject.isIso_iff_mk_eq_top r).mp (inferInstance : IsIso r)

namespace MinimalProjectivePresentation

/-- A minimal projective cover of a nonzero uniserial object has
indecomposable source. -/
theorem source_indecomposable_of_uniserial
    {M : C} (P : MinimalProjectivePresentation M)
    (hM : IsUniserialObject M) (hMzero : ¬ IsZero M) :
    Indecomposable P.p := by
  constructor
  · intro hPzero
    exact hMzero (IsZero.of_epi P.f hPzero)
  · intro Y Z e
    let iY : Y ⟶ P.p := biprod.inl ≫ e.inv
    let iZ : Z ⟶ P.p := biprod.inr ≫ e.inv
    let rY : P.p ⟶ Y := e.hom ≫ biprod.fst
    let rZ : P.p ⟶ Z := e.hom ≫ biprod.snd
    have hiYrY : iY ≫ rY = 𝟙 Y := by simp [iY, rY, Category.assoc]
    have hiZrZ : iZ ≫ rZ = 𝟙 Z := by simp [iZ, rZ, Category.assoc]
    have hYprojective : Projective Y :=
      projective_of_retract (inferInstance : Projective P.p)
        iY rY hiYrY
    have hZprojective : Projective Z :=
      projective_of_retract (inferInstance : Projective P.p)
        iZ rZ hiZrZ
    let pY : Y ⟶ M := iY ≫ P.f
    let pZ : Z ⟶ M := iZ ≫ P.f
    let IY := imageSubobject pY
    let IZ := imageSubobject pZ
    have hessential : IsEssentialEpi P.f :=
      isEssentialEpi_of_isRightMinimal P.f P.rightMinimal
    have leftZero_of_le (hYZ : IY ≤ IZ) : IsZero Y := by
      let qY : Y ⟶ (IY : C) := factorThruImageSubobject pY
      let qZ : Z ⟶ (IZ : C) := factorThruImageSubobject pZ
      let j : (IY : C) ⟶ (IZ : C) := Subobject.ofLE IY IZ hYZ
      let b : Y ⟶ (IZ : C) := qY ≫ j
      letI : Projective Y := hYprojective
      let l : Y ⟶ Z := Projective.factorThru b qZ
      have hl : l ≫ pZ = pY := by
        rw [← imageSubobject_arrow_comp pZ, ← Category.assoc,
          Projective.factorThru_comp]
        dsimp only [b]
        rw [Category.assoc, Subobject.ofLE_arrow,
          imageSubobject_arrow_comp]
      let q : P.p ⟶ Z := e.hom ≫ biprod.desc l (𝟙 Z)
      have hq : q ≫ pZ = P.f := by
        have hdesc : biprod.desc l (𝟙 Z) ≫ pZ = e.inv ≫ P.f := by
          apply biprod.hom_ext'
          · simpa only [biprod.inl_desc_assoc, Category.id_comp,
              pY, iY, Category.assoc] using hl
          · simp [pZ, iZ, Category.assoc]
        dsimp only [q]
        rw [Category.assoc, hdesc, e.hom_inv_id_assoc]
      haveI : Epi pZ := epi_of_epi_fac hq
      haveI : Epi iZ := hessential.2 iZ (inferInstance : Epi pZ)
      haveI : IsIso iZ := isIso_of_mono_of_epi iZ
      haveI : IsIso (biprod.inr : Z ⟶ Y ⊞ Z) := by
        apply IsIso.of_isIso_comp_right biprod.inr e.inv
      apply (IsZero.iff_id_eq_zero Y).2
      have hfst : (biprod.fst : Y ⊞ Z ⟶ Y) = 0 := by
        apply (cancel_epi (biprod.inr : Z ⟶ Y ⊞ Z)).1
        simp
      rw [← biprod.inl_fst, hfst, comp_zero]
    have rightZero_of_le (hZY : IZ ≤ IY) : IsZero Z := by
      let qZ : Z ⟶ (IZ : C) := factorThruImageSubobject pZ
      let qY : Y ⟶ (IY : C) := factorThruImageSubobject pY
      let j : (IZ : C) ⟶ (IY : C) := Subobject.ofLE IZ IY hZY
      let b : Z ⟶ (IY : C) := qZ ≫ j
      letI : Projective Z := hZprojective
      let l : Z ⟶ Y := Projective.factorThru b qY
      have hl : l ≫ pY = pZ := by
        rw [← imageSubobject_arrow_comp pY, ← Category.assoc,
          Projective.factorThru_comp]
        dsimp only [b]
        rw [Category.assoc, Subobject.ofLE_arrow,
          imageSubobject_arrow_comp]
      let q : P.p ⟶ Y := e.hom ≫ biprod.desc (𝟙 Y) l
      have hq : q ≫ pY = P.f := by
        have hdesc : biprod.desc (𝟙 Y) l ≫ pY = e.inv ≫ P.f := by
          apply biprod.hom_ext'
          · simp [pY, iY, Category.assoc]
          · simpa only [biprod.inr_desc_assoc, Category.id_comp,
              pZ, iZ, Category.assoc] using hl
        dsimp only [q]
        rw [Category.assoc, hdesc, e.hom_inv_id_assoc]
      haveI : Epi pY := epi_of_epi_fac hq
      haveI : Epi iY := hessential.2 iY (inferInstance : Epi pY)
      haveI : IsIso iY := isIso_of_mono_of_epi iY
      haveI : IsIso (biprod.inl : Y ⟶ Y ⊞ Z) := by
        apply IsIso.of_isIso_comp_right biprod.inl e.inv
      exact (Biprod.isIso_inl_iff_isZero Y Z).mp inferInstance
    rcases hM.total IY IZ with hYZ | hZY
    · exact Or.inl (leftZero_of_le hYZ)
    · exact Or.inr (rightZero_of_le hZY)

end MinimalProjectivePresentation

end MagnitudeConjecture
