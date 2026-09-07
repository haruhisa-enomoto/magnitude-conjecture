import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslate

/-!
# Coset invariance of normal-orbit translations

For a normal subgroup `N ◁ G`, ambient elements representing the same coset
in `G / N` induce canonically naturally isomorphic translation functors on the
`N`-shift-orbit category.  The same comparison is transported to the chosen
strict deck-orbit skeleton.  These isomorphisms are the descent datum for the
residual quotient-group shift.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

private theorem conjugateNaturality
    {B : Type u} [Category.{v} B]
    (F₁ F₂ : B ⥤ B) (η : F₁ ⟶ F₂)
    {X Y X₁ Y₁ X₂ Y₂ : B}
    (e₁X : F₁.obj X ≅ X₁) (e₁Y : F₁.obj Y ≅ Y₁)
    (e₂X : F₂.obj X ≅ X₂) (e₂Y : F₂.obj Y ≅ Y₂)
    (f : X ⟶ Y) :
    (e₁X.inv ≫ F₁.map f ≫ e₁Y.hom) ≫
        (e₁Y.inv ≫ η.app Y ≫ e₂Y.hom) =
      (e₁X.inv ≫ η.app X ≫ e₂X.hom) ≫
        (e₂X.inv ≫ F₂.map f ≫ e₂Y.hom) := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun z ↦ e₁X.inv ≫ z ≫ e₂Y.hom) (η.naturality f)

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

noncomputable def shiftOrbitNormalTranslateEmbeddingIso
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateFunctor N g ⋙
        D.shiftOrbitSubgroupFunctor N ≅
      D.shiftOrbitSubgroupFunctor N := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  refine NatIso.ofComponents (fun X ↦
    (ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g)).symm) ?_
  intro X Y f
  change D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateMap N g f) ≫
          (ShiftOrbitCategory.objectShiftIso
            (show C from Y) (Additive.ofMul g)).inv =
      (ShiftOrbitCategory.objectShiftIso
          (show C from X) (Additive.ofMul g)).inv ≫
        D.shiftOrbitSubgroupMap N _ _ f
  rw [D.shiftOrbitSubgroupMap_normalTranslateMap]
  unfold shiftOrbitAmbientConjugate
  simp

noncomputable def shiftOrbitNormalTranslateComparisonMap
    (N : Subgroup G) [N.Normal] (g₁ g₂ : G)
    (_h : (g₁ : G ⧸ N) = (g₂ : G ⧸ N)) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N)
      ((shiftFunctor C (Additive.ofMul g₁)).obj X)
      ((shiftFunctor C (Additive.ofMul g₂)).obj X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact D.shiftOrbitSubgroupProjection N _ _
    ((ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g₁)).inv ≫
      (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g₂)).hom)

set_option backward.isDefEq.respectTransparency false in
theorem shiftOrbitSubgroupMap_normalTranslateComparisonMap
    (N : Subgroup G) [N.Normal] (g₁ g₂ : G)
    (h : (g₁ : G ⧸ N) = (g₂ : G ⧸ N)) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N _ _
        (D.shiftOrbitNormalTranslateComparisonMap N g₁ g₂ h X) =
      (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g₁)).inv ≫
        (ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g₂)).hom := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold shiftOrbitNormalTranslateComparisonMap
  simp only [ShiftOrbitCategory.objectShiftIso]
  change D.shiftOrbitSubgroupMap N _ _
      (D.shiftOrbitSubgroupProjection N _ _
        (shiftOrbitCompHom (shiftOrbitFromShift X (Additive.ofMul g₁))
          (shiftOrbitToShift X (Additive.ofMul g₂)))) =
    shiftOrbitCompHom (shiftOrbitFromShift X (Additive.ofMul g₁))
      (shiftOrbitToShift X (Additive.ofMul g₂))
  rw [shiftOrbitFromShift, shiftOrbitToShift, shiftOrbitCompHom_of_of]
  apply D.shiftOrbitSubgroupMap_projection_of_mem
  have hmem : g₂⁻¹ * g₁ ∈ N := by
    have := N.inv_mem (QuotientGroup.leftRel_apply.mp (Quotient.exact h))
    simpa using this
  simpa using hmem

set_option backward.isDefEq.respectTransparency false in
noncomputable def shiftOrbitNormalTranslateIsoOfQuotientEq
    (N : Subgroup G) [N.Normal] (g₁ g₂ : G)
    (h : (g₁ : G ⧸ N) = (g₂ : G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitNormalTranslateFunctor N g₁ ≅
      D.shiftOrbitNormalTranslateFunctor N g₂ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  refine NatIso.ofComponents (fun X ↦
    { hom := D.shiftOrbitNormalTranslateComparisonMap N g₁ g₂ h X
      inv := D.shiftOrbitNormalTranslateComparisonMap N g₂ g₁ h.symm X
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (D.shiftOrbitNormalTranslateComparisonMap N g₁ g₂ h (show C from X))
          (D.shiftOrbitNormalTranslateComparisonMap N g₂ g₁ h.symm (show C from X))) =
      D.shiftOrbitSubgroupMap N _ _ (shiftOrbitId _)
    rw [D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
      D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
      D.shiftOrbitSubgroupMap_id]
    let u₁ := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g₁)
    let u₂ := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g₂)
    have hcat : (u₁.inv ≫ u₂.hom) ≫ (u₂.inv ≫ u₁.hom) = 𝟙 _ := by
      simp
    exact hcat
  · apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (D.shiftOrbitNormalTranslateComparisonMap N g₂ g₁ h.symm (show C from X))
          (D.shiftOrbitNormalTranslateComparisonMap N g₁ g₂ h (show C from X))) =
      D.shiftOrbitSubgroupMap N _ _ (shiftOrbitId _)
    rw [D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
      D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
      D.shiftOrbitSubgroupMap_id]
    let u₁ := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g₁)
    let u₂ := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g₂)
    have hcat : (u₂.inv ≫ u₁.hom) ≫ (u₁.inv ≫ u₂.hom) = 𝟙 _ := by
      simp
    exact hcat
  · intro X Y f
    apply D.shiftOrbitSubgroupMap_injective N _ _
    change D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom (D.shiftOrbitNormalTranslateMap N g₁ f)
          (D.shiftOrbitNormalTranslateComparisonMap N g₁ g₂ h (show C from Y))) =
      D.shiftOrbitSubgroupMap N _ _
        (shiftOrbitCompHom
          (D.shiftOrbitNormalTranslateComparisonMap N g₁ g₂ h (show C from X))
          (D.shiftOrbitNormalTranslateMap N g₂ f))
    rw [D.shiftOrbitSubgroupMap_comp, D.shiftOrbitSubgroupMap_comp,
      D.shiftOrbitSubgroupMap_normalTranslateMap,
      D.shiftOrbitSubgroupMap_normalTranslateMap,
      D.shiftOrbitSubgroupMap_normalTranslateComparisonMap,
      D.shiftOrbitSubgroupMap_normalTranslateComparisonMap]
    unfold shiftOrbitAmbientConjugate
    let u₁X := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g₁)
    let u₂X := ShiftOrbitCategory.objectShiftIso
      (show C from X) (Additive.ofMul g₂)
    let u₁Y := ShiftOrbitCategory.objectShiftIso
      (show C from Y) (Additive.ofMul g₁)
    let u₂Y := ShiftOrbitCategory.objectShiftIso
      (show C from Y) (Additive.ofMul g₂)
    let ef := D.shiftOrbitSubgroupMap N (show C from X) (show C from Y) f
    have hcat :
        (u₁X.inv ≫ ef ≫ u₁Y.hom) ≫
            (u₁Y.inv ≫ u₂Y.hom) =
          (u₁X.inv ≫ u₂X.hom) ≫
            (u₂X.inv ≫ ef ≫ u₂Y.hom) := by
      simp
    exact hcat

set_option backward.isDefEq.respectTransparency false in
noncomputable def deckOrbitNormalTranslateComparisonIsoApp
    (N : Subgroup G) [N.Normal] (g₁ g₂ : G)
    (h : (g₁ : G ⧸ N) = (g₂ : G ⧸ N))
    (q : MulAction.orbitRel.Quotient N C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.deckOrbitNormalTranslateFunctor N g₁).obj
        (show DeckOrbitSkeleton C N from q) ≅
      (D.deckOrbitNormalTranslateFunctor N g₂).obj
        (show DeckOrbitSkeleton C N from q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let η := D.shiftOrbitNormalTranslateIsoOfQuotientEq N g₁ g₂ h
  exact
    { hom := InducedCategory.homMk
        ((D.shiftOrbitNormalTranslateRepresentativeIso N g₁ q).inv ≫
          η.hom.app (deckOrbitRepresentative (C := C) (G := N) q) ≫
          (D.shiftOrbitNormalTranslateRepresentativeIso N g₂ q).hom)
      inv := InducedCategory.homMk
        ((D.shiftOrbitNormalTranslateRepresentativeIso N g₂ q).inv ≫
          η.inv.app (deckOrbitRepresentative (C := C) (G := N) q) ≫
          (D.shiftOrbitNormalTranslateRepresentativeIso N g₁ q).hom)
      hom_inv_id := by
        apply InducedCategory.hom_ext
        simp
      inv_hom_id := by
        apply InducedCategory.hom_ext
        simp }

set_option backward.isDefEq.respectTransparency false in
noncomputable def deckOrbitNormalTranslateIsoOfQuotientEq
    (N : Subgroup G) [N.Normal] (g₁ g₂ : G)
    (h : (g₁ : G ⧸ N) = (g₂ : G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.deckOrbitNormalTranslateFunctor N g₁ ≅
      D.deckOrbitNormalTranslateFunctor N g₂ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let η := D.shiftOrbitNormalTranslateIsoOfQuotientEq N g₁ g₂ h
  refine NatIso.ofComponents (fun q ↦
    D.deckOrbitNormalTranslateComparisonIsoApp N g₁ g₂ h q) ?_
  intro q r f
  apply InducedCategory.hom_ext
  let F₁ := D.shiftOrbitNormalTranslateFunctor N g₁
  let F₂ := D.shiftOrbitNormalTranslateFunctor N g₂
  let Xq : ShiftOrbitCategory C (Additive N) :=
    deckOrbitRepresentative (C := C) (G := N) q
  let Xr : ShiftOrbitCategory C (Additive N) :=
    deckOrbitRepresentative (C := C) (G := N) r
  let e₁q := D.shiftOrbitNormalTranslateRepresentativeIso N g₁ q
  let e₁r := D.shiftOrbitNormalTranslateRepresentativeIso N g₁ r
  let e₂q := D.shiftOrbitNormalTranslateRepresentativeIso N g₂ q
  let e₂r := D.shiftOrbitNormalTranslateRepresentativeIso N g₂ r
  change (e₁q.inv ≫ F₁.map f.hom ≫ e₁r.hom) ≫
      (e₁r.inv ≫ η.hom.app Xr ≫ e₂r.hom) =
    (e₁q.inv ≫ η.hom.app Xq ≫ e₂q.hom) ≫
      (e₂q.inv ≫ F₂.map f.hom ≫ e₂r.hom)
  exact conjugateNaturality F₁ F₂ η.hom e₁q e₁r e₂q e₂r f.hom

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
