import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslate

/-!
# Linearity of normal deck-orbit translations

Ambient normal translations preserve scalar multiplication on both the
nonskeletal shift-orbit category and its chosen strict deck-orbit skeleton.
The proof first checks subgroup-degree inclusion on direct-sum generators,
then uses its injectivity to descend linearity from ambient conjugation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable {k : Type uK} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : Additive G, (D.core.F a).Linear k]

private theorem shiftOrbitOf_smul
    {A : Type w} [AddMonoid A] [HasShift C A]
    [∀ a : A, (shiftFunctor C a).Additive]
    [∀ a : A, (shiftFunctor C a).Linear k]
    {X Y : C} (a : A) (r : k) (f : ShiftHom X Y a) :
    shiftOrbitOf X Y a (r • f) =
      r • shiftOrbitOf X Y a f := by
  classical
  change shiftOrbitLof (k := k) X Y a (r • f) =
    r • shiftOrbitLof (k := k) X Y a f
  exact (shiftOrbitLof (k := k) X Y a).map_smul r f

private theorem conjugate_smul
    {B : Type u} [Category.{v} B] [Preadditive B]
    [CategoryTheory.Linear k B]
    {X Y X' Y' : B} (eX : X ≅ X') (eY : Y ≅ Y')
    (r : k) (f : X ⟶ Y) :
    eX.inv ≫ (r • f) ≫ eY.hom =
      r • (eX.inv ≫ f ≫ eY.hom) := by
  calc
    eX.inv ≫ (r • f) ≫ eY.hom =
        eX.inv ≫ (r • (f ≫ eY.hom)) := by
      rw [CategoryTheory.Linear.smul_comp]
    _ = r • (eX.inv ≫ (f ≫ eY.hom)) := by
      rw [CategoryTheory.Linear.comp_smul]
    _ = r • (eX.inv ≫ f ≫ eY.hom) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extending subgroup-graded orbit morphisms by zero preserves scalar
multiplication. -/
theorem shiftOrbitSubgroupMap_smul
    (N : Subgroup G) {X Y : C} (r : k)
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    D.shiftOrbitSubgroupMap N X Y (r • f) =
      r • D.shiftOrbitSubgroupMap N X Y f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  classical
  letI : DecidableEq (Additive N) := Classical.decEq _
  letI : DecidableEq (Additive G) := Classical.decEq _
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    rw [← DirectSum.of_smul]
    have h₁ := D.shiftOrbitSubgroupMap_of N X Y a (r • fa)
    have h₂ := D.shiftOrbitSubgroupMap_of N X Y a fa
    calc
      D.shiftOrbitSubgroupMap N X Y
          (DirectSum.of (fun b : Additive N ↦ ShiftHom X Y b) a (r • fa)) =
          _ := h₁
      _ = r • _ := by
        apply shiftOrbitOf_smul (k := k)
      _ = r • D.shiftOrbitSubgroupMap N X Y
          (DirectSum.of (fun b : Additive N ↦ ShiftHom X Y b) a fa) :=
        congrArg (r • ·) h₂.symm
  · intro f₁ f₂ hf₁ hf₂
    rw [smul_add, map_add, map_add, hf₁, hf₂, smul_add]

set_option backward.isDefEq.respectTransparency false in
/-- Normal translation on the nonskeletal orbit Hom preserves scalar
multiplication. -/
theorem shiftOrbitNormalTranslateMap_smul
    (N : Subgroup G) [N.Normal] (g : G) {X Y : C}
    (r : k)
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    D.shiftOrbitNormalTranslateMap N g (r • f) =
      r • D.shiftOrbitNormalTranslateMap N g f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  apply D.shiftOrbitSubgroupMap_injective N _ _
  rw [D.shiftOrbitSubgroupMap_smul,
    D.shiftOrbitSubgroupMap_normalTranslateMap,
    D.shiftOrbitSubgroupMap_normalTranslateMap]
  unfold shiftOrbitAmbientConjugate
  rw [D.shiftOrbitSubgroupMap_smul]
  exact conjugate_smul _ _ r _

instance shiftOrbitNormalTranslateFunctor_linear
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.shiftOrbitNormalTranslateFunctor N g).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  constructor
  intro X Y f r
  exact D.shiftOrbitNormalTranslateMap_smul N g r f

set_option backward.isDefEq.respectTransparency false in
/-- Strict normal translation on the deck-orbit skeleton preserves scalar
multiplication. -/
theorem deckOrbitNormalTranslateMap_smul
    (N : Subgroup G) [N.Normal] (g : G)
    {q s : MulAction.orbitRel.Quotient N C}
    (r : k)
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      (show DeckOrbitSkeleton C N from q) ⟶
        (show DeckOrbitSkeleton C N from s)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    D.deckOrbitNormalTranslateMap N g (r • f) =
      r • D.deckOrbitNormalTranslateMap N g f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  apply InducedCategory.hom_ext
  change (D.shiftOrbitNormalTranslateRepresentativeIso N g q).inv ≫
      (D.shiftOrbitNormalTranslateFunctor N g).map (r • f.hom) ≫
        (D.shiftOrbitNormalTranslateRepresentativeIso N g s).hom =
    r • ((D.shiftOrbitNormalTranslateRepresentativeIso N g q).inv ≫
      (D.shiftOrbitNormalTranslateFunctor N g).map f.hom ≫
        (D.shiftOrbitNormalTranslateRepresentativeIso N g s).hom)
  simp

instance deckOrbitNormalTranslateFunctor_linear
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.deckOrbitNormalTranslateFunctor N g).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  constructor
  intro q s f r
  exact D.deckOrbitNormalTranslateMap_smul N g r f

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
