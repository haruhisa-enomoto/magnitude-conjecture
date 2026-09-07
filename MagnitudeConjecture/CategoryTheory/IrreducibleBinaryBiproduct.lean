import QuotientSubmoduleEquidistribution.CategoryTheory.CategoricalRadicalIdeal
import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleCofinite

/-!
# Irreducible maps and binary biproducts

This file formalizes the standard Butler--Ringel observation that two
irreducible maps from one local object assemble to an irreducible map into a
binary biproduct when every morphism between the two target summands is
categorically radical.  The dual statement treats a binary-biproduct source.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]

omit [HasBinaryBiproducts C] in
/-- Negating a morphism preserves categorical irreducibility. -/
theorem isIrreducibleMorphism_neg
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism (-f) := by
  have hsplitMono_of_neg : ∀ {A B : C} (q : A ⟶ B),
      IsSplitMono (-q) → IsSplitMono q := by
    intro A B q hq
    letI : IsSplitMono (-q) := hq
    exact IsSplitMono.mk'
      { retraction := -(retraction (-q))
        id := by
          simpa only [Preadditive.comp_neg, Preadditive.neg_comp,
            neg_neg] using IsSplitMono.id (-q) }
  have hsplitEpi_of_neg : ∀ {A B : C} (q : A ⟶ B),
      IsSplitEpi (-q) → IsSplitEpi q := by
    intro A B q hq
    letI : IsSplitEpi (-q) := hq
    exact IsSplitEpi.mk'
      { section_ := -(section_ (-q))
        id := by
          simpa only [Preadditive.comp_neg, Preadditive.neg_comp,
            neg_neg] using IsSplitEpi.id (-q) }
  refine
    { not_isSplitMono := fun h ↦ hf.not_isSplitMono
        (hsplitMono_of_neg f h)
      not_isSplitEpi := fun h ↦ hf.not_isSplitEpi
        (hsplitEpi_of_neg f h)
      factorization := ?_ }
  intro N a b hab
  have hfactor : (-a) ≫ b = f := by
    rw [Preadditive.neg_comp, hab, neg_neg]
  rcases hf.factorization (-a) b hfactor with ha | hb
  · exact Or.inl (hsplitMono_of_neg a ha)
  · exact Or.inr hb

/-- Two irreducible maps with a common local source assemble to an
irreducible map into a binary biproduct when both off-diagonal Hom groups are
radical. -/
theorem isIrreducibleMorphism_biprod_lift
    {X Y₁ Y₂ : C} [IsLocalRing (End X)]
    (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂)
    (hf₁ : IsIrreducibleMorphism f₁)
    (hf₂ : IsIrreducibleMorphism f₂)
    (h₁₂ : ∀ q : Y₁ ⟶ Y₂, IsRadicalMorphism q)
    (h₂₁ : ∀ q : Y₂ ⟶ Y₁, IsRadicalMorphism q) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  let f : X ⟶ Y₁ ⊞ Y₂ := biprod.lift f₁ f₂
  have hnotMono : ¬ IsSplitMono f := by
    intro hf
    letI : IsSplitMono f := hf
    let r : Y₁ ⊞ Y₂ ⟶ X := retraction f
    let r₁ : Y₁ ⟶ X := (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ≫ r
    let r₂ : Y₂ ⟶ X := (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) ≫ r
    have hsum : f₁ ≫ r₁ + f₂ ≫ r₂ = 𝟙 X := by
      calc
        f₁ ≫ r₁ + f₂ ≫ r₂ = f ≫ r := by
          simp [f, r₁, r₂, biprod.lift_eq, Preadditive.add_comp,
            Category.assoc]
        _ = 𝟙 X := IsSplitMono.id f
    have hnonunit₁ : ¬ IsUnit (End.of (f₁ ≫ r₁)) := by
      intro hu
      letI : IsIso (f₁ ≫ r₁) :=
        (isUnit_iff_isIso (End.of (f₁ ≫ r₁))).1 hu
      apply hf₁.not_isSplitMono
      exact IsSplitMono.mk'
        { retraction := r₁ ≫ inv (f₁ ≫ r₁)
          id := by rw [← Category.assoc]; simp }
    have hnonunit₂ : ¬ IsUnit (End.of (f₂ ≫ r₂)) := by
      intro hu
      letI : IsIso (f₂ ≫ r₂) :=
        (isUnit_iff_isIso (End.of (f₂ ≫ r₂))).1 hu
      apply hf₂.not_isSplitMono
      exact IsSplitMono.mk'
        { retraction := r₂ ≫ inv (f₂ ≫ r₂)
          id := by rw [← Category.assoc]; simp }
    have hunit : IsUnit (End.of (f₁ ≫ r₁ + f₂ ≫ r₂)) := by
      rw [hsum]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with h | h
    · exact hnonunit₁ h
    · exact hnonunit₂ h
  have hnotEpi : ¬ IsSplitEpi f := by
    intro hf
    letI : IsSplitEpi f := hf
    haveI : IsSplitEpi
        (f ≫ (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)) := inferInstance
    apply hf₁.not_isSplitEpi
    simpa [f] using
      (inferInstance : IsSplitEpi
        (f ≫ (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)))
  refine
    { not_isSplitMono := hnotMono
      not_isSplitEpi := hnotEpi
      factorization := ?_ }
  intro N a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  right
  let p₁ : N ⟶ Y₁ := b ≫ (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)
  let p₂ : N ⟶ Y₂ := b ≫ (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂)
  have hfactor₁ : a ≫ p₁ = f₁ := by
    calc
      a ≫ p₁ = (a ≫ b) ≫ (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) := by
        simp only [p₁, Category.assoc]
      _ = biprod.lift f₁ f₂ ≫ biprod.fst := by rw [hab]
      _ = f₁ := biprod.lift_fst f₁ f₂
  have hfactor₂ : a ≫ p₂ = f₂ := by
    calc
      a ≫ p₂ = (a ≫ b) ≫ (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) := by
        simp only [p₂, Category.assoc]
      _ = biprod.lift f₁ f₂ ≫ biprod.snd := by rw [hab]
      _ = f₂ := biprod.lift_snd f₁ f₂
  have hp₁ : IsSplitEpi p₁ :=
    (hf₁.factorization a p₁ hfactor₁).resolve_left ha
  have hp₂ : IsSplitEpi p₂ :=
    (hf₂.factorization a p₂ hfactor₂).resolve_left ha
  letI : IsSplitEpi p₁ := hp₁
  letI : IsSplitEpi p₂ := hp₂
  let s₁ : Y₁ ⟶ N := section_ p₁
  let s₂ : Y₂ ⟶ N := section_ p₂
  let q₁₂ : Y₁ ⟶ Y₂ := s₁ ≫ p₂
  let q₂₁ : Y₂ ⟶ Y₁ := s₂ ≫ p₁
  let r : Y₁ ⊞ Y₂ ⟶ Y₁ ⊞ Y₂ :=
    (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ≫ q₁₂ ≫
        (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) +
      (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ≫ q₂₁ ≫
        (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂)
  have hr : IsRadicalMorphism r := by
    apply isRadicalMorphism_add
    · have hq : IsRadicalMorphism
          ((biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ≫ q₁₂) :=
        isRadicalMorphism_precomp biprod.fst (h₁₂ q₁₂)
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) hq)
    · have hq : IsRadicalMorphism
          ((biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ≫ q₂₁) :=
        isRadicalMorphism_precomp biprod.snd (h₂₁ q₂₁)
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) hq)
  let s : Y₁ ⊞ Y₂ ⟶ N := biprod.desc s₁ s₂
  have hsb : s ≫ b = 𝟙 (Y₁ ⊞ Y₂) + r := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [s, p₁, s₁, r, q₁₂, q₂₁, Category.assoc]
      · simp [s, p₂, s₁, r, q₁₂, q₂₁, Category.assoc]
    · apply biprod.hom_ext
      · simp [s, p₁, s₂, r, q₁₂, q₂₁, Category.assoc]
      · simp [s, p₂, s₂, r, q₁₂, q₂₁, Category.assoc]
  have hsplit : IsSplitEpi (𝟙 (Y₁ ⊞ Y₂) + r) :=
    isSplitEpi_add_of_isRadicalMorphism (𝟙 (Y₁ ⊞ Y₂)) hr
  rw [← hsb] at hsplit
  letI : IsSplitEpi (s ≫ b) := hsplit
  exact IsSplitEpi.mk'
    { section_ := section_ (s ≫ b) ≫ s
      id := by rw [Category.assoc, IsSplitEpi.id] }

/-- Two irreducible maps with a common local target assemble to an
irreducible map out of a binary biproduct when both off-diagonal Hom groups
are radical. -/
theorem isIrreducibleMorphism_biprod_desc
    {Y₁ Y₂ Z : C} [IsLocalRing (End Z)]
    (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z)
    (hg₁ : IsIrreducibleMorphism g₁)
    (hg₂ : IsIrreducibleMorphism g₂)
    (h₁₂ : ∀ q : Y₁ ⟶ Y₂, IsRadicalMorphism q)
    (h₂₁ : ∀ q : Y₂ ⟶ Y₁, IsRadicalMorphism q) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  let g : Y₁ ⊞ Y₂ ⟶ Z := biprod.desc g₁ g₂
  have hnotEpi : ¬ IsSplitEpi g := by
    intro hg
    letI : IsSplitEpi g := hg
    let s : Z ⟶ Y₁ ⊞ Y₂ := section_ g
    let s₁ : Z ⟶ Y₁ := s ≫ (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)
    let s₂ : Z ⟶ Y₂ := s ≫ (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂)
    have hsum : s₁ ≫ g₁ + s₂ ≫ g₂ = 𝟙 Z := by
      calc
        s₁ ≫ g₁ + s₂ ≫ g₂ = s ≫ g := by
          simp [g, s₁, s₂, biprod.desc_eq, Preadditive.comp_add,
            Category.assoc]
        _ = 𝟙 Z := IsSplitEpi.id g
    have hnonunit₁ : ¬ IsUnit (End.of (s₁ ≫ g₁)) := by
      intro hu
      letI : IsIso (s₁ ≫ g₁) :=
        (isUnit_iff_isIso (End.of (s₁ ≫ g₁))).1 hu
      apply hg₁.not_isSplitEpi
      exact IsSplitEpi.mk'
        { section_ := inv (s₁ ≫ g₁) ≫ s₁
          id := by rw [Category.assoc]; simp }
    have hnonunit₂ : ¬ IsUnit (End.of (s₂ ≫ g₂)) := by
      intro hu
      letI : IsIso (s₂ ≫ g₂) :=
        (isUnit_iff_isIso (End.of (s₂ ≫ g₂))).1 hu
      apply hg₂.not_isSplitEpi
      exact IsSplitEpi.mk'
        { section_ := inv (s₂ ≫ g₂) ≫ s₂
          id := by rw [Category.assoc]; simp }
    have hunit : IsUnit (End.of (s₁ ≫ g₁ + s₂ ≫ g₂)) := by
      rw [hsum]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hunit with h | h
    · exact hnonunit₁ h
    · exact hnonunit₂ h
  have hnotMono : ¬ IsSplitMono g := by
    intro hg
    letI : IsSplitMono g := hg
    haveI : IsSplitMono
        ((biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ≫ g) := inferInstance
    apply hg₁.not_isSplitMono
    simpa [g] using
      (inferInstance : IsSplitMono
        ((biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ≫ g))
  refine
    { not_isSplitMono := hnotMono
      not_isSplitEpi := hnotEpi
      factorization := ?_ }
  intro N a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  left
  let q₁ : Y₁ ⟶ N := (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ≫ a
  let q₂ : Y₂ ⟶ N := (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) ≫ a
  have hfactor₁ : q₁ ≫ b = g₁ := by
    calc
      q₁ ≫ b = (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ≫ (a ≫ b) := by
        simp only [q₁, Category.assoc]
      _ = biprod.inl ≫ biprod.desc g₁ g₂ := by rw [hab]
      _ = g₁ := biprod.inl_desc g₁ g₂
  have hfactor₂ : q₂ ≫ b = g₂ := by
    calc
      q₂ ≫ b = (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) ≫ (a ≫ b) := by
        simp only [q₂, Category.assoc]
      _ = biprod.inr ≫ biprod.desc g₁ g₂ := by rw [hab]
      _ = g₂ := biprod.inr_desc g₁ g₂
  have hq₁ : IsSplitMono q₁ :=
    (hg₁.factorization q₁ b hfactor₁).resolve_right hb
  have hq₂ : IsSplitMono q₂ :=
    (hg₂.factorization q₂ b hfactor₂).resolve_right hb
  letI : IsSplitMono q₁ := hq₁
  letI : IsSplitMono q₂ := hq₂
  let t₁ : N ⟶ Y₁ := retraction q₁
  let t₂ : N ⟶ Y₂ := retraction q₂
  let q₁₂ : Y₁ ⟶ Y₂ := q₁ ≫ t₂
  let q₂₁ : Y₂ ⟶ Y₁ := q₂ ≫ t₁
  let r : Y₁ ⊞ Y₂ ⟶ Y₁ ⊞ Y₂ :=
    (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ≫ q₁₂ ≫
        (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) +
      (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ≫ q₂₁ ≫
        (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂)
  have hr : IsRadicalMorphism r := by
    apply isRadicalMorphism_add
    · have hq : IsRadicalMorphism
          ((biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁) ≫ q₁₂) :=
        isRadicalMorphism_precomp biprod.fst (h₁₂ q₁₂)
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) hq)
    · have hq : IsRadicalMorphism
          ((biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂) ≫ q₂₁) :=
        isRadicalMorphism_precomp biprod.snd (h₂₁ q₂₁)
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) hq)
  let t : N ⟶ Y₁ ⊞ Y₂ := biprod.lift t₁ t₂
  have hq₁t₁ : q₁ ≫ t₁ = 𝟙 Y₁ := IsSplitMono.id q₁
  have hq₂t₂ : q₂ ≫ t₂ = 𝟙 Y₂ := IsSplitMono.id q₂
  have hinl_a : (biprod.inl : Y₁ ⟶ Y₁ ⊞ Y₂) ≫ a = q₁ := rfl
  have hinr_a : (biprod.inr : Y₂ ⟶ Y₁ ⊞ Y₂) ≫ a = q₂ := rfl
  have hat : a ≫ t = 𝟙 (Y₁ ⊞ Y₂) + r := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [t, r, q₁₂, q₂₁, Category.assoc]
        rw [← Category.assoc, hinl_a, hq₁t₁]
      · simp [t, r, q₁₂, q₂₁, Category.assoc]
        rw [← Category.assoc, hinl_a]
    · apply biprod.hom_ext
      · simp [t, r, q₁₂, q₂₁, Category.assoc]
        rw [← Category.assoc, hinr_a]
      · simp [t, r, q₁₂, q₂₁, Category.assoc]
        rw [← Category.assoc, hinr_a, hq₂t₂]
  have hsplit : IsSplitMono (𝟙 (Y₁ ⊞ Y₂) + r) :=
    isSplitMono_add_of_isRadicalMorphism (𝟙 (Y₁ ⊞ Y₂)) hr
  rw [← hat] at hsplit
  letI : IsSplitMono (a ≫ t) := hsplit
  exact IsSplitMono.mk'
    { retraction := t ≫ retraction (a ≫ t)
      id := by rw [← Category.assoc, IsSplitMono.id] }

end MagnitudeConjecture.CategoryTheory
