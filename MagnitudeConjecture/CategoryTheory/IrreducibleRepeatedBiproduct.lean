import MagnitudeConjecture.CategoryTheory.IrreducibleBinaryBiproduct
import MagnitudeConjecture.CategoryTheory.AlmostSplitDuality
import MagnitudeConjecture.CategoryTheory.RadicalMinimality
import MagnitudeConjecture.LinearAlgebra.LocalAlgebraResidue

/-!
# Irreducible maps with a repeated binary-biproduct summand

When the two summands in the target of a binary lift are isomorphic, the
off-diagonal-radical criterion does not apply.  This file replaces it by the
standard multiplicity-space criterion.  Endomorphisms of the repeated
indecomposable are assumed scalar modulo the categorical radical, and every
scalar row operation on the two component maps is assumed irreducible.

The proof is Gaussian elimination modulo the radical.  After removing the
scalar part of one cross term, the corresponding linear combination is still
irreducible and hence supplies a second splitting.  The remaining cross terms
are radical, so the resulting two-by-two matrix is the identity plus a radical
morphism and is invertible.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CategoryTheory

universe u v w

variable {K : Type w} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear K C] [HasBinaryBiproducts C]

omit [HasBinaryBiproducts C] in
/-- Over an algebraically closed field, an endomorphism of a nonzero object
with finite-dimensional local endomorphism ring is scalar modulo the
categorical radical. -/
theorem exists_scalar_sub_isRadicalMorphism_of_algClosed
    [IsAlgClosed K] {Y : C} [FiniteDimensional K (End Y)]
    [IsLocalRing (End Y)] (hY : ¬ IsZero Y) (q : Y ⟶ Y) :
    ∃ c : K, IsRadicalMorphism (q - c • 𝟙 Y) := by
  obtain ⟨c, hc⟩ :=
    MagnitudeConjecture.LocalAlgebraResidue.exists_isResidueScalar
      K (E := End Y) q
  refine ⟨c,
    (isRadicalMorphism_iff_not_isSplitEpi_of_local_end hY _).2 ?_⟩
  intro hsplit
  let r : End Y := q - c • 𝟙 Y
  have hrNonunit : ¬ IsUnit r := by
    change ¬ IsUnit (End.of q - c • (1 : End Y))
    simpa only [MagnitudeConjecture.LocalAlgebraResidue.IsResidueScalar,
      Algebra.algebraMap_eq_smul_one] using hc
  letI : IsSplitEpi r := hsplit
  letI : IsArtinianRing (End Y) := IsArtinianRing.of_finite K (End Y)
  have hproduct : IsUnit (r * End.of (section_ r)) := by
    rw [End.mul_def, IsSplitEpi.id]
    exact isUnit_one
  exact hrNonunit (isUnit_of_mul_isUnit_left hproduct)

/-- A repeated-summand binary lift is irreducible when scalar row operations
on its two components remain irreducible and endomorphisms of the repeated
summand are scalar modulo the radical. -/
theorem isIrreducibleMorphism_biprod_lift_repeated
    {X Y : C} [IsLocalRing (End X)]
    (f₁ f₂ : X ⟶ Y)
    (hf₁ : IsIrreducibleMorphism f₁)
    (hcombination : ∀ c : K,
      IsIrreducibleMorphism (f₂ - c • f₁))
    (hscalar : ∀ q : Y ⟶ Y, ∃ c : K,
      IsRadicalMorphism (q - c • 𝟙 Y)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  let f : X ⟶ Y ⊞ Y := biprod.lift f₁ f₂
  have hf₂ : IsIrreducibleMorphism f₂ := by
    simpa using hcombination 0
  have hnotMono : ¬ IsSplitMono f := by
    intro hf
    letI : IsSplitMono f := hf
    let r : Y ⊞ Y ⟶ X := retraction f
    let r₁ : Y ⟶ X := (biprod.inl : Y ⟶ Y ⊞ Y) ≫ r
    let r₂ : Y ⟶ X := (biprod.inr : Y ⟶ Y ⊞ Y) ≫ r
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
        (f ≫ (biprod.fst : Y ⊞ Y ⟶ Y)) := inferInstance
    apply hf₁.not_isSplitEpi
    simpa [f] using
      (inferInstance : IsSplitEpi
        (f ≫ (biprod.fst : Y ⊞ Y ⟶ Y)))
  refine
    { not_isSplitMono := hnotMono
      not_isSplitEpi := hnotEpi
      factorization := ?_ }
  intro N a b hab
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  right
  let p₁ : N ⟶ Y := b ≫ (biprod.fst : Y ⊞ Y ⟶ Y)
  let p₂ : N ⟶ Y := b ≫ (biprod.snd : Y ⊞ Y ⟶ Y)
  have hfactor₁ : a ≫ p₁ = f₁ := by
    calc
      a ≫ p₁ = (a ≫ b) ≫ (biprod.fst : Y ⊞ Y ⟶ Y) := by
        simp only [p₁, Category.assoc]
      _ = biprod.lift f₁ f₂ ≫ biprod.fst := by rw [hab]
      _ = f₁ := biprod.lift_fst f₁ f₂
  have hfactor₂ : a ≫ p₂ = f₂ := by
    calc
      a ≫ p₂ = (a ≫ b) ≫ (biprod.snd : Y ⊞ Y ⟶ Y) := by
        simp only [p₂, Category.assoc]
      _ = biprod.lift f₁ f₂ ≫ biprod.snd := by rw [hab]
      _ = f₂ := biprod.lift_snd f₁ f₂
  have hp₁ : IsSplitEpi p₁ :=
    (hf₁.factorization a p₁ hfactor₁).resolve_left ha
  letI : IsSplitEpi p₁ := hp₁
  let s₁ : Y ⟶ N := section_ p₁
  let q₁₂ : Y ⟶ Y := s₁ ≫ p₂
  obtain ⟨c, hc⟩ := hscalar q₁₂
  let p₂' : N ⟶ Y := p₂ - c • p₁
  have hfactor₂' : a ≫ p₂' = f₂ - c • f₁ := by
    simp only [p₂', Preadditive.comp_sub, Linear.comp_smul,
      hfactor₁, hfactor₂]
  have hp₂' : IsSplitEpi p₂' :=
    ((hcombination c).factorization a p₂' hfactor₂').resolve_left ha
  letI : IsSplitEpi p₂' := hp₂'
  let s₂ : Y ⟶ N := section_ p₂'
  let r₁₂ : Y ⟶ Y := s₁ ≫ p₂'
  have hr₁₂ : IsRadicalMorphism r₁₂ := by
    have hr₁₂eq : r₁₂ = q₁₂ - c • 𝟙 Y := by
      simp only [r₁₂, q₁₂, p₂', Preadditive.comp_sub,
        Linear.comp_smul]
      rw [IsSplitEpi.id p₁]
    rw [hr₁₂eq]
    exact hc
  let q₂₁ : Y ⟶ Y := s₂ ≫ p₁
  obtain ⟨d, hd⟩ := hscalar q₂₁
  let t₂ : Y ⟶ N := s₂ - d • s₁
  let e₂ : Y ⟶ Y := t₂ ≫ p₂'
  have he₂eq : e₂ = 𝟙 Y - d • r₁₂ := by
    simp only [e₂, t₂, r₁₂, Preadditive.sub_comp,
      Linear.smul_comp]
    rw [IsSplitEpi.id p₂']
  have hdrad : IsRadicalMorphism (d • r₁₂) := by
    have hcomp : d • r₁₂ = (d • 𝟙 Y) ≫ r₁₂ := by
      simp
    rw [hcomp]
    exact isRadicalMorphism_precomp (d • 𝟙 Y) hr₁₂
  haveI : IsIso e₂ := by
    rw [he₂eq]
    simpa using hdrad (𝟙 Y)
  let s₂' : Y ⟶ N := inv e₂ ≫ t₂
  have hs₂' : s₂' ≫ p₂' = 𝟙 Y := by
    simp only [s₂', e₂, Category.assoc, IsIso.inv_hom_id]
  have hr₂₁ : IsRadicalMorphism (s₂' ≫ p₁) := by
    have ht₂p₁ : t₂ ≫ p₁ = q₂₁ - d • 𝟙 Y := by
      simp only [t₂, q₂₁, Preadditive.sub_comp,
        Linear.smul_comp]
      rw [IsSplitEpi.id p₁]
    change IsRadicalMorphism ((inv e₂ ≫ t₂) ≫ p₁)
    rw [Category.assoc, ht₂p₁]
    exact isRadicalMorphism_precomp (inv e₂) hd
  let b' : N ⟶ Y ⊞ Y := biprod.lift p₁ p₂'
  let s : Y ⊞ Y ⟶ N := biprod.desc s₁ s₂'
  let r : Y ⊞ Y ⟶ Y ⊞ Y :=
    (biprod.fst : Y ⊞ Y ⟶ Y) ≫ r₁₂ ≫
        (biprod.inr : Y ⟶ Y ⊞ Y) +
      (biprod.snd : Y ⊞ Y ⟶ Y) ≫ (s₂' ≫ p₁) ≫
        (biprod.inl : Y ⟶ Y ⊞ Y)
  have hr : IsRadicalMorphism r := by
    apply isRadicalMorphism_add
    · have hq : IsRadicalMorphism
          ((biprod.fst : Y ⊞ Y ⟶ Y) ≫ r₁₂) :=
        isRadicalMorphism_precomp biprod.fst hr₁₂
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inr : Y ⟶ Y ⊞ Y) hq)
    · have hq : IsRadicalMorphism
          ((biprod.snd : Y ⊞ Y ⟶ Y) ≫ (s₂' ≫ p₁)) :=
        isRadicalMorphism_precomp biprod.snd hr₂₁
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inl : Y ⟶ Y ⊞ Y) hq)
  have hsb' : s ≫ b' = 𝟙 (Y ⊞ Y) + r := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [s, b', r, r₁₂, p₁, s₁, Category.assoc]
      · simp [s, b', r, r₁₂, Category.assoc]
    · apply biprod.hom_ext
      · simp [s, b', r, Category.assoc]
      · simp [s, b', r, hs₂', Category.assoc]
  have hsplit : IsSplitEpi (𝟙 (Y ⊞ Y) + r) :=
    isSplitEpi_add_of_isRadicalMorphism (𝟙 (Y ⊞ Y)) hr
  rw [← hsb'] at hsplit
  letI : IsSplitEpi (s ≫ b') := hsplit
  have hb' : IsSplitEpi b' := IsSplitEpi.mk'
    { section_ := section_ (s ≫ b') ≫ s
      id := by rw [Category.assoc, IsSplitEpi.id] }
  let e : Y ⊞ Y ⟶ Y ⊞ Y :=
    biprod.lift (biprod.fst : Y ⊞ Y ⟶ Y)
      ((-c) • (biprod.fst : Y ⊞ Y ⟶ Y) + biprod.snd)
  let eInv : Y ⊞ Y ⟶ Y ⊞ Y :=
    biprod.lift (biprod.fst : Y ⊞ Y ⟶ Y)
      (c • (biprod.fst : Y ⊞ Y ⟶ Y) + biprod.snd)
  have heInv : e ≫ eInv = 𝟙 (Y ⊞ Y) := by
    apply biprod.hom_ext
    · simp [e, eInv]
    · simp [e, eInv, Preadditive.comp_add, Linear.comp_smul]
  have hInve : eInv ≫ e = 𝟙 (Y ⊞ Y) := by
    apply biprod.hom_ext
    · simp [e, eInv]
    · simp [e, eInv, Preadditive.comp_add, Linear.comp_smul]
  letI : IsIso e := ⟨⟨eInv, heInv, hInve⟩⟩
  have hb'eq : b' = b ≫ e := by
    apply biprod.hom_ext
    · simp [b', e, p₁]
    · simp [b', e, p₁, p₂', p₂, Preadditive.comp_add,
        Linear.comp_smul]
      abel
  rw [hb'eq] at hb'
  letI : IsSplitEpi (b ≫ e) := hb'
  exact IsSplitEpi.mk'
    { section_ := e ≫ section_ (b ≫ e)
      id := by
        rw [← cancel_mono e]
        simp [Category.assoc] }

/-- The symmetric form of the repeated-summand lift criterion, with scalar
row operations based at the second component. -/
theorem isIrreducibleMorphism_biprod_lift_repeated_symm
    {X Y : C} [IsLocalRing (End X)]
    (f₁ f₂ : X ⟶ Y)
    (hf₂ : IsIrreducibleMorphism f₂)
    (hcombination : ∀ c : K,
      IsIrreducibleMorphism (f₁ - c • f₂))
    (hscalar : ∀ q : Y ⟶ Y, ∃ c : K,
      IsRadicalMorphism (q - c • 𝟙 Y)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  have hswapped := isIrreducibleMorphism_biprod_lift_repeated
    f₂ f₁ hf₂ hcombination hscalar
  have hbraided := hswapped.postcomp_iso (biprod.braiding Y Y)
  convert hbraided using 1
  apply biprod.hom_ext <;> simp [biprod.braiding]

/-- A repeated-summand binary desc is irreducible when scalar column
operations on its two components remain irreducible and endomorphisms of the
repeated summand are scalar modulo the radical. -/
theorem isIrreducibleMorphism_biprod_desc_repeated
    {Y Z : C} [IsLocalRing (End Z)]
    (g₁ g₂ : Y ⟶ Z)
    (hg₁ : IsIrreducibleMorphism g₁)
    (hcombination : ∀ c : K,
      IsIrreducibleMorphism (g₂ - c • g₁))
    (hscalar : ∀ q : Y ⟶ Y, ∃ c : K,
      IsRadicalMorphism (q - c • 𝟙 Y)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  let g : Y ⊞ Y ⟶ Z := biprod.desc g₁ g₂
  have hg₂ : IsIrreducibleMorphism g₂ := by
    simpa using hcombination 0
  have hnotEpi : ¬ IsSplitEpi g := by
    intro hg
    letI : IsSplitEpi g := hg
    let s : Z ⟶ Y ⊞ Y := section_ g
    let s₁ : Z ⟶ Y := s ≫ (biprod.fst : Y ⊞ Y ⟶ Y)
    let s₂ : Z ⟶ Y := s ≫ (biprod.snd : Y ⊞ Y ⟶ Y)
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
        ((biprod.inl : Y ⟶ Y ⊞ Y) ≫ g) := inferInstance
    apply hg₁.not_isSplitMono
    simpa [g] using
      (inferInstance : IsSplitMono
        ((biprod.inl : Y ⟶ Y ⊞ Y) ≫ g))
  refine
    { not_isSplitMono := hnotMono
      not_isSplitEpi := hnotEpi
      factorization := ?_ }
  intro N a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  left
  let q₁ : Y ⟶ N := (biprod.inl : Y ⟶ Y ⊞ Y) ≫ a
  let q₂ : Y ⟶ N := (biprod.inr : Y ⟶ Y ⊞ Y) ≫ a
  have hfactor₁ : q₁ ≫ b = g₁ := by
    calc
      q₁ ≫ b = (biprod.inl : Y ⟶ Y ⊞ Y) ≫ (a ≫ b) := by
        simp only [q₁, Category.assoc]
      _ = biprod.inl ≫ biprod.desc g₁ g₂ := by rw [hab]
      _ = g₁ := biprod.inl_desc g₁ g₂
  have hfactor₂ : q₂ ≫ b = g₂ := by
    calc
      q₂ ≫ b = (biprod.inr : Y ⟶ Y ⊞ Y) ≫ (a ≫ b) := by
        simp only [q₂, Category.assoc]
      _ = biprod.inr ≫ biprod.desc g₁ g₂ := by rw [hab]
      _ = g₂ := biprod.inr_desc g₁ g₂
  have hq₁ : IsSplitMono q₁ :=
    (hg₁.factorization q₁ b hfactor₁).resolve_right hb
  letI : IsSplitMono q₁ := hq₁
  let t₁ : N ⟶ Y := retraction q₁
  let q₂₁ : Y ⟶ Y := q₂ ≫ t₁
  obtain ⟨c, hc⟩ := hscalar q₂₁
  let q₂' : Y ⟶ N := q₂ - c • q₁
  have hfactor₂' : q₂' ≫ b = g₂ - c • g₁ := by
    simp only [q₂', Preadditive.sub_comp, Linear.smul_comp,
      hfactor₁, hfactor₂]
  have hq₂' : IsSplitMono q₂' :=
    ((hcombination c).factorization q₂' b hfactor₂').resolve_right hb
  letI : IsSplitMono q₂' := hq₂'
  let t₂ : N ⟶ Y := retraction q₂'
  let r₂₁ : Y ⟶ Y := q₂' ≫ t₁
  have hr₂₁ : IsRadicalMorphism r₂₁ := by
    have hr₂₁eq : r₂₁ = q₂₁ - c • 𝟙 Y := by
      simp only [r₂₁, q₂₁, q₂', Preadditive.sub_comp,
        Linear.smul_comp]
      rw [IsSplitMono.id q₁]
    rw [hr₂₁eq]
    exact hc
  let q₁₂ : Y ⟶ Y := q₁ ≫ t₂
  obtain ⟨d, hd⟩ := hscalar q₁₂
  let u₂ : N ⟶ Y := t₂ - d • t₁
  let e₂ : Y ⟶ Y := q₂' ≫ u₂
  have he₂eq : e₂ = 𝟙 Y - d • r₂₁ := by
    simp only [e₂, u₂, r₂₁, Preadditive.comp_sub,
      Linear.comp_smul]
    rw [IsSplitMono.id q₂']
  have hdrad : IsRadicalMorphism (d • r₂₁) := by
    have hcomp : d • r₂₁ = r₂₁ ≫ (d • 𝟙 Y) := by
      simp
    rw [hcomp]
    exact isRadicalMorphism_postcomp (d • 𝟙 Y) hr₂₁
  haveI : IsIso e₂ := by
    rw [he₂eq]
    simpa using hdrad (𝟙 Y)
  let t₂' : N ⟶ Y := u₂ ≫ inv e₂
  have ht₂' : q₂' ≫ t₂' = 𝟙 Y := by
    simp only [t₂', e₂, ← Category.assoc, IsIso.hom_inv_id]
  have hr₁₂ : IsRadicalMorphism (q₁ ≫ t₂') := by
    have hq₁u₂ : q₁ ≫ u₂ = q₁₂ - d • 𝟙 Y := by
      simp only [u₂, q₁₂, Preadditive.comp_sub,
        Linear.comp_smul]
      rw [IsSplitMono.id q₁]
    change IsRadicalMorphism (q₁ ≫ (u₂ ≫ inv e₂))
    rw [← Category.assoc, hq₁u₂]
    exact isRadicalMorphism_postcomp (inv e₂) hd
  let a' : Y ⊞ Y ⟶ N := biprod.desc q₁ q₂'
  let t : N ⟶ Y ⊞ Y := biprod.lift t₁ t₂'
  let r : Y ⊞ Y ⟶ Y ⊞ Y :=
    (biprod.fst : Y ⊞ Y ⟶ Y) ≫ (q₁ ≫ t₂') ≫
        (biprod.inr : Y ⟶ Y ⊞ Y) +
      (biprod.snd : Y ⊞ Y ⟶ Y) ≫ r₂₁ ≫
        (biprod.inl : Y ⟶ Y ⊞ Y)
  have hr : IsRadicalMorphism r := by
    apply isRadicalMorphism_add
    · have hq : IsRadicalMorphism
          ((biprod.fst : Y ⊞ Y ⟶ Y) ≫ (q₁ ≫ t₂')) :=
        isRadicalMorphism_precomp biprod.fst hr₁₂
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inr : Y ⟶ Y ⊞ Y) hq)
    · have hq : IsRadicalMorphism
          ((biprod.snd : Y ⊞ Y ⟶ Y) ≫ r₂₁) :=
        isRadicalMorphism_precomp biprod.snd hr₂₁
      simpa only [Category.assoc] using
        (isRadicalMorphism_postcomp (biprod.inl : Y ⟶ Y ⊞ Y) hq)
  have ha't : a' ≫ t = 𝟙 (Y ⊞ Y) + r := by
    have hq₁t₁ : q₁ ≫ t₁ = 𝟙 Y := IsSplitMono.id q₁
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [a', t, r, hq₁t₁, Category.assoc]
      · simp [a', t, r, Category.assoc]
    · apply biprod.hom_ext
      · simp [a', t, r, r₂₁, Category.assoc]
      · simp [a', t, r, ht₂', Category.assoc]
  have hsplit : IsSplitMono (𝟙 (Y ⊞ Y) + r) :=
    isSplitMono_add_of_isRadicalMorphism (𝟙 (Y ⊞ Y)) hr
  rw [← ha't] at hsplit
  letI : IsSplitMono (a' ≫ t) := hsplit
  have ha' : IsSplitMono a' := IsSplitMono.mk'
    { retraction := t ≫ retraction (a' ≫ t)
      id := by rw [← Category.assoc, IsSplitMono.id] }
  let e : Y ⊞ Y ⟶ Y ⊞ Y :=
    biprod.desc (biprod.inl : Y ⟶ Y ⊞ Y)
      ((-c) • (biprod.inl : Y ⟶ Y ⊞ Y) + biprod.inr)
  let eInv : Y ⊞ Y ⟶ Y ⊞ Y :=
    biprod.desc (biprod.inl : Y ⟶ Y ⊞ Y)
      (c • (biprod.inl : Y ⟶ Y ⊞ Y) + biprod.inr)
  have heInv : e ≫ eInv = 𝟙 (Y ⊞ Y) := by
    apply biprod.hom_ext'
    · simp [e, eInv]
    · simp [e, eInv, Preadditive.add_comp, Linear.smul_comp]
  have hInve : eInv ≫ e = 𝟙 (Y ⊞ Y) := by
    apply biprod.hom_ext'
    · simp [e, eInv]
    · simp [e, eInv, Preadditive.add_comp, Linear.smul_comp]
  letI : IsIso e := ⟨⟨eInv, heInv, hInve⟩⟩
  have ha'eq : a' = e ≫ a := by
    apply biprod.hom_ext'
    · simp [a', e, q₁]
    · simp [a', e, q₁, q₂', q₂, Preadditive.add_comp,
        Linear.smul_comp]
      abel
  rw [ha'eq] at ha'
  letI : IsSplitMono (e ≫ a) := ha'
  exact IsSplitMono.mk'
    { retraction := retraction (e ≫ a) ≫ e
      id := by
        calc
          a ≫ retraction (e ≫ a) ≫ e =
              inv e ≫ ((e ≫ a) ≫ retraction (e ≫ a)) ≫ e := by
                simp only [Category.assoc, IsIso.inv_hom_id_assoc]
          _ = inv e ≫ e := by rw [IsSplitMono.id]; simp
          _ = 𝟙 (Y ⊞ Y) := by simp }

/-- The symmetric form of the repeated-summand desc criterion, with scalar
column operations based at the second component. -/
theorem isIrreducibleMorphism_biprod_desc_repeated_symm
    {Y Z : C} [IsLocalRing (End Z)]
    (g₁ g₂ : Y ⟶ Z)
    (hg₂ : IsIrreducibleMorphism g₂)
    (hcombination : ∀ c : K,
      IsIrreducibleMorphism (g₁ - c • g₂))
    (hscalar : ∀ q : Y ⟶ Y, ∃ c : K,
      IsRadicalMorphism (q - c • 𝟙 Y)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  have hswapped := isIrreducibleMorphism_biprod_desc_repeated
    g₂ g₁ hg₂ hcombination hscalar
  have hbraided := hswapped.precomp_iso (biprod.braiding Y Y)
  convert hbraided using 1
  apply biprod.hom_ext' <;> simp [biprod.braiding]

/-- The repeated-summand lift criterion after identifying two isomorphic
target summands. -/
theorem isIrreducibleMorphism_biprod_lift_isomorphic
    {X Y₁ Y₂ : C} [IsLocalRing (End X)]
    (e : Y₂ ≅ Y₁) (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂)
    (hf₁ : IsIrreducibleMorphism f₁)
    (hcombination : ∀ c : K,
      IsIrreducibleMorphism (f₂ ≫ e.hom - c • f₁))
    (hscalar : ∀ q : Y₁ ⟶ Y₁, ∃ c : K,
      IsRadicalMorphism (q - c • 𝟙 Y₁)) :
    IsIrreducibleMorphism (biprod.lift f₁ f₂) := by
  let E : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₁ := biprod.mapIso (Iso.refl Y₁) e
  have htransformed : IsIrreducibleMorphism
      (biprod.lift f₁ (f₂ ≫ e.hom)) :=
    isIrreducibleMorphism_biprod_lift_repeated
      f₁ (f₂ ≫ e.hom) hf₁ hcombination hscalar
  have hback := htransformed.postcomp_iso E.symm
  have heq : biprod.lift f₁ (f₂ ≫ e.hom) ≫ E.inv =
      biprod.lift f₁ f₂ := by
    apply biprod.hom_ext
    · simp [E]
    · simp [E, Category.assoc]
  change IsIrreducibleMorphism
    (biprod.lift f₁ (f₂ ≫ e.hom) ≫ E.inv) at hback
  rw [heq] at hback
  exact hback

/-- The repeated-summand desc criterion after identifying two isomorphic
source summands. -/
theorem isIrreducibleMorphism_biprod_desc_isomorphic
    {Y₁ Y₂ Z : C} [IsLocalRing (End Z)]
    (e : Y₂ ≅ Y₁) (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z)
    (hg₁ : IsIrreducibleMorphism g₁)
    (hcombination : ∀ c : K,
      IsIrreducibleMorphism (e.inv ≫ g₂ - c • g₁))
    (hscalar : ∀ q : Y₁ ⟶ Y₁, ∃ c : K,
      IsRadicalMorphism (q - c • 𝟙 Y₁)) :
    IsIrreducibleMorphism (biprod.desc g₁ g₂) := by
  let E : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₁ := biprod.mapIso (Iso.refl Y₁) e
  have htransformed : IsIrreducibleMorphism
      (biprod.desc g₁ (e.inv ≫ g₂)) :=
    isIrreducibleMorphism_biprod_desc_repeated
      g₁ (e.inv ≫ g₂) hg₁ hcombination hscalar
  have hback := htransformed.precomp_iso E
  have heq : E.hom ≫ biprod.desc g₁ (e.inv ≫ g₂) =
      biprod.desc g₁ g₂ := by
    apply biprod.hom_ext'
    · simp [E]
    · simp [E]
  rw [heq] at hback
  exact hback

end MagnitudeConjecture.CategoryTheory
