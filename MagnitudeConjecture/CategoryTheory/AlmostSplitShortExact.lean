import MagnitudeConjecture.CategoryTheory.AlmostSplitComparison
import MagnitudeConjecture.CategoryTheory.IndecomposableFiniteEnd
import MagnitudeConjecture.CategoryTheory.RadicalMinimality
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaTauSequence

/-!
# Almost-split morphisms in short exact sequences

This file records three intrinsic facts used to rotate the density-free
push-down theorem.  A right almost-split morphism has indecomposable target;
a radical kernel map in a short exact sequence makes the quotient map right
minimal; and a right-minimal right almost-split quotient makes the displayed
kernel map left almost split.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C]

/-- The target of a right almost-split morphism is indecomposable in any
preadditive category with binary biproducts. -/
theorem IsRightAlmostSplit.target_indecomposable
    [Preadditive C] [HasBinaryBiproducts C]
    {E Z : C} (f : E ⟶ Z) (hf : IsRightAlmostSplit f) :
    Indecomposable Z := by
  constructor
  · intro hZ
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := 0
        id := hZ.eq_of_tgt _ _ }
  · intro X Y e
    let p : Z ⟶ Z :=
      e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
    have hp : p ≫ p = p := by
      simp [p, Category.assoc]
    have splitEpi_idempotent_eq_id
        (q : Z ⟶ Z) (hq : q ≫ q = q) (hsplit : IsSplitEpi q) :
        q = 𝟙 Z := by
      letI : IsSplitEpi q := hsplit
      apply (cancel_epi q).1
      simpa only [Category.comp_id] using hq
    have hpzero_or_one : p = 0 ∨ p = 𝟙 Z := by
      by_cases hpSplit : IsSplitEpi p
      · exact Or.inr (splitEpi_idempotent_eq_id p hp hpSplit)
      · let q : Z ⟶ Z := 𝟙 Z - p
        have hq : q ≫ q = q :=
          CategoryTheory.Idempotents.idem_of_id_sub_idem p hp
        by_cases hqSplit : IsSplitEpi q
        · left
          have hqone := splitEpi_idempotent_eq_id q hq hqSplit
          dsimp only [q] at hqone
          exact sub_eq_self.mp hqone
        · obtain ⟨a, ha⟩ := hf.factors p hpSplit
          obtain ⟨b, hb⟩ := hf.factors q hqSplit
          exfalso
          apply hf.not_isSplitEpi
          apply IsSplitEpi.mk'
          refine
            { section_ := a + b
              id := ?_ }
          rw [Preadditive.add_comp, ha, hb]
          dsimp only [q]
          abel
    rcases hpzero_or_one with hpzero | hpone
    · left
      apply (IsZero.iff_id_eq_zero X).mpr
      have hproj :
          (biprod.fst : X ⊞ Y ⟶ X) ≫
              (biprod.inl : X ⟶ X ⊞ Y) = 0 := by
        calc
          biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by
            simp [p, Category.assoc]
          _ = 0 := by rw [hpzero]; simp
      have h := congrArg
        (fun q : End (X ⊞ Y) ↦ biprod.inl ≫ q ≫ biprod.fst) hproj
      simpa [Category.assoc] using h
    · right
      apply (IsZero.iff_id_eq_zero Y).mpr
      have hproj :
          (biprod.fst : X ⊞ Y ⟶ X) ≫
              (biprod.inl : X ⟶ X ⊞ Y) = 𝟙 (X ⊞ Y) := by
        calc
          biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by
            simp [p, Category.assoc]
          _ = 𝟙 (X ⊞ Y) := by rw [hpone]; simp
      have h := congrArg
        (fun q : End (X ⊞ Y) ↦ biprod.inr ≫ q ≫ biprod.snd) hproj
      simpa [Category.assoc] using h.symm

/-- An equivalence transports a weak-kernel diagram. -/
theorem isWeakKernel_map_equivalence
    {D : Type u'} [Category.{v'} D] [HasZeroMorphisms C]
    [HasZeroMorphisms D]
    {S : ShortComplex C}
    (hS : QuotientSubmoduleEquidistribution.Iyama.ShortComplex.IsWeakKernel S)
    (E : C ≌ D) :
    QuotientSubmoduleEquidistribution.Iyama.ShortComplex.IsWeakKernel
      (S.map E.functor) := by
  rw [QuotientSubmoduleEquidistribution.Iyama.ShortComplex.isWeakKernel_iff]
  change ∀ {W : D} (q : W ⟶ E.functor.obj S.X₂),
    q ≫ E.functor.map S.g = 0 →
      ∃ l : W ⟶ E.functor.obj S.X₁, l ≫ E.functor.map S.f = q
  intro W q hq
  let e : E.functor.obj (E.inverse.obj W) ≅ W := E.counitIso.app W
  let q' : E.inverse.obj W ⟶ S.X₂ :=
    E.functor.preimage (e.hom ≫ q)
  have hq' : q' ≫ S.g = 0 := by
    apply E.functor.map_injective
    rw [E.functor.map_comp, E.functor.map_preimage, E.functor.map_zero]
    rw [Category.assoc, hq, comp_zero]
  obtain ⟨l, hl⟩ :=
    (QuotientSubmoduleEquidistribution.Iyama.ShortComplex.isWeakKernel_iff S).mp
      hS q' hq'
  refine ⟨e.inv ≫ E.functor.map l, ?_⟩
  rw [Category.assoc, ← E.functor.map_comp, hl,
    E.functor.map_preimage, Iso.inv_hom_id_assoc]

/-- A monic weak kernel is an actual kernel. -/
def isLimit_kernelFork_of_isWeakKernel
    [HasZeroMorphisms C] {S : ShortComplex C}
    (hS : QuotientSubmoduleEquidistribution.Iyama.ShortComplex.IsWeakKernel S)
    [Mono S.f] : IsLimit (KernelFork.ofι S.f S.zero) := by
  refine Fork.IsLimit.mk _
    (fun s ↦ hS.lift (Fork.ι s) (KernelFork.condition s))
    (fun s ↦ hS.lift_f (Fork.ι s) (KernelFork.condition s)) ?_
  intro s m hm
  apply (cancel_mono S.f).1
  have hm' : m ≫ S.f = Fork.ι s := hm
  exact hm'.trans (hS.lift_f (Fork.ι s) (KernelFork.condition s)).symm

variable [Abelian C]

/-- If a target endomorphism fixes a left almost-split morphism, then
factoring that morphism through the endomorphism's image remains left almost
split. -/
theorem IsLeftAlmostSplit.comp_factorThruImage_of_comp_eq_self
    {M E : C} (f : M ⟶ E) (hf : IsLeftAlmostSplit f)
    (e : E ⟶ E) (he : f ≫ e = f) :
    IsLeftAlmostSplit (f ≫ Abelian.factorThruImage e) := by
  let q : E ⟶ Abelian.image e := Abelian.factorThruImage e
  let i : Abelian.image e ⟶ E := Abelian.image.ι e
  constructor
  · intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitMono
    apply hf.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := q ≫ s.retraction
        id := by simpa only [q, Category.assoc] using s.id }
  · intro X g hg
    obtain ⟨h, hh⟩ := hf.factors g hg
    refine ⟨i ≫ h, ?_⟩
    calc
      (f ≫ Abelian.factorThruImage e) ≫ (i ≫ h) =
          f ≫ (q ≫ i) ≫ h := by
            simp only [q, Category.assoc]
      _ = f ≫ e ≫ h := by rw [Abelian.image.fac]
      _ = f ≫ h := by rw [← Category.assoc, he]
      _ = g := hh

/-- In a short exact sequence, a radical kernel map makes the quotient map
right minimal. -/
theorem ShortComplex.ShortExact.isRightMinimal_g_of_isRadicalMorphism_f
    {S : ShortComplex C} (hS : S.ShortExact)
    (hf : IsRadicalMorphism S.f) : IsRightMinimal S.g := by
  letI : Mono S.f := hS.mono_f
  intro e he
  have hezero : (e - 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
  obtain ⟨l, hl⟩ := hS.exact.lift' (e - 𝟙 S.X₂) hezero
  have hlrad : IsRadicalMorphism (l ≫ S.f) :=
    isRadicalMorphism_precomp l hf
  have hi : IsIso (𝟙 S.X₂ - (l ≫ S.f) ≫ (-𝟙 S.X₂)) :=
    hlrad (-𝟙 S.X₂)
  have hid : 𝟙 S.X₂ - (l ≫ S.f) ≫ (-𝟙 S.X₂) = e := by
    rw [hl]
    simp
  exact hid ▸ hi

/-- A nonsplit epimorphism in a short exact sequence whose kernel has local
endomorphism ring is right minimal. -/
theorem ShortComplex.ShortExact.isRightMinimal_g_of_local_end
    {S : ShortComplex C} (hS : S.ShortExact)
    [IsLocalRing (End S.X₁)]
    (hg : ¬ IsSplitEpi S.g) : IsRightMinimal S.g := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  intro a ha
  have hfaZero : (S.f ≫ a) ≫ S.g = 0 := by
    rw [Category.assoc, ha, S.zero]
  let c : S.X₁ ⟶ S.X₁ := hS.exact.lift (S.f ≫ a) hfaZero
  have hc : c ≫ S.f = S.f ≫ a :=
    hS.exact.lift_f (S.f ≫ a) hfaZero
  have hsum : IsUnit (End.of c + (1 - End.of c)) := by
    rw [add_sub_cancel]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with
    hcUnit | hOneSubUnit
  · letI : IsIso c := (isUnit_iff_isIso (End.of c)).1 hcUnit
    let phi : S ⟶ S :=
      { τ₁ := c
        τ₂ := a
        τ₃ := 𝟙 _
        comm₁₂ := hc
        comm₂₃ := by simpa using ha }
    change IsIso phi.τ₂
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ phi hS hS
  · have hOneSubIso : IsIso (𝟙 S.X₁ - c) :=
      (isUnit_iff_isIso (1 - End.of c)).1 hOneSubUnit
    letI : IsIso (𝟙 S.X₁ - c) := hOneSubIso
    have hOneSubAZero : (𝟙 S.X₂ - a) ≫ S.g = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, ha, sub_self]
    let d : S.X₂ ⟶ S.X₁ :=
      hS.exact.lift (𝟙 S.X₂ - a) hOneSubAZero
    have hd : d ≫ S.f = 𝟙 S.X₂ - a :=
      hS.exact.lift_f (𝟙 S.X₂ - a) hOneSubAZero
    have hfd : S.f ≫ d = 𝟙 S.X₁ - c := by
      apply (cancel_mono S.f).1
      rw [Category.assoc, hd, Preadditive.comp_sub, Category.comp_id,
        Preadditive.sub_comp, Category.id_comp, hc]
    let r : S.X₂ ⟶ S.X₁ := d ≫ inv (𝟙 S.X₁ - c)
    have hfr : S.f ≫ r = 𝟙 S.X₁ := by
      dsimp only [r]
      rw [← Category.assoc, hfd, IsIso.hom_inv_id]
    let splitting := ShortComplex.Splitting.ofExactOfRetraction
      S hS.exact r hfr hS.epi_g
    haveI : IsSplitEpi S.g := splitting.isSplitEpi_g
    exact (hg inferInstance).elim

/-- A right-minimal right almost-split quotient in a short exact sequence
makes its displayed kernel map left almost split. -/
theorem ShortComplex.ShortExact.isLeftAlmostSplit_f_of_rightAlmostSplit_g
    {S : ShortComplex C} (hS : S.ShortExact)
    (hg : IsRightAlmostSplit S.g) (hmin : IsRightMinimal S.g) :
    IsLeftAlmostSplit S.f := by
  letI : Epi S.g := hS.epi_g
  have hk : IsLeftAlmostSplit (kernel.ι S.g) :=
    hg.kernel_ι_isLeftAlmostSplit S.g hmin
  let e : S.X₁ ≅ kernel S.g :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel).symm
  have he : e.hom ≫ kernel.ι S.g = S.f := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp hS.fIsKernel
      (kernelIsKernel S.g) WalkingParallelPair.zero
  rw [← he]
  exact hk.precomp_iso e

end MagnitudeConjecture.CategoryTheory
