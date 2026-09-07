import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Removing an injective kernel from a right almost-split map

An injective kernel splits off the source of a right almost-split morphism.
The induced morphism on the complementary summand is monic, right almost
split, and therefore right minimal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasBinaryBiproducts C]

/-- A right almost-split morphism with injective kernel is the direct sum of
that kernel, mapped to zero, and a monic minimal right almost-split map. -/
theorem exists_mono_rightAlmostSplit_complement_of_injective_kernel
    {E Y : C} (f : E ⟶ Y) (hf : IsRightAlmostSplit f)
    [Injective (kernel f)] :
    ∃ (E' : C) (g : E' ⟶ Y),
      Mono g ∧ IsRightAlmostSplit g ∧ IsRightMinimal g ∧
        Nonempty (E ≅ kernel f ⊞ E') := by
  let i : kernel f ⟶ E := kernel.ι f
  letI : IsSplitMono i := IsSplitMono.mk'
    { retraction := Injective.factorThru (𝟙 (kernel f)) i
      id := Injective.comp_factorThru (𝟙 (kernel f)) i }
  let c : CokernelCofork i := Cofork.ofπ (cokernel.π i)
    ((cokernel.condition i).trans zero_comp.symm)
  let hc : IsColimit c := cokernelIsCokernel i
  let B := binaryBiconeOfIsSplitMonoOfCokernel hc
  let hB : B.IsBilimit :=
    isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hc
  let inl : kernel f ⟶ E := B.inl
  let inr : c.pt ⟶ E := B.inr
  let fst : E ⟶ kernel f := B.fst
  let snd : E ⟶ c.pt := B.snd
  have hBinl : inl = kernel.ι f := rfl
  have hBinl_f : inl ≫ f = 0 := by
    rw [hBinl]
    exact kernel.condition f
  have hInlFst : inl ≫ fst = 𝟙 (kernel f) := by
    dsimp only [inl, fst, B]
    exact (binaryBiconeOfIsSplitMonoOfCokernel hc).inl_fst
  have hInrFst : inr ≫ fst = 0 := by
    dsimp only [inr, fst, B]
    exact (binaryBiconeOfIsSplitMonoOfCokernel hc).inr_fst
  have hInrSnd : inr ≫ snd = 𝟙 c.pt := by
    dsimp only [inr, snd, B]
    exact (binaryBiconeOfIsSplitMonoOfCokernel hc).inr_snd
  have hTotal : fst ≫ inl + snd ≫ inr = 𝟙 E := by
    dsimp only [fst, inl, snd, inr, B]
    exact CategoryTheory.Limits.IsBilimit.binary_total
      (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hc)
  letI : IsSplitMono inr := IsSplitMono.mk'
    { retraction := snd
      id := hInrSnd }
  let g : c.pt ⟶ Y := inr ≫ f
  have hgNotSplitEpi : ¬ IsSplitEpi g := by
    intro hg
    obtain ⟨s⟩ := hg.exists_splitEpi
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := s.section_ ≫ inr
        id := by
          rw [Category.assoc]
          exact s.id }
  have hgAlmost : IsRightAlmostSplit g := by
    refine ⟨hgNotSplitEpi, ?_⟩
    intro X q hq
    obtain ⟨a, ha⟩ := hf.factors q hq
    have hdecomp :
        a = (a ≫ fst) ≫ inl + (a ≫ snd) ≫ inr := by
      calc
        a = a ≫ 𝟙 E := by simp
        _ = a ≫ (fst ≫ inl + snd ≫ inr) := by rw [hTotal]
        _ = (a ≫ fst) ≫ inl + (a ≫ snd) ≫ inr := by
          rw [Preadditive.comp_add]
          simp only [Category.assoc]
    refine ⟨a ≫ snd, ?_⟩
    rw [← ha]
    calc
      (a ≫ snd) ≫ g =
          ((a ≫ snd) ≫ inr) ≫ f := by
            simp only [g, Category.assoc]
      _ = ((a ≫ fst) ≫ inl + (a ≫ snd) ≫ inr) ≫ f := by
            rw [Preadditive.add_comp]
            simp only [Category.assoc, hBinl_f, comp_zero, zero_add]
      _ = a ≫ f := by rw [← hdecomp]
  have hgMono : Mono g := by
    apply Preadditive.mono_of_cancel_zero
    intro Z a ha
    have hainrf : (a ≫ inr) ≫ f = 0 := by
      simpa only [g, Category.assoc] using ha
    let l : Z ⟶ kernel f := kernel.lift f (a ≫ inr) hainrf
    have hlift : l ≫ inl = a ≫ inr := by
      dsimp only [l]
      rw [hBinl, kernel.lift_ι]
    have hl : l = 0 := by
      calc
        l = l ≫ 𝟙 (kernel f) := by simp
        _ = l ≫ (inl ≫ fst) := by rw [hInlFst]
        _ = (l ≫ inl) ≫ fst := by simp
        _ = (a ≫ inr) ≫ fst := by rw [hlift]
        _ = 0 := by rw [Category.assoc, hInrFst, comp_zero]
    apply zero_of_comp_mono inr
    calc
      a ≫ inr = l ≫ inl := hlift.symm
      _ = 0 := by simp only [hl, zero_comp]
  letI : Mono g := hgMono
  have hgMinimal : IsRightMinimal g := by
    intro e he
    have heq : e = 𝟙 _ := by
      apply (cancel_mono g).1
      simpa using he
    rw [heq]
    infer_instance
  exact ⟨c.pt, g, hgMono, hgAlmost, hgMinimal,
    ⟨biprod.uniqueUpToIso (kernel f) c.pt hB⟩⟩

end MagnitudeConjecture.CategoryTheory
