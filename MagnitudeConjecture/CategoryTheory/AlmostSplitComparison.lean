import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Comparing short exact sequences with an almost-split sequence

This file isolates the final diagram argument in Gabriel's preservation
proof.  Given a comparison to a right almost-split short exact sequence, it
is enough to identify the left terms and to know that every noninvertible
endomorphism of the source left term factors through its injection.  The
comparison on the middle terms is then invertible by exactness.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

section

variable [Preadditive C] [Balanced C]

/-- In a short exact sequence, a splitting of the terminal epimorphism also
splits the initial monomorphism. -/
theorem ShortComplex.ShortExact.isSplitMono_f_of_isSplitEpi_g
    {S : ShortComplex C} (hS : S.ShortExact) [IsSplitEpi S.g] :
    IsSplitMono S.f := by
  let b := binaryBiconeOfIsSplitEpiOfKernel hS.fIsKernel
  apply IsSplitMono.mk'
  exact
    { retraction := b.fst
      id := b.inl_fst }

/-- Contrapositive splitting lemma for a short exact sequence. -/
theorem ShortComplex.ShortExact.not_isSplitEpi_g_of_not_isSplitMono_f
    {S : ShortComplex C} (hS : S.ShortExact)
    (hf : ¬ IsSplitMono S.f) : ¬ IsSplitEpi S.g := by
  intro hg
  apply hf
  letI : IsSplitEpi S.g := hg
  exact ShortComplex.ShortExact.isSplitMono_f_of_isSplitEpi_g hS

end

variable [Abelian C]

/-- A short exact sequence is right almost split when its endpoint is
identified with that of a right almost-split short exact sequence, its left
term is identified with the comparison kernel, and every noninvertible
endomorphism of its left term factors through its injection.

The proof first constructs the comparison of short exact sequences.  If its
left component were noninvertible, the factorization hypothesis and the
cokernel property would split the right almost-split terminal map.  Thus the
left component is invertible, and the short five lemma makes the middle
component invertible as well. -/
theorem ShortComplex.ShortExact.isRightAlmostSplit_of_leftEndomorphismFactorization
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (hTg : IsRightAlmostSplit T.g) (hSg : ¬ IsSplitEpi S.g)
    (e₁ : T.X₁ ≅ S.X₁) (e₃ : S.X₃ ≅ T.X₃)
    (hfac : ∀ q : S.X₁ ⟶ S.X₁, ¬ IsIso q →
      ∃ c : S.X₂ ⟶ S.X₁, S.f ≫ c = q) :
    IsRightAlmostSplit S.g := by
  have hSg_comp : ¬ IsSplitEpi (S.g ≫ e₃.hom) := by
    intro hs
    apply hSg
    letI : IsSplitEpi (S.g ≫ e₃.hom) := hs
    rw [show S.g = (S.g ≫ e₃.hom) ≫ e₃.inv by simp]
    infer_instance
  obtain ⟨a, ha⟩ := hTg.factors (S.g ≫ e₃.hom) hSg_comp
  haveI := hT.mono_f
  obtain ⟨b, hb⟩ := hT.exact.lift'
    (S.f ≫ a) (by
      rw [Category.assoc, ha, ← Category.assoc, S.zero, zero_comp])
  let φ : S ⟶ T :=
    { τ₁ := b
      τ₂ := a
      τ₃ := e₃.hom
      comm₁₂ := hb
      comm₂₃ := ha }
  let q : S.X₁ ⟶ S.X₁ := b ≫ e₁.hom
  have hq : IsIso q := by
    by_contra hqnot
    obtain ⟨c, hc⟩ := hfac q hqnot
    have hbq : b = S.f ≫ c ≫ e₁.inv := by
      apply (cancel_mono e₁.hom).1
      simp only [Category.assoc, e₁.inv_hom_id, Category.comp_id]
      simpa only [q] using hc.symm
    let r : S.X₂ ⟶ T.X₂ := a - c ≫ e₁.inv ≫ T.f
    have hr : S.f ≫ r = 0 := by
      simp only [r, Preadditive.comp_sub, ← hb]
      simp only [← Category.assoc, ← hbq, sub_self]
    haveI := hS.epi_g
    obtain ⟨d, hd⟩ := hS.exact.desc' r hr
    have hdg : d ≫ T.g = e₃.hom := by
      apply (cancel_epi S.g).1
      rw [← Category.assoc, hd]
      dsimp only [r]
      rw [Preadditive.sub_comp, ha]
      simp only [Category.assoc, T.zero, comp_zero, sub_zero]
    apply hTg.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := e₃.inv ≫ d
        id := by rw [Category.assoc, hdg, e₃.inv_hom_id] }
  letI : IsIso q := hq
  have hbq : b = q ≫ e₁.inv := by
    change b = (b ≫ e₁.hom) ≫ e₁.inv
    rw [Category.assoc, e₁.hom_inv_id, Category.comp_id]
  haveI : IsIso b := by
    rw [hbq]
    infer_instance
  haveI : IsIso φ.τ₁ := inferInstanceAs (IsIso b)
  haveI : IsIso φ.τ₃ := inferInstanceAs (IsIso e₃.hom)
  haveI : IsIso a :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hT
  have hcomp := rightAlmostSplit_precomp_iso (asIso a) hTg
  change IsRightAlmostSplit (a ≫ T.g) at hcomp
  rw [ha] at hcomp
  have hback := hcomp.postcomp_iso e₃.symm
  change IsRightAlmostSplit ((S.g ≫ e₃.hom) ≫ e₃.inv) at hback
  simpa only [Category.assoc, e₃.hom_inv_id, Category.comp_id] using hback

end MagnitudeConjecture.CategoryTheory
