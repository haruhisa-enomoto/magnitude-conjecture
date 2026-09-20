import MagnitudeConjecture.CategoryTheory.AlmostSplitComparison
import MagnitudeConjecture.CategoryTheory.ExtOneRealization

/-! # Hom vanishing into an almost-split kernel kills extensions -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A short exact sequence splits if its kernel has no maps to the kernel
of a right almost-split sequence with the same endpoint. -/
theorem splitEpi_of_hom_to_almostSplit_kernel_zero
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (hTg : IsRightAlmostSplit T.g) (e : S.X₃ ≅ T.X₃)
    (hHom : ∀ f : S.X₁ ⟶ T.X₁, f = 0) : IsSplitEpi S.g := by
  classical
  by_contra hn
  have hn' : ¬ IsSplitEpi (S.g ≫ e.hom) := by
    intro h
    letI := h
    apply hn
    rw [show S.g = (S.g ≫ e.hom) ≫ e.inv by simp]
    infer_instance
  obtain ⟨a, ha⟩ := hTg.factors (S.g ≫ e.hom) hn'
  haveI := hT.mono_f
  obtain ⟨b, hb⟩ := hT.exact.lift' (S.f ≫ a) (by
    rw [Category.assoc, ha, ← Category.assoc, S.zero, zero_comp])
  have hz : S.f ≫ a = 0 := by rw [← hb, hHom b, zero_comp]
  haveI := hS.epi_g
  obtain ⟨d, hd⟩ := hS.exact.desc' a hz
  have hdg : d ≫ T.g = e.hom := by
    apply (cancel_epi S.g).1
    rw [← Category.assoc, hd, ha]
  apply hTg.not_isSplitEpi
  exact IsSplitEpi.mk' ⟨e.inv ≫ d, by simp [Category.assoc, hdg]⟩

/-- The Hom-vanishing consequence of AR duality follows directly from the
factorization property and realization of degree-one extensions. -/
theorem extOne_eq_zero_of_hom_to_almostSplit_kernel_zero
    [HasExt.{w} C] [EnoughProjectives C]
    {T : ShortComplex C} (hT : T.ShortExact)
    (hTg : IsRightAlmostSplit T.g) (K : C)
    (hHom : ∀ f : K ⟶ T.X₁, f = 0) (xi : Ext.{w} T.X₃ K 1) : xi = 0 := by
  obtain ⟨E, i, q, hz, hs, he⟩ :=
    MagnitudeConjecture.ExtOneRealization.exists_shortExact_with_extClass_eq T.X₃ K xi
  letI : IsSplitEpi q := splitEpi_of_hom_to_almostSplit_kernel_zero
    hs hT hTg (Iso.refl _) hHom
  rw [← he]
  have hzero := hs.comp_extClass
  have h := congrArg
    (fun eta : Ext.{w} E K 1 ↦
      (Ext.mk₀ (section_ q)).comp eta (zero_add 1)) hzero
  simpa [Ext.mk₀_comp_mk₀_assoc] using h

/-- Ext vanishing lifts every map through the epimorphism of a short exact
sequence. -/
theorem hom_lift_of_extOne_eq_zero [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Q : C)
    (hExt : ∀ xi : Ext.{w} Q S.X₁ 1, xi = 0) (f : Q ⟶ S.X₃) :
    ∃ g : Q ⟶ S.X₂, g ≫ S.g = f := by
  obtain ⟨g, hg⟩ := Ext.covariant_sequence_exact₃ Q hS (Ext.mk₀ f)
    (rfl : 0 + 1 = 1) (hExt _)
  refine ⟨Ext.addEquiv₀ g, ?_⟩
  apply (Ext.mk₀_bijective Q S.X₃).1
  rw [← Ext.mk₀_comp_mk₀]
  simpa using hg

end MagnitudeConjecture.CategoryTheory
