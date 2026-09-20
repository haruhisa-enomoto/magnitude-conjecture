import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Isomorphic kernels force proportional maps under an extension hypothesis -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.FiniteKernel
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C] [Abelian C] [Linear k C]

/-- A map annihilating the kernel of f factors through f when its target is
injective. The coimage realizes the required intermediate quotient. -/
theorem exists_end_factor_of_kernel_comp_zero {Z I : C} [Injective I]
    (f g : Z ⟶ I) (hg : kernel.ι f ≫ g = 0) :
    ∃ a : I ⟶ I, f ≫ a = g := by
  let d := cokernel.desc (kernel.ι f) g hg
  obtain ⟨a, ha⟩ := Injective.factors d (Abelian.factorThruCoimage f)
  refine ⟨a, ?_⟩
  rw [← Abelian.coimage.fac f, Category.assoc, ha]
  exact cokernel.π_desc _ _ _

/-- Scalar endomorphisms of an injective target turn kernel containment into
proportionality of the maps. -/
theorem exists_scalar_of_kernel_comp_zero {Z I : C} [Injective I]
    (hI : ∀ a : I ⟶ I, ∃ c : k, a = c • 𝟙 I)
    (f g : Z ⟶ I) (hg : kernel.ι f ≫ g = 0) :
    ∃ c : k, c • f = g := by
  obtain ⟨a, ha⟩ := exists_end_factor_of_kernel_comp_zero f g hg
  obtain ⟨c, rfl⟩ := hI a
  exact ⟨c, by simpa using ha⟩

/-- If maps from ker f to Z extend over Z, scalar endomorphisms of Z and of
an injective target imply that isomorphic kernels give proportional maps. -/
theorem exists_scalar_of_kernel_iso {Z I : C} [Injective I]
    (hZ : ∀ a : Z ⟶ Z, ∃ c : k, a = c • 𝟙 Z)
    (hI : ∀ a : I ⟶ I, ∃ c : k, a = c • 𝟙 I)
    (f g : Z ⟶ I) (e : kernel f ≅ kernel g)
    (hext : ∀ h : kernel f ⟶ Z, ∃ a : Z ⟶ Z, kernel.ι f ≫ a = h) :
    ∃ c : k, c • f = g := by
  apply exists_scalar_of_kernel_comp_zero hI f g
  by_cases hz : IsZero (kernel f)
  · rw [hz.eq_zero_of_src (kernel.ι f), zero_comp]
  · obtain ⟨a, ha⟩ := hext (e.hom ≫ kernel.ι g)
    obtain ⟨c, rfl⟩ := hZ a
    have hc : c ≠ 0 := by
      intro hc
      subst c
      have hzero : e.hom ≫ kernel.ι g = 0 := by simpa using ha.symm
      exact hz (IsZero.of_mono_eq_zero _ hzero)
    have h := congrArg (fun h : kernel f ⟶ Z ↦ h ≫ g) ha
    have hsmul : c • (kernel.ι f ≫ g) = 0 := by simpa [Category.assoc] using h
    have hcancel := congrArg (fun x : kernel f ⟶ I ↦ c⁻¹ • x) hsmul
    simpa [smul_smul, inv_mul_cancel₀ hc] using hcancel

end MagnitudeConjecture.FiniteKernel
