import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The coefficient-dual annihilator lemma

Only the annihilator calculation required by the stable Hom--Ext argument is
retained here.  For an injective coefficient module, the image of dual
precomposition by `t` consists precisely of the functionals vanishing on
`ker t`.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.CoefficientDual

universe uk uM uN uE

variable {k : Type uk} {M : Type uM} {E : Type uE} [CommRing k]
  [AddCommGroup M] [Module k M]
  [AddCommGroup E] [Module k E]

/-- The submodule of coefficient-valued functionals vanishing on `N`. -/
def annihilator (N : Submodule k M) : Submodule k (M →ₗ[k] E) :=
  LinearMap.ker (LinearMap.lcomp k E N.subtype)

@[simp]
theorem mem_annihilator_iff (N : Submodule k M) (phi : M →ₗ[k] E) :
    phi ∈ annihilator (E := E) N ↔ ∀ n ∈ N, phi n = 0 := by
  rw [annihilator, LinearMap.mem_ker]
  change phi.comp N.subtype = 0 ↔ _
  constructor
  · intro h n hn
    exact LinearMap.congr_fun h ⟨n, hn⟩
  · intro h
    ext n
    exact h n.1 n.2

/-- Dual precomposition by `t` has image the annihilator of `ker t`. -/
theorem range_lcomp_eq_annihilator_ker
    {N : Type uN} [AddCommGroup N] [Module k N]
    [Small.{uE} k] [Module.Injective k E]
    (t : M →ₗ[k] N) :
    LinearMap.range (LinearMap.lcomp k E t) =
      annihilator (E := E) (LinearMap.ker t) := by
  apply le_antisymm
  · rintro phi ⟨psi, rfl⟩
    rw [mem_annihilator_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    simp [LinearMap.lcomp_apply, hm]
  · intro phi hphi
    have hker : LinearMap.ker t ≤ LinearMap.ker phi := by
      intro m hm
      rw [LinearMap.mem_ker]
      exact (mem_annihilator_iff (LinearMap.ker t) phi).mp hphi m hm
    let psi : LinearMap.range t →ₗ[k] E :=
      (LinearMap.ker t).liftQ phi hker ∘ₗ
        t.quotKerEquivRange.symm.toLinearMap
    obtain ⟨extension, hextension⟩ :=
      Module.Injective.extension_property k E (LinearMap.range t) N
        (LinearMap.range t).subtype Subtype.val_injective psi
    refine ⟨extension, ?_⟩
    ext m
    change extension (t m) = phi m
    have hvalue := LinearMap.congr_fun hextension
      ⟨t m, LinearMap.mem_range_self t m⟩
    calc
      extension (t m) = psi ⟨t m, LinearMap.mem_range_self t m⟩ := by
        simpa using hvalue
      _ = phi m := by
        simp [psi, LinearMap.quotKerEquivRange_symm_apply_image,
          Submodule.liftQ_apply]

end MagnitudeConjecture.CoefficientDual
