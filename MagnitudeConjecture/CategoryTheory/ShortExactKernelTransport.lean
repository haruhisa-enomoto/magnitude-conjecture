import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Transporting the kernel of a short exact complex
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If a short exact complex's second map is transported across an isomorphism
of its target, its source remains a kernel of the transported map. -/
def sourceIsoKernelOfShortExactCompIso
    (S : _root_.CategoryTheory.ShortComplex C) (hS : S.ShortExact)
    {Y : C} (g : S.X₂ ⟶ Y) (e : S.X₃ ≅ Y)
    (h : S.g ≫ e.hom = g) :
    S.X₁ ≅ kernel g := by
  letI : Mono S.f := hS.mono_f
  have hback : g ≫ e.inv = S.g := by
    calc
      g ≫ e.inv = (S.g ≫ e.hom) ≫ e.inv := by rw [h]
      _ = S.g := by simp
  have hzero : S.f ≫ g = 0 := by
    rw [← h, ← Category.assoc, S.zero, zero_comp]
  let hKernel : IsLimit (KernelFork.ofι S.f hzero) :=
    IsKernel.ofCompIso S.g g e.symm hback hS.exact.fIsKernel
  exact (IsLimit.conePointUniqueUpToIso (kernelIsKernel g) hKernel).symm

end CategoryTheory.ShortComplex
