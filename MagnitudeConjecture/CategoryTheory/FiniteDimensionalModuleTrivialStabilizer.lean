import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Trivial stabilizers of finite-support modules

A nonzero finite-support module cannot be isomorphic to a nontrivial deck
translate when the deck group is torsion-free and acts freely on objects.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [IsMulTorsionFree G]
variable [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- A nonzero finite-dimensional module has a supported object. -/
theorem finiteDimensionalModule_moduleSupport_nonempty
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (hM : ¬ IsZero M) : (moduleSupport k M.obj.obj).Nonempty := by
  by_contra hs
  apply hM
  have hfun : IsZero M.obj.obj := by
    apply Functor.isZero
    intro X
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply not_nontrivial_iff_subsingleton.mp
    intro hX
    exact hs ⟨X, hX⟩
  have hlinear : IsZero M.obj :=
    IsZero.of_full_of_faithful_of_isZero
      (IsLinearModule (C := C) k).ι M.obj hfun
  exact IsZero.of_full_of_faithful_of_isZero
    (IsFiniteDimensionalModule (C := C) k).ι M hlinear

/-- A nonzero finite-support module has trivial translation stabilizer when
the deck group is torsion-free and acts freely on objects. -/
theorem finiteDimensionalModule_trivialStabilizer
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (hM : ¬ IsZero M) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0 := by
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro a ha
  let g : G := a.toMul
  let e := (IsLinearModule (C := C) k).ι.mapIso
    ((IsFiniteDimensionalModule (C := C) k).ι.mapIso (Classical.choice ha))
  have hsupportIso :
      moduleSupport k M.obj.obj =
        moduleSupport k
          ((IsFiniteDimensionalModule (C := C) k).ι.obj (M⟦a⟧)).obj := by
    ext X
    exact (e.app X).toLinearEquiv.toEquiv.nontrivial_congr
  have hsupport :
      moduleSupport k M.obj.obj =
        (g • ·) ⁻¹' moduleSupport k M.obj.obj := by
    exact hsupportIso.trans (by
      simpa only [show a = Additive.ofMul g by rfl] using
        D.finiteDimensionalModuleSupport_shift_eq_preimage (k := k) M g)
  obtain ⟨X, hX⟩ := finiteDimensionalModule_moduleSupport_nonempty
    (k := k) M hM
  have hclosed : ∀ Y : C, Y ∈ moduleSupport k M.obj.obj →
      g • Y ∈ moduleSupport k M.obj.obj := by
    intro Y hY
    change Y ∈ (g • ·) ⁻¹' moduleSupport k M.obj.obj
    rw [← hsupport]
    exact hY
  have hpowers : ∀ n : ℕ,
      g ^ n • X ∈ moduleSupport k M.obj.obj := by
    intro n
    induction n with
    | zero => simpa using hX
    | succ n ih => simpa [pow_succ', smul_smul] using hclosed (g ^ n • X) ih
  have hg : g = 1 := by
    by_contra hg
    have hpowerInjective : Function.Injective (fun n : ℕ ↦ g ^ n) :=
      IsMulTorsionFree.pow_right_injective hg
    have horbitInjective : Function.Injective (fun n : ℕ ↦ g ^ n • X) := by
      intro n m hnm
      exact hpowerInjective (IsCancelSMul.right_cancel (g ^ n) (g ^ m) X hnm)
    exact (finite_moduleSupport k M).not_infinite
      (Set.infinite_of_injective_forall_mem horbitInjective hpowers)
  change Additive.ofMul g = 0
  rw [hg]
  rfl

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
