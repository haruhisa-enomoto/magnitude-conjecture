import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Kernels in a split-epic map of cokernel rows

This is the elementary abelian-category calculation behind the pullback
diagram in Auslander--Reiten Proposition 2.4.  If a map of cokernel rows has
a split-epic middle component and a monic left composite, then the kernel of
the induced endpoint map is the image of the kernel of the middle component.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A commutative square whose top map is split epic is a pullback when the
restriction of its left map to the top kernel is a kernel of the bottom map. -/
theorem isPullback_of_splitEpi_of_kernel_restriction
    {E P D Q : C} (t : E ⟶ P) (b : E ⟶ D) (q : P ⟶ Q) (h : D ⟶ Q)
    [IsSplitEpi t] (hsq : b ≫ h = t ≫ q)
    (hk : IsLimit (KernelFork.ofι (kernel.ι t ≫ b) (by
      rw [Category.assoc, hsq, ← Category.assoc, kernel.condition,
        zero_comp]))) :
    IsPullback t b q h := by
  let k : kernel t ⟶ E := kernel.ι t
  let s : P ⟶ E := section_ t
  let d : (c : PullbackCone h q) → (c.pt ⟶ D) := fun c =>
    c.fst - c.snd ≫ s ≫ b
  have hd : ∀ (c : PullbackCone h q), d c ≫ h = 0 := by
    intro c
    dsimp only [d, s]
    rw [Preadditive.sub_comp, c.condition]
    simp only [Category.assoc, hsq, IsSplitEpi.id_assoc, sub_self]
  let z : (c : PullbackCone h q) → (c.pt ⟶ kernel t) := fun c =>
    hk.lift (KernelFork.ofι (d c) (hd c))
  have hz : ∀ (c : PullbackCone h q), (z c ≫ k) ≫ b = d c := by
    intro c
    dsimp only [k]
    rw [Category.assoc]
    dsimp only [z]
    exact hk.fac (KernelFork.ofι (d c) (hd c)) WalkingParallelPair.zero
  let lift : (c : PullbackCone h q) → (c.pt ⟶ E) := fun c =>
    c.snd ≫ s + z c ≫ k
  have lift_t : ∀ (c : PullbackCone h q), lift c ≫ t = c.snd := by
    intro c
    dsimp only [lift, s, k]
    rw [Preadditive.add_comp, Category.assoc, IsSplitEpi.id,
      Category.comp_id, Category.assoc, kernel.condition, comp_zero, add_zero]
  have lift_b : ∀ (c : PullbackCone h q), lift c ≫ b = c.fst := by
    intro c
    dsimp only [lift]
    rw [Preadditive.add_comp, Category.assoc, hz]
    dsimp only [d]
    abel
  refine (IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk hsq lift lift_b lift_t ?_)).flip
  intro c m hm_b hm_t
  have hmt : (m - lift c) ≫ t = 0 := by
    rw [Preadditive.sub_comp, hm_t, lift_t, sub_self]
  have hmb : (m - lift c) ≫ b = 0 := by
    rw [Preadditive.sub_comp, hm_b, lift_b, sub_self]
  let ell : c.pt ⟶ kernel t := kernel.lift t (m - lift c) hmt
  have hell : ell ≫ k = m - lift c := kernel.lift_ι t _ hmt
  haveI : Mono (k ≫ b) := mono_of_isLimit_fork hk
  have hellzero : ell = 0 := by
    apply (cancel_mono (k ≫ b)).1
    rw [← Category.assoc, hell, hmb, zero_comp]
  apply sub_eq_zero.mp
  rw [← hell, hellzero, zero_comp]

/-- In a commutative map of cokernel rows with split-epic middle map, the
kernel of the endpoint map is obtained by restricting the upper cokernel map
to the kernel of the middle map. -/
noncomputable def kernelLimit_of_splitEpi_cokernel_rows
    {U E P D Q : C} (a : U ⟶ E) (t : E ⟶ P) (b : E ⟶ D)
    (q : P ⟶ Q) (h : D ⟶ Q)
    [IsSplitEpi t] [Epi b] [Epi q] [Mono (a ≫ t)]
    (hab : a ≫ b = 0)
    (ha : IsLimit (KernelFork.ofι a hab))
    (hq : ∀ {W : C} (r : P ⟶ W), (a ≫ t) ≫ r = 0 →
      { c : Q ⟶ W // q ≫ c = r })
    (hsq : b ≫ h = t ≫ q) :
    IsLimit (KernelFork.ofι (kernel.ι t ≫ b) (by
      rw [Category.assoc, hsq, ← Category.assoc, kernel.condition,
        zero_comp])) := by
  let k : kernel t ⟶ E := kernel.ι t
  have hkbzero : (k ≫ b) ≫ h = 0 := by
    rw [Category.assoc, hsq, ← Category.assoc, kernel.condition, zero_comp]
  haveI : Mono (k ≫ b) := by
    apply Preadditive.mono_of_cancel_zero
    intro W z hz
    let r : W ⟶ U := ha.lift (KernelFork.ofι (z ≫ k) (by
      rw [Category.assoc]
      exact hz))
    have hra : r ≫ a = z ≫ k :=
      ha.fac _ WalkingParallelPair.zero
    have hrzero : r = 0 := by
      apply (cancel_mono (a ≫ t)).1
      rw [← Category.assoc, hra, Category.assoc, kernel.condition, zero_comp,
        comp_zero]
    apply (cancel_mono k).1
    rw [← hra, hrzero, zero_comp, zero_comp]
  haveI : Epi h := epi_of_epi_fac hsq
  have hcokernel : IsColimit (CokernelCofork.ofπ h hkbzero) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro W r hr
    let m : E ⟶ W := b ≫ r
    have hkmzero : k ≫ m = 0 := by
      dsimp only [m]
      rw [← Category.assoc]
      exact hr
    let s : P ⟶ E := section_ t
    let e : E ⟶ E := 𝟙 E - t ≫ s
    have hetzero : e ≫ t = 0 := by
      dsimp only [e, s]
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        IsSplitEpi.id, Category.comp_id, sub_self]
    let ell : E ⟶ kernel t := kernel.lift t e hetzero
    have hel : ell ≫ k = e := kernel.lift_ι t e hetzero
    have htm : t ≫ (s ≫ m) = m := by
      have hem : e ≫ m = 0 := by
        rw [← hel, Category.assoc, hkmzero, comp_zero]
      dsimp only [e] at hem
      rw [Preadditive.sub_comp, Category.id_comp] at hem
      simpa only [Category.assoc] using (sub_eq_zero.mp hem).symm
    let j : P ⟶ W := s ≫ m
    have hgt : (a ≫ t) ≫ j = 0 := by
      rw [Category.assoc, htm]
      dsimp only [m]
      rw [← Category.assoc, hab, zero_comp]
    obtain ⟨c, hc⟩ := hq j hgt
    refine ⟨c, ?_⟩
    apply (cancel_epi b).1
    change q ≫ c = j at hc
    calc
      b ≫ h ≫ c = (b ≫ h) ≫ c := (Category.assoc _ _ _).symm
      _ = (t ≫ q) ≫ c := by rw [hsq]
      _ = t ≫ (q ≫ c) := Category.assoc _ _ _
      _ = t ≫ j := by rw [hc]
      _ = m := htm
      _ = b ≫ r := rfl
  let T := ShortComplex.mk (k ≫ b) h hkbzero
  have hTexact : T.Exact := T.exact_of_g_is_cokernel hcokernel
  simpa only [k] using hTexact.fIsKernel

end MagnitudeConjecture.CategoryTheory
