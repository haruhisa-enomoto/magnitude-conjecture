import MagnitudeConjecture.CategoryTheory.IrreducibleAbelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Factorization across an irreducible kernel

If an epimorphism has irreducible kernel, a morphism into its target which
does not lift through the epimorphism must instead contain that epimorphism.
This is the pullback argument used in Auslander--Reiten IV, Proposition 2.7.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `g` be the kernel of an epimorphism `q`. If `g` is irreducible, then
every morphism into the target of `q` which does not lift through `q` admits
`q` as a factor. -/
theorem exists_factor_thru_of_not_exists_lift_of_irreducible_kernel
    {A B D X : C} (g : A ⟶ B) [Mono g] (q : B ⟶ D) [Epi q]
    (hzero : g ≫ q = 0)
    (hgKernel : IsLimit (KernelFork.ofι g hzero))
    (hg : IsIrreducibleMorphism g) (h : X ⟶ D)
    (hnot : ¬ ∃ l : X ⟶ B, l ≫ q = h) :
    ∃ r : B ⟶ X, r ≫ h = q := by
  let a : A ⟶ pullback q h := pullback.lift g 0 (by rw [hzero, zero_comp])
  let e : pullback q h ⟶ X := pullback.snd q h
  let b : pullback q h ⟶ B := pullback.fst q h
  have hae : a ≫ e = 0 := by
    exact pullback.lift_snd _ _ _
  have hab : a ≫ b = g := by
    exact pullback.lift_fst _ _ _
  letI : Mono a := by
    constructor
    intro W x y hxy
    apply (cancel_mono g).1
    calc
      x ≫ g = (x ≫ a) ≫ b := by rw [← hab, ← Category.assoc]
      _ = (y ≫ a) ≫ b := by rw [hxy]
      _ = y ≫ (a ≫ b) := Category.assoc _ _ _
      _ = y ≫ g := by rw [hab]
  have haKernel : IsLimit (KernelFork.ofι a hae) := by
    apply KernelFork.IsLimit.ofι' a hae
    intro W k hk
    have hkbq : (k ≫ b) ≫ q = 0 := by
      calc
        (k ≫ b) ≫ q = k ≫ (b ≫ q) := Category.assoc _ _ _
        _ = k ≫ (e ≫ h) := by rw [← pullback.condition]
        _ = (k ≫ e) ≫ h := (Category.assoc _ _ _).symm
        _ = 0 := by rw [hk, zero_comp]
    let u : W ⟶ A := hgKernel.lift
      (KernelFork.ofι (k ≫ b) hkbq)
    have hug : u ≫ g = k ≫ b :=
      hgKernel.fac (KernelFork.ofι (k ≫ b) hkbq) WalkingParallelPair.zero
    refine ⟨u, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hab, hug]
    · rw [Category.assoc, hae, comp_zero]
      exact hk.symm
  rcases hg.factorization a b hab with ha | hb
  · letI : IsSplitMono a := ha
    let S := ShortComplex.mk a e hae
    have hExact : S.Exact := S.exact_of_f_is_kernel haKernel
    let splitting := ShortComplex.Splitting.ofExactOfRetraction S hExact
      (retraction a) (IsSplitMono.id a) inferInstance
    apply False.elim
    apply hnot
    refine ⟨splitting.s ≫ b, ?_⟩
    calc
      (splitting.s ≫ b) ≫ q = splitting.s ≫ (b ≫ q) := Category.assoc _ _ _
      _ = splitting.s ≫ (e ≫ h) := by rw [← pullback.condition]
      _ = (splitting.s ≫ e) ≫ h := (Category.assoc _ _ _).symm
      _ = h := by rw [splitting.s_g, Category.id_comp]
  · letI : IsSplitEpi b := hb
    refine ⟨section_ b ≫ e, ?_⟩
    calc
      (section_ b ≫ e) ≫ h = section_ b ≫ (e ≫ h) := Category.assoc _ _ _
      _ = section_ b ≫ (b ≫ q) := by rw [← pullback.condition]
      _ = (section_ b ≫ b) ≫ q := (Category.assoc _ _ _).symm
      _ = q := by rw [IsSplitEpi.id, Category.id_comp]

end MagnitudeConjecture.CategoryTheory
