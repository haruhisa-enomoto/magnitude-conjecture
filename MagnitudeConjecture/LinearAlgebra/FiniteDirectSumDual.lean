import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duality for a direct sum with finite nontrivial support

The canonical map from the direct sum of the coefficient duals to the dual
of a direct sum is an isomorphism when only finitely many summands are
nontrivial.  The construction is independent of any chosen bases.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture

universe u v w

variable {k : Type u} [Field k]
variable {ι : Type v} (V : ι → Type w)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- A family of linear equivalences induces a linear equivalence of direct
sums without changing the index. -/
noncomputable def directSumLinearEquivCongrRight
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (e : ∀ i, V i ≃ₗ[k] W i) :
    DirectSum ι V ≃ₗ[k] DirectSum ι W where
  toLinearMap := DirectSum.lmap fun i ↦ (e i).toLinearMap
  invFun := DirectSum.lmap fun i ↦ (e i).symm.toLinearMap
  left_inv x := by
    apply DirectSum.ext
    intro i
    simp
  right_inv x := by
    apply DirectSum.ext
    intro i
    simp

/-- The canonical inclusion of one summand, with the classical decidable
equality choice hidden from the public interface. -/
noncomputable def directSumInclusion (i : ι) :
    V i →ₗ[k] DirectSum ι V := by
  classical
  exact DirectSum.lof k ι V i

@[simp]
theorem directSumInclusion_apply_self (i : ι) (x : V i) :
    directSumInclusion (k := k) V i x i = x := by
  classical
  unfold directSumInclusion
  exact DirectSum.lof_apply k i x

theorem directSumInclusion_apply_of_ne
    {i j : ι} (hij : i ≠ j) (x : V i) :
    directSumInclusion (k := k) V i x j = 0 := by
  classical
  unfold directSumInclusion
  rw [DirectSum.lof_eq_of]
  simp [DirectSum.of_apply, hij]

/-- Extend one coefficient functional by zero on all other summands. -/
def dualComponentExtension (i : ι) :
    Module.Dual k (V i) →ₗ[k] Module.Dual k (DirectSum ι V) where
  toFun phi := phi.comp (DirectSum.component k ι V i)
  map_add' phi psi := by
    ext x
    rfl
  map_smul' r phi := by
    ext x
    rfl

/-- Extend a finite-support family of coefficient functionals to a
functional on the direct sum. -/
def directSumDualToDual :
    DirectSum ι (fun i ↦ Module.Dual k (V i)) →ₗ[k]
      Module.Dual k (DirectSum ι V) := by
  classical
  exact DirectSum.toModule k ι _ (dualComponentExtension (k := k) V)

@[simp]
theorem directSumDualToDual_lof_apply
    (i : ι) (phi : Module.Dual k (V i)) (x : DirectSum ι V) :
    directSumDualToDual (k := k) V
        (directSumInclusion (k := k)
          (fun j ↦ Module.Dual k (V j)) i phi) x =
      phi (x i) := by
  classical
  have hmap : directSumDualToDual (k := k) V
      (directSumInclusion (k := k)
        (fun j ↦ Module.Dual k (V j)) i phi) =
        dualComponentExtension (k := k) V i phi := by
    unfold directSumDualToDual directSumInclusion
    exact DirectSum.toModule_lof (R := k)
      (M := fun j ↦ Module.Dual k (V j))
      (φ := dualComponentExtension (k := k) V) i phi
  exact LinearMap.congr_fun hmap x

@[simp]
theorem directSumDualToDual_apply_lof
    (Phi : DirectSum ι (fun i ↦ Module.Dual k (V i)))
    (i : ι) (x : V i) :
    directSumDualToDual (k := k) V Phi
      (directSumInclusion (k := k) V i x) = Phi i x := by
  classical
  induction Phi using DirectSum.induction_on with
  | zero => simp
  | of j phi =>
      by_cases hji : j = i
      · subst j
        simpa [directSumInclusion, DirectSum.lof_eq_of] using
          directSumDualToDual_lof_apply (k := k) V i phi
            (directSumInclusion (k := k) V i x)
      · simpa [directSumInclusion, DirectSum.lof_eq_of,
          DirectSum.of_apply, hji, Ne.symm hji] using
          directSumDualToDual_lof_apply (k := k) V j phi
            (directSumInclusion (k := k) V i x)
  | add Phi Psi hPhi hPsi =>
      simp [hPhi, hPsi]

/-- Restrict a functional to each nontrivial summand and assemble the
restrictions over the finite set of such summands. -/
def dualToDirectSumDual
    (h : {i : ι | Nontrivial (V i)}.Finite) :
    Module.Dual k (DirectSum ι V) →ₗ[k]
      DirectSum ι (fun i ↦ Module.Dual k (V i)) := by
  classical
  let S : Set ι := {i | Nontrivial (V i)}
  letI : Fintype S := h.fintype
  exact ∑ i : S,
    (directSumInclusion (k := k)
      (fun j ↦ Module.Dual k (V j)) i.1).comp
      (directSumInclusion (k := k) V i.1).dualMap

@[simp]
theorem dualToDirectSumDual_apply
    (h : {i : ι | Nontrivial (V i)}.Finite)
    (phi : Module.Dual k (DirectSum ι V)) (i : ι) :
    dualToDirectSumDual (k := k) V h phi i =
      (directSumInclusion (k := k) V i).dualMap phi := by
  classical
  by_cases hi : Nontrivial (V i)
  · let S : Set ι := {i | Nontrivial (V i)}
    letI : Fintype S := h.fintype
    let ii : S := ⟨i, hi⟩
    simp only [dualToDirectSumDual, LinearMap.sum_apply]
    rw [DirectSum.sum_apply]
    rw [Finset.sum_eq_single ii]
    · simp [ii]
    · intro c _ hcii
      have hci : c.1 ≠ i := by
        intro h
        apply hcii
        exact Subtype.ext h
      rw [LinearMap.comp_apply]
      unfold directSumInclusion
      rw [DirectSum.lof_eq_of]
      simp [DirectSum.of_apply, hci]
    · simp
  · letI : Subsingleton (V i) :=
      not_nontrivial_iff_subsingleton.mp hi
    exact Subsingleton.elim _ _

theorem directSumDualToDual_dualToDirectSumDual
    (h : {i : ι | Nontrivial (V i)}.Finite)
    (phi : Module.Dual k (DirectSum ι V)) :
    directSumDualToDual (k := k) V
      (dualToDirectSumDual (k := k) V h phi) = phi := by
  classical
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
      have hgen :
          directSumDualToDual (k := k) V
              (dualToDirectSumDual (k := k) V h phi)
              (directSumInclusion (k := k) V i x) =
            phi (directSumInclusion (k := k) V i x) := by
        rw [directSumDualToDual_apply_lof,
          dualToDirectSumDual_apply]
        rfl
      simpa [directSumInclusion, DirectSum.lof_eq_of] using hgen
  | add x y hx hy =>
      simp [hx, hy]

theorem directSumDualToDual_injective :
    Function.Injective (directSumDualToDual (k := k) V) := by
  classical
  intro Phi Psi hPhiPsi
  apply DirectSum.ext
  intro i
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun hPhiPsi
    (directSumInclusion (k := k) V i x)
  simpa using h

/-- The canonical, basis-free finite-duality isomorphism

`(⨁ i, Vᵢ*) ≃ (⨁ i, Vᵢ)*`.
-/
noncomputable def directSumDualEquivDual
    (h : {i : ι | Nontrivial (V i)}.Finite) :
    DirectSum ι (fun i ↦ Module.Dual k (V i)) ≃ₗ[k]
      Module.Dual k (DirectSum ι V) :=
  LinearEquiv.ofBijective (directSumDualToDual (k := k) V)
    ⟨directSumDualToDual_injective (k := k) V,
      fun phi ↦ ⟨dualToDirectSumDual (k := k) V h phi,
        directSumDualToDual_dualToDirectSumDual (k := k) V h phi⟩⟩

/-- Variant whose finiteness hypothesis is stated on the coefficient duals.
Over a field a vector space is nontrivial exactly when its dual is. -/
noncomputable def directSumDualEquivDualOfFiniteDual
    (h : {i : ι | Nontrivial (Module.Dual k (V i))}.Finite) :
    DirectSum ι (fun i ↦ Module.Dual k (V i)) ≃ₗ[k]
      Module.Dual k (DirectSum ι V) :=
  directSumDualEquivDual (k := k) V (by
    simpa only [Module.nontrivial_dual_iff k] using h)

@[simp]
theorem directSumDualEquivDual_apply
    (h : {i : ι | Nontrivial (V i)}.Finite)
    (Phi : DirectSum ι (fun i ↦ Module.Dual k (V i))) :
    directSumDualEquivDual (k := k) V h Phi =
      directSumDualToDual (k := k) V Phi :=
  rfl

end MagnitudeConjecture
