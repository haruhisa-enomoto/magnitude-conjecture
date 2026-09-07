import Mathlib.Algebra.DirectSum.Module

/-!
# Generator formulas for direct-sum Fubini equivalences

Small reusable lemmas for the three direct-sum operations used in orbit
Fubini arguments: mapping each fiber, uncurrying a dependent pair of indices,
and reindexing along an equivalence.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.DirectSumFubini

universe uR uI uM uT

noncomputable def mapRangeLinearEquiv
    {R : Type uR} [Semiring R] {iota : Type uI}
    {beta : iota → Type uM} {gamma : iota → Type uT}
    [∀ i, AddCommMonoid (beta i)] [∀ i, Module R (beta i)]
    [∀ i, AddCommMonoid (gamma i)] [∀ i, Module R (gamma i)]
    (e : ∀ i, beta i ≃ₗ[R] gamma i) :
    DirectSum iota beta ≃ₗ[R] DirectSum iota gamma :=
  DFinsupp.mapRange.linearEquiv e

@[simp]
theorem mapRangeLinearEquiv_of
    {R : Type uR} [Semiring R] {iota : Type uI}
    {beta : iota → Type uM} {gamma : iota → Type uT}
    [DecidableEq iota]
    [∀ i, AddCommMonoid (beta i)] [∀ i, Module R (beta i)]
    [∀ i, AddCommMonoid (gamma i)] [∀ i, Module R (gamma i)]
    (e : ∀ i, beta i ≃ₗ[R] gamma i) (i : iota) (x : beta i) :
    mapRangeLinearEquiv e (DirectSum.of beta i x) =
      DirectSum.of gamma i (e i x) := by
  apply DFinsupp.ext
  intro j
  by_cases h : i = j
  · subst j
    change (e i) ((DFinsupp.single i x) i) =
      (DFinsupp.single i (e i x)) i
    simp
  · change (e j) ((DFinsupp.single i x) j) =
      (DFinsupp.single i (e i x)) j
    rw [DFinsupp.single_eq_of_ne (Ne.symm h),
      DFinsupp.single_eq_of_ne (Ne.symm h)]
    exact (e j).map_zero

@[simp]
theorem sigmaLcurryEquiv_symm_of_of
    {R : Type uR} [Semiring R] {iota : Type uI}
    {alpha : iota → Type uM} {T : (i : iota) → alpha i → Type uT}
    [DecidableEq iota] [∀ i, DecidableEq (alpha i)]
    [∀ i j, AddCommMonoid (T i j)] [∀ i j, Module R (T i j)]
    (i : iota) (j : alpha i) (x : T i j) :
    (DirectSum.sigmaLcurryEquiv R).symm
        (DirectSum.of (fun i ↦ DirectSum (alpha i) (T i)) i
          (DirectSum.of (T i) j x)) =
      DirectSum.of (fun p : Σ i, alpha i ↦ T p.1 p.2)
        (⟨i, j⟩ : Σ i, alpha i) x := by
  change DFinsupp.sigmaUncurry
      (DFinsupp.single i (DFinsupp.single j x)) =
    DFinsupp.single ⟨i, j⟩ x
  exact DFinsupp.sigmaUncurry_single i j x

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem reindexCastLinearEquiv_of
    {R : Type uR} [Semiring R] {iota : Type uI} {kappa : Type uM}
    [DecidableEq iota] [DecidableEq kappa] (e : iota ≃ kappa)
    {T : kappa → Type uT}
    [∀ i, AddCommMonoid (T i)] [∀ i, Module R (T i)]
    (i : iota) (x : T (e i)) :
    (mapRangeLinearEquiv fun j ↦
        LinearEquiv.cast (R := R) (e.apply_symm_apply j))
        ((DirectSum.lequivCongrLeft R e)
          (DirectSum.of (fun i ↦ T (e i)) i x)) =
      DirectSum.of T (e i) x := by
  change (mapRangeLinearEquiv fun j ↦
      LinearEquiv.cast (R := R) (e.apply_symm_apply j))
      ((DirectSum.lequivCongrLeft R e)
        (DirectSum.lof R iota (fun i ↦ T (e i)) i x)) =
    DirectSum.lof R kappa T (e i) x
  let h : i = e.symm (e i) := (e.symm_apply_apply i).symm
  let y : T (e (e.symm (e i))) :=
    cast (congrArg (fun j ↦ T (e j)) h) x
  have hri := DirectSum.lequivCongrLeft_lof
    (M := fun i ↦ T (e i)) (e := e) (i := i) (k := e i)
    R h x y rfl
  rw [hri, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
    mapRangeLinearEquiv_of]
  congr 1
  apply eq_of_heq
  exact (cast_heq _ y).trans (by
    dsimp only [y]
    exact cast_heq _ x)

end MagnitudeConjecture.DirectSumFubini
