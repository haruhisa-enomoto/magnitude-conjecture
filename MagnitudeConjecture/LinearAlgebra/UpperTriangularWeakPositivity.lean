import MagnitudeConjecture.LinearAlgebra.CartanCoordinateEstimate
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Weak positivity makes an upper-triangular Cartan matrix thin

For a nonnegative upper-unitriangular integral Cartan matrix, weak positivity
of the inverse-Cartan quadratic form forces every matrix entry to be at most
one.  The proof truncates a projective column at a chosen row and subtracts
the corresponding unit vector.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace MagnitudeConjecture.CartanCoordinate

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

namespace WeaklyPositiveCartanData

/-- The tail of a Cartan column beginning at a chosen index. -/
def columnTail (C : Matrix ι ι ℤ) (i j : ι) : ι → ℤ :=
  fun t ↦ if i ≤ t then C t j else 0

theorem inverse_blockTriangular
    (D : WeaklyPositiveCartanData (ι := ι))
    (hC : D.C.BlockTriangular id) :
    D.Cinv.BlockTriangular id := by
  letI : Invertible D.C :=
    invertibleOfRightInverse D.C D.Cinv D.mul_inverse
  have hinv : D.C⁻¹ = D.Cinv := Matrix.inv_eq_right_inv D.mul_inverse
  rw [← hinv]
  exact blockTriangular_inv_of_blockTriangular hC

theorem inverse_diagonal_eq_one
    (D : WeaklyPositiveCartanData (ι := ι))
    (hC : D.C.BlockTriangular id) (i : ι) :
    D.Cinv i i = 1 := by
  have hCinv := D.inverse_blockTriangular hC
  have hentry := congrArg (fun M : Matrix ι ι ℤ ↦ M i i) D.inverse_mul
  simp only [Matrix.mul_apply, Matrix.one_apply, if_pos] at hentry
  rw [Finset.sum_eq_single i] at hentry
  · simpa [D.diagonal i] using hentry
  · intro t _ht hti
    rcases lt_or_gt_of_ne hti with hti' | hit'
    · rw [hCinv hti', zero_mul]
    · rw [hC hit', mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem inverse_mulVec_columnTail
    (D : WeaklyPositiveCartanData (ι := ι))
    (hC : D.C.BlockTriangular id)
    {i j t : ι} (hit : i ≤ t) :
    D.Cinv.mulVec (columnTail D.C i j) t =
      (Pi.single j (1 : ℤ) : ι → ℤ) t := by
  have hCinv := D.inverse_blockTriangular hC
  have hentry := congrArg (fun M : Matrix ι ι ℤ ↦ M t j) D.inverse_mul
  simp only [Matrix.mul_apply, Matrix.one_apply] at hentry
  unfold Matrix.mulVec dotProduct
  calc
    ∑ s, D.Cinv t s * columnTail D.C i j s =
        ∑ s, D.Cinv t s * D.C s j := by
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases his : i ≤ s
      · simp [columnTail, his]
      · have hst : s < t := (lt_of_not_ge his).trans_le hit
        rw [hCinv hst, zero_mul]
        simp
    _ = (1 : Matrix ι ι ℤ) t j := hentry
    _ = (Pi.single j (1 : ℤ) : ι → ℤ) t := by
      by_cases htj : t = j <;> simp [Matrix.one_apply, htj]

theorem quadraticForm_columnTail
    (D : WeaklyPositiveCartanData (ι := ι))
    (hC : D.C.BlockTriangular id)
    {i j : ι} (hij : i ≤ j) :
    quadraticForm D.Cinv (columnTail D.C i j) = 1 := by
  unfold quadraticForm dotProduct
  calc
    ∑ t, columnTail D.C i j t *
        D.Cinv.mulVec (columnTail D.C i j) t =
      ∑ t, columnTail D.C i j t *
        (Pi.single j (1 : ℤ) : ι → ℤ) t := by
        apply Finset.sum_congr rfl
        intro t _ht
        by_cases hit : i ≤ t
        · rw [D.inverse_mulVec_columnTail hC hit]
        · simp [columnTail, hit]
    _ = columnTail D.C i j j * 1 := by
      simpa only [dotProduct] using
        (dotProduct_single (columnTail D.C i j) (1 : ℤ) j)
    _ = 1 := by simp [columnTail, hij, D.diagonal j]

theorem columnTail_dot_inverse_unit
    (D : WeaklyPositiveCartanData (ι := ι))
    (hC : D.C.BlockTriangular id) (i j : ι) :
    columnTail D.C i j ⬝ᵥ D.Cinv.mulVec (Pi.single i 1) =
      D.C i j := by
  have hCinv := D.inverse_blockTriangular hC
  have hdiag := D.inverse_diagonal_eq_one hC i
  have hmul : D.Cinv.mulVec (Pi.single i (1 : ℤ)) = D.Cinv.col i := by
    simp [Matrix.mulVec_single]
  rw [hmul]
  unfold dotProduct
  rw [Finset.sum_eq_single i]
  · simp [columnTail, hdiag]
  · intro t _ht hti
    rcases lt_or_gt_of_ne hti with hti' | hit'
    · simp [columnTail, not_le.mpr hti']
    · change columnTail D.C i j t * D.Cinv t i = 0
      rw [hCinv hit', mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Every entry of a nonnegative upper-unitriangular weakly positive Cartan
matrix is zero or one. -/
theorem entry_le_one_of_blockTriangular
    (D : WeaklyPositiveCartanData (ι := ι))
    (hC : D.C.BlockTriangular id) (i j : ι) :
    D.C i j ≤ 1 := by
  rcases lt_trichotomy i j with hij | hij | hij
  · by_contra hnot
    have hijle : i ≤ j := hij.le
    let u := columnTail D.C i j
    let e : ι → ℤ := Pi.single i 1
    let x := u - e
    have hxpos : IsPositive x := by
      constructor
      · intro t
        by_cases hti : t = i
        · subst t
          dsimp [x, u, e]
          simp only [columnTail, le_refl, ↓reduceIte,
            Pi.single_eq_same]
          omega
        · have hezero : e t = 0 := by simp [e, hti]
          rw [show x t = u t - e t by rfl, hezero, sub_zero]
          by_cases hit : i ≤ t
          · simpa [u, columnTail, hit] using D.nonnegative t j
          · simp [u, columnTail, hit]
      · intro hzero
        have hj := congrFun hzero j
        have hji : j ≠ i := ne_of_gt hij
        simp [x, u, e, columnTail, hijle, D.diagonal j, hji] at hj
    have hqu : quadraticForm D.Cinv u = 1 :=
      D.quadraticForm_columnTail hC hijle
    have heisu : e ⬝ᵥ D.Cinv.mulVec u = 0 := by
      dsimp only [e]
      rw [single_dotProduct]
      simp only [one_mul]
      change D.Cinv.mulVec (columnTail D.C i j) i = 0
      rw [D.inverse_mulVec_columnTail hC (le_refl i)]
      simp [ne_of_lt hij]
    have huise : u ⬝ᵥ D.Cinv.mulVec e = D.C i j :=
      D.columnTail_dot_inverse_unit hC i j
    have hqe : quadraticForm D.Cinv e = 1 := by
      dsimp only [e]
      unfold quadraticForm
      rw [single_dotProduct]
      simp only [one_mul]
      have hmul : D.Cinv.mulVec (Pi.single i (1 : ℤ)) = D.Cinv.col i := by
        simp [Matrix.mulVec_single]
      rw [hmul]
      exact D.inverse_diagonal_eq_one hC i
    have hqx : quadraticForm D.Cinv x = 2 - D.C i j := by
      unfold x
      unfold quadraticForm at hqu hqe ⊢
      rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
      rw [hqu, heisu, huise, hqe]
      ring
    have hweak := D.weaklyPositive x hxpos
    rw [hqx] at hweak
    omega
  · subst j
    rw [D.diagonal i]
  · rw [hC hij]
    omega

end WeaklyPositiveCartanData

end MagnitudeConjecture.CartanCoordinate
