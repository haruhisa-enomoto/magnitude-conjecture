import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# The Cartan quadratic-form coordinate estimate

This file formalizes the numerical heart of Appendix A in the frozen
manuscript.  For a nonnegative unimodular integral Cartan matrix with weakly
positive quadratic form, a positive root and its positive Coxeter transform
differ by at most one in every coordinate.

The module-theoretic application must still construct this data and identify
dimension vectors along Auslander--Reiten translation.  No such facts are
assumed here under representation-theoretic names.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace MagnitudeConjecture.CartanCoordinate

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The integral quadratic form represented by an inverse Cartan matrix. -/
def quadraticForm (Cinv : Matrix ι ι ℤ) (x : ι → ℤ) : ℤ :=
  x ⬝ᵥ Cinv.mulVec x

/-- The projective root belonging to a Cartan index. -/
def projectiveRoot (C : Matrix ι ι ℤ) (a : ι) : ι → ℤ :=
  C.col a

/-- The Coxeter matrix in the row-vector convention of the manuscript. -/
def coxeterMatrix (C Cinv : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  -(Cinv.transpose * C)

/-- The inverse Coxeter matrix. -/
def inverseCoxeterMatrix (C Cinv : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  -(Cinv * C.transpose)

/-- A positive integral vector: coordinatewise nonnegative and nonzero. -/
def IsPositive (x : ι → ℤ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ x ≠ 0

/-- Exact integral Cartan-form input used in the quadratic proof. -/
structure WeaklyPositiveCartanData where
  C : Matrix ι ι ℤ
  Cinv : Matrix ι ι ℤ
  inverse_mul : Cinv * C = 1
  mul_inverse : C * Cinv = 1
  diagonal : ∀ i, C i i = 1
  nonnegative : ∀ i j, 0 ≤ C i j
  weaklyPositive : ∀ x, IsPositive x → 1 ≤ quadraticForm Cinv x

namespace WeaklyPositiveCartanData

/-- The Coxeter transformation attached to the data. -/
def coxeter (D : WeaklyPositiveCartanData (ι := ι)) : Matrix ι ι ℤ :=
  coxeterMatrix D.C D.Cinv

/-- The inverse Coxeter transformation attached to the data. -/
def coxeterInv (D : WeaklyPositiveCartanData (ι := ι)) : Matrix ι ι ℤ :=
  inverseCoxeterMatrix D.C D.Cinv

omit [DecidableEq ι] in
/-- Polarization of the integral quadratic form. -/
theorem quadraticForm_add (Cinv : Matrix ι ι ℤ) (x y : ι → ℤ) :
    quadraticForm Cinv (x + y) =
      quadraticForm Cinv x + quadraticForm Cinv y +
        x ⬝ᵥ Cinv.mulVec y + y ⬝ᵥ Cinv.mulVec x := by
  rw [quadraticForm, Matrix.mulVec_add, add_dotProduct,
    dotProduct_add, dotProduct_add]
  simp only [quadraticForm]
  ring

/-- The polarized pairing with a projective root is the coordinate change
under the Coxeter transformation. -/
theorem crossTerm_projectiveRoot
    (C Cinv : Matrix ι ι ℤ) (hinv : Cinv * C = 1)
    (x : ι → ℤ) (a : ι) :
    x ⬝ᵥ Cinv.mulVec (projectiveRoot C a) +
        projectiveRoot C a ⬝ᵥ Cinv.mulVec x =
      x a - Matrix.vecMul x (coxeterMatrix C Cinv) a := by
  have hfirst : Cinv.mulVec (projectiveRoot C a) = Pi.single a 1 := by
    rw [projectiveRoot,
      ← show C.mulVec (Pi.single a 1) = C.col a by
        simpa using Matrix.mulVec_single C a (1 : ℤ)]
    rw [Matrix.mulVec_mulVec, hinv]
    ext i
    by_cases hia : i = a <;> simp [hia]
  rw [hfirst, dotProduct_single]
  simp only [mul_one, coxeterMatrix, Matrix.vecMul_neg, Pi.neg_apply,
    sub_neg_eq_add]
  congr 1
  calc
    projectiveRoot C a ⬝ᵥ Cinv.mulVec x =
        Cinv.mulVec x ⬝ᵥ projectiveRoot C a := dotProduct_comm _ _
    _ = Matrix.vecMul (Cinv.mulVec x) C a := rfl
    _ = Matrix.vecMul (Matrix.vecMul x Cinv.transpose) C a := by
      rw [Matrix.vecMul_transpose]
    _ = Matrix.vecMul x (Cinv.transpose * C) a := by
      rw [Matrix.vecMul_vecMul]

/-- Every Cartan column is a positive integral vector. -/
theorem projectiveRoot_positive
    (D : WeaklyPositiveCartanData (ι := ι)) (a : ι) :
    IsPositive (projectiveRoot D.C a) := by
  constructor
  · exact fun i ↦ D.nonnegative i a
  · intro hzero
    have h := congrFun hzero a
    simp [projectiveRoot, D.diagonal a] at h

/-- Every Cartan column is a root of the quadratic form. -/
theorem projectiveRoot_quadraticForm
    (D : WeaklyPositiveCartanData (ι := ι)) (a : ι) :
    quadraticForm D.Cinv (projectiveRoot D.C a) = 1 := by
  have hfirst :
      D.Cinv.mulVec (projectiveRoot D.C a) = Pi.single a 1 := by
    rw [projectiveRoot,
      ← show D.C.mulVec (Pi.single a 1) = D.C.col a by
        simpa using Matrix.mulVec_single D.C a (1 : ℤ)]
    rw [Matrix.mulVec_mulVec, D.inverse_mul]
    ext i
    by_cases hia : i = a <;> simp [hia]
  rw [quadraticForm, hfirst, dotProduct_single]
  simp [projectiveRoot, D.diagonal a]

/-- Forward half of the quadratic estimate: a positive root changes
upward by at most one under the Coxeter transformation. -/
theorem coxeter_apply_le_add_one
    (D : WeaklyPositiveCartanData (ι := ι)) (x : ι → ℤ)
    (hxpos : IsPositive x) (hxroot : quadraticForm D.Cinv x = 1)
    (a : ι) :
    Matrix.vecMul x D.coxeter a ≤ x a + 1 := by
  have hppos := D.projectiveRoot_positive a
  have haddpos : IsPositive (x + projectiveRoot D.C a) := by
    constructor
    · intro i
      exact add_nonneg (hxpos.1 i) (hppos.1 i)
    · intro hzero
      have h := congrFun hzero a
      have hpa : projectiveRoot D.C a a = 1 := by
        simp [projectiveRoot, D.diagonal]
      have hxa := hxpos.1 a
      change x a + projectiveRoot D.C a a = 0 at h
      rw [hpa] at h
      omega
  have hweak := D.weaklyPositive
    (x + projectiveRoot D.C a) haddpos
  have hqadd := quadraticForm_add D.Cinv x (projectiveRoot D.C a)
  have hcross := crossTerm_projectiveRoot
    D.C D.Cinv D.inverse_mul x a
  rw [hxroot, D.projectiveRoot_quadraticForm a,
    add_assoc, hcross] at hqadd
  change Matrix.vecMul x (coxeterMatrix D.C D.Cinv) a ≤ x a + 1
  rw [hqadd] at hweak
  omega

/-- The displayed Coxeter inverse is a right inverse. -/
theorem coxeter_mul_coxeterInv
    (D : WeaklyPositiveCartanData (ι := ι)) :
    D.coxeter * D.coxeterInv = 1 := by
  calc
    D.coxeter * D.coxeterInv =
        D.Cinv.transpose * (D.C * D.Cinv) * D.C.transpose := by
      simp [coxeter, coxeterInv, coxeterMatrix, inverseCoxeterMatrix,
        Matrix.mul_assoc]
    _ = D.Cinv.transpose * D.C.transpose := by
      rw [D.mul_inverse]
      simp
    _ = (D.C * D.Cinv).transpose := by rw [Matrix.transpose_mul]
    _ = 1 := by rw [D.mul_inverse]; simp

/-- The Coxeter transformation preserves the inverse-Cartan bilinear matrix. -/
theorem coxeter_mul_Cinv_mul_transpose
    (D : WeaklyPositiveCartanData (ι := ι)) :
    D.coxeter * D.Cinv * D.coxeter.transpose = D.Cinv := by
  calc
    D.coxeter * D.Cinv * D.coxeter.transpose =
        D.Cinv.transpose * (D.C * D.Cinv) * D.C.transpose * D.Cinv := by
      simp [coxeter, coxeterMatrix, Matrix.mul_assoc]
    _ = D.Cinv.transpose * D.C.transpose * D.Cinv := by
      rw [D.mul_inverse]
      simp
    _ = (D.C * D.Cinv).transpose * D.Cinv := by
      rw [Matrix.transpose_mul]
    _ = D.Cinv := by rw [D.mul_inverse]; simp

/-- The inverse-Cartan quadratic form is invariant under the Coxeter
transformation. -/
theorem quadraticForm_coxeter
    (D : WeaklyPositiveCartanData (ι := ι)) (x : ι → ℤ) :
    quadraticForm D.Cinv (Matrix.vecMul x D.coxeter) =
      quadraticForm D.Cinv x := by
  unfold quadraticForm
  calc
    Matrix.vecMul x D.coxeter ⬝ᵥ
        D.Cinv.mulVec (Matrix.vecMul x D.coxeter) =
      Matrix.vecMul (Matrix.vecMul x D.coxeter) D.Cinv ⬝ᵥ
        Matrix.vecMul x D.coxeter :=
      Matrix.dotProduct_mulVec _ _ _
    _ = Matrix.vecMul x (D.coxeter * D.Cinv) ⬝ᵥ
        Matrix.vecMul x D.coxeter := by rw [Matrix.vecMul_vecMul]
    _ = x ⬝ᵥ (D.coxeter * D.Cinv).mulVec
        (Matrix.vecMul x D.coxeter) :=
      (Matrix.dotProduct_mulVec _ _ _).symm
    _ = x ⬝ᵥ (D.coxeter * D.Cinv).mulVec
        (D.coxeter.transpose.mulVec x) := by
      apply congrArg (fun y => x ⬝ᵥ (D.coxeter * D.Cinv).mulVec y)
      simpa using (Matrix.vecMul_transpose D.coxeter.transpose x)
    _ = x ⬝ᵥ
        (D.coxeter * D.Cinv * D.coxeter.transpose).mulVec x := by
      rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ D.Cinv.mulVec x := by
      rw [D.coxeter_mul_Cinv_mul_transpose]

/-- Applying the Coxeter transformation and then its displayed inverse
returns the original row vector. -/
theorem vecMul_coxeter_coxeterInv
    (D : WeaklyPositiveCartanData (ι := ι)) (x : ι → ℤ) :
    Matrix.vecMul (Matrix.vecMul x D.coxeter) D.coxeterInv = x := by
  rw [Matrix.vecMul_vecMul, D.coxeter_mul_coxeterInv]
  simp

omit [DecidableEq ι] in
/-- Transposing the inverse matrix leaves its quadratic form unchanged. -/
theorem quadraticForm_transpose (M : Matrix ι ι ℤ) (x : ι → ℤ) :
    quadraticForm M.transpose x = quadraticForm M x := by
  unfold quadraticForm
  calc
    x ⬝ᵥ M.transpose.mulVec x =
        x ⬝ᵥ Matrix.vecMul x M := by
      rw [show M.transpose.mulVec x = Matrix.vecMul x M by
        simpa using (Matrix.vecMul_transpose M.transpose x).symm]
    _ = Matrix.vecMul x M ⬝ᵥ x := dotProduct_comm _ _
    _ = x ⬝ᵥ M.mulVec x := (Matrix.dotProduct_mulVec x M x).symm

/-- The opposite Cartan matrix carries the transposed weakly positive
Cartan data. -/
def transpose (D : WeaklyPositiveCartanData (ι := ι)) :
    WeaklyPositiveCartanData (ι := ι) where
  C := D.C.transpose
  Cinv := D.Cinv.transpose
  inverse_mul := by
    rw [← Matrix.transpose_mul, D.mul_inverse]
    simp
  mul_inverse := by
    rw [← Matrix.transpose_mul, D.inverse_mul]
    simp
  diagonal := D.diagonal
  nonnegative := fun i j ↦ D.nonnegative j i
  weaklyPositive := by
    intro x hx
    rw [quadraticForm_transpose]
    exact D.weaklyPositive x hx

@[simp]
theorem transpose_coxeter
    (D : WeaklyPositiveCartanData (ι := ι)) :
    D.transpose.coxeter = D.coxeterInv := by
  simp [transpose, coxeter, coxeterInv, coxeterMatrix,
    inverseCoxeterMatrix]

/-- Quadratic-form form of the coordinate estimate.  If both `x`
and its Coxeter transform are positive roots, every coordinate changes by at
most one. -/
theorem coxeter_coordinate_abs_sub_le_one
    (D : WeaklyPositiveCartanData (ι := ι)) (x : ι → ℤ)
    (hxpos : IsPositive x) (hxroot : quadraticForm D.Cinv x = 1)
    (hypos : IsPositive (Matrix.vecMul x D.coxeter))
    (hyroot :
      quadraticForm D.Cinv (Matrix.vecMul x D.coxeter) = 1)
    (a : ι) :
    abs (x a - Matrix.vecMul x D.coxeter a) ≤ 1 := by
  let y := Matrix.vecMul x D.coxeter
  change abs (x a - y a) ≤ 1
  have hforward := D.coxeter_apply_le_add_one x hxpos hxroot a
  change y a ≤ x a + 1 at hforward
  have hyrootT : quadraticForm D.transpose.Cinv y = 1 := by
    change quadraticForm D.Cinv.transpose y = 1
    rw [quadraticForm_transpose]
    exact hyroot
  have hback :=
    D.transpose.coxeter_apply_le_add_one y hypos hyrootT a
  rw [transpose_coxeter] at hback
  have hyx : Matrix.vecMul y D.coxeterInv = x :=
    D.vecMul_coxeter_coxeterInv x
  change Matrix.vecMul y D.coxeterInv a ≤ y a + 1 at hback
  rw [congrFun hyx a] at hback
  rw [abs_le]
  constructor <;> omega

end WeaklyPositiveCartanData

/-- Local numerical data for one coordinate of a positive-root pair related
by a Coxeter transformation.

This wrapper is designed for the support-restriction argument in Appendix A of
the frozen manuscript.  The finite index type and Cartan form may depend on the
Auslander--Reiten sequence: no ambient weak-positivity statement is built into
the interface. -/
structure LocalRootPairCoordinateData (a b : ℤ) where
  index : Type u
  [indexFintype : Fintype index]
  [indexDecidableEq : DecidableEq index]
  cartan : WeaklyPositiveCartanData (ι := index)
  root : index → ℤ
  root_positive : IsPositive root
  root_quadraticForm : quadraticForm cartan.Cinv root = 1
  transform_positive : IsPositive (Matrix.vecMul root cartan.coxeter)
  transform_quadraticForm :
    quadraticForm cartan.Cinv (Matrix.vecMul root cartan.coxeter) = 1
  coordinate : index
  root_coordinate : root coordinate = a
  transform_coordinate : Matrix.vecMul root cartan.coxeter coordinate = b

namespace LocalRootPairCoordinateData

/-- The local positive-root package implies the manuscript's bound for its
identified coordinate. -/
theorem abs_sub_le_one {a b : ℤ} (D : LocalRootPairCoordinateData a b) :
    abs (a - b) ≤ 1 := by
  letI := D.indexFintype
  letI := D.indexDecidableEq
  have h := D.cartan.coxeter_coordinate_abs_sub_le_one
    D.root D.root_positive D.root_quadraticForm
    D.transform_positive D.transform_quadraticForm D.coordinate
  simpa only [D.root_coordinate, D.transform_coordinate] using h

end LocalRootPairCoordinateData

end MagnitudeConjecture.CartanCoordinate
