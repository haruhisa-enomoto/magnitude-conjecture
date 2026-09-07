import MagnitudeConjecture.Combinatorics.PosetSpaceAdaptedBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Endomorphism stabilizers of subspace filtrations

This file gives the dimension-intersection argument needed for the
manuscript's two-filtration step.  It reduces the Schur-dimension conclusion to
lower bounds for the stabilizers of the two individual chains.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

open Module

variable {k T : Type u} [Field k] [PartialOrder T]

/-- Upper-triangular matrix-unit indices: `(i,j)` with `i ≤ j`. -/
def TriangularIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≤ p.2}

/-- Triangular indices are equivalently a column `j` together with a row in
`Fin (j+1)`. -/
def triangularIndexEquivSigma (n : ℕ) :
    TriangularIndex n ≃ Σ j : Fin n, Fin (j.val + 1) where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, Nat.lt_succ_iff.mpr p.2⟩⟩
  invFun p :=
    ⟨(⟨p.2.val, lt_of_le_of_lt (Nat.le_of_lt_succ p.2.isLt) p.1.isLt⟩, p.1),
      Nat.le_of_lt_succ p.2.isLt⟩
  left_inv := by rintro ⟨⟨i, j⟩, hij⟩; rfl
  right_inv := by rintro ⟨j, i⟩; rfl

instance (n : ℕ) : Fintype (TriangularIndex n) :=
  Fintype.ofEquiv (Σ j : Fin n, Fin (j.val + 1))
    (triangularIndexEquivSigma n).symm

/-- Twice the number of triangular matrix units is `n(n+1)`. -/
theorem two_mul_card_triangularIndex (n : ℕ) :
    2 * Fintype.card (TriangularIndex n) = n * (n + 1) := by
  rw [Fintype.card_congr (triangularIndexEquivSigma n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change 2 * (∑ j : Fin n, (j.val + 1)) = n * (n + 1)
  have hsum : (∑ j : Fin n, (j.val + 1)) =
      ∑ i ∈ Finset.range n, (i + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [dif_pos hi]
  rw [hsum]
  have hclosed : ∀ m : ℕ,
      2 * (∑ i ∈ Finset.range m, (i + 1)) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        nlinarith
  exact hclosed n

/-- The triangular matrix units attached to a basis. -/
def triangularEnd {V : Type u} [AddCommGroup V] [Module k V]
    {n : ℕ} (b : Basis (Fin n) k V) (p : TriangularIndex n) :
    V →ₗ[k] V :=
  { toFun := fun x ↦ (b.coord p.1.2 x) • b p.1.1
    map_add' := by
      intro x y
      simp [add_smul]
    map_smul' := by
      intro c x
      simp [mul_smul] }

/-- The subspace of endomorphisms spanned by the triangular matrix units. -/
def triangularEndSpan {V : Type u} [AddCommGroup V] [Module k V]
    {n : ℕ} (b : Basis (Fin n) k V) :
    Submodule k (Module.End k V) :=
  Submodule.span k (Set.range (triangularEnd b))

/-- The triangular matrix units are linearly independent. -/
theorem linearIndependent_triangularEnd {V : Type u}
    [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Basis (Fin n) k V) :
    LinearIndependent k (triangularEnd b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have happ := LinearMap.congr_fun hg (b p.1.2)
  have hcoord := congrArg (fun x ↦ b.coord p.1.1 x) happ
  simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    triangularEnd, Basis.coord_apply] at hcoord
  rw [Fintype.sum_eq_single p] at hcoord
  · simpa [Finsupp.single_apply] using hcoord
  · intro q hqp
    by_cases hcol : p.1.2 = q.1.2
    · have hrow : q.1.1 ≠ p.1.1 := by
        intro hrow
        apply hqp
        apply Subtype.ext
        exact Prod.ext hrow hcol.symm
      simp [hcol, hrow]
    · simp [hcol]

/-- The triangular endomorphism subspace has the expected dimension. -/
theorem finrank_triangularEndSpan {V : Type u}
    [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Basis (Fin n) k V) :
    Module.finrank k (triangularEndSpan b) =
      Fintype.card (TriangularIndex n) := by
  exact finrank_span_eq_card (linearIndependent_triangularEnd b)

/-- Every upper-triangular matrix unit preserves every flag subspace of its
basis. -/
theorem triangularEnd_preserves_flag {V : Type u}
    [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Basis (Fin n) k V) (p : TriangularIndex n)
    (m : Fin (n + 1)) {x : V} (hx : x ∈ b.flag m) :
    triangularEnd b p x ∈ b.flag m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨r, hr, rfl⟩
      by_cases h : r = p.1.2
      · subst r
        simpa [triangularEnd] using b.self_mem_flag
          (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr p.2) hr)
      · simp [triangularEnd, Basis.coord_apply, h]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
      simpa using Submodule.smul_mem _ c ih

/-- The subspaces indexed by `S` form subspaces in a single complete flag. -/
def HasFlagBasisOn (X : Obj k T) (S : Set T) : Prop :=
  ∃ b : Basis (Fin (Module.finrank k X)) k X,
    ∀ t ∈ S, ∃ m : Fin (Module.finrank k X + 1),
      X.subspace t = b.flag m

/-- Linear endomorphisms preserving the distinguished subspaces indexed by
the set `S`. -/
def stabilizerOn (X : Obj k T) (S : Set T) :
    Submodule k (X →ₗ[k] X) where
  carrier := {f | ∀ t ∈ S, ∀ x, x ∈ X.subspace t → f x ∈ X.subspace t}
  zero_mem' := by
    intro t ht x hx
    simp
  add_mem' := by
    intro f g hf hg t ht x hx
    exact Submodule.add_mem _ (hf t ht x hx) (hg t ht x hx)
  smul_mem' := by
    intro c f hf t ht x hx
    exact Submodule.smul_mem _ c (hf t ht x hx)

@[simp]
theorem mem_stabilizerOn_iff (X : Obj k T) (S : Set T) (f : X →ₗ[k] X) :
    f ∈ stabilizerOn X S ↔
      ∀ t ∈ S, ∀ x, x ∈ X.subspace t → f x ∈ X.subspace t :=
  Iff.rfl

/-- The triangular endomorphism subspace attached to a flag basis lies in the
stabilizer of all subspaces belonging to that flag. -/
theorem triangularEndSpan_le_stabilizerOn
    (X : Obj k T) (S : Set T)
    (b : Basis (Fin (Module.finrank k X)) k X)
    (hb : ∀ t ∈ S, ∃ m : Fin (Module.finrank k X + 1),
      X.subspace t = b.flag m) :
    triangularEndSpan b ≤ stabilizerOn X S := by
  rw [triangularEndSpan]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨p, rfl⟩
  change triangularEnd b p ∈ stabilizerOn X S
  rw [mem_stabilizerOn_iff]
  intro t ht x hx
  obtain ⟨m, hm⟩ := hb t ht
  rw [hm] at hx ⊢
  exact triangularEnd_preserves_flag b p m hx

/-- A family of subspaces contained in one complete flag has a stabilizer of
dimension at least `n(n+1)/2`. -/
theorem card_triangularIndex_le_finrank_stabilizerOn
    (X : Obj k T) (S : Set T) (hflag : HasFlagBasisOn X S) :
    Fintype.card (TriangularIndex (Module.finrank k X)) ≤
      Module.finrank k (stabilizerOn X S) := by
  rcases hflag with ⟨b, hb⟩
  rw [← finrank_triangularEndSpan b]
  exact Submodule.finrank_mono
    (triangularEndSpan_le_stabilizerOn X S b hb)

/-- Preserving a union of index sets is the intersection of the two
stabilizer subspaces. -/
theorem stabilizerOn_union (X : Obj k T) (A B : Set T) :
    stabilizerOn X (A ∪ B) = stabilizerOn X A ⊓ stabilizerOn X B := by
  ext f
  simp only [mem_stabilizerOn_iff, Submodule.mem_inf, Set.mem_union]
  aesop

/-- An element of the full stabilizer is an endomorphism of the poset space. -/
def homOfMemStabilizerOnUniv (X : Obj k T)
    (f : stabilizerOn X Set.univ) : X ⟶ X where
  linear := f.1
  map_subspace := by
    intro t x hx
    exact f.2 t (Set.mem_univ t) x hx

/-- The full stabilizer of a Schur poset space has dimension at most one. -/
theorem finrank_stabilizerOn_univ_le_one_of_isSchur
    (X : Obj k T) (hschur : IsSchur k T X) :
    Module.finrank k (stabilizerOn X Set.univ) ≤ 1 := by
  have hid : (LinearMap.id : X →ₗ[k] X) ≠ 0 := by
    obtain ⟨x, hx⟩ := hschur.1
    intro hzero
    have happ := LinearMap.congr_fun hzero x
    simp only [LinearMap.id_apply, LinearMap.zero_apply] at happ
    exact hx happ
  have hle : stabilizerOn X Set.univ ≤
      k ∙ (LinearMap.id : X →ₗ[k] X) := by
    intro f hf
    obtain ⟨c, hc⟩ := hschur.2
      (homOfMemStabilizerOnUniv X ⟨f, hf⟩)
    have hfc : f = c • (LinearMap.id : X →ₗ[k] X) := hc
    rw [hfc]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  exact (Submodule.finrank_mono hle).trans_eq
    (finrank_span_singleton hid)

/-- If two partial stabilizers are jointly larger than the ambient
endomorphism space by at least two dimensions, then their intersection has
dimension at least two. -/
theorem two_le_finrank_stabilizerOn_union
    (X : Obj k T) (A B : Set T)
    (hlarge : Module.finrank k (X →ₗ[k] X) + 2 ≤
      Module.finrank k (stabilizerOn X A) +
        Module.finrank k (stabilizerOn X B)) :
    2 ≤ Module.finrank k (stabilizerOn X (A ∪ B)) := by
  have hsup : Module.finrank k
      (stabilizerOn X A ⊔ stabilizerOn X B : Submodule k (X →ₗ[k] X)) ≤
      Module.finrank k (X →ₗ[k] X) :=
    Submodule.finrank_le _
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (stabilizerOn X A) (stabilizerOn X B)
  rw [stabilizerOn_union]
  omega

/-- Dimension bounds for two covering filtration stabilizers force a Schur
poset space to have dimension at most one. -/
theorem finrank_le_one_of_isSchur_of_two_stabilizer_bounds
    (X : Obj k T) (hschur : IsSchur k T X)
    (A B : Set T) (hcover : A ∪ B = Set.univ)
    (hlarge : 2 ≤ Module.finrank k X →
      Module.finrank k (X →ₗ[k] X) + 2 ≤
        Module.finrank k (stabilizerOn X A) +
          Module.finrank k (stabilizerOn X B)) :
    Module.finrank k X ≤ 1 := by
  by_contra hnot
  have hrank : 2 ≤ Module.finrank k X := by omega
  have htwo := two_le_finrank_stabilizerOn_union X A B (hlarge hrank)
  rw [hcover] at htwo
  have hone := finrank_stabilizerOn_univ_le_one_of_isSchur X hschur
  omega

/-- Two flag-indexed covering families give the stabilizer dimension bound
needed in the Schur argument. -/
theorem two_flag_bases_stabilizer_bound
    (X : Obj k T) (A B : Set T)
    (hA : HasFlagBasisOn X A) (hB : HasFlagBasisOn X B)
    (hrank : 2 ≤ Module.finrank k X) :
    Module.finrank k (X →ₗ[k] X) + 2 ≤
      Module.finrank k (stabilizerOn X A) +
        Module.finrank k (stabilizerOn X B) := by
  let n := Module.finrank k X
  let c := Fintype.card (TriangularIndex n)
  have hA' : c ≤ Module.finrank k (stabilizerOn X A) :=
    card_triangularIndex_le_finrank_stabilizerOn X A hA
  have hB' : c ≤ Module.finrank k (stabilizerOn X B) :=
    card_triangularIndex_le_finrank_stabilizerOn X B hB
  have hcard : 2 * c = n * (n + 1) :=
    two_mul_card_triangularIndex n
  have hquad : n * n + 2 ≤ 2 * c := by
    rw [hcard]
    dsimp only [n] at hrank ⊢
    nlinarith
  dsimp only [n, c] at hA' hB' hquad
  rw [Module.finrank_linearMap]
  exact hquad.trans (by omega)

/-- A Schur poset space whose distinguished subspaces are covered by two
complete flags has total dimension at most one. -/
theorem finrank_le_one_of_isSchur_of_two_flag_bases
    (X : Obj k T) (hschur : IsSchur k T X)
    (A B : Set T) (hcover : A ∪ B = Set.univ)
    (hA : HasFlagBasisOn X A) (hB : HasFlagBasisOn X B) :
    Module.finrank k X ≤ 1 := by
  exact finrank_le_one_of_isSchur_of_two_stabilizer_bounds
    X hschur A B hcover fun hrank ↦
      two_flag_bases_stabilizer_bound X A B hA hB hrank

/-- In particular, a nonzero Schur poset space covered by two flag-indexed
families is one-dimensional. -/
theorem finrank_eq_one_of_isSchur_of_two_flag_bases
    (X : Obj k T) (hschur : IsSchur k T X)
    (A B : Set T) (hcover : A ∪ B = Set.univ)
    (hA : HasFlagBasisOn X A) (hB : HasFlagBasisOn X B) :
    Module.finrank k X = 1 := by
  have hle := finrank_le_one_of_isSchur_of_two_flag_bases
    X hschur A B hcover hA hB
  have hpos : 0 < Module.finrank k X :=
    Module.finrank_pos_iff_exists_ne_zero.mpr hschur.1
  omega

end MagnitudeConjecture.PosetSpace
