import MagnitudeConjecture.Combinatorics.PosetSpaceFiltrationStabilizer
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Data.Finset.Max

/-!
# Finite chains of subspaces and basis flags

This file proves the linear-algebraic bridge from a finite chain of subspaces
to a complete basis flag containing that chain.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

open Module

variable {k : Type u} [Field k]

/-- The `m`-th subspace in a basis flag has dimension `m`. -/
theorem finrank_flag {V : Type u} [AddCommGroup V] [Module k V]
    {n : ℕ} (b : Basis (Fin n) k V) (m : Fin (n + 1)) :
    Module.finrank k (b.flag m) = m.val := by
  let I := {i : Fin n // i.castSucc < m}
  have hrange : Set.range (fun i : I ↦ b i.1) =
      b '' {i : Fin n | i.castSucc < m} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hli : LinearIndependent k (fun i : I ↦ b i.1) :=
    b.linearIndependent.comp (fun i : I ↦ i.1) Subtype.val_injective
  rw [Basis.flag, ← hrange, finrank_span_eq_card hli]
  change Fintype.card {i : Fin n // i.val < m.val} = m.val
  simpa [I] using
    (Fintype.card_fin_lt_of_le (Nat.le_of_lt_succ m.isLt))

/-- Append a basis of the quotient by `U` after a basis of `U`. -/
def appendQuotientBasis {V : Type u} [AddCommGroup V] [Module k V]
    (U : Submodule k V) {d q : ℕ}
    (bU : Basis (Fin d) k U) (bQ : Basis (Fin q) k (V ⧸ U)) :
    Basis (Fin (d + q)) k V :=
  (bU.sumQuot bQ).reindex finSumFinEquiv

@[simp]
theorem appendQuotientBasis_castAdd {V : Type u}
    [AddCommGroup V] [Module k V]
    (U : Submodule k V) {d q : ℕ}
    (bU : Basis (Fin d) k U) (bQ : Basis (Fin q) k (V ⧸ U))
    (i : Fin d) :
    appendQuotientBasis U bU bQ (Fin.castAdd q i) = bU i := by
  simp [appendQuotientBasis, Basis.reindex_apply]

/-- A flag subspace of the basis of `U` becomes the same initial flag
subspace after appending a quotient basis. -/
theorem map_flag_eq_appendQuotientBasis_flag {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (U : Submodule k V) {d q : ℕ}
    (bU : Basis (Fin d) k U) (bQ : Basis (Fin q) k (V ⧸ U))
    (m : Fin (d + 1)) :
    (bU.flag m).map U.subtype =
      (appendQuotientBasis U bU bQ).flag
        ⟨m.val, by omega⟩ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.map_le_iff_le_comap, bU.flag_le_iff]
    intro i hi
    have hmem := (appendQuotientBasis U bU bQ).self_mem_flag
      (i := Fin.castAdd q i) (k := ⟨m.val, by omega⟩)
      (by
        change i.val < m.val at hi ⊢
        exact hi)
    simpa using hmem
  · rw [Submodule.finrank_map_subtype_eq, finrank_flag, finrank_flag]

/-- Auxiliary dimension-indexed form of the finite-chain flag theorem. -/
private theorem exists_flag_basis_of_finset_chain_aux {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (n : ℕ) (hn : Module.finrank k V = n)
    (C : Finset (Submodule k V))
    (hC : IsChain (· ≤ ·) (C : Set (Submodule k V))) :
    ∃ b : Basis (Fin n) k V,
      ∀ U ∈ C, ∃ m : Fin (n + 1), U = b.flag m := by
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      classical
      let P := C.filter (fun U ↦ U ≠ ⊤)
      by_cases hP : P.Nonempty
      · obtain ⟨U, hUP, hmax⟩ :=
          Finset.exists_max_image P
            (fun U : Submodule k V ↦ Module.finrank k U) hP
        have hUC : U ∈ C := (Finset.mem_filter.mp hUP).1
        have hUne : U ≠ ⊤ := (Finset.mem_filter.mp hUP).2
        have hUmax : ∀ W ∈ P, W ≤ U := by
          intro W hWP
          have hWC : W ∈ C := (Finset.mem_filter.mp hWP).1
          rcases hC.total hWC hUC with hWU | hUW
          · exact hWU
          · have hdimWU : Module.finrank k W ≤ Module.finrank k U :=
              hmax W hWP
            have hdimUW : Module.finrank k U ≤ Module.finrank k W :=
              Submodule.finrank_mono hUW
            have heq : U = W :=
              Submodule.eq_of_le_of_finrank_eq hUW
                (Nat.le_antisymm hdimUW hdimWU)
            simp [heq]
        let D : Finset (Submodule k U) :=
          P.image (fun W ↦ W.comap U.subtype)
        have hD : IsChain (· ≤ ·) (D : Set (Submodule k U)) := by
          intro A hAD B hBD hAB
          obtain ⟨A₀, hA₀P, rfl⟩ := Finset.mem_image.mp hAD
          obtain ⟨B₀, hB₀P, rfl⟩ := Finset.mem_image.mp hBD
          have hA₀C : A₀ ∈ C := (Finset.mem_filter.mp hA₀P).1
          have hB₀C : B₀ ∈ C := (Finset.mem_filter.mp hB₀P).1
          exact (hC.total hA₀C hB₀C).imp
            Submodule.comap_mono Submodule.comap_mono
        have hUn : Module.finrank k U < n := by
          rw [← hn]
          exact Submodule.finrank_lt hUne
        obtain ⟨bU, hbU⟩ :=
          ih (Module.finrank k U) hUn rfl D hD
        let q := Module.finrank k (V ⧸ U)
        let bQ : Basis (Fin q) k (V ⧸ U) := Module.finBasis k (V ⧸ U)
        have hsize : Module.finrank k U + q = n := by
          dsimp only [q]
          rw [add_comm, U.finrank_quotient_add_finrank, hn]
        let b := appendQuotientBasis U bU bQ
        rw [← hsize]
        refine ⟨b, ?_⟩
        intro W hWC
        by_cases hWtop : W = ⊤
        · subst W
          exact ⟨Fin.last (Module.finrank k U + q), by simp [b]⟩
        · have hWP : W ∈ P := Finset.mem_filter.mpr ⟨hWC, hWtop⟩
          have hWU : W ≤ U := hUmax W hWP
          have hWD : W.comap U.subtype ∈ D :=
            Finset.mem_image.mpr ⟨W, hWP, rfl⟩
          obtain ⟨m, hm⟩ := hbU (W.comap U.subtype) hWD
          let m' : Fin (Module.finrank k U + q + 1) :=
            ⟨m.val, by omega⟩
          refine ⟨m', ?_⟩
          calc
            W = (W.comap U.subtype).map U.subtype := by
              rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWU]
            _ = (bU.flag m).map U.subtype := by rw [hm]
            _ = b.flag m' := by
              exact map_flag_eq_appendQuotientBasis_flag U bU bQ m
      · have htop : ∀ U ∈ C, U = ⊤ := by
          intro U hUC
          by_contra hUne
          exact hP ⟨U, Finset.mem_filter.mpr ⟨hUC, hUne⟩⟩
        let b : Basis (Fin n) k V := Module.finBasisOfFinrankEq k V hn
        refine ⟨b, ?_⟩
        intro U hUC
        have hUtop := htop U hUC
        subst U
        exact ⟨Fin.last n, by simp [b]⟩

/-- Every finite chain of subspaces of a finite-dimensional vector space is
contained in the complete flag of some basis. -/
theorem exists_flag_basis_of_finset_chain {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (C : Finset (Submodule k V))
    (hC : IsChain (· ≤ ·) (C : Set (Submodule k V))) :
    ∃ b : Basis (Fin (Module.finrank k V)) k V,
      ∀ U ∈ C, ∃ m : Fin (Module.finrank k V + 1),
        U = b.flag m := by
  exact exists_flag_basis_of_finset_chain_aux
    (Module.finrank k V) rfl C hC

section Poset

variable {T : Type u} [PartialOrder T] [Fintype T]

/-- A chain of indices gives a family of distinguished subspaces lying in
one complete basis flag. -/
theorem hasFlagBasisOn_of_isChain (X : Obj k T) (S : Set T)
    (hS : IsChain (· ≤ ·) S) :
    HasFlagBasisOn X S := by
  classical
  let C : Finset (Submodule k X) :=
    Finset.univ.image (fun t : S ↦ X.subspace t.1)
  have hC : IsChain (· ≤ ·) (C : Set (Submodule k X)) := by
    intro U hUC V hVC hUV
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hUC
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hVC
    rcases hS.total s.2 t.2 with hst | hts
    · exact Or.inl (X.monotone_subspace hst)
    · exact Or.inr (X.monotone_subspace hts)
  obtain ⟨b, hb⟩ := exists_flag_basis_of_finset_chain C hC
  refine ⟨b, ?_⟩
  intro t ht
  apply hb (X.subspace t)
  exact Finset.mem_image.mpr
    ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩

/-- If two chains cover the indexing poset, every Schur poset space is
one-dimensional. -/
theorem finrank_eq_one_of_isSchur_of_two_chain_cover
    (X : Obj k T) (hschur : IsSchur k T X)
    (A B : Set T) (hcover : A ∪ B = Set.univ)
    (hA : IsChain (· ≤ ·) A) (hB : IsChain (· ≤ ·) B) :
    Module.finrank k X = 1 := by
  exact finrank_eq_one_of_isSchur_of_two_flag_bases
    X hschur A B hcover
      (hasFlagBasisOn_of_isChain X A hA)
      (hasFlagBasisOn_of_isChain X B hB)

end Poset

end MagnitudeConjecture.PosetSpace
