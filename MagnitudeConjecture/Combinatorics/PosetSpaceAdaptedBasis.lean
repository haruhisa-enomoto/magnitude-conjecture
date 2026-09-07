import MagnitudeConjecture.Combinatorics.PosetSpaceRealization
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Coordinate subspaces and Schur poset spaces

This file isolates the linear-algebraic endpoint of the manuscript's
common-adapted-basis argument.  Once all distinguished subspaces of a poset
space are coordinate subspaces for one basis, a coordinate projection is a
poset-space endomorphism.  The Schur condition then forces total dimension at
most one.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u v

open Module

variable {k V T : Type u} [Field k]
variable [AddCommGroup V] [Module k V]

namespace AdaptedBasis

/-- A subspace is adapted to a basis when it is spanned by a subset of the
basis vectors. -/
def AdaptsSubmodule {ι : Type v} (b : Basis ι k V)
    (U : Submodule k V) : Prop :=
  ∃ S : Set ι, U = Submodule.span k (b '' S)

/-- Projection onto one basis coordinate. -/
def coordinateProjection {ι : Type v} (b : Basis ι k V) (i : ι) :
    V →ₗ[k] V where
  toFun := fun x ↦ (b.coord i x) • b i
  map_add' := by
    intro x y
    simp [add_smul]
  map_smul' := by
    intro c x
    simp [mul_smul]

@[simp]
theorem coordinateProjection_self {ι : Type v} (b : Basis ι k V) (i : ι) :
    coordinateProjection b i (b i) = b i := by
  simp [coordinateProjection, Basis.coord_apply]

@[simp]
theorem coordinateProjection_of_ne {ι : Type v} (b : Basis ι k V)
    {i j : ι} (hji : j ≠ i) :
    coordinateProjection b i (b j) = 0 := by
  simp [coordinateProjection, Basis.coord_apply, hji]

/-- A coordinate projection preserves every subspace adapted to the basis. -/
theorem coordinateProjection_mem_of_mem {ι : Type v} (b : Basis ι k V)
    {U : Submodule k V} (hU : AdaptsSubmodule b U) (i : ι)
    {x : V} (hx : x ∈ U) :
    coordinateProjection b i x ∈ U := by
  rcases hU with ⟨S, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, hj, rfl⟩
      by_cases hji : j = i
      · subst j
        simpa using
          (Submodule.subset_span (R := k)
            (show b i ∈ b '' S from ⟨i, hj, rfl⟩))
      · simp [coordinateProjection_of_ne b hji]
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa using Submodule.smul_mem _ c ih

end AdaptedBasis

section Poset

variable [PartialOrder T]

/-- All distinguished subspaces of `X` are coordinate subspaces for one
finite basis. -/
def HasCommonAdaptedBasis (X : Obj k T) : Prop :=
  ∃ b : Basis (Fin (Module.finrank k X)) k X,
    ∀ t, AdaptedBasis.AdaptsSubmodule b (X.subspace t)

/-- A coordinate projection, regarded as an endomorphism of a poset space. -/
def coordinateProjectionHom (X : Obj k T)
    (b : Basis (Fin (Module.finrank k X)) k X)
    (hb : ∀ t, AdaptedBasis.AdaptsSubmodule b (X.subspace t))
    (i : Fin (Module.finrank k X)) : X ⟶ X where
  linear := AdaptedBasis.coordinateProjection b i
  map_subspace := by
    intro t x hx
    exact AdaptedBasis.coordinateProjection_mem_of_mem b (hb t) i hx

/-- A Schur poset space admitting a common adapted basis has total dimension
at most one. -/
theorem finrank_le_one_of_isSchur_of_hasCommonAdaptedBasis
    (X : Obj k T) (hschur : IsSchur k T X)
    (hadapted : HasCommonAdaptedBasis X) :
    Module.finrank k X ≤ 1 := by
  rcases hadapted with ⟨b, hb⟩
  by_contra hnot
  have hrank : 2 ≤ Module.finrank k X := by omega
  let i : Fin (Module.finrank k X) := ⟨0, by omega⟩
  let j : Fin (Module.finrank k X) := ⟨1, by omega⟩
  have hij : j ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  obtain ⟨c, hc⟩ := hschur.2 (coordinateProjectionHom X b hb i)
  have hi := LinearMap.congr_fun hc (b i)
  have hj := LinearMap.congr_fun hc (b j)
  have hc_one : c = 1 := by
    have hcoord := congrArg (fun x ↦ b.coord i x) hi
    simpa [coordinateProjectionHom, i] using hcoord.symm
  rw [hc_one] at hj
  have hzero : b j = 0 := by
    simpa [coordinateProjectionHom, hij] using hj.symm
  exact (b.ne_zero j) hzero

/-- In particular, a nonzero Schur poset space with a common adapted basis is
one-dimensional. -/
theorem finrank_eq_one_of_isSchur_of_hasCommonAdaptedBasis
    (X : Obj k T) (hschur : IsSchur k T X)
    (hadapted : HasCommonAdaptedBasis X) :
    Module.finrank k X = 1 := by
  have hle := finrank_le_one_of_isSchur_of_hasCommonAdaptedBasis X hschur hadapted
  have hpos : 0 < Module.finrank k X :=
    Module.finrank_pos_iff_exists_ne_zero.mpr hschur.1
  omega

end Poset

end MagnitudeConjecture.PosetSpace
