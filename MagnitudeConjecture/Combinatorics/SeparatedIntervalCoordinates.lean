import MagnitudeConjecture.Combinatorics.SeparatedIntervals
import Mathlib.Data.Fintype.EquivFin

/-! # Finite coordinates for separated interval blocks -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.GradedInterval

/-- The last retained degree for q positive blocks. -/
def packingEnd (r h q : ℕ) : ℕ := (q - 1) * (r + h + 1) + r

/-- This endpoint agrees with the manuscript's q(r+h+1)-h-1. -/
theorem packingEnd_eq (r h q : ℕ) (hq : 1 ≤ q) :
    packingEnd r h q = q * (r + h + 1) - h - 1 := by
  have he : q * (r + h + 1) = (q - 1) * (r + h + 1) + (r + h + 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hq]
    rw [Nat.add_mul, Nat.one_mul]
  unfold packingEnd
  omega

/-- The degree of a point in one of the retained blocks. -/
def blockPoint (r h q : ℕ) (j : Fin q) (t : Fin (r + 1)) : Fin (packingEnd r h q + 1) :=
  ⟨j.val * (r + h + 1) + t.val, by
    have hj : j.val ≤ q - 1 := by have hj := j.isLt; omega
    have hm := Nat.mul_le_mul_right (r + h + 1) hj
    have ht := t.isLt
    unfold packingEnd
    omega⟩

/-- Each block coordinate lies in its specified retained block. -/
theorem blockPoint_inBlock (r h q : ℕ) (j : Fin q) (t : Fin (r + 1)) :
    InBlock r h j.val ((blockPoint r h q j t).val : ℤ) := by
  have ht := t.isLt
  dsimp [blockPoint, InBlock]
  push_cast
  constructor <;> omega

/-- The pair of block number and offset is recovered from its degree. -/
theorem blockPoint_injective (r h q : ℕ) :
    Function.Injective (fun p : Fin q × Fin (r + 1) ↦ blockPoint r h q p.1 p.2) := by
  intro p t he
  have hv := congrArg (fun x : Fin (packingEnd r h q + 1) ↦ (x.val : ℤ)) he
  have hj : p.1.val = t.1.val := block_index_eq_of_close r h
    (blockPoint_inBlock r h q p.1 p.2) (blockPoint_inBlock r h q t.1 t.2)
    (by rw [hv]; simp)
  apply Prod.ext (Fin.ext hj)
  apply Fin.ext
  have hn := congrArg Fin.val he
  change p.1.val * (r + h + 1) + p.2.val = t.1.val * (r + h + 1) + t.2.val at hn
  rw [hj] at hn
  exact Nat.add_left_cancel hn

/-- Every retained finite degree has a block coordinate. -/
theorem exists_blockPoint_of_retained (r h q : ℕ)
    (d : Fin (packingEnd r h q + 1)) (hd : Retained r h q (d.val : ℤ)) :
    ∃ p : Fin q × Fin (r + 1), blockPoint r h q p.1 p.2 = d := by
  obtain ⟨j, hj, hlo, hhi⟩ := hd
  have hlo' : j * (r + h + 1) ≤ d.val := by exact_mod_cast hlo
  have hhi' : d.val ≤ j * (r + h + 1) + r := by exact_mod_cast hhi
  refine ⟨(⟨j, hj⟩, ⟨d.val - j * (r + h + 1), by omega⟩), ?_⟩
  apply Fin.ext
  dsimp [blockPoint]
  omega

/-- The retained degree set is exactly q copies of the finite interval. -/
def retainedDegreeEquiv (r h q : ℕ) :
    Fin q × Fin (r + 1) ≃ {d : Fin (packingEnd r h q + 1) // Retained r h q (d.val : ℤ)} :=
  Equiv.ofBijective
    (fun p ↦ ⟨blockPoint r h q p.1 p.2, p.1.val, p.1.isLt, blockPoint_inBlock r h q p.1 p.2⟩)
    ⟨fun _ _ he ↦ blockPoint_injective r h q (congrArg Subtype.val he), by
      intro d
      obtain ⟨p, hp⟩ := exists_blockPoint_of_retained r h q d.val d.property
      exact ⟨p, Subtype.ext hp⟩⟩

end MagnitudeConjecture.GradedInterval
