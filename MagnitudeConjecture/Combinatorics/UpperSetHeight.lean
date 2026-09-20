import MagnitudeConjecture.Combinatorics.PosetSpaceRealization
import Mathlib.Order.Minimal

/-! # Height bounds for every finite upper set -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.UpperSetHeight
universe u
variable {T : Type u} [PartialOrder T] [Fintype T]

/-- A strictly increasing height on upper sets rises by at least the number
of elements added between any two upper sets. -/
theorem card_difference_le_height_difference
    (height : Finset T → ℕ)
    (hstep : ∀ U V : Finset T, IsUpperSet (U : Set T) → IsUpperSet (V : Set T) →
      U ⊂ V → height U < height V)
    (U V : Finset T) (hU : IsUpperSet (U : Set T)) (hV : IsUpperSet (V : Set T))
    (hUV : U ⊆ V) : height U + V.card ≤ height V + U.card := by
  classical
  letI : WellFoundedLT T := ⟨Finite.wellFounded_of_trans_of_irrefl (· < ·)⟩
  revert hV hUV
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    intro hV hUV
    by_cases heq : U = V
    · subst V
      omega
    have hex : ∃ a : T, a ∈ V ∧ a ∉ U := by
      by_contra! h
      exact heq (Finset.Subset.antisymm hUV h)
    obtain ⟨a, ha, hamin⟩ := exists_minimal_of_wellFoundedLT
      (fun a : T ↦ a ∈ V ∧ a ∉ U) hex
    have hmin : ∀ b ∈ (V : Set T), b ≤ a → b = a := by
      intro b hb hba
      have hbU : b ∉ U := by
        intro hbU
        exact ha.2 (hU hba hbU)
      exact le_antisymm hba (hamin ⟨hb, hbU⟩ hba)
    have hW : IsUpperSet ((V.erase a : Finset T) : Set T) := by
      simpa only [Finset.coe_erase] using hV.erase hmin
    have hUW : U ⊆ V.erase a := by
      intro b hb
      exact Finset.mem_erase.mpr ⟨by intro h; subst b; exact ha.2 hb, hUV hb⟩
    have hproper : V.erase a ⊂ V := Finset.erase_ssubset ha.1
    have hi := ih (V.erase a) hproper hW hUW
    have hs := hstep (V.erase a) V hW hV hproper
    have hc := Finset.card_erase_add_one ha.1
    omega

/-- If the total height bound is the size of the poset, every upper set
has height equal to its cardinality. -/
theorem height_eq_card
    (height : Finset T → ℕ)
    (hstep : ∀ U V : Finset T, IsUpperSet (U : Set T) → IsUpperSet (V : Set T) →
      U ⊂ V → height U < height V)
    (hbound : height Finset.univ ≤ Fintype.card T)
    (U : Finset T) (hU : IsUpperSet (U : Set T)) : height U = U.card := by
  classical
  have hlo := card_difference_le_height_difference height hstep ∅ U
    (by simp [IsUpperSet]) hU (Finset.empty_subset U)
  have hhi := card_difference_le_height_difference height hstep U Finset.univ
    hU (by simp [IsUpperSet]) (Finset.subset_univ U)
  simp only [Finset.card_empty, Finset.card_univ] at hlo hhi
  omega

end MagnitudeConjecture.UpperSetHeight
