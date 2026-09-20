import MagnitudeConjecture.Combinatorics.UpperSetHeight

/-! # Sharp heights of all one-dimensional upper-set representations -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.PosetSpace
universe u
variable {k T : Type u} [Field k] [PartialOrder T] [Fintype T]

/-- In a sharp positive grading every upper-set line has its support size
as height, independently of any chosen reverse enumeration. -/
theorem line_level_eq_card_of_sharp_grading
    {L : ℕ} (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    (hL : L ≤ Fintype.card T) (U : Finset T) (hU : IsUpperSet (U : Set T)) :
    G.level (line k T (U : Set T) hU) = U.card := by
  classical
  let height : Finset T → ℕ := fun V ↦
    if hV : IsUpperSet (V : Set T) then G.level (line k T (V : Set T) hV) else 0
  have heval : ∀ (V : Finset T) (hV : IsUpperSet (V : Set T)),
      height V = G.level (line k T (V : Set T) hV) := by
    intro V hV
    exact dif_pos hV
  have hstep : ∀ V W : Finset T, IsUpperSet (V : Set T) → IsUpperSet (W : Set T) →
      V ⊂ W → height V < height W := by
    intro V W hV hW hVW
    rw [heval V hV, heval W hW]
    have hset : (V : Set T) ⊂ (W : Set T) := by exact_mod_cast hVW
    exact G.lt_of_nonzero_not_isIso (lineHom k T hset.1)
      (line_isSchur k T _ hV) (line_isSchur k T _ hW)
      (lineHom_ne_zero k T hset.1) (lineHom_not_isIso k T hset)
  have htop : IsUpperSet ((Finset.univ : Finset T) : Set T) := by simp [IsUpperSet]
  have hbound : height Finset.univ ≤ Fintype.card T := by
    rw [heval Finset.univ htop]
    exact (G.level_le _ (line_isSchur k T _ htop)).trans hL
  rw [← heval U hU]
  exact UpperSetHeight.height_eq_card height hstep hbound U hU

end MagnitudeConjecture.PosetSpace
