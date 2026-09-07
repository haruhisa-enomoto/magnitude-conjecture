import MagnitudeConjecture.Combinatorics.PosetSpaceAntichainExtension
import MagnitudeConjecture.Combinatorics.PosetSpaceSelectableSupport

/-!
# The unconditional three-antichain obstruction

This file combines the selectable consecutive-antichain extension with the
global three-line construction and selectable support chain.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

open CategoryTheory
open CategoryTheory.Limits

section Field

variable (k : Type u) [Field k]
variable {T : Type u} [PartialOrder T] [Fintype T]

/-- A consecutive three-position block in a selectable reverse enumeration
which is an antichain in the original poset. -/
structure ConsecutiveAntichainBlockFor (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T) : Prop where
  le_eq_of_mem_block : ∀ {s t : T},
    q ≤ (ReverseEnumeration.index T R s).val →
    (ReverseEnumeration.index T R s).val ≤ q + 2 →
    q ≤ (ReverseEnumeration.index T R t).val →
    (ReverseEnumeration.index T R t).val ≤ q + 2 →
    s ≤ t → s = t

/-- Three prescribed consecutive antichain elements certify that their
positions form an antichain block. -/
theorem consecutiveAntichainBlockForOfThree
    (R : ReverseEnumeration T) {a b c : T} (H : IsThreeAntichain a b c)
    (q : ℕ) (hq : q + 2 < Fintype.card T)
    (ha : (ReverseEnumeration.index T R a).val = q)
    (hb : (ReverseEnumeration.index T R b).val = q + 1)
    (hc : (ReverseEnumeration.index T R c).val = q + 2) :
    ConsecutiveAntichainBlockFor R q hq where
  le_eq_of_mem_block := by
    intro s t hslo hshi htlo hthi hst
    have hspos : (ReverseEnumeration.index T R s).val = q ∨
        (ReverseEnumeration.index T R s).val = q + 1 ∨
        (ReverseEnumeration.index T R s).val = q + 2 := by
      omega
    have htpos : (ReverseEnumeration.index T R t).val = q ∨
        (ReverseEnumeration.index T R t).val = q + 1 ∨
        (ReverseEnumeration.index T R t).val = q + 2 := by
      omega
    have hs : s = a ∨ s = b ∨ s = c := by
      rcases hspos with hspos | hspos | hspos
      · left
        apply ReverseEnumeration.index_injective T R
        apply Fin.ext
        omega
      · right; left
        apply ReverseEnumeration.index_injective T R
        apply Fin.ext
        omega
      · right; right
        apply ReverseEnumeration.index_injective T R
        apply Fin.ext
        omega
    have ht : t = a ∨ t = b ∨ t = c := by
      rcases htpos with htpos | htpos | htpos
      · left
        apply ReverseEnumeration.index_injective T R
        apply Fin.ext
        omega
      · right; left
        apply ReverseEnumeration.index_injective T R
        apply Fin.ext
        omega
      · right; right
        apply ReverseEnumeration.index_injective T R
        apply Fin.ext
        omega
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · rfl
    · exact (H.not_ab hst).elim
    · exact (H.not_ac hst).elim
    · exact (H.not_ba hst).elim
    · rfl
    · exact (H.not_bc hst).elim
    · exact (H.not_ca hst).elim
    · exact (H.not_cb hst).elim
    · rfl

/-- The global full/axes/diagonal/zero plane for a block in a selectable
enumeration. -/
def blockPlaneSubspaceFor (R : ReverseEnumeration T) (q : ℕ) (t : T) :
    Submodule k (k × k) :=
  if (ReverseEnumeration.index T R t).val < q then ⊤
  else if (ReverseEnumeration.index T R t).val = q then firstAxis k
  else if (ReverseEnumeration.index T R t).val = q + 1 then secondAxis k
  else if (ReverseEnumeration.index T R t).val = q + 2 then diagonal k
  else ⊥

/-- The global two-dimensional `T`-space for a selectable consecutive
antichain block. -/
abbrev blockThreeLinePlaneFor (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) : Obj k T where
  carrier := k × k
  subspace := blockPlaneSubspaceFor k R q
  monotone_subspace := by
    intro s t hst
    have hindex : (ReverseEnumeration.index T R t).val ≤
        (ReverseEnumeration.index T R s).val := R.index_anti hst
    change blockPlaneSubspaceFor k R q s ≤ blockPlaneSubspaceFor k R q t
    by_cases htpre : (ReverseEnumeration.index T R t).val < q
    · have httop : blockPlaneSubspaceFor k R q t = ⊤ := by
        simp [blockPlaneSubspaceFor, htpre]
      rw [httop]
      exact le_top
    by_cases hsafter : q + 2 < (ReverseEnumeration.index T R s).val
    · have hsnpre : ¬(ReverseEnumeration.index T R s).val < q := by omega
      have hs0 : (ReverseEnumeration.index T R s).val ≠ q := by omega
      have hs1 : (ReverseEnumeration.index T R s).val ≠ q + 1 := by omega
      have hs2 : (ReverseEnumeration.index T R s).val ≠ q + 2 := by omega
      have hsbot : blockPlaneSubspaceFor k R q s = ⊥ := by
        simp [blockPlaneSubspaceFor, hsnpre, hs0, hs1, hs2]
      rw [hsbot]
      exact bot_le
    · have hslo : q ≤ (ReverseEnumeration.index T R s).val := by omega
      have hshi : (ReverseEnumeration.index T R s).val ≤ q + 2 := by omega
      have htlo : q ≤ (ReverseEnumeration.index T R t).val := by omega
      have hthi : (ReverseEnumeration.index T R t).val ≤ q + 2 := by omega
      have heq : s = t :=
        D.le_eq_of_mem_block hslo hshi htlo hthi hst
      subst t
      exact le_rfl

/-- The selected-block map `1 ↦ e₁`. -/
def blockInMapFor (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    supportLineFor k T R
        ⟨q + 1, Nat.lt_succ_iff.mpr (Nat.le_of_lt (by omega))⟩ ⟶
      blockThreeLinePlaneFor k R q hq D where
  linear :=
    { toFun := fun x ↦ (x, 0)
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
  map_subspace := by
    intro t x hx
    by_cases hpre : (ReverseEnumeration.index T R t).val < q
    · change (x, 0) ∈ blockPlaneSubspaceFor k R q t
      simp [blockPlaneSubspaceFor, hpre]
    by_cases heq : (ReverseEnumeration.index T R t).val = q
    · change (x, 0) ∈ blockPlaneSubspaceFor k R q t
      simp [blockPlaneSubspaceFor, heq, firstAxis]
    · have hx0 : x = 0 := by
        simpa [supportLineFor, supportAtFor, show
          ¬(ReverseEnumeration.index T R t).val ≤ q by omega] using hx
      subst x
      exact Submodule.zero_mem _

/-- The selected-block map `(x,y) ↦ x-y`. -/
def blockOutMapFor (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    blockThreeLinePlaneFor k R q hq D ⟶
      supportLineFor k T R
        ⟨q + 2, Nat.lt_succ_iff.mpr (Nat.le_of_lt hq)⟩ where
  linear :=
    { toFun := fun x ↦ x.1 - x.2
      map_add' := by
        intros
        simp only [Prod.fst_add, Prod.snd_add]
        abel
      map_smul' := by intros; simp [mul_sub] }
  map_subspace := by
    intro t x hx
    change x.1 - x.2 ∈
      (supportLineFor k T R
        ⟨q + 2, Nat.lt_succ_iff.mpr (Nat.le_of_lt hq)⟩).subspace t
    by_cases htarget : (ReverseEnumeration.index T R t).val < q + 2
    · simp [supportLineFor, supportAtFor, htarget]
    · have htargetle : ¬(ReverseEnumeration.index T R t).val ≤ q + 1 := by
        omega
      have hzero : x.1 - x.2 = 0 := by
        by_cases heq : (ReverseEnumeration.index T R t).val = q + 2
        · have hxdiag : x.1 = x.2 := by
            change x ∈ blockPlaneSubspaceFor k R q t at hx
            simpa [blockPlaneSubspaceFor, heq] using hx
          simpa [hxdiag]
        · have hx0 : x = 0 := by
            change x ∈ blockPlaneSubspaceFor k R q t at hx
            have hpre : ¬(ReverseEnumeration.index T R t).val < q := by omega
            have h0 : (ReverseEnumeration.index T R t).val ≠ q := by omega
            have h1 : (ReverseEnumeration.index T R t).val ≠ q + 1 := by omega
            simpa [blockPlaneSubspaceFor, hpre, h0, h1, heq] using hx
          subst x
          simp
      simpa [supportLineFor, supportAtFor, htargetle, hzero]

theorem blockInMapFor_ne_zero (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    blockInMapFor k R q hq D ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear (1 : k)) hzero
  change ((1 : k), 0) = (0, 0) at h
  exact one_ne_zero (congrArg Prod.fst h)

theorem blockOutMapFor_ne_zero (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    blockOutMapFor k R q hq D ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear ((1 : k), 0)) hzero
  have hcalc : (blockOutMapFor k R q hq D).linear ((1 : k), 0) = 1 := by
    simp [blockOutMapFor]
  rw [hcalc, zero_linear, LinearMap.zero_apply] at h
  exact one_ne_zero h

theorem blockInMapFor_not_isIso (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    ¬IsIso (blockInMapFor k R q hq D) := by
  apply not_isIso_of_finrank_ne k
  simp only [Module.finrank_self, Module.finrank_prod]
  omega

theorem blockOutMapFor_not_isIso (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    ¬IsIso (blockOutMapFor k R q hq D) := by
  apply not_isIso_of_finrank_ne k
  simp only [Module.finrank_self, Module.finrank_prod]
  omega

/-- The selectable global three-line plane is Schur. -/
theorem blockThreeLinePlaneFor_isSchur (R : ReverseEnumeration T) (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    IsSchur k T (blockThreeLinePlaneFor k R q hq D) := by
  let t₀ : T := R.equiv ⟨q, by omega⟩
  let t₁ : T := R.equiv ⟨q + 1, by omega⟩
  let t₂ : T := R.equiv ⟨q + 2, hq⟩
  have hsub₀ : (blockThreeLinePlaneFor k R q hq D).subspace t₀ =
      firstAxis k := by
    change blockPlaneSubspaceFor k R q t₀ = firstAxis k
    simp [blockPlaneSubspaceFor, t₀, ReverseEnumeration.index_equiv]
  have hsub₁ : (blockThreeLinePlaneFor k R q hq D).subspace t₁ =
      secondAxis k := by
    change blockPlaneSubspaceFor k R q t₁ = secondAxis k
    simp [blockPlaneSubspaceFor, t₁, ReverseEnumeration.index_equiv]
  have hsub₂ : (blockThreeLinePlaneFor k R q hq D).subspace t₂ =
      diagonal k := by
    change blockPlaneSubspaceFor k R q t₂ = diagonal k
    simp [blockPlaneSubspaceFor, t₂, ReverseEnumeration.index_equiv]
  constructor
  · refine ⟨((1 : k), 0), ?_⟩
    intro hzero
    exact one_ne_zero (congrArg Prod.fst hzero)
  · intro f
    let v₁ : k × k := f.linear ((1 : k), 0)
    let v₂ : k × k := f.linear (0, (1 : k))
    have hv₁₂ : v₁.2 = 0 := by
      have hmem := f.map_subspace t₀ ((1 : k), 0) (by
        rw [hsub₀]
        simp [firstAxis])
      rw [hsub₀] at hmem
      exact hmem
    have hv₂₁ : v₂.1 = 0 := by
      have hmem := f.map_subspace t₁ (0, (1 : k)) (by
        rw [hsub₁]
        simp [secondAxis])
      rw [hsub₁] at hmem
      exact hmem
    have hvdiag :
        (f.linear ((1 : k), 1)).1 = (f.linear ((1 : k), 1)).2 := by
      have hmem := f.map_subspace t₂ ((1 : k), 1) (by
        rw [hsub₂]
        simp [diagonal])
      rw [hsub₂] at hmem
      exact hmem
    have hsum : f.linear ((1 : k), 1) = v₁ + v₂ := by
      change f.linear ((1 : k), 1) =
        f.linear ((1 : k), 0) + f.linear (0, (1 : k))
      rw [← LinearMap.map_add]
      congr 1
      ext <;> simp
    have hv₁₁_eq_v₂₂ : v₁.1 = v₂.2 := by
      rw [hsum] at hvdiag
      simpa [hv₁₂, hv₂₁] using hvdiag
    refine ⟨v₁.1, ?_⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hdecomp : (x, y) =
        x • ((1 : k), 0) + y • (0, (1 : k)) := by
      ext <;> simp
    rw [hdecomp, LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul]
    apply Prod.ext
    · simp [v₁, v₂, hv₂₁, mul_comm]
    · simp [v₁, v₂, hv₁₂, hv₁₁_eq_v₂₂, mul_comm]

/-- A selected consecutive block constructs the selectable Schur detour. -/
def ConsecutiveAntichainBlockFor.selectableSchurDetour
    (R : ReverseEnumeration T) (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlockFor R q hq) :
    SelectableSchurDetour k T R q hq where
  middle := blockThreeLinePlaneFor k R q hq D
  middle_schur := blockThreeLinePlaneFor_isSchur k R q hq D
  inMap := blockInMapFor k R q hq D
  outMap := blockOutMapFor k R q hq D
  inMap_ne_zero := blockInMapFor_ne_zero k R q hq D
  outMap_ne_zero := blockOutMapFor_ne_zero k R q hq D
  inMap_not_isIso := blockInMapFor_not_isIso k R q hq D
  outMap_not_isIso := blockOutMapFor_not_isIso k R q hq D

/-- The manuscript's strict realization bound whenever the poset contains a
three-element antichain. -/
theorem card_add_one_le_of_threeAntichain {a b c : T} {L : ℕ}
    (H : IsThreeAntichain a b c)
    (G : PositiveGrading (Obj k T) (IsSchur k T) L) :
    Fintype.card T + 1 ≤ L := by
  obtain ⟨R, q, hq, ha, hb, hc⟩ :=
    exists_reverseEnumeration_three_consecutive H
  let D : ConsecutiveAntichainBlockFor R q hq :=
    consecutiveAntichainBlockForOfThree R H q hq ha hb hc
  exact card_add_one_le_of_selectableSchurDetour k T R G
    (D.selectableSchurDetour k R q hq)

end Field

end MagnitudeConjecture.PosetSpace
