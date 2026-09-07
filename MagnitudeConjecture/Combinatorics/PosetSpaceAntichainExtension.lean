import MagnitudeConjecture.Combinatorics.PosetSpaceThreeAntichain

/-!
# Reverse linear extensions with a consecutive antichain block

This file constructs the order extension invoked in the equality argument of
the frozen manuscript: any specified three-element antichain can be made a
consecutive block in a reverse linear extension.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

/-- Three specified elements are pairwise incomparable. -/
structure IsThreeAntichain {T : Type u} [PartialOrder T] (a b c : T) : Prop where
  not_ab : ¬a ≤ b
  not_ba : ¬b ≤ a
  not_ac : ¬a ≤ c
  not_ca : ¬c ≤ a
  not_bc : ¬b ≤ c
  not_cb : ¬c ≤ b

namespace IsThreeAntichain

variable {T : Type u} [PartialOrder T] {a b c : T}

theorem ne_ab (H : IsThreeAntichain a b c) : a ≠ b := by
  intro h
  subst b
  exact H.not_ab le_rfl

theorem ne_ac (H : IsThreeAntichain a b c) : a ≠ c := by
  intro h
  subst c
  exact H.not_ac le_rfl

theorem ne_bc (H : IsThreeAntichain a b c) : b ≠ c := by
  intro h
  subst c
  exact H.not_bc le_rfl

end IsThreeAntichain

section Rank

variable {T : Type u} [PartialOrder T]

local instance : DecidableEq T := Classical.decEq T
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Elements forced before the antichain block in a reverse extension are
those strictly above at least one of its elements. -/
def aboveThree (a b c x : T) : Prop :=
  a < x ∨ b < x ∨ c < x

/-- Five-layer rank: elements above the antichain, the three specified
elements in order, and all remaining elements. -/
def antichainBlockRank (a b c x : T) : ℕ :=
  if aboveThree a b c x then 0
  else if x = a then 1
  else if x = b then 2
  else if x = c then 3
  else 4

theorem not_aboveThree_a {a b c : T} (H : IsThreeAntichain a b c) :
    ¬aboveThree a b c a := by
  rintro (haa | hba | hca)
  · exact (lt_irrefl a) haa
  · exact H.not_ba hba.le
  · exact H.not_ca hca.le

theorem not_aboveThree_b {a b c : T} (H : IsThreeAntichain a b c) :
    ¬aboveThree a b c b := by
  rintro (hab | hbb | hcb)
  · exact H.not_ab hab.le
  · exact (lt_irrefl b) hbb
  · exact H.not_cb hcb.le

theorem not_aboveThree_c {a b c : T} (H : IsThreeAntichain a b c) :
    ¬aboveThree a b c c := by
  rintro (hac | hbc | hcc)
  · exact H.not_ac hac.le
  · exact H.not_bc hbc.le
  · exact (lt_irrefl c) hcc

@[simp]
theorem antichainBlockRank_a {a b c : T} (H : IsThreeAntichain a b c) :
    antichainBlockRank a b c a = 1 := by
  simp [antichainBlockRank, not_aboveThree_a H]

@[simp]
theorem antichainBlockRank_b {a b c : T} (H : IsThreeAntichain a b c) :
    antichainBlockRank a b c b = 2 := by
  simp [antichainBlockRank, not_aboveThree_b H, H.ne_ab.symm]

@[simp]
theorem antichainBlockRank_c {a b c : T} (H : IsThreeAntichain a b c) :
    antichainBlockRank a b c c = 3 := by
  simp [antichainBlockRank, not_aboveThree_c H, H.ne_ac.symm,
    H.ne_bc.symm]

/-- The block rank reverses the original partial order. -/
theorem antichainBlockRank_anti {a b c x y : T}
    (H : IsThreeAntichain a b c) (hxy : y ≤ x) :
    antichainBlockRank a b c x ≤ antichainBlockRank a b c y := by
  by_cases hxabove : aboveThree a b c x
  · simp [antichainBlockRank, hxabove]
  have hyabove : ¬aboveThree a b c y := by
    intro hy
    rcases hy with hay | hby | hcy
    · have hax : a < x := lt_of_lt_of_le hay hxy
      exact hxabove (Or.inl hax)
    · have hbx : b < x := lt_of_lt_of_le hby hxy
      exact hxabove (Or.inr (Or.inl hbx))
    · have hcx : c < x := lt_of_lt_of_le hcy hxy
      exact hxabove (Or.inr (Or.inr hcx))
  by_cases hxa : x = a
  · subst x
    rw [antichainBlockRank_a H]
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
      by_cases hyc : y = c <;>
        simp [antichainBlockRank, hyabove, hya, hyb, hyc,
          not_aboveThree_a H, not_aboveThree_b H, not_aboveThree_c H,
          H.ne_ab.symm, H.ne_ac.symm, H.ne_bc.symm]
  by_cases hxb : x = b
  · subst x
    have hyna : y ≠ a := by
      intro hya
      subst y
      exact H.not_ab hxy
    rw [antichainBlockRank_b H]
    by_cases hyb : y = b <;> by_cases hyc : y = c <;>
      simp [antichainBlockRank, hyabove, hyna, hyb, hyc,
        not_aboveThree_b H, not_aboveThree_c H,
        H.ne_ab.symm, H.ne_ac.symm, H.ne_bc.symm]
  by_cases hxc : x = c
  · subst x
    have hyna : y ≠ a := by
      intro hya
      subst y
      exact H.not_ac hxy
    have hynb : y ≠ b := by
      intro hyb
      subst y
      exact H.not_bc hxy
    rw [antichainBlockRank_c H]
    by_cases hyc : y = c <;>
      simp [antichainBlockRank, hyabove, hyna, hynb, hyc,
        not_aboveThree_c H, H.ne_ac.symm, H.ne_bc.symm]
  · have hyna : y ≠ a := by
      intro hya
      subst y
      have hlt : a < x := lt_of_le_of_ne hxy (Ne.symm hxa)
      exact hxabove (Or.inl hlt)
    have hynb : y ≠ b := by
      intro hyb
      subst y
      have hlt : b < x := lt_of_le_of_ne hxy (Ne.symm hxb)
      exact hxabove (Or.inr (Or.inl hlt))
    have hync : y ≠ c := by
      intro hyc
      subst y
      have hlt : c < x := lt_of_le_of_ne hxy (Ne.symm hxc)
      exact hxabove (Or.inr (Or.inr hlt))
    simp [antichainBlockRank, hxabove, hyabove, hxa, hxb, hxc,
      hyna, hynb, hync]

/-- Lexicographic refinement of the reverse partial order by the five-layer
block rank. -/
def antichainBlockRel (a b c x y : T) : Prop :=
  antichainBlockRank a b c x < antichainBlockRank a b c y ∨
    (antichainBlockRank a b c x = antichainBlockRank a b c y ∧ y ≤ x)

instance antichainBlockRel_isPartialOrder (a b c : T) :
    IsPartialOrder T (antichainBlockRel a b c) where
  refl x := Or.inr ⟨rfl, le_rfl⟩
  trans x y z hxy hyz := by
    rcases hxy with hxy | ⟨hrxy, hyx⟩
    · rcases hyz with hyz | ⟨hryz, hzy⟩
      · exact Or.inl (lt_trans hxy hyz)
      · exact Or.inl (hryz ▸ hxy)
    · rcases hyz with hyz | ⟨hryz, hzy⟩
      · exact Or.inl (hrxy ▸ hyz)
      · exact Or.inr ⟨hrxy.trans hryz, le_trans hzy hyx⟩
  antisymm x y hxy hyx := by
    rcases hxy with hxy | ⟨hrxy, hyx'⟩
    · rcases hyx with hyx | ⟨hryx, hxy'⟩ <;> omega
    · rcases hyx with hyx | ⟨hryx, hxy'⟩
      · omega
      · exact le_antisymm hxy' hyx'

theorem antichainBlockRel_of_ge {a b c x y : T}
    (H : IsThreeAntichain a b c) (hxy : y ≤ x) :
    antichainBlockRel a b c x y := by
  have hrank := antichainBlockRank_anti H hxy
  rcases lt_or_eq_of_le hrank with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hxy⟩

end Rank

section Extension

variable {T : Type u} [PartialOrder T] [Fintype T]

/-- A wrapped copy of `T` on which the block-refined reverse order can be
installed without replacing the original order on `T`. -/
structure AntichainBlockCarrier (a b c : T) where
  value : T

namespace AntichainBlockCarrier

variable (a b c : T)

/-- Forgetting the wrapper is an equivalence with the original poset. -/
def equiv : AntichainBlockCarrier a b c ≃ T where
  toFun := value
  invFun := fun x ↦ ⟨x⟩
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by intro x; rfl

instance : Fintype (AntichainBlockCarrier a b c) :=
  Fintype.ofEquiv T (equiv a b c).symm

/-- The partial order on the wrapped carrier is the five-layer refinement of
the reverse order. -/
instance : PartialOrder (AntichainBlockCarrier a b c) where
  le x y := antichainBlockRel a b c x.value y.value
  le_refl x := (antichainBlockRel_isPartialOrder a b c).refl x.value
  le_trans x y z hxy hyz :=
    (antichainBlockRel_isPartialOrder a b c).trans
      x.value y.value z.value hxy hyz
  le_antisymm x y hxy hyx := by
    cases x with
    | mk x =>
        cases y with
        | mk y =>
            congr
            exact (antichainBlockRel_isPartialOrder a b c).antisymm x y hxy hyx

end AntichainBlockCarrier

/-- The chosen linear extension of the block-refined reverse order. -/
abbrev AntichainBlockLinearExtension (a b c : T) :=
  LinearExtension (AntichainBlockCarrier a b c)

/-- Forgetting both order-extension wrappers recovers the original poset. -/
def antichainBlockLinearExtensionEquiv (a b c : T) :
    AntichainBlockLinearExtension a b c ≃ T where
  toFun := fun x ↦ x.value
  invFun := fun x ↦ ⟨x⟩
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by intro x; rfl

instance (a b c : T) : Fintype (AntichainBlockLinearExtension a b c) :=
  Fintype.ofEquiv T (antichainBlockLinearExtensionEquiv a b c).symm

/-- The increasing enumeration of the chosen block-refined linear order. -/
def antichainBlockOrderIso (a b c : T) :
    Fin (Fintype.card T) ≃o AntichainBlockLinearExtension a b c :=
  Fintype.orderIsoFinOfCardEq _
    (Fintype.card_congr (antichainBlockLinearExtensionEquiv a b c))

/-- The position of an original element in the block-refined linear
extension. -/
def antichainBlockIndex (a b c x : T) : Fin (Fintype.card T) :=
  (antichainBlockOrderIso a b c).symm
    ((antichainBlockLinearExtensionEquiv a b c).symm x)

theorem antichainBlockIndex_le_of_rel {a b c x y : T}
    (hxy : antichainBlockRel a b c x y) :
    antichainBlockIndex a b c x ≤ antichainBlockIndex a b c y := by
  apply (antichainBlockOrderIso a b c).symm.monotone
  change
    (@toLinearExtension (AntichainBlockCarrier a b c)
      (AntichainBlockCarrier.instPartialOrder a b c) ⟨x⟩) ≤
    (@toLinearExtension (AntichainBlockCarrier a b c)
      (AntichainBlockCarrier.instPartialOrder a b c) ⟨y⟩)
  exact (@toLinearExtension (AntichainBlockCarrier a b c)
    (AntichainBlockCarrier.instPartialOrder a b c)).monotone hxy

theorem antichainBlockIndex_lt_of_rel {a b c x y : T}
    (hxy : antichainBlockRel a b c x y) (hne : x ≠ y) :
    antichainBlockIndex a b c x < antichainBlockIndex a b c y := by
  apply (antichainBlockOrderIso a b c).symm.strictMono
  apply lt_of_le_of_ne
  · change
      (@toLinearExtension (AntichainBlockCarrier a b c)
        (AntichainBlockCarrier.instPartialOrder a b c) ⟨x⟩) ≤
      (@toLinearExtension (AntichainBlockCarrier a b c)
        (AntichainBlockCarrier.instPartialOrder a b c) ⟨y⟩)
    exact (@toLinearExtension (AntichainBlockCarrier a b c)
      (AntichainBlockCarrier.instPartialOrder a b c)).monotone hxy
  · intro heq
    apply hne
    exact congrArg (antichainBlockLinearExtensionEquiv a b c) heq

omit [Fintype T] in
/-- Every element outside the chosen triple lies wholly before or wholly
after the block in the refined partial order. -/
theorem antichainBlockRel_other {a b c x : T}
    (H : IsThreeAntichain a b c) (hxa : x ≠ a) (hxb : x ≠ b)
    (hxc : x ≠ c) :
    antichainBlockRel a b c x a ∨ antichainBlockRel a b c c x := by
  classical
  by_cases habove : aboveThree a b c x
  · left
    apply Or.inl
    rw [antichainBlockRank_a H]
    simp [antichainBlockRank, habove]
  · right
    apply Or.inl
    rw [antichainBlockRank_c H]
    simp [antichainBlockRank, habove, hxa, hxb, hxc]

/-- The reverse enumeration obtained by linearly extending the block-refined
order. -/
def antichainBlockReverseEnumeration {a b c : T}
    (H : IsThreeAntichain a b c) : ReverseEnumeration T where
  equiv := (antichainBlockOrderIso a b c).toEquiv.trans
    (antichainBlockLinearExtensionEquiv a b c)
  index_anti := by
    intro s t hst
    apply (antichainBlockOrderIso a b c).symm.monotone
    exact (@toLinearExtension (AntichainBlockCarrier a b c)
      (AntichainBlockCarrier.instPartialOrder a b c)).monotone
        (antichainBlockRel_of_ge H hst)

@[simp]
theorem antichainBlockReverseEnumeration_index {a b c : T}
    (H : IsThreeAntichain a b c) (x : T) :
    ReverseEnumeration.index T (antichainBlockReverseEnumeration H) x =
      antichainBlockIndex a b c x :=
  rfl

/-- In the selected reverse enumeration, `b` immediately follows `a`. -/
theorem antichainBlockIndex_b_eq_add_one {a b c : T}
    (H : IsThreeAntichain a b c) :
    (antichainBlockIndex a b c b).val =
      (antichainBlockIndex a b c a).val + 1 := by
  have hab : antichainBlockIndex a b c a < antichainBlockIndex a b c b := by
    apply antichainBlockIndex_lt_of_rel
    · apply Or.inl
      rw [antichainBlockRank_a H, antichainBlockRank_b H]
      omega
    · exact H.ne_ab
  by_contra hne
  have hgap : (antichainBlockIndex a b c a).val + 1 <
      (antichainBlockIndex a b c b).val := by
    omega
  let j : Fin (Fintype.card T) :=
    ⟨(antichainBlockIndex a b c a).val + 1,
      lt_trans hgap (antichainBlockIndex a b c b).isLt⟩
  let x : T := (antichainBlockLinearExtensionEquiv a b c)
    (antichainBlockOrderIso a b c j)
  have hxindex : antichainBlockIndex a b c x = j := by
    simp [antichainBlockIndex, x]
  have hxa : x ≠ a := by
    intro h
    have hv := congrArg Fin.val hxindex
    rw [h] at hv
    dsimp [j] at hv
    omega
  have hxb : x ≠ b := by
    intro h
    have hv := congrArg Fin.val hxindex
    rw [h] at hv
    dsimp [j] at hv
    omega
  have hbc : antichainBlockIndex a b c b <
      antichainBlockIndex a b c c := by
    apply antichainBlockIndex_lt_of_rel
    · apply Or.inl
      rw [antichainBlockRank_b H, antichainBlockRank_c H]
      omega
    · exact H.ne_bc
  have hxc : x ≠ c := by
    intro h
    have hv := congrArg Fin.val hxindex
    rw [h] at hv
    dsimp [j] at hv
    omega
  rcases antichainBlockRel_other H hxa hxb hxc with hbefore | hafter
  · have hle := antichainBlockIndex_le_of_rel hbefore
    rw [hxindex] at hle
    change (antichainBlockIndex a b c a).val + 1 ≤
      (antichainBlockIndex a b c a).val at hle
    omega
  · have hle := antichainBlockIndex_le_of_rel hafter
    rw [hxindex] at hle
    change (antichainBlockIndex a b c c).val ≤
      (antichainBlockIndex a b c a).val + 1 at hle
    omega

/-- In the selected reverse enumeration, `c` immediately follows `b`. -/
theorem antichainBlockIndex_c_eq_add_one {a b c : T}
    (H : IsThreeAntichain a b c) :
    (antichainBlockIndex a b c c).val =
      (antichainBlockIndex a b c b).val + 1 := by
  have hab : antichainBlockIndex a b c a < antichainBlockIndex a b c b := by
    apply antichainBlockIndex_lt_of_rel
    · apply Or.inl
      rw [antichainBlockRank_a H, antichainBlockRank_b H]
      omega
    · exact H.ne_ab
  have hbc : antichainBlockIndex a b c b <
      antichainBlockIndex a b c c := by
    apply antichainBlockIndex_lt_of_rel
    · apply Or.inl
      rw [antichainBlockRank_b H, antichainBlockRank_c H]
      omega
    · exact H.ne_bc
  by_contra hne
  have hgap : (antichainBlockIndex a b c b).val + 1 <
      (antichainBlockIndex a b c c).val := by
    omega
  let j : Fin (Fintype.card T) :=
    ⟨(antichainBlockIndex a b c b).val + 1,
      lt_trans hgap (antichainBlockIndex a b c c).isLt⟩
  let x : T := (antichainBlockLinearExtensionEquiv a b c)
    (antichainBlockOrderIso a b c j)
  have hxindex : antichainBlockIndex a b c x = j := by
    simp [antichainBlockIndex, x]
  have hxa : x ≠ a := by
    intro h
    have hv := congrArg Fin.val hxindex
    rw [h] at hv
    dsimp [j] at hv
    omega
  have hxb : x ≠ b := by
    intro h
    have hv := congrArg Fin.val hxindex
    rw [h] at hv
    dsimp [j] at hv
    omega
  have hxc : x ≠ c := by
    intro h
    have hv := congrArg Fin.val hxindex
    rw [h] at hv
    dsimp [j] at hv
    omega
  rcases antichainBlockRel_other H hxa hxb hxc with hbefore | hafter
  · have hle := antichainBlockIndex_le_of_rel hbefore
    rw [hxindex] at hle
    change (antichainBlockIndex a b c b).val + 1 ≤
      (antichainBlockIndex a b c a).val at hle
    omega
  · have hle := antichainBlockIndex_le_of_rel hafter
    rw [hxindex] at hle
    change (antichainBlockIndex a b c c).val ≤
      (antichainBlockIndex a b c b).val + 1 at hle
    omega

/-- Any chosen three-element antichain occurs as a consecutive block in a
selectable reverse linear enumeration. -/
theorem exists_reverseEnumeration_three_consecutive {a b c : T}
    (H : IsThreeAntichain a b c) :
    ∃ (R : ReverseEnumeration T) (q : ℕ),
      q + 2 < Fintype.card T ∧
      (ReverseEnumeration.index T R a).val = q ∧
      (ReverseEnumeration.index T R b).val = q + 1 ∧
      (ReverseEnumeration.index T R c).val = q + 2 := by
  refine ⟨antichainBlockReverseEnumeration H,
    (antichainBlockIndex a b c a).val, ?_⟩
  rw [antichainBlockReverseEnumeration_index,
    antichainBlockReverseEnumeration_index,
    antichainBlockReverseEnumeration_index]
  have hab := antichainBlockIndex_b_eq_add_one H
  have hbc := antichainBlockIndex_c_eq_add_one H
  constructor
  · omega
  · exact ⟨rfl, hab, by omega⟩

end Extension

end MagnitudeConjecture.PosetSpace
