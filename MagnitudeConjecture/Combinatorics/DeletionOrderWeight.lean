import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Weights from finite deletion orders

For a finite control set `Ω`, the frozen magnitude proof assigns a subset
`S ⊆ Ω` the probability that precisely the elements of `S` precede one
distinguished object in a uniformly ordered copy of `insert x Ω`.  This file
records the coefficient and the positivity facts used by the equality case.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MagnitudeConjecture.DeletionOrderAverage

universe u

variable {α : Type u}

/-- The coefficient attached to a predecessor set `S` inside `Ω`.

The intended use has `S ⊆ Ω`; keeping the definition total is convenient for
finite sums. -/
def weight (Ω S : Finset α) : ℚ :=
  (S.card.factorial * (Ω.card - S.card).factorial : ℚ) /
    (Ω.card + 1).factorial

/-- Every predecessor-set coefficient is strictly positive. -/
theorem weight_pos (Ω S : Finset α) : 0 < weight Ω S := by
  unfold weight
  positivity

/-- The empty predecessor set has coefficient `1 / (|Ω| + 1)`. -/
theorem weight_empty (Ω : Finset α) :
    weight Ω ∅ = 1 / (Ω.card + 1 : ℚ) := by
  have hfac : (Ω.card.factorial : ℚ) ≠ 0 := by positivity
  simp only [weight, Finset.card_empty, Nat.factorial_zero, Nat.cast_mul,
    Nat.cast_one, one_mul, Nat.sub_zero, Nat.factorial_succ, Nat.cast_add,
    div_eq_mul_inv]
  field_simp

/-- The full predecessor set has the same coefficient as the empty set. -/
theorem weight_self (Ω : Finset α) :
    weight Ω Ω = 1 / (Ω.card + 1 : ℚ) := by
  have hfac : (Ω.card.factorial : ℚ) ≠ 0 := by positivity
  simp only [weight, Nat.sub_self, Nat.factorial_zero, mul_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, div_eq_mul_inv]
  field_simp

/-- In particular the coefficient used to recover the undeleted local term
from a zero weighted average is nonzero. -/
theorem weight_empty_ne_zero (Ω : Finset α) : weight Ω ∅ ≠ 0 :=
  ne_of_gt (weight_pos Ω ∅)

/-- Pairing predecessor sets according to whether a newly adjoined object is
present recovers the coefficient for the smaller control set. -/
theorem weight_insert_pair [DecidableEq α]
    (Ω S : Finset α) (a : α) (ha : a ∉ Ω) (hS : S ⊆ Ω) :
    weight (insert a Ω) S + weight (insert a Ω) (insert a S) = weight Ω S := by
  have haS : a ∉ S := fun h ↦ ha (hS h)
  have hcard : S.card ≤ Ω.card := Finset.card_le_card hS
  have hsub1 : (Ω.card + 1) - S.card = (Ω.card - S.card) + 1 := by omega
  have hsub2 : (Ω.card + 1) - (S.card + 1) = Ω.card - S.card := by omega
  simp only [weight, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem haS, hsub1, hsub2, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hk : (S.card.factorial : ℚ) ≠ 0 := by positivity
  have hm : ((Ω.card - S.card).factorial : ℚ) ≠ 0 := by positivity
  have hn : (Ω.card + 1 : ℚ) ≠ 0 := by positivity
  have hn2 : (Ω.card + 2 : ℚ) ≠ 0 := by positivity
  field_simp
  norm_cast
  omega

/-- The predecessor-set coefficients form a probability distribution on the
powerset of the finite control set. -/
theorem sum_weight_powerset [DecidableEq α] (Ω : Finset α) :
    ∑ S ∈ Ω.powerset, weight Ω S = 1 := by
  classical
  induction Ω using Finset.induction_on with
  | empty => norm_num [weight]
  | @insert a Ω ha ih =>
      have hdisjoint : Disjoint Ω.powerset
          (Ω.powerset.image (fun S ↦ insert a S)) := by
        rw [Finset.disjoint_left]
        intro S hS hSa
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hSa
        have hsub : insert a T ⊆ Ω := Finset.mem_powerset.mp hS
        exact ha (hsub (Finset.mem_insert_self a T))
      have hinjective : Set.InjOn (fun S : Finset α ↦ insert a S)
          (Ω.powerset : Set (Finset α)) := by
        intro S hS T hT hEq
        have hsubS : S ⊆ Ω := Finset.mem_powerset.mp hS
        have hsubT : T ⊆ Ω := Finset.mem_powerset.mp hT
        apply Finset.ext
        intro x
        by_cases hx : x = a
        · subst x
          simp only [show a ∉ S from fun h ↦ ha (hsubS h),
            show a ∉ T from fun h ↦ ha (hsubT h)]
        · have hxEq := congrArg (fun U : Finset α ↦ x ∈ U) hEq
          simpa [hx] using hxEq
      rw [Finset.powerset_insert, Finset.sum_union hdisjoint,
        Finset.sum_image hinjective]
      rw [← Finset.sum_add_distrib]
      calc
        ∑ S ∈ Ω.powerset,
            (weight (insert a Ω) S + weight (insert a Ω) (insert a S)) =
            ∑ S ∈ Ω.powerset, weight Ω S := by
              apply Finset.sum_congr rfl
              intro S hS
              exact weight_insert_pair Ω S a ha (Finset.mem_powerset.mp hS)
        _ = 1 := ih

/-- Incidences consisting of a distinguished element and a predecessor set
not containing it may instead be indexed by the predecessor set first. -/
def predecessorIncidenceEquiv [DecidableEq α] (Ω : Finset α) :
    (Σ x : {x : α // x ∈ Ω},
      {S : Finset α // S ⊆ Ω.erase x.1}) ≃
    (Σ S : {S : Finset α // S ⊆ Ω},
      {x : α // x ∈ Ω ∧ x ∉ S.1}) where
  toFun p :=
    ⟨⟨p.2.1, fun y hy ↦ (Finset.mem_erase.mp (p.2.2 hy)).2⟩,
      ⟨p.1.1, p.1.2, fun hx ↦
        (Finset.mem_erase.mp (p.2.2 hx)).1 rfl⟩⟩
  invFun p :=
    ⟨⟨p.2.1, p.2.2.1⟩,
      ⟨p.1.1, fun y hy ↦
        Finset.mem_erase.mpr
          ⟨fun hyx ↦ p.2.2.2 (hyx ▸ hy), p.1.2 hy⟩⟩⟩
  left_inv p := by
    rcases p with ⟨x, S⟩
    rfl
  right_inv p := by
    rcases p with ⟨S, x⟩
    rfl

/-- The same incidence may be indexed by the set obtained immediately after
inserting the distinguished element. -/
def successorIncidenceEquiv [DecidableEq α] (Ω : Finset α) :
    (Σ x : {x : α // x ∈ Ω},
      {S : Finset α // S ⊆ Ω.erase x.1}) ≃
    (Σ x : {x : α // x ∈ Ω},
      {U : Finset α // U ⊆ Ω ∧ x.1 ∈ U}) where
  toFun p :=
    ⟨p.1, ⟨insert p.1.1 p.2.1, fun y hy ↦ by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact p.1.2
        · exact (Finset.mem_erase.mp (p.2.2 hy)).2,
      Finset.mem_insert_self _ _⟩⟩
  invFun p :=
    ⟨p.1, ⟨p.2.1.erase p.1.1, fun y hy ↦ by
        have h := Finset.mem_erase.mp hy
        exact Finset.mem_erase.mpr ⟨h.1, p.2.2.1 h.2⟩⟩⟩
  left_inv p := by
    rcases p with ⟨x, S⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact Finset.erase_insert
        (fun hx ↦ (Finset.mem_erase.mp (S.2 hx)).1 rfl)
  right_inv p := by
    rcases p with ⟨x, U⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact Finset.insert_erase U.2.2

/-- Swap the two coordinates after insertion, so successor incidences are
grouped by the resulting subset. -/
def successorIncidenceSwapEquiv (Ω : Finset α) :
    (Σ x : {x : α // x ∈ Ω},
      {U : Finset α // U ⊆ Ω ∧ x.1 ∈ U}) ≃
    (Σ U : {U : Finset α // U ⊆ Ω},
      {x : α // x ∈ U.1}) where
  toFun p := ⟨⟨p.2.1, p.2.2.1⟩, ⟨p.1.1, p.2.2.2⟩⟩
  invFun p := ⟨⟨p.2.1, p.1.2 p.2.2⟩, ⟨p.1.1, p.1.2, p.2.2⟩⟩
  left_inv p := by
    rcases p with ⟨x, U⟩
    rfl
  right_inv p := by
    rcases p with ⟨U, x⟩
    rfl

/-- Summing the predecessor coefficient over all possible next elements gives
the common interior coefficient of a subset. -/
theorem sum_weight_erase_over_complement [DecidableEq α]
    (Ω S : Finset α) (hS : S ⊆ Ω) (hne : S ≠ Ω) :
    ∑ x ∈ Ω \ S, weight (Ω.erase x) S =
      (S.card.factorial * (Ω.card - S.card).factorial : ℚ) /
        Ω.card.factorial := by
  have hcard : S.card < Ω.card :=
    Finset.card_lt_card (lt_of_le_of_ne hS hne)
  have hdiff : 0 < Ω.card - S.card := by omega
  have heraseCard : Ω.card - 1 + 1 = Ω.card := by omega
  have hstep : Ω.card - 1 - S.card + 1 = Ω.card - S.card := by omega
  have hfac : (Ω.card.factorial : ℚ) ≠ 0 := by positivity
  calc
    ∑ x ∈ Ω \ S, weight (Ω.erase x) S =
        ∑ _x ∈ Ω \ S,
          ((S.card.factorial * (Ω.card - 1 - S.card).factorial : ℚ) /
            Ω.card.factorial) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxΩ : x ∈ Ω := (Finset.mem_sdiff.mp hx).1
          simp only [weight, Finset.card_erase_of_mem hxΩ, heraseCard]
    _ =
        (Ω \ S).card •
          ((S.card.factorial * (Ω.card - 1 - S.card).factorial : ℚ) /
            Ω.card.factorial) := by
          rw [Finset.sum_const]
    _ = (S.card.factorial * (Ω.card - S.card).factorial : ℚ) /
        Ω.card.factorial := by
          rw [Finset.card_sdiff_of_subset hS]
          have hfacstep : (Ω.card - S.card).factorial =
              (Ω.card - S.card) * (Ω.card - 1 - S.card).factorial := by
            calc
              (Ω.card - S.card).factorial =
                  (Ω.card - 1 - S.card + 1).factorial :=
                congrArg Nat.factorial hstep.symm
              _ = (Ω.card - 1 - S.card + 1) *
                  (Ω.card - 1 - S.card).factorial := Nat.factorial_succ _
              _ = (Ω.card - S.card) *
                  (Ω.card - 1 - S.card).factorial := by rw [hstep]
          rw [hfacstep]
          rw [nsmul_eq_mul]
          push_cast
          ring

/-- Summing the predecessor coefficient over all possible last-inserted
elements gives the same common interior coefficient. -/
theorem sum_weight_erase_over_members [DecidableEq α]
    (Ω S : Finset α) (hS : S ⊆ Ω) (hnonempty : S.Nonempty) :
    ∑ x ∈ S, weight (Ω.erase x) (S.erase x) =
      (S.card.factorial * (Ω.card - S.card).factorial : ℚ) /
        Ω.card.factorial := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hnonempty
  have hΩcard : 0 < Ω.card := lt_of_lt_of_le hScard (Finset.card_le_card hS)
  have hΩstep : Ω.card - 1 + 1 = Ω.card := by omega
  have hSstep : S.card - 1 + 1 = S.card := by omega
  have hdiff : Ω.card - 1 - (S.card - 1) = Ω.card - S.card := by omega
  calc
    ∑ x ∈ S, weight (Ω.erase x) (S.erase x) =
        ∑ _x ∈ S,
          (((S.card - 1).factorial *
              (Ω.card - S.card).factorial : ℚ) /
            Ω.card.factorial) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxΩ : x ∈ Ω := hS hx
          simp only [weight, Finset.card_erase_of_mem hxΩ,
            Finset.card_erase_of_mem hx, hΩstep, hdiff]
    _ = S.card •
          (((S.card - 1).factorial *
              (Ω.card - S.card).factorial : ℚ) /
            Ω.card.factorial) := by
          rw [Finset.sum_const]
    _ = (S.card.factorial * (Ω.card - S.card).factorial : ℚ) /
        Ω.card.factorial := by
          have hfacstep : S.card.factorial =
              S.card * (S.card - 1).factorial := by
            calc
              S.card.factorial = (S.card - 1 + 1).factorial :=
                congrArg Nat.factorial hSstep.symm
              _ = (S.card - 1 + 1) * (S.card - 1).factorial :=
                Nat.factorial_succ _
              _ = S.card * (S.card - 1).factorial := by rw [hSstep]
          rw [hfacstep, nsmul_eq_mul]
          push_cast
          ring

/-- The coefficient of the empty predecessor set in the full marginal sum
is one whenever there is at least one available element. -/
theorem sum_weight_erase_empty [DecidableEq α]
    (Ω : Finset α) (hne : Ω.Nonempty) :
    ∑ x ∈ Ω, weight (Ω.erase x) ∅ = 1 := by
  have h := sum_weight_erase_over_complement Ω ∅ (by simp)
    (Ne.symm hne.ne_empty)
  have hfac : (Ω.card.factorial : ℚ) ≠ 0 := by positivity
  simpa [hfac] using h


/-- The coefficient of the full successor set in the full marginal sum is
one whenever the available set is nonempty. -/
theorem sum_weight_erase_self [DecidableEq α]
    (Ω : Finset α) (hne : Ω.Nonempty) :
    ∑ x ∈ Ω, weight (Ω.erase x) (Ω.erase x) = 1 := by
  have h := sum_weight_erase_over_members Ω Ω (by simp) hne
  have hfac : (Ω.card.factorial : ℚ) ≠ 0 := by positivity
  rw [h]
  simp only [Nat.sub_self, Nat.factorial_zero, mul_one]
  field_simp
  norm_num

/-- A zero average of nonnegative local changes forces every local change to
vanish.  This is the equality mechanism used after the covering formula. -/
theorem localChange_eq_zero_of_weighted_sum_eq_zero [DecidableEq α]
    (Ω : Finset α) (localChange : Finset α → ℚ)
    (hnonnegative : ∀ S ∈ Ω.powerset, 0 ≤ localChange S)
    (hzero : ∑ S ∈ Ω.powerset, weight Ω S * localChange S = 0) :
    ∀ S ∈ Ω.powerset, localChange S = 0 := by
  have hterm : ∀ S ∈ Ω.powerset,
      0 ≤ weight Ω S * localChange S := by
    intro S hS
    exact mul_nonneg (le_of_lt (weight_pos Ω S)) (hnonnegative S hS)
  have heach :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero
  intro S hS
  have hmul : weight Ω S * localChange S = 0 := heach S hS
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (weight_pos Ω S))

/-- The equality case may be read only at the empty predecessor set. -/
theorem empty_localChange_eq_zero_of_weighted_sum_eq_zero [DecidableEq α]
    (Ω : Finset α) (localChange : Finset α → ℚ)
    (hnonnegative : ∀ S ∈ Ω.powerset, 0 ≤ localChange S)
    (hzero : ∑ S ∈ Ω.powerset, weight Ω S * localChange S = 0) :
    localChange ∅ = 0 := by
  exact localChange_eq_zero_of_weighted_sum_eq_zero Ω localChange
    hnonnegative hzero ∅ (by simp)

end MagnitudeConjecture.DeletionOrderAverage
