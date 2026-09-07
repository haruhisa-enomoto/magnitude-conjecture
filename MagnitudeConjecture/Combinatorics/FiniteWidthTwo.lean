import MagnitudeConjecture.Combinatorics.PosetSpaceChainFlag
import MagnitudeConjecture.Combinatorics.PosetSpaceAntichainExtension
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite posets of width at most two

We prove the width-two case of Dilworth's theorem in the exact form needed by
the magnitude argument: a finite poset without a three-element antichain is
the union of two chains.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

variable {T : Type u} [PartialOrder T] [Fintype T]

/-- The minimal elements of a finite subset of a poset. -/
def minimalIn (A : Finset T) : Finset T := by
  classical
  exact A.filter fun x ↦ ∀ y ∈ A, ¬y < x

/-- If the ambient poset has no three-element antichain, a finite subset has
at most two minimal elements. -/
theorem card_minimalIn_le_two
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c)
    (A : Finset T) :
    (minimalIn A).card ≤ 2 := by
  classical
  by_contra hnot
  have hlt : 2 < (minimalIn A).card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hlt
  apply hno a b c
  have haA := (Finset.mem_filter.mp ha).1
  have hbA := (Finset.mem_filter.mp hb).1
  have hcA := (Finset.mem_filter.mp hc).1
  have hamin := (Finset.mem_filter.mp ha).2
  have hbmin := (Finset.mem_filter.mp hb).2
  have hcmin := (Finset.mem_filter.mp hc).2
  refine
    { not_ab := ?_
      not_ba := ?_
      not_ac := ?_
      not_ca := ?_
      not_bc := ?_
      not_cb := ?_ }
  · intro hle
    exact hbmin a haA (lt_of_le_of_ne hle hab)
  · intro hle
    exact hamin b hbA (lt_of_le_of_ne hle hab.symm)
  · intro hle
    exact hcmin a haA (lt_of_le_of_ne hle hac)
  · intro hle
    exact hamin c hcA (lt_of_le_of_ne hle hac.symm)
  · intro hle
    exact hcmin b hbA (lt_of_le_of_ne hle hbc)
  · intro hle
    exact hbmin c hcA (lt_of_le_of_ne hle hbc.symm)

/-- A left vertex may be matched either to a strictly larger poset element
or to one of two terminal symbols. -/
def successorRel (x : T) : T ⊕ Fin 2 → Prop
  | Sum.inl y => x < y
  | Sum.inr _ => True

/-- Hall's theorem supplies an injective successor assignment with two
terminals. -/
theorem exists_injective_successor
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    ∃ f : T → T ⊕ Fin 2, Function.Injective f ∧
      ∀ x, successorRel x (f x) := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (successorRel (T := T))).mp
  intro A
  let M := minimalIn A
  have hMcard : Fintype.card M ≤ Fintype.card (Fin 2) := by
    simpa [M] using card_minimalIn_le_two hno A
  let e : M ↪ Fin 2 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hMcard)
  let g : A → T ⊕ Fin 2 := fun a ↦
    if ha : a.1 ∈ M then Sum.inr (e ⟨a.1, ha⟩)
    else Sum.inl a.1
  have hg_injective : Function.Injective g := by
    intro a b hab
    by_cases ha : a.1 ∈ M <;> by_cases hb : b.1 ∈ M
    · have he : (⟨a.1, ha⟩ : M) = ⟨b.1, hb⟩ := by
        apply e.injective
        simpa [g, ha, hb] using hab
      apply Subtype.ext
      exact congrArg (fun z : M ↦ z.1) he
    · simp [g, ha, hb] at hab
    · simp [g, ha, hb] at hab
    · exact Subtype.ext (by simpa [g, ha, hb] using hab)
  have hg_mem (a : A) : ∃ x ∈ A, successorRel x (g a) := by
    by_cases ha : a.1 ∈ M
    · exact ⟨a.1, a.2, by simp [g, ha, successorRel]⟩
    · have hnonmin : ∃ x ∈ A, x < a.1 := by
        have ha' : ¬∀ x, x ∈ A → ¬x < a.1 := by
          intro h
          apply ha
          exact Finset.mem_filter.mpr ⟨a.2, fun x hx ↦ h x hx⟩
        push Not at ha'
        exact ha'
      obtain ⟨x, hxA, hxa⟩ := hnonmin
      exact ⟨x, hxA, by simpa [g, ha, successorRel] using hxa⟩
  let N : Finset (T ⊕ Fin 2) :=
    Finset.univ.filter fun z ↦ ∃ x ∈ A, successorRel x z
  let gN : A → N := fun a ↦
    ⟨g a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_mem a⟩⟩
  have hgN_injective : Function.Injective gN := by
    intro a b hab
    apply hg_injective
    exact congrArg Subtype.val hab
  have hcard : A.card ≤ N.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective gN hgN_injective
  simpa [N] using hcard

/-- Strict upper set of an element, used as a termination measure. -/
def strictUpperFinset (x : T) : Finset T := by
  classical
  exact Finset.univ.filter fun y ↦ x < y

/-- Moving strictly upward strictly decreases the cardinality of the strict
upper set. -/
theorem card_strictUpperFinset_lt_of_lt {x y : T} (hxy : x < y) :
    (strictUpperFinset y).card < (strictUpperFinset x).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨y, by simp [strictUpperFinset, hxy],
      by simp [strictUpperFinset]⟩
  · intro z hz
    simp only [strictUpperFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz ⊢
    exact lt_trans hxy hz

/-- An injective successor assignment whose only non-poset outputs are two
terminal symbols. -/
structure TwoSuccessor (T : Type u) [PartialOrder T] where
  next : T → T ⊕ Fin 2
  next_injective : Function.Injective next
  related : ∀ x, successorRel x (next x)

namespace TwoSuccessor

variable (F : TwoSuccessor T)

theorem lt_of_next_eq_inl {S : Type u} [PartialOrder S]
    (F : TwoSuccessor S) {x y : S} (h : F.next x = Sum.inl y) :
    x < y := by
  have hr := F.related x
  rw [h] at hr
  exact hr

/-- Terminal label and number of successor steps remaining. -/
def trace {S : Type u} [PartialOrder S] [Fintype S]
    (F : TwoSuccessor S) (x : S) : Fin 2 × ℕ :=
  match h : F.next x with
  | Sum.inr d => (d, 0)
  | Sum.inl y =>
      let p := trace F y
      (p.1, p.2 + 1)
termination_by (strictUpperFinset x).card
decreasing_by
  exact card_strictUpperFinset_lt_of_lt (F.lt_of_next_eq_inl h)

@[simp]
theorem trace_of_next_eq_inr {x : T} {d : Fin 2}
    (h : F.next x = Sum.inr d) :
    F.trace x = (d, 0) := by
  rw [trace.eq_1, h]

@[simp]
theorem trace_of_next_eq_inl {x y : T}
    (h : F.next x = Sum.inl y) :
    F.trace x = ((F.trace y).1, (F.trace y).2 + 1) := by
  rw [trace.eq_1, h]

/-- The terminal label together with the remaining path length uniquely
determines a vertex. -/
theorem eq_of_trace_eq {S : Type u} [PartialOrder S] [Fintype S]
    (F : TwoSuccessor S) {x y : S}
    (htrace : F.trace x = F.trace y) : x = y := by
  cases hx : F.next x with
  | inl x' =>
      cases hy : F.next y with
      | inl y' =>
          rw [F.trace_of_next_eq_inl hx,
            F.trace_of_next_eq_inl hy] at htrace
          have hfst := congrArg Prod.fst htrace
          have hsnd := congrArg Prod.snd htrace
          have htail : F.trace x' = F.trace y' := by
            apply Prod.ext
            · exact hfst
            · exact Nat.add_right_cancel hsnd
          have hxy : x' = y' := eq_of_trace_eq F htail
          apply F.next_injective
          rw [hx, hy, hxy]
      | inr d =>
          rw [F.trace_of_next_eq_inl hx,
            F.trace_of_next_eq_inr hy] at htrace
          have hsnd := congrArg Prod.snd htrace
          omega
  | inr d =>
      cases hy : F.next y with
      | inl y' =>
          rw [F.trace_of_next_eq_inr hx,
            F.trace_of_next_eq_inl hy] at htrace
          have hsnd := congrArg Prod.snd htrace
          omega
      | inr e =>
          rw [F.trace_of_next_eq_inr hx,
            F.trace_of_next_eq_inr hy] at htrace
          have hde : d = e := congrArg Prod.fst htrace
          apply F.next_injective
          rw [hx, hy, hde]
termination_by (strictUpperFinset x).card
decreasing_by
  exact card_strictUpperFinset_lt_of_lt (F.lt_of_next_eq_inl hx)

/-- The full two-terminal trace is injective. -/
theorem trace_injective (F : TwoSuccessor T) :
    Function.Injective F.trace := by
  intro x y h
  exact eq_of_trace_eq F h

/-- Along one terminal fiber, greater remaining path length means a smaller
poset element. -/
theorem le_of_trace_fst_eq_of_snd_le
    {S : Type u} [PartialOrder S] [Fintype S]
    (F : TwoSuccessor S) {x y : S}
    (hfst : (F.trace x).1 = (F.trace y).1)
    (hsnd : (F.trace y).2 ≤ (F.trace x).2) :
    x ≤ y := by
  cases hx : F.next x with
  | inl x' =>
      rw [F.trace_of_next_eq_inl hx] at hfst hsnd
      by_cases htail : (F.trace y).2 ≤ (F.trace x').2
      · exact (F.lt_of_next_eq_inl hx).le.trans
          (le_of_trace_fst_eq_of_snd_le F hfst htail)
      · have hfirst : (F.trace x).1 = (F.trace y).1 := by
          rw [F.trace_of_next_eq_inl hx]
          exact hfst
        have hsecond : (F.trace x).2 = (F.trace y).2 := by
          rw [F.trace_of_next_eq_inl hx]
          omega
        exact (F.eq_of_trace_eq (Prod.ext hfirst hsecond)).le
  | inr d =>
      rw [F.trace_of_next_eq_inr hx] at hfst hsnd
      have hfirst : (F.trace x).1 = (F.trace y).1 := by
        rw [F.trace_of_next_eq_inr hx]
        exact hfst
      have hsecond : (F.trace x).2 = (F.trace y).2 := by
        rw [F.trace_of_next_eq_inr hx]
        omega
      exact (F.eq_of_trace_eq (Prod.ext hfirst hsecond)).le
termination_by (strictUpperFinset x).card
decreasing_by
  exact card_strictUpperFinset_lt_of_lt (F.lt_of_next_eq_inl hx)

/-- Vertices with the same terminal label are comparable. -/
theorem comparable_of_trace_fst_eq (F : TwoSuccessor T) {x y : T}
    (hfst : (F.trace x).1 = (F.trace y).1) :
    x ≤ y ∨ y ≤ x := by
  rcases le_total (F.trace y).2 (F.trace x).2 with h | h
  · exact Or.inl (F.le_of_trace_fst_eq_of_snd_le hfst h)
  · exact Or.inr (F.le_of_trace_fst_eq_of_snd_le hfst.symm h)

/-- Fiber of the successor trace over one of the two terminal labels. -/
def terminalFiber (F : TwoSuccessor T) (d : Fin 2) : Set T :=
  {x | (F.trace x).1 = d}

/-- Each terminal fiber is a chain. -/
theorem isChain_terminalFiber (F : TwoSuccessor T) (d : Fin 2) :
    IsChain (· ≤ ·) (terminalFiber F d) := by
  intro x hx y hy hxy
  exact F.comparable_of_trace_fst_eq (hx.trans hy.symm)

/-- The two terminal fibers cover the whole poset. -/
theorem terminalFiber_zero_union_one (F : TwoSuccessor T) :
    terminalFiber F 0 ∪ terminalFiber F 1 = Set.univ := by
  ext x
  simp only [Set.mem_union, terminalFiber, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  generalize hd : (F.trace x).1 = d
  fin_cases d <;> simp_all

end TwoSuccessor

/-- The Hall assignment as a bundled successor structure. -/
theorem exists_twoSuccessor
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    Nonempty (TwoSuccessor T) := by
  obtain ⟨f, hf, hrel⟩ := exists_injective_successor hno
  exact ⟨⟨f, hf, hrel⟩⟩

/-- Width-two Dilworth: a finite poset without a three-element antichain is
covered by two chains. -/
theorem exists_two_chain_cover_of_no_threeAntichain
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    ∃ A B : Set T,
      A ∪ B = Set.univ ∧
        IsChain (· ≤ ·) A ∧ IsChain (· ≤ ·) B := by
  let F := Classical.choice (exists_twoSuccessor hno)
  exact ⟨F.terminalFiber 0, F.terminalFiber 1,
    F.terminalFiber_zero_union_one,
    F.isChain_terminalFiber 0, F.isChain_terminalFiber 1⟩

section Schur

variable {k : Type u} [Field k]

/-- If the indexing poset has width at most two, every Schur poset space is
one-dimensional. -/
theorem finrank_eq_one_of_isSchur_of_no_threeAntichain
    (X : Obj k T) (hschur : IsSchur k T X)
    (hno : ∀ a b c : T, ¬IsThreeAntichain a b c) :
    Module.finrank k X = 1 := by
  obtain ⟨A, B, hcover, hA, hB⟩ :=
    exists_two_chain_cover_of_no_threeAntichain hno
  exact finrank_eq_one_of_isSchur_of_two_chain_cover
    X hschur A B hcover hA hB

/-- Consequently, every Schur poset space of dimension at least two forces a
three-element antichain in the indexing poset. -/
theorem exists_threeAntichain_of_isSchur_of_two_le_finrank
    (X : Obj k T) (hschur : IsSchur k T X)
    (hrank : 2 ≤ Module.finrank k X) :
    ∃ a b c : T, IsThreeAntichain a b c := by
  by_contra hnot
  simp only [not_exists] at hnot
  have hone := finrank_eq_one_of_isSchur_of_no_threeAntichain
    X hschur hnot
  omega

end Schur

end MagnitudeConjecture.PosetSpace
