import MagnitudeConjecture.Combinatorics.PosetSpaceUpperSetHeight

/-! # The upper-set cube above a finite antichain -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.AntichainUpperCube
universe u
variable {T : Type u} [PartialOrder T] [Fintype T] [DecidableEq T]

/-- Elements strictly above at least one member of the antichain. -/
def base (A : Finset T) : Finset T := by
  classical
  exact Finset.univ.filter (fun t ↦ ∃ a ∈ A, a < t)

@[simp]
theorem mem_base (A : Finset T) (t : T) : t ∈ base A ↔ ∃ a ∈ A, a < t := by
  classical
  simp [base]

/-- The strict upper part is an upper set. -/
theorem base_isUpperSet (A : Finset T) : IsUpperSet (base A : Set T) := by
  intro x y hxy hx
  obtain ⟨a, ha, hax⟩ := (mem_base A x).1 hx
  exact (mem_base A y).2 ⟨a, ha, hax.trans_le hxy⟩

/-- The strict upper part contains no member of the antichain. -/
theorem base_disjoint (A : Finset T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b) : Disjoint (base A) A := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hb hbA
  obtain ⟨a, ha, hab⟩ := (mem_base A b).1 hb
  exact hab.ne (hA a ha b hbA hab.le)

/-- Adjoining any subset of the antichain to the strict upper part gives
an upper set. -/
theorem union_isUpperSet (A B : Finset T) (hB : B ⊆ A) :
    IsUpperSet ((base A ∪ B : Finset T) : Set T) := by
  classical
  intro x y hxy hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (base_isUpperSet A hxy hx)
  · by_cases heq : x = y
    · subst y
      exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ ((mem_base A y).2 ⟨x, hB hx, lt_of_le_of_ne hxy heq⟩)

/-- The cube vertex indexed by B has exactly |B| more elements than its base. -/
theorem card_union (A B : Finset T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b) (hB : B ⊆ A) :
    (base A ∪ B).card = (base A).card + B.card := by
  classical
  exact Finset.card_union_of_disjoint ((base_disjoint A hA).mono_right hB)

/-- Different subsets of the antichain give different cube vertices. -/
theorem union_injective (A : Finset T)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≤ b → a = b)
    {B C : Finset T} (hB : B ⊆ A) (hC : C ⊆ A)
    (heq : base A ∪ B = base A ∪ C) : B = C := by
  classical
  have hb := (base_disjoint A hA).mono_right hB
  have hc := (base_disjoint A hA).mono_right hC
  have h := congrArg (fun U : Finset T ↦ U \ base A) heq
  simpa [Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint.mpr hb.symm,
    Finset.sdiff_eq_self_iff_disjoint.mpr hc.symm] using h

end MagnitudeConjecture.AntichainUpperCube
