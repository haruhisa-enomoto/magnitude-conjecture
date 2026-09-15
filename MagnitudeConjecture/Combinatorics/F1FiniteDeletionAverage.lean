import MagnitudeConjecture.Combinatorics.DeletionOrderWeight

/-!
# Finite positive deletion-order averages

The frozen proof only averages over the finite support visible to one deleted
object. These lemmas package the positivity and equality steps for the
integer-valued local changes supplied by the category-theoretic support
modules.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MagnitudeConjecture.DeletionOrderAverage

universe u v w

variable {α : Type u}

/-- A finite deletion-order average of nonnegative integer local changes is
nonnegative after casting to the rational coefficient field. -/
theorem weightedIntegerAverage_nonnegative [DecidableEq α]
    (Ω : Finset α) (localChange : Finset α → ℤ)
    (hnonnegative : ∀ S ∈ Ω.powerset, 0 ≤ localChange S) :
    0 ≤ ∑ S ∈ Ω.powerset, weight Ω S * (localChange S : ℚ) := by
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (le_of_lt (weight_pos Ω S))
    (by exact_mod_cast hnonnegative S hS)

/-- A zero finite deletion-order average forces the empty predecessor local
change to vanish. -/
theorem empty_weightedIntegerAverage_eq_zero
    [DecidableEq α] (Ω : Finset α) (localChange : Finset α → ℤ)
    (hnonnegative : ∀ S ∈ Ω.powerset, 0 ≤ localChange S)
    (hzero : ∑ S ∈ Ω.powerset,
      weight Ω S * (localChange S : ℚ) = 0) :
    localChange ∅ = 0 := by
  have hcast : ∀ S ∈ Ω.powerset, 0 ≤ (localChange S : ℚ) := by
    intro S hS
    exact_mod_cast hnonnegative S hS
  have h := localChange_eq_zero_of_weighted_sum_eq_zero Ω
    (fun S ↦ (localChange S : ℚ)) hcast hzero
  exact_mod_cast h ∅ (by simp)

/-- The coefficient used by the undeleted term is strictly positive. -/
theorem emptyCoefficient_pos (Ω : Finset α) : 0 < weight Ω ∅ :=
  weight_pos Ω ∅

/- The finite-order telescoping identity used before introducing the group
action.  For each `y`, the predecessor sets in an order of `K.erase y`
produce the marginal contribution of inserting `y`; summing over `y` makes
all interior coefficients cancel, leaving the two endpoints. -/
theorem weightedDeletionTelescope [DecidableEq α]
    (K : Finset α) (f : Finset α → ℚ) :
    ∑ y ∈ K, ∑ S ∈ (K.erase y).powerset,
      weight (K.erase y) S * (f S - f (insert y S)) =
      f ∅ - f K := by
  classical
  letI : Fintype {y : α // y ∈ K} := Finset.fintypeCoeSort K
  letI : ∀ y : {y : α // y ∈ K}, Fintype {S : Finset α // S ⊆ K.erase y.1} :=
    fun y ↦ Fintype.ofFinset (K.erase y.1).powerset (by
      intro S
      simp only [Finset.mem_powerset]
      rfl)
  letI : Fintype {S : Finset α // S ⊆ K} :=
    Fintype.ofFinset K.powerset (by
      intro S
      simp only [Finset.mem_powerset]
      rfl)
  letI : ∀ S : {S : Finset α // S ⊆ K},
      Fintype {y : α // y ∈ K ∧ y ∉ S.1} :=
    fun S ↦ Fintype.ofFinset (K \ S.1) (by
      intro y
      simp only [Finset.mem_sdiff]
      rfl)
  letI : ∀ U : {U : Finset α // U ⊆ K}, Fintype {y : α // y ∈ U.1} :=
    fun U ↦ Finset.fintypeCoeSort U.1
  let A : (Σ y : {y : α // y ∈ K},
      {S : Finset α // S ⊆ K.erase y.1}) → ℚ := fun p ↦
    weight (K.erase p.1.1) p.2.1 *
      (f p.2.1 - f (insert p.1.1 p.2.1))
  have hleft :
      (∑ y ∈ K, ∑ S ∈ (K.erase y).powerset,
        weight (K.erase y) S * (f S - f (insert y S))) =
      ∑ p : (Σ y : {y : α // y ∈ K},
        {S : Finset α // S ⊆ K.erase y.1}), A p := by
    calc
      (∑ y ∈ K, ∑ S ∈ (K.erase y).powerset,
        weight (K.erase y) S * (f S - f (insert y S))) =
          ∑ y : {y : α // y ∈ K},
            ∑ S ∈ (K.erase y.1).powerset,
              weight (K.erase y.1) S *
                (f S - f (insert y.1 S)) := by
        exact Finset.sum_subtype K (by simp) (fun y ↦
          ∑ S ∈ (K.erase y).powerset,
            weight (K.erase y) S * (f S - f (insert y S)))
      _ = ∑ p : (Σ y : {y : α // y ∈ K},
          {S : Finset α // S ⊆ K.erase y.1}), A p := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro y hy
        exact Finset.sum_subtype (K.erase y.1).powerset (by simp) (fun S ↦
          weight (K.erase y.1) S *
            (f S - f (insert y.1 S)))
  rw [hleft]
  let F₁ : (Σ y : {y : α // y ∈ K},
      {S : Finset α // S ⊆ K.erase y.1}) → ℚ := fun p ↦
    weight (K.erase p.1.1) p.2.1 * f p.2.1
  let F₂ : (Σ y : {y : α // y ∈ K},
      {S : Finset α // S ⊆ K.erase y.1}) → ℚ := fun p ↦
    weight (K.erase p.1.1) p.2.1 * f (insert p.1.1 p.2.1)
  have hsplit : (∑ p : (Σ y : {y : α // y ∈ K},
      {S : Finset α // S ⊆ K.erase y.1}), A p) =
      (∑ p, F₁ p) - ∑ p, F₂ p := by
    simp only [A, F₁, F₂, mul_sub]
    rw [← Finset.sum_sub_distrib]
  rw [hsplit]
  let e₁ := predecessorIncidenceEquiv K
  let e₂ := (successorIncidenceEquiv K).trans (successorIncidenceSwapEquiv K)
  have hfirst : (∑ p : (Σ y : {y : α // y ∈ K},
      {S : Finset α // S ⊆ K.erase y.1}), F₁ p) =
      ∑ q : {S : Finset α // S ⊆ K},
        (∑ y : {y : α // y ∈ K ∧ y ∉ q.1},
          weight (K.erase y.1) q.1) * f q.1 := by
    calc
      (∑ p : (Σ y : {y : α // y ∈ K},
          {S : Finset α // S ⊆ K.erase y.1}), F₁ p) =
          ∑ q : (Σ S : {S : Finset α // S ⊆ K},
            {y : α // y ∈ K ∧ y ∉ S.1}), F₁ (e₁.symm q) := by
        simpa using (Fintype.sum_equiv e₁ (fun p ↦ F₁ p)
          (fun q ↦ F₁ (e₁.symm q)) (fun p ↦ by simp))
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro S hS
        change (∑ y : {y : α // y ∈ K ∧ y ∉ S.1},
          weight (K.erase y.1) S.1 * f S.1) = _
        rw [← Finset.sum_mul]
  have hsecond : (∑ p : (Σ y : {y : α // y ∈ K},
      {S : Finset α // S ⊆ K.erase y.1}), F₂ p) =
      ∑ q : {U : Finset α // U ⊆ K},
        (∑ y : {y : α // y ∈ q.1},
          weight (K.erase y.1) (q.1.erase y.1)) * f q.1 := by
    calc
      (∑ p : (Σ y : {y : α // y ∈ K},
          {S : Finset α // S ⊆ K.erase y.1}), F₂ p) =
          ∑ q : (Σ U : {U : Finset α // U ⊆ K},
            {y : α // y ∈ U.1}), F₂ (e₂.symm q) := by
        simpa using (Fintype.sum_equiv e₂ (fun p ↦ F₂ p)
          (fun q ↦ F₂ (e₂.symm q)) (fun p ↦ by simp))
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro U hU
        change (∑ y : {y : α // y ∈ U.1},
          F₂ (e₂.symm ⟨U, y⟩)) = _
        simp only [F₂]
        simp [e₂, successorIncidenceEquiv, successorIncidenceSwapEquiv]
        rw [Finset.sum_mul]
  rw [hfirst, hsecond]
  let cA : {S : Finset α // S ⊆ K} → ℚ := fun q ↦
    ∑ y : {y : α // y ∈ K ∧ y ∉ q.1}, weight (K.erase y.1) q.1
  let cB : {U : Finset α // U ⊆ K} → ℚ := fun q ↦
    ∑ y : {y : α // y ∈ q.1}, weight (K.erase y.1) (q.1.erase y.1)
  change (∑ q : {S : Finset α // S ⊆ K}, cA q * f q.1) -
      ∑ q : {S : Finset α // S ⊆ K}, cB q * f q.1 = f ∅ - f K
  by_cases hK : K.Nonempty
  · let q0 : {S : Finset α // S ⊆ K} := ⟨∅, by simp⟩
    let qK : {S : Finset α // S ⊆ K} := ⟨K, subset_rfl⟩
    have hqK0 : qK ≠ q0 := by
      intro h
      have hEq : K = ∅ := congrArg Subtype.val h
      exact hK.ne_empty hEq
    have hAconvert (q : {S : Finset α // S ⊆ K}) :
        cA q = ∑ y ∈ K \ q.1, weight (K.erase y) q.1 := by
      dsimp [cA]
      symm
      simpa [Finset.mem_sdiff] using
        (Finset.sum_subtype (K \ q.1) (by simp)
          (fun y ↦ weight (K.erase y) q.1))
    have hBconvert (q : {S : Finset α // S ⊆ K}) :
        cB q = ∑ y ∈ q.1, weight (K.erase y) (q.1.erase y) := by
      dsimp [cB]
      exact Finset.sum_coe_sort q.1
        (fun y ↦ weight (K.erase y) (q.1.erase y))
    have hcA0 : cA q0 = 1 := by
      rw [hAconvert q0]
      simpa [q0] using (sum_weight_erase_empty K hK)
    have hcB0 : cB q0 = 0 := by
      rw [hBconvert q0]
      simp [q0]
    have hcAK : cA qK = 0 := by
      rw [hAconvert qK]
      simp [qK]
    have hcBK : cB qK = 1 := by
      rw [hBconvert qK]
      simpa [qK] using (sum_weight_erase_self K hK)
    have hcAB (q : {S : Finset α // S ⊆ K})
        (hq0 : q ≠ q0) (hqK : q ≠ qK) : cA q = cB q := by
      have hne : q.1 ≠ ∅ := by
        intro h
        apply hq0
        exact Subtype.ext h
      have hneK : q.1 ≠ K := by
        intro h
        apply hqK
        exact Subtype.ext h
      have hA := sum_weight_erase_over_complement K q.1 q.2 hneK
      have hB := sum_weight_erase_over_members K q.1 q.2
        (Finset.nonempty_iff_ne_empty.mpr hne)
      rw [hAconvert q, hBconvert q]
      exact hA.trans hB.symm
    let d : {S : Finset α // S ⊆ K} → ℚ := fun q ↦
      (cA q - cB q) * f q.1
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    change (∑ q : {S : Finset α // S ⊆ K}, d q) = f ∅ - f K
    have hzero : ∀ q : {S : Finset α // S ⊆ K},
        q ≠ q0 → q ≠ qK → d q = 0 := by
      intro q hq0 hqK
      simp [d, hcAB q hq0 hqK]
    have hmem0 : q0 ∈ (Finset.univ : Finset {S : Finset α // S ⊆ K}) :=
      Finset.mem_univ _
    have hmemK : qK ∈ (Finset.univ.erase q0 :
        Finset {S : Finset α // S ⊆ K}) := by
      rw [Finset.mem_erase]
      exact ⟨hqK0, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ d hmem0]
    rw [← Finset.sum_erase_add _ d hmemK]
    have hinterior : ∑ q ∈ (Finset.univ.erase q0).erase qK, d q = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqK : q ≠ qK := (Finset.mem_erase.mp hq).1
      have hq0 : q ≠ q0 := (Finset.mem_erase.mp
        (Finset.mem_erase.mp hq).2).1
      exact hzero q hq0 hqK
    rw [hinterior]
    simp [d, q0, qK, hcA0, hcB0, hcAK, hcBK]
    ring_nf
  · have hEq : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    subst K
    let q0 : {S : Finset α // S ⊆ ∅} := ⟨∅, by simp⟩
    letI : Unique {S : Finset α // S ⊆ ∅} :=
      { default := q0
        uniq := by
          intro q
          apply Subtype.ext
          exact Finset.subset_empty.mp q.property }
    rw [Fintype.sum_unique, Fintype.sum_unique]
    have hdef : (default : {S : Finset α // S ⊆ (∅ : Finset α)}) = q0 :=
      Subsingleton.elim _ _
    rw [hdef]
    haveI : IsEmpty {y : α // y ∈ (∅ : Finset α) ∧ y ∉ (∅ : Finset α)} :=
      ⟨fun y ↦ by simpa using y.property.1⟩
    simp [cA, cB, q0]

/- The direct F1 average only needs positivity of each insertion marginal.
   Unlike the constant-marginal specialization below, this form keeps the
   marginal value attached to the inserted element. -/

/-- The telescoping identity summed over a finite family of local-density
contributions.  This is the exact finite-order cancellation used before the
orbit reindexing: all intermediate deletion subsets cancel independently for
 each family member. -/
theorem weightedDeletionTelescope_family [DecidableEq α]
    {β : Type u} (K : Finset α) (W : Finset β)
    (f : β → Finset α → ℚ) :
    ∑ y ∈ K, ∑ S ∈ K.erase y |>.powerset,
      weight (K.erase y) S *
        ((∑ b ∈ W, f b S) - (∑ b ∈ W, f b (insert y S))) =
      (∑ b ∈ W, f b ∅) - (∑ b ∈ W, f b K) := by
  let F : Finset α → ℚ := fun S ↦ ∑ b ∈ W, f b S
  have h := weightedDeletionTelescope K F
  simpa only [F] using h

/-! The finite-order form used by the frozen universal-cover argument.  The
 categorical layer supplies the incidence equality: it says that summing the
 expected marginal over all dependency objects of orbit representatives is
 the same as summing the marginal at the distinguished object over the finite
 affected family.  Once that equality is available, the endpoint formula is
 pure finite arithmetic and does not mention a finite-index subgroup. -/

/-- The expected insertion marginal of a finite dependency set. -/
def insertionMarginal [DecidableEq α]
    (K : Finset α) (f : Finset α → ℚ) (y : α) : ℚ :=
  ∑ S ∈ (K.erase y).powerset,
    weight (K.erase y) S * (f S - f (insert y S))

/- A deck translate reindexes a finite dependency set and its insertion
   marginal without changing any factorial coefficient.  This is the
   finite-set transport used by the categorical incidence bridge. -/
theorem weight_finsetCongr {α β : Type u} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (Ω S : Finset α) :
    weight (e.finsetCongr Ω) (e.finsetCongr S) = weight Ω S := by
  simp only [Equiv.finsetCongr_apply, weight, Finset.card_map]

theorem insertionMarginal_finsetCongr {α β : Type u}
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (K : Finset α) (f : Finset α → ℚ) (y : α) :
    insertionMarginal (e.finsetCongr K)
      (fun S' ↦ f (e.symm.finsetCongr S')) (e y) =
      insertionMarginal K f y := by
  classical
  let E : Finset α ≃ Finset β := e.finsetCongr
  have hmem : ∀ S : Finset α,
      S ∈ (K.erase y).powerset ↔ E S ∈ ((E K).erase (e y)).powerset := by
    intro S
    rw [Finset.mem_powerset, Finset.mem_powerset]
    dsimp [E]
    have hmapErase : Finset.map e.toEmbedding (K.erase y) =
        (Finset.map e.toEmbedding K).erase (e y) :=
      Finset.map_erase e.toEmbedding K y
    rw [← hmapErase]
    exact (Finset.map_subset_map (f := e.toEmbedding)).symm
  unfold insertionMarginal
  rw [Finset.sum_equiv E hmem]
  intro S hS
  have hmap_erase : E (K.erase y) = (E K).erase (e y) := by
    simp [E]
  have hsymm : e.symm.finsetCongr (E S) = S := by
    apply Finset.ext
    intro z
    simp [E, Equiv.finsetCongr_apply]
  have hinsert : e.symm.finsetCongr (insert (e y) (E S)) = insert y S := by
    apply Finset.ext
    intro z
    simp [E, Equiv.finsetCongr_apply]
  rw [← hmap_erase]
  rw [weight_finsetCongr e (K.erase y) S]
  simp only [hsymm, hinsert]

theorem endpoint_difference_eq_sum_insertionMarginal [DecidableEq α]
    (K : Finset α) (f : Finset α → ℚ) :
    f ∅ - f K = ∑ y ∈ K, insertionMarginal K f y := by
  simp only [insertionMarginal]
  exact weightedDeletionTelescope K f |>.symm

/-- The exact finite-support orbit-average identity.  `incidence` is the
 finite certificate supplied by the categorical action: it reindexes every
 dependency occurrence `(b,y)` of an orbit representative `b` to the finite
 affected family `W` at `x`, and restricts the corresponding random order to
 `insert x T`.  No residual-finiteness or finite-cover data occurs in the
 statement. -/
theorem finiteSupportOrbitAverage_of_incidence [DecidableEq α]
    {β : Type u} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    (W : Finset β)
    (incidence :
      ∑ b ∈ R, ∑ y ∈ K b, insertionMarginal (K b) (f b) y =
        ∑ S ∈ T.powerset, weight T S *
          (∑ b ∈ W, (f b S - f b (insert x S)))) :
    (∑ b ∈ R, (f b ∅ - f b (K b))) =
      ∑ S ∈ T.powerset, weight T S *
        (∑ b ∈ W, (f b S - f b (insert x S))) := by
  calc
    (∑ b ∈ R, (f b ∅ - f b (K b))) =
        ∑ b ∈ R, ∑ y ∈ K b, insertionMarginal (K b) (f b) y := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [endpoint_difference_eq_sum_insertionMarginal (K b) (f b)]
    _ = _ := incidence

/-- The finite-support orbit average is nonnegative once the categorical
incidence certificate identifies its right-hand side with nonnegative local
changes at the distinguished object.  This is the direct Section 10 sign
interface: all coefficients are positive, and no residual finite quotient is
needed at this layer. -/
theorem finiteSupportOrbitAverage_nonnegative_of_incidence [DecidableEq α]
    {β : Type u} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    (W : Finset β)
    (incidence :
      ∑ b ∈ R, ∑ y ∈ K b, insertionMarginal (K b) (f b) y =
        ∑ S ∈ T.powerset, weight T S *
          (∑ b ∈ W, (f b S - f b (insert x S))))
    (hlocal : ∀ S ∈ T.powerset,
      0 ≤ ∑ b ∈ W, (f b S - f b (insert x S))) :
    0 ≤ ∑ b ∈ R, (f b ∅ - f b (K b)) := by
  rw [finiteSupportOrbitAverage_of_incidence R K f T x hx W incidence]
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (le_of_lt (weight_pos T S)) (hlocal S hS)

theorem endpoint_difference_nonnegative_of_nonnegative_marginals
    [DecidableEq α] (K : Finset α) (f : Finset α → ℚ)
    (hmargin : ∀ y ∈ K,
      0 ≤ ∑ S ∈ K.erase y |>.powerset,
        weight (K.erase y) S * (f S - f (insert y S))) :
    0 ≤ f ∅ - f K := by
  have hsum :
      0 ≤ ∑ y ∈ K, ∑ S ∈ K.erase y |>.powerset,
        weight (K.erase y) S * (f S - f (insert y S)) := by
    apply Finset.sum_nonneg
    intro y hy
    exact hmargin y hy
  rw [← weightedDeletionTelescope K f]
  exact hsum

theorem endpoint_difference_nonnegative_of_family_nonnegative_marginals
    [DecidableEq α] {β : Type u} (K : Finset α) (W : Finset β)
    (f : β → Finset α → ℚ)
    (hmargin : ∀ y ∈ K,
      0 ≤ ∑ b ∈ W, ∑ S ∈ K.erase y |>.powerset,
        weight (K.erase y) S * (f b S - f b (insert y S))) :
    0 ≤ (∑ b ∈ W, f b ∅) - (∑ b ∈ W, f b K) := by
  have hsum :
      0 ≤ ∑ y ∈ K, ∑ S ∈ K.erase y |>.powerset,
        weight (K.erase y) S *
          ((∑ b ∈ W, f b S) - (∑ b ∈ W, f b (insert y S))) := by
    apply Finset.sum_nonneg
    intro y hy
    calc
      0 ≤ ∑ b ∈ W, ∑ S ∈ K.erase y |>.powerset,
        weight (K.erase y) S * (f b S - f b (insert y S)) :=
        hmargin y hy
      _ = ∑ S ∈ K.erase y |>.powerset,
          weight (K.erase y) S *
            ((∑ b ∈ W, f b S) - (∑ b ∈ W, f b (insert y S))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S hS
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [weightedDeletionTelescope_family K W f] at hsum
  exact hsum

/-! The next lemma is the finite arithmetic interface for the frozen
averaging argument.  The categorical part supplies the symmetry certificate:
all insertion marginals in the finite support `insert x T` have the same
value.  The telescope then turns that certificate into the endpoint
average, without introducing a finite quotient of the acting group. -/

theorem weightedMarginal_eq_endpoint_div_card
    [DecidableEq α] (T : Finset α) (x : α) (hx : x ∉ T)
    (f : Finset α → ℚ) (D : ℚ)
    (hconstant : ∀ y ∈ insert x T,
      ∑ S ∈ (insert x T).erase y |>.powerset,
        weight ((insert x T).erase y) S *
          (f S - f (insert y S)) = D) :
    ∑ S ∈ T.powerset,
      weight T S * (f S - f (insert x S)) =
        (1 / (T.card + 1 : ℚ)) * (f ∅ - f (insert x T)) := by
  let K := insert x T
  have htel := weightedDeletionTelescope K f
  have hsum :
      ∑ y ∈ K, ∑ S ∈ K.erase y |>.powerset,
        weight (K.erase y) S * (f S - f (insert y S)) =
        (K.card : ℚ) * D := by
    calc
      ∑ y ∈ K, ∑ S ∈ K.erase y |>.powerset,
          weight (K.erase y) S * (f S - f (insert y S)) =
          ∑ y ∈ K, D := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hconstant y hy
      _ = (K.card : ℚ) * D := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hKcard : K.card = T.card + 1 := by
    simp [K, hx, Nat.add_comm]
  have hxeq :
      ∑ S ∈ K.erase x |>.powerset,
        weight (K.erase x) S * (f S - f (insert x S)) =
      ∑ S ∈ T.powerset,
        weight T S * (f S - f (insert x S)) := by
    simpa [K, hx]
  have hsum' :
      (∑ S ∈ K.erase x |>.powerset,
        weight (K.erase x) S * (f S - f (insert x S))) =
      (K.card : ℚ)⁻¹ * (f ∅ - f K) := by
    have hself :
        (∑ S ∈ K.erase x |>.powerset,
          weight (K.erase x) S * (f S - f (insert x S))) = D :=
      hconstant x (Finset.mem_insert_self x T)
    have htel' : f ∅ - f K = (K.card : ℚ) * D := htel.symm.trans hsum
    rw [hself, htel']
    field_simp
  rw [← hxeq, hsum']
  rw [hKcard]
  simp only [K]
  push_cast
  field_simp

theorem weightedMarginal_eq_endpoint_of_constant
    [DecidableEq α] (T : Finset α) (x : α) (hx : x ∉ T)
    (f : Finset α → ℚ) (D : ℚ)
    (hconstant : ∀ y ∈ insert x T,
      ∑ S ∈ (insert x T).erase y |>.powerset,
        weight ((insert x T).erase y) S *
          (f S - f (insert y S)) = D) :
    f ∅ - f (insert x T) = (T.card + 1 : ℚ) *
      (∑ S ∈ T.powerset,
        weight T S * (f S - f (insert x S))) := by
  have h := weightedMarginal_eq_endpoint_div_card T x hx f D hconstant
  have hcard : (T.card + 1 : ℚ) ≠ 0 := by positivity
  field_simp [hcard] at h
  linarith

/-- A constant nonnegative insertion marginal forces the endpoint drop to be
nonnegative.  This is the sign extraction used after the finite-support
quotient has supplied the local marginal certificate. -/
theorem endpoint_difference_nonnegative_of_constant_marginal
    [DecidableEq α] (T : Finset α) (x : α) (hx : x ∉ T)
    (f : Finset α → ℚ) (D : ℚ)
    (hconstant : ∀ y ∈ insert x T,
      ∑ S ∈ (insert x T).erase y |>.powerset,
        weight ((insert x T).erase y) S *
          (f S - f (insert y S)) = D)
    (hD : 0 ≤ D) :
    0 ≤ f ∅ - f (insert x T) := by
  rw [weightedMarginal_eq_endpoint_of_constant T x hx f D hconstant]
  have hDx :
      (∑ S ∈ T.powerset, weight T S * (f S - f (insert x S))) = D := by
    simpa [Finset.erase_insert hx] using hconstant x (Finset.mem_insert_self x T)
  rw [hDx]
  positivity


/-- The endpoint sign extraction for a finite family of local-density
contributions.  This is the form consumed by the covering argument: the
family sum has a common insertion marginal on the finite dependency set. -/
theorem endpoint_difference_nonnegative_of_family_constant_marginal
    [DecidableEq α] {β : Type u} (T : Finset α) (x : α) (hx : x ∉ T)
    (W : Finset β) (f : β → Finset α → ℚ) (D : ℚ)
    (hconstant : ∀ y ∈ insert x T,
      ∑ b ∈ W, ∑ S ∈ (insert x T).erase y |>.powerset,
        weight ((insert x T).erase y) S *
          (f b S - f b (insert y S)) = D)
    (hD : 0 ≤ D) :
    0 ≤ (∑ b ∈ W, f b ∅) -
      (∑ b ∈ W, f b (insert x T)) := by
  let F : Finset α → ℚ := fun S ↦ ∑ b ∈ W, f b S
  have hF : ∀ y ∈ insert x T,
      ∑ S ∈ (insert x T).erase y |>.powerset,
        weight ((insert x T).erase y) S *
          (F S - F (insert y S)) = D := by
    intro y hy
    calc
      ∑ S ∈ (insert x T).erase y |>.powerset,
          weight ((insert x T).erase y) S *
            (F S - F (insert y S)) =
          ∑ S ∈ (insert x T).erase y |>.powerset,
            ∑ b ∈ W, weight ((insert x T).erase y) S *
              (f b S - f b (insert y S)) := by
        apply Finset.sum_congr rfl
        intro S hS
        simp only [F]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      _ = ∑ b ∈ W, ∑ S ∈ (insert x T).erase y |>.powerset,
            weight ((insert x T).erase y) S *
              (f b S - f b (insert y S)) := by
        rw [Finset.sum_comm]
      _ = D := hconstant y hy
  have hendpoint := endpoint_difference_nonnegative_of_constant_marginal
    T x hx F D hF hD
  simpa only [F] using hendpoint

/-- A finite occurrence bijection converts all dependency marginals of orbit
representatives into the distinguished-object local-change average. -/
theorem finiteSupportOrbitAverage_of_occurrenceEquiv [DecidableEq α]
    {β : Type u} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    (W : Finset β)
    (e : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}) ≃
      {b : β // b ∈ W})
    (hMarginal : ∀ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
      insertionMarginal (K p.1.1) (f p.1.1) p.2.1 =
        ∑ S ∈ T.powerset, weight T S *
          (f (e p).1 S - f (e p).1 (insert x S))) :
    (∑ b ∈ R, (f b ∅ - f b (K b))) =
      ∑ S ∈ T.powerset, weight T S *
        (∑ b ∈ W, (f b S - f b (insert x S))) := by
  let A := (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1})
  let B := {b : β // b ∈ W}
  have hleft :
      (∑ b ∈ R, ∑ y ∈ K b,
        insertionMarginal (K b) (f b) y) =
      ∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1 := by
    calc
      (∑ b ∈ R, ∑ y ∈ K b,
        insertionMarginal (K b) (f b) y) =
          ∑ b : {b // b ∈ R}, ∑ y ∈ K b.1,
            insertionMarginal (K b.1) (f b.1) y := by
        exact Finset.sum_subtype R (by simp) (fun b ↦
          ∑ y ∈ K b, insertionMarginal (K b) (f b) y)
      _ = ∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1 := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_subtype (K b.1) (by simp) (fun y ↦
          insertionMarginal (K b.1) (f b.1) y)
  have hmiddle :
      (∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1) =
        ∑ q : B, ∑ S ∈ T.powerset, weight T S *
          (f q.1 S - f q.1 (insert x S)) := by
    calc
      (∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1) =
          ∑ p : A, ∑ S ∈ T.powerset, weight T S *
            (f (e p).1 S - f (e p).1 (insert x S)) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hMarginal p
      _ = ∑ q : B, ∑ S ∈ T.powerset, weight T S *
          (f q.1 S - f q.1 (insert x S)) := by
        exact Fintype.sum_equiv e
          (fun p ↦ ∑ S ∈ T.powerset, weight T S *
            (f (e p).1 S - f (e p).1 (insert x S)))
          (fun q ↦ ∑ S ∈ T.powerset, weight T S *
            (f q.1 S - f q.1 (insert x S)))
          (fun p ↦ by rfl)
  calc
    (∑ b ∈ R, (f b ∅ - f b (K b))) =
        ∑ b ∈ R, ∑ y ∈ K b, insertionMarginal (K b) (f b) y := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [endpoint_difference_eq_sum_insertionMarginal (K b) (f b)]
    _ = ∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1 := hleft
    _ = ∑ q : B, ∑ S ∈ T.powerset, weight T S *
          (f q.1 S - f q.1 (insert x S)) := hmiddle
    _ = ∑ S ∈ T.powerset, weight T S *
          (∑ b ∈ W, (f b S - f b (insert x S))) := by
      let inner : β → ℚ := fun b ↦ ∑ S ∈ T.powerset, weight T S *
        (f b S - f b (insert x S))
      have hsub :
          (∑ q : B, inner q.1) = ∑ b ∈ W, inner b := by
        exact (Finset.sum_subtype W (by simp) inner).symm
      calc
        (∑ q : B, ∑ S ∈ T.powerset, weight T S *
            (f q.1 S - f q.1 (insert x S))) =
            ∑ q : B, inner q.1 := by rfl
        _ = ∑ b ∈ W, inner b := hsub
        _ = ∑ S ∈ T.powerset, ∑ b ∈ W, weight T S *
            (f b S - f b (insert x S)) := by
          rw [Finset.sum_comm]
        _ = ∑ S ∈ T.powerset, weight T S *
            (∑ b ∈ W, (f b S - f b (insert x S))) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.mul_sum]

/- The occurrence-indexed form keeps repeated affected modules explicit.  It is
   useful when the categorical bridge has a finite occurrence list but does
   not need to quotient that list by isomorphism classes. -/
theorem finiteSupportOrbitAverage_of_occurrence [DecidableEq α]
    {β : Type v} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    {γ : Type w}
    (q : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}) → γ)
    (g : γ → Finset α → ℚ)
    (hMarginal : ∀ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
      insertionMarginal (K p.1.1) (f p.1.1) p.2.1 =
        ∑ S ∈ T.powerset, weight T S *
          (g (q p) S - g (q p) (insert x S))) :
    (∑ b ∈ R, (f b ∅ - f b (K b))) =
      ∑ S ∈ T.powerset, weight T S *
        (∑ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
          (g (q p) S - g (q p) (insert x S))) := by
  let A := (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1})
  have hleft :
      (∑ b ∈ R, ∑ y ∈ K b,
        insertionMarginal (K b) (f b) y) =
      ∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1 := by
    calc
      (∑ b ∈ R, ∑ y ∈ K b,
        insertionMarginal (K b) (f b) y) =
          ∑ b : {b // b ∈ R}, ∑ y ∈ K b.1,
            insertionMarginal (K b.1) (f b.1) y := by
        exact Finset.sum_subtype R (by simp) (fun b ↦
          ∑ y ∈ K b, insertionMarginal (K b) (f b) y)
      _ = ∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1 := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_subtype (K b.1) (by simp) (fun y ↦
          insertionMarginal (K b.1) (f b.1) y)
  calc
    (∑ b ∈ R, (f b ∅ - f b (K b))) =
        ∑ b ∈ R, ∑ y ∈ K b, insertionMarginal (K b) (f b) y := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [endpoint_difference_eq_sum_insertionMarginal (K b) (f b)]
    _ = ∑ p : A, insertionMarginal (K p.1.1) (f p.1.1) p.2.1 := hleft
    _ = ∑ p : A, ∑ S ∈ T.powerset, weight T S *
          (g (q p) S - g (q p) (insert x S)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hMarginal p
    _ = ∑ S ∈ T.powerset, ∑ p : A, weight T S *
          (g (q p) S - g (q p) (insert x S)) := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ T.powerset, weight T S *
          (∑ p : A, (g (q p) S - g (q p) (insert x S))) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mul_sum]

theorem finiteSupportOrbitAverage_nonnegative_of_occurrence
    [DecidableEq α] {β : Type v} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    {γ : Type w}
    (q : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}) → γ)
    (g : γ → Finset α → ℚ)
    (hMarginal : ∀ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
      insertionMarginal (K p.1.1) (f p.1.1) p.2.1 =
        ∑ S ∈ T.powerset, weight T S *
          (g (q p) S - g (q p) (insert x S)))
    (hlocal : ∀ S ∈ T.powerset,
      0 ≤ ∑ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
        (g (q p) S - g (q p) (insert x S))) :
    0 ≤ ∑ b ∈ R, (f b ∅ - f b (K b)) := by
  rw [finiteSupportOrbitAverage_of_occurrence R K f T x hx q g hMarginal]
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (le_of_lt (weight_pos T S)) (hlocal S hS)

/- A coefficient-preserving insertion of an irrelevant object is the basic
   projection step behind the frozen finite-support average. -/
theorem weightedPowersetSum_insert_irrelevant [DecidableEq α]
    (U : Finset α) (a : α) (ha : a ∉ U) (g : Finset α → ℚ)
    (hinsert : ∀ S ∈ U.powerset, g (insert a S) = g S) :
    (∑ S ∈ (insert a U).powerset, weight (insert a U) S * g S) =
      ∑ S ∈ U.powerset, weight U S * g S := by
  classical
  have hdisjoint : Disjoint U.powerset
      (U.powerset.image (fun S ↦ insert a S)) := by
    rw [Finset.disjoint_left]
    intro S hS hSa
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hSa
    have hsub : insert a T ⊆ U := Finset.mem_powerset.mp hS
    exact ha (hsub (Finset.mem_insert_self a T))
  have hinjective : Set.InjOn (fun S : Finset α ↦ insert a S)
      (U.powerset : Set (Finset α)) := by
    intro S hS T hT hEq
    have hsubS : S ⊆ U := Finset.mem_powerset.mp hS
    have hsubT : T ⊆ U := Finset.mem_powerset.mp hT
    apply Finset.ext
    intro z
    by_cases hz : z = a
    · subst z
      simp only [show a ∉ S from fun h ↦ ha (hsubS h),
        show a ∉ T from fun h ↦ ha (hsubT h)]
    · have hzEq := congrArg (fun V : Finset α ↦ z ∈ V) hEq
      simpa [hz] using hzEq
  rw [Finset.powerset_insert, Finset.sum_union hdisjoint,
    Finset.sum_image hinjective]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [hinsert S hS]
  rw [← add_mul]
  rw [weight_insert_pair U S a ha (Finset.mem_powerset.mp hS)]

/- Iterating the preceding step projects a weighted powerset sum from a
   finite ambient window to any finite dependency subset. -/
theorem weightedPowersetSum_eq_of_subset [DecidableEq α]
    (L T : Finset α) (hLT : L ⊆ T) (g : Finset α → ℚ)
    (hinsert : ∀ a ∈ T, a ∉ L → ∀ S ∈ (T.erase a).powerset,
      g (insert a S) = g S) :
    (∑ S ∈ T.powerset, weight T S * g S) =
      ∑ S ∈ L.powerset, weight L S * g S := by
  classical
  refine Finset.strongInduction
    (p := fun T : Finset α =>
      ∀ (L : Finset α), L ⊆ T → ∀ (g : Finset α → ℚ),
        (∀ a ∈ T, a ∉ L → ∀ S ∈ (T.erase a).powerset,
          g (insert a S) = g S) →
        (∑ S ∈ T.powerset, weight T S * g S) =
          ∑ S ∈ L.powerset, weight L S * g S) ?_ T L hLT g hinsert
  intro U ih L hLU g hins
  by_cases hUL : U ⊆ L
  · have hEq : U = L := Finset.Subset.antisymm hUL hLU
    subst U
    rfl
  · obtain ⟨a, haU, haL⟩ := Finset.not_subset.mp hUL
    have haErase : a ∉ U.erase a := by simp
    have hstep :
        (∑ S ∈ U.powerset, weight U S * g S) =
          ∑ S ∈ (U.erase a).powerset,
            weight (U.erase a) S * g S := by
      rw [← weightedPowersetSum_insert_irrelevant (U.erase a) a haErase g]
      · simpa [Finset.insert_erase haU]
      · intro S hS
        exact hins a haU haL S hS
    have hLsub : L ⊆ U.erase a := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨by
        intro hza
        subst z
        exact haL hz, hLU hz⟩
    have hih := ih (U.erase a) (Finset.erase_ssubset haU) L hLsub g
      (fun b hbU hbL S hS => hins b (Finset.mem_of_mem_erase hbU) hbL S
        (Finset.mem_powerset.mpr (fun z hz => by
          have hz' := Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hz)
          exact Finset.mem_erase.mpr ⟨hz'.1,
            Finset.mem_of_mem_erase hz'.2⟩)))
    exact hstep.trans hih

/- The occurrence form is the one used by the categorical bridge: after the
   incidence bijection has been constructed, positivity is discharged without
   repeating the finite arithmetic. -/
theorem finiteSupportOrbitAverage_nonnegative_of_occurrenceEquiv
    [DecidableEq α] {β : Type u} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    (W : Finset β)
    (e : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}) ≃
      {b : β // b ∈ W})
    (hMarginal : ∀ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
      insertionMarginal (K p.1.1) (f p.1.1) p.2.1 =
        ∑ S ∈ T.powerset, weight T S *
          (f (e p).1 S - f (e p).1 (insert x S)))
    (hlocal : ∀ S ∈ T.powerset,
      0 ≤ ∑ b ∈ W, (f b S - f b (insert x S))) :
    0 ≤ ∑ b ∈ R, (f b ∅ - f b (K b)) := by
  rw [finiteSupportOrbitAverage_of_occurrenceEquiv R K f T x hx W e hMarginal]
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (le_of_lt (weight_pos T S)) (hlocal S hS)

/- A small endpoint wrapper keeps the categorical bridge independent of the
   rational bookkeeping: once its two endpoint sums and the occurrence
   bijection are supplied, the frozen monotonicity statement is immediate. -/
theorem endpoint_le_of_occurrenceEquiv
    [DecidableEq α] {β : Type u} (R : Finset β) (K : β → Finset α)
    (f : β → Finset α → ℚ) (T : Finset α) (x : α) (hx : x ∉ T)
    (W : Finset β)
    (e : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}) ≃
      {b : β // b ∈ W})
    (hMarginal : ∀ p : (Σ b : {b // b ∈ R}, {y : α // y ∈ K b.1}),
      insertionMarginal (K p.1.1) (f p.1.1) p.2.1 =
        ∑ S ∈ T.powerset, weight T S *
          (f (e p).1 S - f (e p).1 (insert x S)))
    (hlocal : ∀ S ∈ T.powerset,
      0 ≤ ∑ b ∈ W, (f b S - f b (insert x S)))
    {a a' : ℚ}
    (ha : a = ∑ b ∈ R, f b ∅)
    (ha' : a' = ∑ b ∈ R, f b (K b)) :
    a' ≤ a := by
  have hsum : 0 ≤ a - a' := by
    rw [ha, ha']
    rw [← Finset.sum_sub_distrib]
    exact finiteSupportOrbitAverage_nonnegative_of_occurrenceEquiv
      R K f T x hx W e hMarginal hlocal
  linarith

end MagnitudeConjecture.DeletionOrderAverage
