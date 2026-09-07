import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory

/-!
# Finite convex neighborhoods from an integer rank

A locally finite relation which strictly raises an integer rank has finite
bounded reachability sets.  This gives finite convex neighborhoods by taking
the bounded upward closure of a finite set.  The result is used for the
height-graded universal mesh cover.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.CoveringHom

universe u

variable {C : Type u}

private theorem rank_le_of_reflTransGen
    (R : C → C → Prop) (rank : C → ℤ)
    (hrank : ∀ {X Y}, R X Y → rank X < rank Y)
    {X Y : C} (hXY : Relation.ReflTransGen R X Y) :
    rank X ≤ rank Y := by
  induction hXY with
  | refl => exact le_rfl
  | tail _ hYZ ih => exact ih.trans (hrank hYZ).le

private theorem finite_bounded_reachable
    (R : C → C → Prop) (rank : C → ℤ)
    (hfinite : ∀ X, {Y | R X Y}.Finite)
    (hrank : ∀ {X Y}, R X Y → rank X < rank Y)
    (b : ℤ) (X : C) (hXb : rank X ≤ b) :
    {Y | Relation.ReflTransGen R X Y ∧ rank Y ≤ b}.Finite := by
  generalize hn : Int.toNat (b - rank X) = n
  induction n using Nat.strong_induction_on generalizing X with
  | h n ih =>
      let next : Set C := {Y | R X Y ∧ rank Y ≤ b}
      have hnext : next.Finite :=
        (hfinite X).subset (fun _ hY ↦ hY.1)
      have htail :
          (⋃ Y ∈ next,
            {Z | Relation.ReflTransGen R Y Z ∧ rank Z ≤ b}).Finite := by
        refine hnext.biUnion fun Y hY ↦ ?_
        change R X Y ∧ rank Y ≤ b at hY
        have hgap : Int.toNat (b - rank Y) < n := by
          rw [← hn]
          have hXY : rank X < rank Y := hrank hY.1
          have hXnonneg : 0 ≤ b - rank X := by omega
          have hYnonneg : 0 ≤ b - rank Y := by omega
          have hXcast : (Int.toNat (b - rank X) : ℤ) = b - rank X :=
            Int.toNat_of_nonneg hXnonneg
          have hYcast : (Int.toNat (b - rank Y) : ℤ) = b - rank Y :=
            Int.toNat_of_nonneg hYnonneg
          omega
        exact ih (Int.toNat (b - rank Y)) hgap Y hY.2 rfl
      refine ((Set.finite_singleton X).union htail).subset ?_
      intro Y hY
      rcases hY.1.cases_head with hYX | ⟨Z, hXZ, hZY⟩
      · subst Y
        exact Or.inl rfl
      · apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨Z, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
        · exact ⟨hXZ,
            (rank_le_of_reflTransGen R rank hrank hZY).trans hY.2⟩
        · exact ⟨hZY, hY.2⟩

/-- If a locally finite relation strictly raises an integer rank, then every
finite set is contained in a finite set convex for its reflexive-transitive
closure. -/
theorem hasFiniteConvexObjectNeighborhoods_of_rank
    (R : C → C → Prop) (rank : C → ℤ)
    (hfinite : ∀ X, {Y | R X Y}.Finite)
    (hrank : ∀ {X Y}, R X Y → rank X < rank Y) :
    ∀ T : Set C, T.Finite →
      ∃ U : Set C, U.Finite ∧ T ⊆ U ∧
        ∀ {X Y Z : C}, X ∈ U → Z ∈ U →
          Relation.ReflTransGen R X Y →
          Relation.ReflTransGen R Y Z → Y ∈ U := by
  intro T hT
  obtain ⟨b, hb⟩ := (hT.image rank).bddAbove
  let U : Set C :=
    ⋃ X ∈ T, {Y | Relation.ReflTransGen R X Y ∧ rank Y ≤ b}
  have hUfinite : U.Finite := by
    refine hT.biUnion fun X hXT ↦ ?_
    exact finite_bounded_reachable R rank hfinite hrank b X
      (hb ⟨X, hXT, rfl⟩)
  refine ⟨U, hUfinite, ?_, ?_⟩
  · intro X hXT
    apply Set.mem_iUnion.mpr
    refine ⟨X, Set.mem_iUnion.mpr ⟨hXT, ?_⟩⟩
    exact ⟨Relation.ReflTransGen.refl, hb ⟨X, hXT, rfl⟩⟩
  · intro X Y Z hXU hZU hXY hYZ
    rcases Set.mem_iUnion.mp hXU with ⟨W, hXU⟩
    rcases Set.mem_iUnion.mp hXU with ⟨hWT, hWX⟩
    rcases Set.mem_iUnion.mp hZU with ⟨V, hZU⟩
    rcases Set.mem_iUnion.mp hZU with ⟨hVT, hVZ⟩
    apply Set.mem_iUnion.mpr
    refine ⟨W, Set.mem_iUnion.mpr ⟨hWT, ?_⟩⟩
    exact ⟨hWX.1.trans hXY,
      (rank_le_of_reflTransGen R rank hrank hYZ).trans hVZ.2⟩

end MagnitudeConjecture.CoveringHom
