import MagnitudeConjecture.Algebra.StringDetectorWordExtension

/-!
# The finite order on endpoint-polarized detector words

Route signs read a word from its fixed target toward its source.  The order
places a positive child below its parent, its parent below an inverse child,
and compares two branches at their first differing sign.  Ringel's word
subspace inclusions then show that distinct detector intervals avoid one
another.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u : Q} {t : Bool}

namespace EndpointWord

/-- The three-valued digit used to realize the in-order route comparison as
an ordinary lexicographic order: positive is below the terminal marker and
inverse is above it. -/
def routeOrderDigit (b : Bool) : Fin 3 :=
  if b then 2 else 0

theorem routeOrderDigit_injective : Function.Injective routeOrderDigit := by
  intro a b h
  cases a <;> cases b <;> simp [routeOrderDigit] at h ⊢

/-- A lexicographic key for the in-order source-extension comparison. -/
def routeOrderKey (C : EndpointWord S u t) : List (Fin 3) :=
  C.routeSigns.map routeOrderDigit ++ [1]

theorem routeOrderKey_injective :
    Function.Injective (routeOrderKey : EndpointWord S u t → List (Fin 3)) := by
  intro C D h
  apply routeSigns_injective
  apply routeOrderDigit_injective.list_map
  exact List.append_cancel_right h

/-- The canonical finite-word order is the ordinary lexicographic order on
the three-valued route key. -/
noncomputable instance endpointWordLinearOrder :
    LinearOrder (EndpointWord S u t) :=
  LinearOrder.lift' routeOrderKey routeOrderKey_injective

/-- In-order comparison of two routes in the source-extension tree.  A
positive descendant is below its ancestor, an inverse descendant is above
its ancestor, and a positive branch is below an inverse branch at their first
split. -/
def RouteLT (a b : List Bool) : Prop :=
  (∃ tail, a = b ++ false :: tail) ∨
    (∃ tail, b = a ++ true :: tail) ∨
      ∃ common left right,
        a = common ++ false :: left ∧
          b = common ++ true :: right

namespace RouteLT

/-- Prefixing the same route sign preserves the in-order comparison. -/
theorem cons {a b : List Bool} (head : Bool) (h : RouteLT a b) :
    RouteLT (head :: a) (head :: b) := by
  rcases h with ⟨tail, h⟩ | ⟨tail, h⟩ |
    ⟨common, left, right, ha, hb⟩
  · left
    refine ⟨tail, ?_⟩
    simpa only [List.cons_append] using congrArg (List.cons head) h
  · right
    left
    refine ⟨tail, ?_⟩
    simpa only [List.cons_append] using congrArg (List.cons head) h
  · right
    right
    refine ⟨head :: common, left, right, ?_, ?_⟩
    · simpa only [List.cons_append] using congrArg (List.cons head) ha
    · simpa only [List.cons_append] using congrArg (List.cons head) hb

end RouteLT

/-- The recursive route comparison implies lexicographic comparison of the
three-valued route keys. -/
theorem routeOrderKey_lt_of_routeLT {C D : EndpointWord S u t}
    (h : RouteLT C.routeSigns D.routeSigns) :
    routeOrderKey C < routeOrderKey D := by
  rcases h with ⟨tail, h⟩ | ⟨tail, h⟩ |
    ⟨common, left, right, hC, hD⟩
  · unfold routeOrderKey
    rw [h, List.map_append]
    change D.routeSigns.map routeOrderDigit ++
        routeOrderDigit false :: tail.map routeOrderDigit ++ [1] <
      D.routeSigns.map routeOrderDigit ++ [1]
    rw [List.append_assoc]
    change List.lt
      (D.routeSigns.map routeOrderDigit ++
        (routeOrderDigit false :: tail.map routeOrderDigit ++ [1]))
      (D.routeSigns.map routeOrderDigit ++ [1])
    have hlex : List.Lex (· < ·)
        (routeOrderDigit false :: tail.map routeOrderDigit ++ [1]) [1] :=
      List.Lex.rel (by decide)
    exact List.Lex.append_left (· < ·) hlex
      (D.routeSigns.map routeOrderDigit)
  · unfold routeOrderKey
    rw [h, List.map_append]
    change C.routeSigns.map routeOrderDigit ++ [1] <
      C.routeSigns.map routeOrderDigit ++
        routeOrderDigit true :: tail.map routeOrderDigit ++ [1]
    rw [List.append_assoc]
    change List.lt (C.routeSigns.map routeOrderDigit ++ [1])
      (C.routeSigns.map routeOrderDigit ++
        (routeOrderDigit true :: tail.map routeOrderDigit ++ [1]))
    have hlex : List.Lex (· < ·) [1]
        (routeOrderDigit true :: tail.map routeOrderDigit ++ [1]) :=
      List.Lex.rel (by decide)
    exact List.Lex.append_left (· < ·) hlex
      (C.routeSigns.map routeOrderDigit)
  · unfold routeOrderKey
    rw [hC, hD, List.map_append, List.map_append]
    change common.map routeOrderDigit ++
        routeOrderDigit false :: left.map routeOrderDigit ++ [1] <
      common.map routeOrderDigit ++
        routeOrderDigit true :: right.map routeOrderDigit ++ [1]
    rw [List.append_assoc, List.append_assoc]
    change List.lt
      (common.map routeOrderDigit ++
        (routeOrderDigit false :: left.map routeOrderDigit ++ [1]))
      (common.map routeOrderDigit ++
        (routeOrderDigit true :: right.map routeOrderDigit ++ [1]))
    have hlex : List.Lex (· < ·)
        (routeOrderDigit false :: left.map routeOrderDigit ++ [1])
        (routeOrderDigit true :: right.map routeOrderDigit ++ [1]) :=
      List.Lex.rel (by decide)
    exact List.Lex.append_left (· < ·) hlex
      (common.map routeOrderDigit)

/-- Any two Boolean routes are equal or comparable in exactly one of the two
in-order directions. -/
theorem route_eq_or_routeLT_or_routeLT (a b : List Bool) :
    a = b ∨ RouteLT a b ∨ RouteLT b a := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => exact Or.inl rfl
      | cons head tail =>
          cases head
          · right
            right
            left
            exact ⟨tail, by simp⟩
          · right
            left
            right
            left
            exact ⟨tail, by simp⟩
  | cons head a ih =>
      cases b with
      | nil =>
          cases head
          · right
            left
            left
            exact ⟨a, by simp⟩
          · right
            right
            right
            left
            exact ⟨a, by simp⟩
      | cons head' b =>
          cases head <;> cases head'
          · rcases ih b with h | h | h
            · exact Or.inl (congrArg (List.cons false) h)
            · exact Or.inr (Or.inl (RouteLT.cons false h))
            · exact Or.inr (Or.inr (RouteLT.cons false h))
          · right
            left
            right
            right
            exact ⟨[], a, b, by simp, by simp⟩
          · right
            right
            right
            right
            exact ⟨[], b, a, by simp, by simp⟩
          · rcases ih b with h | h | h
            · exact Or.inl (congrArg (List.cons true) h)
            · exact Or.inr (Or.inl (RouteLT.cons true h))
            · exact Or.inr (Or.inr (RouteLT.cons true h))

/-- The strict order on endpoint words induced by their route signs. -/
def WordLT (C D : EndpointWord S u t) : Prop :=
  RouteLT C.routeSigns D.routeSigns

/-- Fixed-endpoint words are equal or comparable in the two word-order
directions. -/
theorem eq_or_wordLT_or_wordLT (C D : EndpointWord S u t) :
    C = D ∨ WordLT C D ∨ WordLT D C := by
  rcases route_eq_or_routeLT_or_routeLT C.routeSigns D.routeSigns with
    h | h | h
  · exact Or.inl (routeSigns_injective h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The explicit recursive word comparison is the strict canonical order. -/
theorem wordLT_iff_lt (C D : EndpointWord S u t) :
    WordLT C D ↔ C < D := by
  constructor
  · exact routeOrderKey_lt_of_routeLT
  · intro hlt
    rcases eq_or_wordLT_or_wordLT C D with h | h | h
    · exact (hlt.ne h).elim
    · exact h
    · have hreverse : D < C := routeOrderKey_lt_of_routeLT h
      exact (asymm hlt hreverse).elim

/-- Ringel's word-order implication: if `C < D`, then the upper endpoint of
the interval of `C` lies below the lower endpoint of the interval of `D`. -/
theorem upperSubspace_le_lowerSubspace_of_wordLT
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (C D : EndpointWord S u t) (h : WordLT C D) :
    upperSubspace N C ≤ lowerSubspace N D := by
  rcases h with ⟨tail, h⟩ | ⟨tail, h⟩ |
    ⟨common, left, right, hC, hD⟩
  · exact upperSubspace_le_lowerSubspace_of_routeSigns_eq_append_false
      N D C tail h
  · exact upperSubspace_le_lowerSubspace_of_routeSigns_eq_append_true
      N C D tail h
  · obtain ⟨C₀, prefC, hC₀, _, _⟩ :=
      C.exists_endpointWord_of_routeSigns_eq_append
        common (false :: left) hC
    obtain ⟨D₀, prefD, hD₀, _, _⟩ :=
      D.exists_endpointWord_of_routeSigns_eq_append
        common (true :: right) hD
    have hbase : C₀ = D₀ := routeSigns_injective (hC₀.trans hD₀.symm)
    subst D₀
    calc
      upperSubspace N C ≤ lowerSubspace N C₀ :=
        upperSubspace_le_lowerSubspace_of_routeSigns_eq_append_false
          N C₀ C left (by simpa only [hC₀] using hC)
      _ ≤ upperSubspace N C₀ := lowerSubspace_le_upperSubspace N C₀
      _ ≤ lowerSubspace N D :=
        upperSubspace_le_lowerSubspace_of_routeSigns_eq_append_true
          N C₀ D right (by simpa only [hC₀] using hD)

/-- Distinct fixed-endpoint word intervals avoid one another. -/
theorem eq_or_intervals_avoid
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (C D : EndpointWord S u t) :
    C = D ∨ upperSubspace N C ≤ lowerSubspace N D ∨
      upperSubspace N D ≤ lowerSubspace N C := by
  rcases eq_or_wordLT_or_wordLT C D with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (upperSubspace_le_lowerSubspace_of_wordLT N C D h))
  · exact Or.inr (Or.inr (upperSubspace_le_lowerSubspace_of_wordLT N D C h))

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
