import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.OrbitPullupPushdownDecomposition
import MagnitudeConjecture.Combinatorics.TranslationInvariantSubset
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Finite-support summands of pull-up/push-down

An idempotent on the explicit direct sum of pairwise nonisomorphic
indecomposable translates is the identity if every diagonal component is an
isomorphism.  The proof restricts each individual direct-sum element to its
finite support and applies the finite Krull--Schmidt matrix theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

variable (M : C ⥤ ModuleCat.{w} k)
variable [M.Additive] [M.Linear k]

local instance : HasFiniteBiproducts
    (C ⥤ ModuleCat.{w} k) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A small finite index type enumerating a finite subset of the deck group. -/
abbrev orbitPullupPushdownFiniteIndex (s : Finset A) :=
  Fin (Fintype.card s)

/-- The deck-group label at one index of the chosen finite enumeration. -/
noncomputable def orbitPullupPushdownFiniteLabel
    (s : Finset A) (i : orbitPullupPushdownFiniteIndex s) : A :=
  ((Fintype.equivFin s).symm i).1

omit [AddGroup A] in
theorem orbitPullupPushdownFiniteLabel_mem
    (s : Finset A) (i : orbitPullupPushdownFiniteIndex s) :
    orbitPullupPushdownFiniteLabel s i ∈ s :=
  ((Fintype.equivFin s).symm i).2

omit [AddGroup A] in
theorem orbitPullupPushdownFiniteLabel_injective (s : Finset A) :
    Function.Injective (orbitPullupPushdownFiniteLabel s) := by
  intro i j hij
  apply (Fintype.equivFin s).symm.injective
  exact Subtype.ext hij

/-- The finite biproduct of translates indexed by a finite subset of the
deck group. -/
abbrev orbitPullupPushdownFiniteTranslate (s : Finset A) :=
  ⨁ fun i : orbitPullupPushdownFiniteIndex s ↦
    orbitPullupPushdownTranslate (A := A) M
      (orbitPullupPushdownFiniteLabel s i)

/-- Include a finite biproduct of translates in the full direct sum. -/
noncomputable def orbitPullupPushdownFiniteInclude (s : Finset A) :
    orbitPullupPushdownFiniteTranslate (A := A) M s ⟶
      orbitPullupPushdown (A := A) M :=
  biproduct.desc fun b ↦
    orbitPullupPushdownTranslateLof (A := A) M
      (orbitPullupPushdownFiniteLabel s b)

/-- Project the full direct sum onto a finite biproduct of translates. -/
noncomputable def orbitPullupPushdownFiniteProject (s : Finset A) :
    orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdownFiniteTranslate (A := A) M s :=
  biproduct.lift fun b ↦
    orbitPullupPushdownTranslateComponent (A := A) M
      (orbitPullupPushdownFiniteLabel s b)

/-- The finite square matrix obtained by restricting an endomorphism of the
full translate sum to a finite set of rows and columns. -/
noncomputable def orbitPullupPushdownFiniteRestriction
    (s : Finset A)
    (p : orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdown (A := A) M) :
    orbitPullupPushdownFiniteTranslate (A := A) M s ⟶
      orbitPullupPushdownFiniteTranslate (A := A) M s :=
  orbitPullupPushdownFiniteInclude (A := A) M s ≫ p ≫
    orbitPullupPushdownFiniteProject (A := A) M s

@[reassoc]
theorem orbitPullupPushdownFiniteRestriction_component
    (s : Finset A)
    (p : orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdown (A := A) M)
    (b c : orbitPullupPushdownFiniteIndex s) :
    biproduct.ι (fun i : orbitPullupPushdownFiniteIndex s ↦
        orbitPullupPushdownTranslate (A := A) M
          (orbitPullupPushdownFiniteLabel s i)) b ≫
        orbitPullupPushdownFiniteRestriction (A := A) M s p ≫
        biproduct.π (fun i : orbitPullupPushdownFiniteIndex s ↦
          orbitPullupPushdownTranslate (A := A) M
            (orbitPullupPushdownFiniteLabel s i)) c =
      orbitPullupPushdownTranslateLof (A := A) M
          (orbitPullupPushdownFiniteLabel s b) ≫ p ≫
        orbitPullupPushdownTranslateComponent (A := A) M
          (orbitPullupPushdownFiniteLabel s c) := by
  simp [orbitPullupPushdownFiniteRestriction,
    orbitPullupPushdownFiniteInclude,
    orbitPullupPushdownFiniteProject, Category.assoc]

/-- The finite restriction has invertible diagonal, hence is invertible. -/
theorem orbitPullupPushdownFiniteRestriction_isIso
    (s : Finset A)
    (p : orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdown (A := A) M)
    (hindecomp : ∀ b : A,
      Indecomposable (orbitPullupPushdownTranslate (A := A) M b))
    (hlocal : ∀ b : A,
      IsLocalRing (End
        (orbitPullupPushdownTranslate (A := A) M b)))
    (hpair : ∀ b c : A, b ≠ c →
      ¬ Nonempty
        (orbitPullupPushdownTranslate (A := A) M b ≅
          orbitPullupPushdownTranslate (A := A) M c))
    (hdiag : ∀ b : A, IsIso
      (orbitPullupPushdownTranslateLof (A := A) M b ≫ p ≫
        orbitPullupPushdownTranslateComponent (A := A) M b)) :
    IsIso (orbitPullupPushdownFiniteRestriction (A := A) M s p) := by
  apply MagnitudeConjecture.CategoryTheory.isIso_of_finBiproduct_diagonal_isIso
    (fun i : orbitPullupPushdownFiniteIndex s ↦
      orbitPullupPushdownTranslate (A := A) M
        (orbitPullupPushdownFiniteLabel s i))
    (fun i ↦ hindecomp (orbitPullupPushdownFiniteLabel s i))
    (fun i ↦ hlocal (orbitPullupPushdownFiniteLabel s i))
    (fun i j hij ↦ hpair _ _ fun h ↦
      hij (orbitPullupPushdownFiniteLabel_injective s h))
  intro b
  rw [orbitPullupPushdownFiniteRestriction_component]
  exact hdiag (orbitPullupPushdownFiniteLabel s b)

set_option backward.isDefEq.respectTransparency false in
/-- Projecting an element onto the finite biproduct indexed by its support and
then including it again recovers the element. -/
theorem orbitPullupPushdownFiniteProject_include_apply_support
    (s : Finset A) (X : C) (x : orbitPushdownValue (A := A) M X)
    (hx : ∀ b : A, b ∉ s → x b = 0) :
    ((orbitPullupPushdownFiniteProject (A := A) M s ≫
        orbitPullupPushdownFiniteInclude (A := A) M s).app X).hom x =
      x := by
  classical
  have hcomp :
      orbitPullupPushdownFiniteProject (A := A) M s ≫
          orbitPullupPushdownFiniteInclude (A := A) M s =
        ∑ i : orbitPullupPushdownFiniteIndex s,
          orbitPullupPushdownTranslateComponent (A := A) M
              (orbitPullupPushdownFiniteLabel s i) ≫
            orbitPullupPushdownTranslateLof (A := A) M
              (orbitPullupPushdownFiniteLabel s i) := by
    exact biproduct.lift_desc
      (C := C ⥤ ModuleCat.{w} k)
      (J := orbitPullupPushdownFiniteIndex s)
      (f := fun i : orbitPullupPushdownFiniteIndex s ↦
        orbitPullupPushdownTranslate (A := A) M
          (orbitPullupPushdownFiniteLabel s i))
      (T := orbitPullupPushdown (A := A) M)
      (U := orbitPullupPushdown (A := A) M)
      (g := fun i : orbitPullupPushdownFiniteIndex s ↦
        orbitPullupPushdownTranslateComponent (A := A) M
          (orbitPullupPushdownFiniteLabel s i))
      (h := fun i : orbitPullupPushdownFiniteIndex s ↦
        orbitPullupPushdownTranslateLof (A := A) M
          (orbitPullupPushdownFiniteLabel s i))
  calc
    ((orbitPullupPushdownFiniteProject (A := A) M s ≫
          orbitPullupPushdownFiniteInclude (A := A) M s).app X).hom x =
        ((∑ i : orbitPullupPushdownFiniteIndex s,
          orbitPullupPushdownTranslateComponent (A := A) M
              (orbitPullupPushdownFiniteLabel s i) ≫
            orbitPullupPushdownTranslateLof (A := A) M
              (orbitPullupPushdownFiniteLabel s i)).app X).hom x := by
      rw [hcomp]
    _ = ∑ i : orbitPullupPushdownFiniteIndex s,
        orbitPushdownLof M X (orbitPullupPushdownFiniteLabel s i)
          (DirectSum.component k A
            (fun c ↦ M.obj ((shiftFunctor C c).obj X))
              (orbitPullupPushdownFiniteLabel s i) x) := by
      simp [orbitPullupPushdownTranslateComponent,
        orbitPullupPushdownTranslateLof]
      rfl
    _ = x := by
      apply DirectSum.ext_component k
      intro b
      simp only [map_sum]
      by_cases hb : b ∈ s
      · let b' : orbitPullupPushdownFiniteIndex s :=
          Fintype.equivFin s ⟨b, hb⟩
        have hlabel : orbitPullupPushdownFiniteLabel s b' = b := by
          simp [orbitPullupPushdownFiniteLabel, b']
        rw [Finset.sum_eq_single b']
        · rw [hlabel, orbitPushdownLof,
            DirectSum.component.lof_self]
        · intro c hc hcb
          have hne : orbitPullupPushdownFiniteLabel s c ≠ b :=
            fun h ↦ hcb (orbitPullupPushdownFiniteLabel_injective s
              (h.trans hlabel.symm))
          rw [orbitPushdownLof, DirectSum.component.of]
          simp [hne]
        · intro hb'
          exact (hb' (Finset.mem_univ b')).elim
      · rw [Finset.sum_eq_zero]
        · exact (hx b hb).symm
        · intro c hc
          have hne : orbitPullupPushdownFiniteLabel s c ≠ b :=
            fun h ↦ hb (h ▸ orbitPullupPushdownFiniteLabel_mem s c)
          rw [orbitPushdownLof, DirectSum.component.of]
          simp [hne]

set_option backward.isDefEq.respectTransparency false in
/-- An idempotent on the explicit translate direct sum is the identity when
all its diagonal components are invertible. -/
theorem orbitPullupPushdown_idempotent_eq_id_of_diagonal_isIso
    (p : orbitPullupPushdown (A := A) M ⟶
      orbitPullupPushdown (A := A) M)
    (hp : p ≫ p = p)
    (hindecomp : ∀ b : A,
      Indecomposable (orbitPullupPushdownTranslate (A := A) M b))
    (hlocal : ∀ b : A,
      IsLocalRing (End
        (orbitPullupPushdownTranslate (A := A) M b)))
    (hpair : ∀ b c : A, b ≠ c →
      ¬ Nonempty
        (orbitPullupPushdownTranslate (A := A) M b ≅
          orbitPullupPushdownTranslate (A := A) M c))
    (hdiag : ∀ b : A, IsIso
      (orbitPullupPushdownTranslateLof (A := A) M b ≫ p ≫
        orbitPullupPushdownTranslateComponent (A := A) M b)) :
    p = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hzero (y : orbitPushdownValue (A := A) M X)
      (hy : p.app X y = 0) : y = 0 := by
    let s : Finset A := y.support
    let q := orbitPullupPushdownFiniteRestriction (A := A) M s p
    letI : IsIso q :=
      orbitPullupPushdownFiniteRestriction_isIso (A := A) M s p
        hindecomp hlocal hpair hdiag
    let z :=
      (orbitPullupPushdownFiniteProject (A := A) M s).app X y
    have hz : q.app X z = 0 := by
      change
        (orbitPullupPushdownFiniteProject (A := A) M s).app X
          (p.app X
            ((orbitPullupPushdownFiniteInclude (A := A) M s).app X z)) = 0
      have hrecover :=
        orbitPullupPushdownFiniteProject_include_apply_support
          (A := A) M s X y (fun b hb ↦
            DFinsupp.notMem_support_iff.mp hb)
      change
        (orbitPullupPushdownFiniteInclude (A := A) M s).app X z = y at hrecover
      rw [hrecover, hy]
      simp
    have hz0 : z = 0 := by
      have hzinv := congrArg
        (fun a ↦ (inv (q.app X)).hom a) hz
      simpa using hzinv
    have hrecover :=
      orbitPullupPushdownFiniteProject_include_apply_support
        (A := A) M s X y (fun b hb ↦
          DFinsupp.notMem_support_iff.mp hb)
    change
      (orbitPullupPushdownFiniteInclude (A := A) M s).app X z = y at hrecover
    rw [hz0] at hrecover
    calc
      y = (orbitPullupPushdownFiniteInclude (A := A) M s).app X 0 :=
        hrecover.symm
      _ = 0 := map_zero _
  have hpx := congrArg (fun q ↦ q.app X) hp
  have hpx' := congrArg (fun q ↦ q.hom x) hpx
  have hdiff : p.app X (p.app X x - x) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hpx'
  have hzero' := hzero (p.app X x - x) hdiff
  exact sub_eq_zero.mp hzero'

/-- A retract of the translate direct sum is the whole direct sum when the
associated projector has invertible diagonal components. -/
theorem orbitPullupPushdown_isIso_of_retraction_of_diagonal_isIso
    {L : C ⥤ ModuleCat.{w} k}
    (j : L ⟶ orbitPullupPushdown (A := A) M)
    (r : orbitPullupPushdown (A := A) M ⟶ L)
    (hjr : j ≫ r = 𝟙 L)
    (hindecomp : ∀ b : A,
      Indecomposable (orbitPullupPushdownTranslate (A := A) M b))
    (hlocal : ∀ b : A,
      IsLocalRing (End
        (orbitPullupPushdownTranslate (A := A) M b)))
    (hpair : ∀ b c : A, b ≠ c →
      ¬ Nonempty
        (orbitPullupPushdownTranslate (A := A) M b ≅
          orbitPullupPushdownTranslate (A := A) M c))
    (hdiag : ∀ b : A, IsIso
      (orbitPullupPushdownTranslateLof (A := A) M b ≫
        r ≫ j ≫
        orbitPullupPushdownTranslateComponent (A := A) M b)) :
    IsIso j := by
  have hp : (r ≫ j) ≫ (r ≫ j) = r ≫ j := by
    calc
      _ = r ≫ (j ≫ r) ≫ j := by simp only [Category.assoc]
      _ = r ≫ j := by rw [hjr]; simp
  have hpid := orbitPullupPushdown_idempotent_eq_id_of_diagonal_isIso
    (A := A) M (r ≫ j) hp hindecomp hlocal hpair (fun b ↦ by
      simpa only [Category.assoc] using hdiag b)
  apply IsIso.mk
  exact ⟨r, hjr, hpid⟩

/-- Explicit-retraction form of the invariant-summand theorem.  This form is
stable under applying a functor because it retains the chosen complementary
projectors rather than asking `IsSplitMono` to choose new retractions. -/
theorem orbitPullupPushdown_one_retract_inclusion_isIso_of_invariant_diagonal
    {L Q : C ⥤ ModuleCat.{w} k}
    (j : L ⟶ orbitPullupPushdown (A := A) M)
    (r : orbitPullupPushdown (A := A) M ⟶ L)
    (hjr : j ≫ r = 𝟙 L)
    (j' : Q ⟶ orbitPullupPushdown (A := A) M)
    (r' : orbitPullupPushdown (A := A) M ⟶ Q)
    (hj'r' : j' ≫ r' = 𝟙 Q)
    (htotal : r ≫ j + r' ≫ j' = 𝟙 _)
    (hindecomp : ∀ b : A,
      Indecomposable (orbitPullupPushdownTranslate (A := A) M b))
    (hlocal : ∀ b : A,
      IsLocalRing (End
        (orbitPullupPushdownTranslate (A := A) M b)))
    (hpair : ∀ b c : A, b ≠ c →
      ¬ Nonempty
        (orbitPullupPushdownTranslate (A := A) M b ≅
          orbitPullupPushdownTranslate (A := A) M c))
    (hinvariant : ∀ a b : A,
      IsIso
          (orbitPullupPushdownTranslateLof (A := A) M b ≫
            r ≫ j ≫
            orbitPullupPushdownTranslateComponent (A := A) M b) ↔
        IsIso
          (orbitPullupPushdownTranslateLof (A := A) M (a + b) ≫
            r ≫ j ≫
            orbitPullupPushdownTranslateComponent (A := A) M (a + b))) :
    IsIso j ∨ IsIso j' := by
  letI localEnd (b : A) : IsLocalRing
      (End (orbitPullupPushdownTranslate (A := A) M b)) := hlocal b
  let H : Set A := {b | IsIso
    (orbitPullupPushdownTranslateLof (A := A) M b ≫
      r ≫ j ≫
      orbitPullupPushdownTranslateComponent (A := A) M b)}
  have hchoice (b : A) :
      IsIso
          (orbitPullupPushdownTranslateLof (A := A) M b ≫
            r ≫ j ≫
            orbitPullupPushdownTranslateComponent (A := A) M b) ∨
        IsIso
          (orbitPullupPushdownTranslateLof (A := A) M b ≫
            r' ≫ j' ≫
            orbitPullupPushdownTranslateComponent (A := A) M b) := by
    apply MagnitudeConjecture.CategoryTheory.isIso_or_isIso_of_add_eq_id
    calc
      (orbitPullupPushdownTranslateLof (A := A) M b ≫
          r ≫ j ≫
          orbitPullupPushdownTranslateComponent (A := A) M b) +
          (orbitPullupPushdownTranslateLof (A := A) M b ≫
            r' ≫ j' ≫
            orbitPullupPushdownTranslateComponent (A := A) M b) =
        orbitPullupPushdownTranslateLof (A := A) M b ≫
          (r ≫ j + r' ≫ j') ≫
          orbitPullupPushdownTranslateComponent (A := A) M b := by
            simp only [Preadditive.comp_add, Preadditive.add_comp,
              Category.assoc]
      _ = orbitPullupPushdownTranslateLof (A := A) M b ≫
          𝟙 _ ≫
          orbitPullupPushdownTranslateComponent (A := A) M b := by
            rw [htotal]
      _ = 𝟙 _ := by simp
  have hH : H = ∅ ∨ H = Set.univ :=
    MagnitudeConjecture.CoveringAction.eq_empty_or_univ_of_add_left_invariant
      H hinvariant
  rcases hH with hH | hH
  · right
    apply orbitPullupPushdown_isIso_of_retraction_of_diagonal_isIso
      (A := A) M j' r' hj'r' hindecomp hlocal hpair
    intro b
    apply (hchoice b).resolve_left
    intro hb
    have hbH : b ∈ H := hb
    rw [hH] at hbH
    exact hbH
  · left
    apply orbitPullupPushdown_isIso_of_retraction_of_diagonal_isIso
      (A := A) M j r hjr hindecomp hlocal hpair
    intro b
    have hbH : b ∈ H := by
      rw [hH]
      exact Set.mem_univ b
    exact hbH

end MagnitudeConjecture.CoveringHom
