import MagnitudeConjecture.CategoryTheory.LinearPathLift
import MagnitudeConjecture.CategoryTheory.LinearPathIncoming

/-!
# Decomposition by the first represented arrow

A morphism in the free reversed linear path category between distinct
vertices is a finite sum of one represented arrow out of its categorical
source followed by a coefficient path.  This is the free-category form used
by Ringel's recursive fullness construction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.LinearPathCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- Reversed quiver arrows whose represented categorical maps start at
`x`. -/
abbrev OutgoingArrow (x : Q) := Σ y : Q, y ⟶ x

variable [∀ x : Q, Fintype (OutgoingArrow x)]

/-- The free-path morphism represented by one arrow out of `x`. -/
def outgoingArrowHom {x : Q} (a : OutgoingArrow x) :
    obj k Q x ⟶ obj k Q a.1 :=
  pathHom a.2.toPath

/-- One free-path coefficient after every arrow out of `x`. -/
abbrev OutgoingCoefficient (x z : Q) :=
  ∀ a : OutgoingArrow x, obj k Q a.1 ⟶ obj k Q z

/-- Sum of all first-arrow factorizations. -/
def outgoingSum {x z : Q} (c : OutgoingCoefficient (k := k) x z) :
    obj k Q x ⟶ obj k Q z :=
  ∑ a : OutgoingArrow x, outgoingArrowHom (k := k) a ≫ c a

/-- A coefficient family supported after one outgoing arrow. -/
def singleOutgoingCoefficient {x z : Q} (a₀ : OutgoingArrow x)
    (f : obj k Q a₀.1 ⟶ obj k Q z) :
    OutgoingCoefficient (k := k) x z := by
  classical
  exact fun a ↦ if h : a₀ = a then
      eqToHom (congrArg (fun b : OutgoingArrow x ↦ obj k Q b.1) h.symm) ≫ f
    else 0

@[simp]
theorem outgoingSum_single {x z : Q} (a₀ : OutgoingArrow x)
    (f : obj k Q a₀.1 ⟶ obj k Q z) :
    outgoingSum (singleOutgoingCoefficient (k := k) a₀ f) =
      outgoingArrowHom (k := k) a₀ ≫ f := by
  classical
  rw [outgoingSum, Finset.sum_eq_single a₀]
  · simp [singleOutgoingCoefficient]
  · intro a _ ha
    simp [singleOutgoingCoefficient, Ne.symm ha]
  · simp

/-- Between distinct vertices, every free-path morphism is a sum grouped by
its first represented categorical arrow. -/
theorem exists_eq_outgoingSum_of_ne {x z : Q} (hxz : x ≠ z)
    (f : obj k Q x ⟶ obj k Q z) :
    ∃ h : OutgoingCoefficient (k := k) x z, f = outgoingSum h := by
  classical
  let f' := homPathLinearEquiv (obj k Q x) (obj k Q z) f
  rw [← (homPathLinearEquiv
    (obj k Q x) (obj k Q z)).symm_apply_apply f]
  change ∃ h : OutgoingCoefficient (k := k) x z,
    (homPathLinearEquiv (obj k Q x) (obj k Q z)).symm f' =
      outgoingSum h
  induction f' using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, ?_⟩
      simp [outgoingSum]
  | add f₁ f₂ hf₁ hf₂ =>
      obtain ⟨h₁, hh₁⟩ := hf₁
      obtain ⟨h₂, hh₂⟩ := hf₂
      refine ⟨h₁ + h₂, ?_⟩
      rw [(homPathLinearEquiv
        (obj k Q x) (obj k Q z)).symm.map_add, hh₁, hh₂]
      simp only [outgoingSum, Pi.add_apply, Preadditive.comp_add,
        Finset.sum_add_distrib]
  | single p r =>
      rw [homPathLinearEquiv_symm_single]
      have hp : p.length ≠ 0 := by
        intro hpzero
        exact hxz (p.eq_of_length_zero hpzero).symm
      obtain ⟨y, q, a, hpq⟩ :=
        (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hp
      subst p
      let a₀ : OutgoingArrow x := ⟨y, a⟩
      let qHom : obj k Q y ⟶ obj k Q z := pathHom q
      refine ⟨singleOutgoingCoefficient (k := k) a₀ (r • qHom), ?_⟩
      rw [outgoingSum_single]
      dsimp only [a₀, qHom, outgoingArrowHom]
      rw [CategoryTheory.Linear.comp_smul, pathHom_comp]
      rfl

/-- Every free-path endomorphism is a scalar identity plus a sum grouped by
its first represented categorical arrow.  This is the diagonal counterpart
of `exists_eq_outgoingSum_of_ne`; the scalar is exactly the coefficient of
the trivial path. -/
theorem exists_eq_smul_id_add_outgoingSum {x : Q}
    (f : obj k Q x ⟶ obj k Q x) :
    ∃ (r : k) (h : OutgoingCoefficient (k := k) x x),
      f = r • 𝟙 (obj k Q x) + outgoingSum h := by
  classical
  let f' := homPathLinearEquiv (obj k Q x) (obj k Q x) f
  rw [← (homPathLinearEquiv
    (obj k Q x) (obj k Q x)).symm_apply_apply f]
  change ∃ (r : k) (h : OutgoingCoefficient (k := k) x x),
    (homPathLinearEquiv (obj k Q x) (obj k Q x)).symm f' =
      r • 𝟙 (obj k Q x) + outgoingSum h
  induction f' using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, 0, ?_⟩
      simp [outgoingSum]
  | add f₁ f₂ hf₁ hf₂ =>
      obtain ⟨r₁, h₁, hh₁⟩ := hf₁
      obtain ⟨r₂, h₂, hh₂⟩ := hf₂
      refine ⟨r₁ + r₂, h₁ + h₂, ?_⟩
      rw [(homPathLinearEquiv
        (obj k Q x) (obj k Q x)).symm.map_add, hh₁, hh₂]
      simp only [add_smul, outgoingSum, Pi.add_apply,
        Preadditive.comp_add, Finset.sum_add_distrib]
      abel
  | single p r =>
      rw [homPathLinearEquiv_symm_single]
      by_cases hp : p.length = 0
      · have hpnil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hp
        subst p
        refine ⟨r, 0, ?_⟩
        simp [outgoingSum]
      · obtain ⟨y, q, a, hpq⟩ :=
          (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hp
        subst p
        let a₀ : OutgoingArrow x := ⟨y, a⟩
        let qHom : obj k Q y ⟶ obj k Q x := pathHom q
        refine ⟨0,
          singleOutgoingCoefficient (k := k) a₀ (r • qHom), ?_⟩
        rw [outgoingSum_single]
        dsimp only [a₀, qHom, outgoingArrowHom]
        rw [CategoryTheory.Linear.comp_smul, pathHom_comp]
        simp only [zero_smul, zero_add]
        rfl

section Incoming

variable [∀ z : Q, Fintype (IncomingArrow z)]

omit [∀ x : Q, Fintype (OutgoingArrow x)] in
/-- Every free-path endomorphism is a scalar identity plus a sum grouped by
its last represented categorical arrow. -/
theorem exists_eq_smul_id_add_incomingSum {z : Q}
    (f : obj k Q z ⟶ obj k Q z) :
    ∃ (r : k) (h : IncomingCoefficient (k := k) z z),
      f = r • 𝟙 (obj k Q z) + incomingSum h := by
  classical
  let f' := homPathLinearEquiv (obj k Q z) (obj k Q z) f
  rw [← (homPathLinearEquiv
    (obj k Q z) (obj k Q z)).symm_apply_apply f]
  change ∃ (r : k) (h : IncomingCoefficient (k := k) z z),
    (homPathLinearEquiv (obj k Q z) (obj k Q z)).symm f' =
      r • 𝟙 (obj k Q z) + incomingSum h
  induction f' using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, 0, ?_⟩
      simp [incomingSum]
  | add f₁ f₂ hf₁ hf₂ =>
      obtain ⟨r₁, h₁, hh₁⟩ := hf₁
      obtain ⟨r₂, h₂, hh₂⟩ := hf₂
      refine ⟨r₁ + r₂, h₁ + h₂, ?_⟩
      rw [(homPathLinearEquiv
        (obj k Q z) (obj k Q z)).symm.map_add, hh₁, hh₂]
      simp only [add_smul, incomingSum, Pi.add_apply,
        Preadditive.add_comp, Finset.sum_add_distrib]
      abel
  | single p r =>
      rw [homPathLinearEquiv_symm_single]
      by_cases hp : p.length = 0
      · have hpnil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hp
        subst p
        refine ⟨r, 0, ?_⟩
        simp [incomingSum]
      · obtain ⟨y, a, q, hpq, hlength⟩ :=
          (Quiver.Path.length_ne_zero_iff_eq_comp p).mp hp
        subst p
        let a₀ : IncomingArrow z := ⟨y, a⟩
        let qHom : obj k Q z ⟶ obj k Q y := pathHom q
        refine ⟨0,
          singleIncomingCoefficient (k := k) a₀ (r • qHom), ?_⟩
        rw [incomingSum_single]
        dsimp only [a₀, qHom]
        rw [CategoryTheory.Linear.smul_comp, pathHom_comp]
        simp only [zero_smul, zero_add]
        rfl

end Incoming

section Realization

variable {C : Type*} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]
variable (F₀ : Q → C)
variable (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))

omit [(x : Q) → Fintype (OutgoingArrow x)] [Preadditive C] in
@[simp]
theorem pathMap_toPath {i j : Q} (a : i ⟶ j) :
    pathMap F₀ F₁ a.toPath = F₁ a := by
  rw [show a.toPath = (Quiver.Path.nil.cons a) from rfl,
    pathMap_cons, pathMap_nil, Category.comp_id]

omit [(x : Q) → Fintype (OutgoingArrow x)] in
@[simp]
theorem lift_map_outgoingArrowHom {x : Q} (a : OutgoingArrow x) :
    (lift (k := k) F₀ F₁).map (outgoingArrowHom (k := k) a) = F₁ a.2 := by
  rw [outgoingArrowHom, lift_map_pathHom]
  exact pathMap_toPath F₀ F₁ a.2

/-- Evaluation of a first-arrow decomposition is the corresponding sum of
represented arrows followed by evaluated coefficients. -/
theorem lift_map_outgoingSum {x z : Q}
    (c : OutgoingCoefficient (k := k) x z) :
    (lift (k := k) F₀ F₁).map (outgoingSum c) =
      ∑ a : OutgoingArrow x, F₁ a.2 ≫
        (lift (k := k) F₀ F₁).map (c a) := by
  simp [outgoingSum]
  rfl

end Realization

section Directed

variable [Preorder Q]

omit [(x : Q) → Fintype (OutgoingArrow x)] in
/-- If every quiver arrow strictly lowers an order, the endpoint of a path
is below its starting vertex. -/
theorem path_target_le_of_arrow_lt
    (harrow : ∀ {i j : Q}, (i ⟶ j) → j < i)
    {i j : Q} (p : Quiver.Path i j) :
    j ≤ i := by
  induction p with
  | nil => exact le_rfl
  | cons p a ih => exact (harrow a).le.trans ih

variable {C : Type*} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

omit [(x : Q) → Fintype (OutgoingArrow x)] [Preadditive C] in
/-- Changing arrow representatives strictly above the start of a path does
not change its evaluation. -/
theorem pathMap_eq_of_eq_on_source_le
    (F₀ : Q → C)
    (F₁ G₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (harrow : ∀ {i j : Q}, (i ⟶ j) → j < i)
    {i j : Q} (p : Quiver.Path i j)
    (h : ∀ {a b : Q} (e : a ⟶ b), a ≤ i → F₁ e = G₁ e) :
    pathMap F₀ F₁ p = pathMap F₀ G₁ p := by
  induction p with
  | nil => simp
  | @cons _ l p e ih =>
      rw [pathMap_cons, pathMap_cons, h e
        (path_target_le_of_arrow_lt harrow p), ih]

omit [(x : Q) → Fintype (OutgoingArrow x)] in
/-- The corresponding stability statement for a linear combination of
paths. -/
theorem homMap_eq_of_eq_on_source_le
    (F₀ : Q → C)
    (F₁ G₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (harrow : ∀ {i j : Q}, (i ⟶ j) → j < i)
    {x z : Q} (f : obj k Q x ⟶ obj k Q z)
    (h : ∀ {a b : Q} (e : a ⟶ b), a ≤ z → F₁ e = G₁ e) :
    homMap F₀ F₁ (obj k Q x) (obj k Q z) f =
      homMap F₀ G₁ (obj k Q x) (obj k Q z) f := by
  let f' := homPathLinearEquiv (obj k Q x) (obj k Q z) f
  rw [← (homPathLinearEquiv (obj k Q x) (obj k Q z)).symm_apply_apply f]
  change
    homMap F₀ F₁ (obj k Q x) (obj k Q z)
        ((homPathLinearEquiv (obj k Q x) (obj k Q z)).symm f') =
      homMap F₀ G₁ (obj k Q x) (obj k Q z)
        ((homPathLinearEquiv (obj k Q x) (obj k Q z)).symm f')
  induction f' using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp only [map_add, hf₁, hf₂]
  | single p r =>
      rw [homPathLinearEquiv_symm_single]
      simp only [map_smul, homMap_pathHom]
      rw [pathMap_eq_of_eq_on_source_le F₀ F₁ G₁ harrow p h]

end Directed

end MagnitudeConjecture.LinearPathCategory
