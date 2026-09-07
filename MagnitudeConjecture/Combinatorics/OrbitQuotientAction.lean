import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

/-!
# Deck quotient action on orbit classes

If a group `G` acts on `X` and `N` is normal, then `G / N` acts on the
set of `N`-orbits in `X`.  A free `G`-action induces a free quotient action.
This is the group-action calculation used for the endpoint scaling in the
finite covering average.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringAction

universe u v

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- An invariant function descends to the orbit quotient. -/
def orbitInvariantDescend
    {M : Type*} [AddCommMonoid M]
    (f : X → M)
    (invariant : ∀ (g : G) (x : X), f (g • x) = f x) :
    MulAction.orbitRel.Quotient G X → M :=
  fun q ↦ Quotient.liftOn' q f fun a b hab ↦ by
    rw [MulAction.orbitRel_apply] at hab
    obtain ⟨g, rfl⟩ := hab
    exact invariant g b

@[simp]
theorem orbitInvariantDescend_mk
    {M : Type*} [AddCommMonoid M]
    (f : X → M)
    (invariant : ∀ (g : G) (x : X), f (g • x) = f x)
    (x : X) :
    orbitInvariantDescend f invariant
        (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) =
      f x :=
  rfl

/-- A function constant on orbits descends to its orbit quotient, without any
algebraic structure on the codomain. -/
def orbitClassifierDescend
    {Y : Type*} (c : X → Y)
    (invariant : ∀ (g : G) (x : X), c (g • x) = c x) :
    MulAction.orbitRel.Quotient G X → Y :=
  fun q ↦ Quotient.liftOn' q c fun a b hab ↦ by
    rw [MulAction.orbitRel_apply] at hab
    obtain ⟨g, rfl⟩ := hab
    exact invariant g b

@[simp]
theorem orbitClassifierDescend_mk
    {Y : Type*} (c : X → Y)
    (invariant : ∀ (g : G) (x : X), c (g • x) = c x)
    (x : X) :
    orbitClassifierDescend c invariant
        (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) = c x :=
  rfl

/-- An orbit classifier is bijective on the orbit quotient when it is
surjective and its fibres are exactly the orbits. -/
theorem orbitClassifierDescend_bijective
    {Y : Type*} (c : X → Y)
    (invariant : ∀ (g : G) (x : X), c (g • x) = c x)
    (surjective : Function.Surjective c)
    (fiber : ∀ x y, c x = c y → ∃ g : G, g • y = x) :
    Function.Bijective (orbitClassifierDescend c invariant) := by
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn' with
    | _ x =>
        induction r using Quotient.inductionOn' with
        | _ y =>
            apply Quotient.sound
            obtain ⟨g, hg⟩ := fiber x y hqr
            rw [← hg]
            exact MulAction.mem_orbit y g
  · intro y
    obtain ⟨x, rfl⟩ := surjective y
    exact ⟨Quotient.mk'' x, rfl⟩

/-- The equivalence induced by a complete orbit classifier with orbit fibres. -/
noncomputable def orbitClassifierEquiv
    {Y : Type*} (c : X → Y)
    (invariant : ∀ (g : G) (x : X), c (g • x) = c x)
    (surjective : Function.Surjective c)
    (fiber : ∀ x y, c x = c y → ∃ g : G, g • y = x) :
    MulAction.orbitRel.Quotient G X ≃ Y :=
  Equiv.ofBijective (orbitClassifierDescend c invariant)
    (orbitClassifierDescend_bijective c invariant surjective fiber)

/-- Reindex an orbit sum along a complete orbit classifier whose fibres are
exactly the orbits. -/
theorem sum_orbitInvariantDescend_eq_sum_of_orbitClassifier
    {Y M : Type*} [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)] [Fintype Y]
    [AddCommMonoid M]
    (c : X → Y)
    (c_invariant : ∀ (g : G) (x : X), c (g • x) = c x)
    (c_surjective : Function.Surjective c)
    (c_fiber : ∀ x y, c x = c y → ∃ g : G, g • y = x)
    (f : X → M)
    (f_invariant : ∀ (g : G) (x : X), f (g • x) = f x)
    (t : Y → M)
    (value_eq : ∀ x, f x = t (c x)) :
    (∑ q : MulAction.orbitRel.Quotient G X,
        orbitInvariantDescend f f_invariant q) =
      ∑ y : Y, t y := by
  classical
  apply Fintype.sum_bijective (orbitClassifierDescend c c_invariant)
    (orbitClassifierDescend_bijective c c_invariant c_surjective c_fiber)
  intro q
  induction q using Quotient.inductionOn' with
  | _ x => exact value_eq x

/-- For a finite free action, the sum of an invariant function is the group
order times its sum over the orbit quotient. -/
theorem sum_eq_card_nsmul_sum_orbitInvariantDescend
    {M : Type*} [AddCommMonoid M]
    [Fintype G] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)]
    [IsCancelSMul G X]
    (f : X → M)
    (invariant : ∀ (g : G) (x : X), f (g • x) = f x) :
    (∑ x, f x) = Fintype.card G •
      ∑ q : MulAction.orbitRel.Quotient G X,
        orbitInvariantDescend f invariant q := by
  let e := MulAction.selfEquivOrbitsQuotientProd (G := G) (X := X)
    (fun x ↦ IsCancelSMul.stabilizer_eq_bot x)
  calc
    (∑ x, f x) =
        ∑ p : MulAction.orbitRel.Quotient G X × G,
          orbitInvariantDescend f invariant p.1 := by
      apply Fintype.sum_equiv e
      intro x
      rfl
    _ = Fintype.card G •
        ∑ q : MulAction.orbitRel.Quotient G X,
          orbitInvariantDescend f invariant q := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ]
      rw [Finset.sum_nsmul]

/-- Integer form of invariant-sum scaling, matching the covering-average
arithmetic. -/
theorem sum_eq_card_mul_sum_orbitInvariantDescend
    [Fintype G] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)]
    [IsCancelSMul G X]
    (f : X → ℤ)
    (invariant : ∀ (g : G) (x : X), f (g • x) = f x) :
    (∑ x, f x) = (Fintype.card G : ℤ) *
      ∑ q : MulAction.orbitRel.Quotient G X,
        orbitInvariantDescend f invariant q := by
  simpa only [nsmul_eq_mul] using
    sum_eq_card_nsmul_sum_orbitInvariantDescend f invariant

/-- Every orbit quotient of a finite free action has uniform fibre size equal
to the order of the acting group.  This cardinal form is what scales the
vertex, arrow-occurrence, and mesh counts at the covering endpoints. -/
theorem card_eq_orbitQuotient_card_mul_group_card
    {Q : Type u} [Group Q] {Y : Type v} [MulAction Q Y]
    [IsCancelSMul Q Y] [Fintype Q] [Fintype Y]
    [Fintype (MulAction.orbitRel.Quotient Q Y)] :
    Fintype.card Y =
      Fintype.card (MulAction.orbitRel.Quotient Q Y) * Fintype.card Q := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr
    (MulAction.selfEquivOrbitsQuotientProd (G := Q) (X := Y)
      (fun y ↦ IsCancelSMul.stabilizer_eq_bot y))

/-- Uniform free fibres scale the integer mesh-minus-arrow surplus by the
order of the acting group. -/
theorem eulerSurplus_scale_of_free_actions
    {Q : Type u} [Group Q] {Arrow Mesh : Type v}
    [MulAction Q Arrow] [MulAction Q Mesh]
    [IsCancelSMul Q Arrow] [IsCancelSMul Q Mesh]
    [Fintype Q] [Fintype Arrow] [Fintype Mesh]
    [Fintype (MulAction.orbitRel.Quotient Q Arrow)]
    [Fintype (MulAction.orbitRel.Quotient Q Mesh)] :
    2 * (Fintype.card Mesh : ℤ) - (Fintype.card Arrow : ℤ) =
      (Fintype.card Q : ℤ) *
        (2 * (Fintype.card (MulAction.orbitRel.Quotient Q Mesh) : ℤ) -
          (Fintype.card (MulAction.orbitRel.Quotient Q Arrow) : ℤ)) := by
  rw [card_eq_orbitQuotient_card_mul_group_card (Q := Q) (Y := Mesh),
    card_eq_orbitQuotient_card_mul_group_card (Q := Q) (Y := Arrow)]
  push_cast
  ring

private abbrev orbitQuotientGroupSMul (N : Subgroup G) [N.Normal] :
    SMul G (MulAction.orbitRel.Quotient N X) where
  smul g := Quotient.map' (g • ·) fun a b hab ↦ by
    rw [MulAction.orbitRel_apply] at hab ⊢
    obtain ⟨n, rfl⟩ := hab
    let c : N := ⟨g * n * g⁻¹, ‹N.Normal›.conj_mem n n.property g⟩
    refine ⟨c, ?_⟩
    simp only [MulAction.subgroup_smul_def, smul_smul, c]
    simp [mul_assoc]

private abbrev orbitQuotientGroupMulAction (N : Subgroup G) [N.Normal] :
    MulAction G (MulAction.orbitRel.Quotient N X) := by
  letI : SMul G (MulAction.orbitRel.Quotient N X) :=
    orbitQuotientGroupSMul N
  exact Function.Surjective.mulAction
    (Quotient.mk'' : X → MulAction.orbitRel.Quotient N X)
    Quotient.mk''_surjective (fun _ _ ↦ rfl)

private theorem subgroup_smul_orbitQuotient_eq
    (N : Subgroup G) [N.Normal] (n : N)
    (z : MulAction.orbitRel.Quotient N X) :
    letI := orbitQuotientGroupMulAction (X := X) N
    (n : G) • z = z := by
  letI := orbitQuotientGroupMulAction (X := X) N
  induction z using Quotient.inductionOn' with
  | _ x =>
      apply Quotient.sound
      exact MulAction.mem_orbit x n

private abbrev orbitQuotientQuotientSMul (N : Subgroup G) [N.Normal] :
    SMul (G ⧸ N) (MulAction.orbitRel.Quotient N X) := by
  letI := orbitQuotientGroupMulAction (X := X) N
  refine ⟨fun q z ↦ Quotient.liftOn' q (fun g ↦ g • z) ?_⟩
  intro g g' hgg'
  have hmem : g⁻¹ * g' ∈ N := QuotientGroup.leftRel_apply.mp hgg'
  have htrivial : (g⁻¹ * g') • z = z :=
    subgroup_smul_orbitQuotient_eq (X := X) N ⟨g⁻¹ * g', hmem⟩ z
  calc
    g • z = g • ((g⁻¹ * g') • z) := congrArg (g • ·) htrivial.symm
    _ = (g * (g⁻¹ * g')) • z := (mul_smul _ _ _).symm
    _ = g' • z := by simp

/-- The canonical action of `G / N` on the set of `N`-orbits in `X`. -/
noncomputable instance orbitQuotientMulAction (N : Subgroup G) [N.Normal] :
    MulAction (G ⧸ N) (MulAction.orbitRel.Quotient N X) := by
  letI := orbitQuotientGroupMulAction (X := X) N
  letI : SMul (G ⧸ N) (MulAction.orbitRel.Quotient N X) :=
    orbitQuotientQuotientSMul (X := X) N
  exact Function.Surjective.mulActionLeft (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (fun _ _ ↦ rfl)

/-- The quotient action is represented by applying a representative before
passing to the orbit quotient. -/
@[simp]
theorem quotient_smul_orbit_mk (N : Subgroup G) [N.Normal]
    (g : G) (x : X) :
    (g : G ⧸ N) •
        (Quotient.mk'' x : MulAction.orbitRel.Quotient N X) =
      Quotient.mk'' (g • x) :=
  rfl

private noncomputable def orbitTowerFlatten
    (N : Subgroup G) [N.Normal] :
    MulAction.orbitRel.Quotient (G ⧸ N)
        (MulAction.orbitRel.Quotient N X) →
      MulAction.orbitRel.Quotient G X := by
  intro z
  refine Quotient.liftOn' z
    (fun w ↦ Quotient.liftOn' w
      (fun x ↦ (Quotient.mk'' x : MulAction.orbitRel.Quotient G X))
      (fun a b hab ↦ MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq'
        (Quotient.sound hab))) ?_
  intro a b hab
  rw [MulAction.orbitRel_apply] at hab
  obtain ⟨q, rfl⟩ := hab
  induction q using Quotient.inductionOn' with
  | _ g =>
      induction b using Quotient.inductionOn' with
      | _ x =>
          apply Quotient.sound
          exact MulAction.mem_orbit x g

private noncomputable def orbitTowerExpand
    (N : Subgroup G) [N.Normal] :
    MulAction.orbitRel.Quotient G X →
      MulAction.orbitRel.Quotient (G ⧸ N)
        (MulAction.orbitRel.Quotient N X) := by
  intro z
  refine Quotient.liftOn' z
    (fun x ↦ Quotient.mk''
      (Quotient.mk'' x : MulAction.orbitRel.Quotient N X)) ?_
  intro a b hab
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  rw [MulAction.orbitRel_apply] at hab
  obtain ⟨g, rfl⟩ := hab
  exact ⟨(g : G ⧸ N), quotient_smul_orbit_mk N g b⟩

/-- Taking `N`-orbits and then `G / N`-orbits gives the same orbit set as
taking `G`-orbits directly. -/
noncomputable def orbitTowerEquiv (N : Subgroup G) [N.Normal] :
    MulAction.orbitRel.Quotient (G ⧸ N)
        (MulAction.orbitRel.Quotient N X) ≃
      MulAction.orbitRel.Quotient G X where
  toFun := orbitTowerFlatten N
  invFun := orbitTowerExpand N
  left_inv z := by
    induction z using Quotient.inductionOn' with
    | _ w =>
        induction w using Quotient.inductionOn' with
        | _ x => simp [orbitTowerFlatten, orbitTowerExpand]
  right_inv z := by
    induction z using Quotient.inductionOn' with
    | _ x => simp [orbitTowerFlatten, orbitTowerExpand]

@[simp]
theorem orbitTowerEquiv_mk (N : Subgroup G) [N.Normal] (x : X) :
    orbitTowerEquiv N
        (Quotient.mk'' (Quotient.mk'' x :
          MulAction.orbitRel.Quotient N X)) =
      (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) := by
  simp [orbitTowerEquiv, orbitTowerFlatten]

@[simp]
theorem orbitTowerEquiv_symm_mk (N : Subgroup G) [N.Normal] (x : X) :
    (orbitTowerEquiv N).symm
        (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) =
      Quotient.mk'' (Quotient.mk'' x :
        MulAction.orbitRel.Quotient N X) := by
  simp [orbitTowerEquiv, orbitTowerExpand]

/-- Freeness descends from a group action to the quotient action on subgroup
orbits.  This is the manuscript's endpoint-fibre freeness argument. -/
instance orbitQuotientIsCancelSMul (N : Subgroup G) [N.Normal]
    [IsCancelSMul G X] :
    IsCancelSMul (G ⧸ N) (MulAction.orbitRel.Quotient N X) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro q z hq
  induction q using Quotient.inductionOn' with
  | _ g =>
      induction z using Quotient.inductionOn' with
      | _ x =>
          change (Quotient.mk'' (g • x) :
              MulAction.orbitRel.Quotient N X) = Quotient.mk'' x at hq
          have horbit : g • x ∈ MulAction.orbit N x := Quotient.exact hq
          obtain ⟨n, hn⟩ := horbit
          have hgn : g = (n : G) :=
            IsCancelSMul.right_cancel g n x hn.symm
          simp [hgn]

end MagnitudeConjecture.CoveringAction
