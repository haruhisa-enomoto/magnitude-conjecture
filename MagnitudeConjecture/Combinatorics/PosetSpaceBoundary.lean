import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option

/-!
# The augmented boundary poset of a poset space

The incidence boundary of a `T`-space is obtained by adjoining a new root
below `OrderDual T`.  We use a dedicated inductive type so that the index is
universe-polymorphic and its root/non-root decomposition remains literal.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.PosetSpace

universe u

variable {T : Type u}

/-- The incidence relation on the root followed by the points of `T`. -/
def boundaryLE [LE T] : Option T → Option T → Prop
  | none, _ => True
  | some _, none => False
  | some t, some s => s ≤ t

theorem boundaryLE_refl [Preorder T] (q : Option T) : boundaryLE q q := by
  cases q <;> simp [boundaryLE]

theorem boundaryLE_trans [Preorder T] {q r s : Option T} :
    boundaryLE q r → boundaryLE r s → boundaryLE q s := by
  intro hqr hrs
  cases q with
  | none => trivial
  | some t =>
      cases r with
      | none => exact False.elim hqr
      | some r =>
          cases s with
          | none => exact False.elim hrs
          | some s => exact hrs.trans hqr

theorem boundaryLE_antisymm [PartialOrder T] {q r : Option T}
    (hqr : boundaryLE q r) (hrq : boundaryLE r q) : q = r := by
  cases q with
  | none =>
      cases r <;> simp_all [boundaryLE]
  | some t =>
      cases r with
      | none => simp_all [boundaryLE]
      | some s =>
          simp only [boundaryLE] at hqr hrq
          exact congrArg some (le_antisymm hrq hqr)

/-- A root adjoined below the dual of `T`. -/
inductive BoundaryIndex (T : Type u)
  | root
  | nonroot (t : T)
  deriving DecidableEq

/-- Forget the order tag on an augmented boundary index. -/
def BoundaryIndex.toOption : BoundaryIndex T → Option T
  | .root => none
  | .nonroot t => some t

/-- The underlying finite type is just `Option T`. -/
def BoundaryIndex.equivOption : BoundaryIndex T ≃ Option T where
  toFun := BoundaryIndex.toOption
  invFun
    | none => .root
    | some t => .nonroot t
  left_inv q := by cases q <;> rfl
  right_inv q := by cases q <;> rfl

noncomputable instance [Fintype T] : Fintype (BoundaryIndex T) :=
  Fintype.ofEquiv (Option T) BoundaryIndex.equivOption.symm

@[simp]
theorem BoundaryIndex.toOption_root :
    (BoundaryIndex.root : BoundaryIndex T).toOption = none :=
  rfl

@[simp]
theorem BoundaryIndex.toOption_nonroot (t : T) :
    (BoundaryIndex.nonroot t).toOption = some t :=
  rfl

theorem BoundaryIndex.toOption_injective :
    Function.Injective (BoundaryIndex.toOption (T := T)) := by
  intro q r h
  cases q <;> cases r <;> simp_all

/-- The augmented order is the boundary incidence relation.  Its non-root
part is `OrderDual T`. -/
instance [PartialOrder T] : PartialOrder (BoundaryIndex T) where
  le q r := boundaryLE q.toOption r.toOption
  le_refl q := boundaryLE_refl q.toOption
  le_trans _ _ _ := boundaryLE_trans
  le_antisymm q r hqr hrq :=
    BoundaryIndex.toOption_injective (boundaryLE_antisymm hqr hrq)

theorem boundaryLE_toOption_iff_le [PartialOrder T]
    (q r : BoundaryIndex T) :
    boundaryLE q.toOption r.toOption ↔ q ≤ r :=
  Iff.rfl

end MagnitudeConjecture.PosetSpace
