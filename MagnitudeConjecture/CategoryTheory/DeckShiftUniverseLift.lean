import MagnitudeConjecture.CategoryTheory.DeckShiftAction
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.ResiduallyFinite

/-!
# Universe lifting for coherent deck shifts

The orbit-category Hom universe is the maximum of the original Hom universe
and the deck-group universe.  The covering-average interfaces therefore put
the deck group in the coefficient-field universe.  Actual combinatorial deck
groups are naturally small.  This file transports their action and coherent
shift through `ULift`, without changing any object or deck transformation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w w' uK

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]

/-- The action of a universe lift is the original action after projecting the
group element back down. -/
noncomputable instance uliftMulAction : MulAction (ULift.{w'} G) C where
  smul g X := g.down • X
  one_smul X := one_smul G X
  mul_smul g h X := mul_smul g.down h.down X

omit [Category C] in
@[simp]
theorem ulift_smul (g : ULift.{w'} G) (X : C) :
    g • X = g.down • X :=
  rfl

/-- Freeness of the object action is unchanged by universe lifting. -/
noncomputable instance uliftIsCancelSMul [IsCancelSMul G C] :
    IsCancelSMul (ULift.{w'} G) C where
  left_cancel' g X Y h := IsCancelSMul.left_cancel g.down X Y h
  right_cancel' g h X e := by
    apply ULift.ext
    exact IsCancelSMul.right_cancel g.down h.down X e

/-- Torsion-freeness is unchanged by universe lifting. -/
noncomputable instance uliftIsMulTorsionFree [IsMulTorsionFree G] :
    IsMulTorsionFree (ULift.{w'} G) where
  pow_left_injective _n hn g h e := by
    apply ULift.ext
    apply IsMulTorsionFree.pow_left_injective hn
    exact congrArg ULift.down e

/-- Residual finiteness is unchanged by universe lifting. -/
noncomputable instance uliftResiduallyFinite [Group.ResiduallyFinite G] :
    Group.ResiduallyFinite (ULift.{w'} G) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hgdown : g.down ≠ 1 := by
    intro h
    apply hg
    apply ULift.ext
    exact h
  obtain ⟨H, hH⟩ :=
    Group.exists_finiteIndexNormalSubgroup_notMem g.down hgdown
  let f : ULift.{w'} G →* G ⧸ H.toSubgroup :=
    (QuotientGroup.mk' H.toSubgroup).comp MulEquiv.ulift.toMonoidHom
  exact ⟨G ⧸ H.toSubgroup, inferInstance, inferInstance, f, by
    change QuotientGroup.mk' H.toSubgroup g.down ≠ 1
    intro h
    exact hH ((QuotientGroup.eq_one_iff g.down).mp h)⟩

/-- Additive degrees of the lifted multiplicative group project to the
original additive degrees. -/
def additiveULiftDown : Additive (ULift.{w'} G) → Additive G :=
  fun a ↦ Additive.ofMul a.toMul.down

@[simp]
theorem additiveULiftDown_zero :
    additiveULiftDown (G := G) (0 : Additive (ULift.{w'} G)) = 0 :=
  rfl

@[simp]
theorem additiveULiftDown_add (a b : Additive (ULift.{w'} G)) :
    additiveULiftDown (G := G) (a + b) =
      additiveULiftDown (G := G) a + additiveULiftDown (G := G) b :=
  rfl

/-- Universe lifting gives an additive equivalence of deck-degree groups. -/
def additiveULiftEquiv : Additive (ULift.{w'} G) ≃+ Additive G where
  toFun := additiveULiftDown
  invFun a := Additive.ofMul (ULift.up a.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

namespace CoherentDeckShift

variable (D : CoherentDeckShift C G)

/-- The same coherent deck shift, with its indexing group moved to a higher
universe.  All functors and coherence isomorphisms are definitionally the
original ones at the projected degree. -/
noncomputable def ulift : CoherentDeckShift C (ULift.{w'} G) where
  core :=
    { F := fun a ↦ D.core.F (additiveULiftDown a)
      zero := D.core.zero
      add := fun a b ↦ D.core.add (additiveULiftDown a) (additiveULiftDown b)
      assoc_hom_app := fun a b c X ↦
        D.core.assoc_hom_app (additiveULiftDown a)
          (additiveULiftDown b) (additiveULiftDown c) X
      zero_add_hom_app := fun a X ↦
        D.core.zero_add_hom_app (additiveULiftDown a) X
      add_zero_hom_app := fun a X ↦
        D.core.add_zero_hom_app (additiveULiftDown a) X }
  objIso g X := D.objIso g.down X

variable [Preadditive C]

noncomputable instance ulift_core_additive
    [∀ a : Additive G, (D.core.F a).Additive]
    (a : Additive (ULift.{w'} G)) :
    ((D.ulift).core.F a).Additive := by
  change (D.core.F (additiveULiftDown a)).Additive
  infer_instance

variable {k : Type uK} [CommSemiring k] [Linear k C]

noncomputable instance ulift_core_linear
    [∀ a : Additive G, (D.core.F a).Linear k]
    (a : Additive (ULift.{w'} G)) :
    ((D.ulift).core.F a).Linear k := by
  change (D.core.F (additiveULiftDown a)).Linear k
  infer_instance

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
