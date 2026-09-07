import MagnitudeConjecture.CategoryTheory.ShiftOrbitIsoComponent

/-!
# Split components of shift-orbit retractions

A retraction in a finite-support shift-orbit category gives a finite sum of
ordinary source endomorphisms equal to the identity.  If the ordinary source
endomorphism ring is local, one summand is invertible, so the corresponding
homogeneous component of the left map is split monic.  Unlike the stronger
isomorphism-component criterion, this requires no local-endomorphism
hypothesis on the target or on the orbit source.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]

include k in
/-- The zero-degree component of convolution with one homogeneous left
factor uses exactly the inverse-degree component of the right factor. -/
theorem shiftOrbitComp_of_left_component_zero
    {X Y Z : C} (a : A) (f : ShiftHom X Y a)
    (r : ShiftOrbitHom A Y Z) :
    (shiftOrbitCompHom (shiftOrbitOf X Y a f) r) 0 =
      shiftHomComp' (neg_add_cancel a) f (r (-a)) := by
  classical
  induction r using DirectSum.induction_on with
  | zero =>
      rw [map_zero]
      change (0 : ShiftHom X Z (0 : A)) =
        shiftHomComp' (neg_add_cancel a) f 0
      simp [shiftHomComp']
  | of b g =>
      by_cases hba : b = -a
      · subst b
        change
          (shiftOrbitCompHom (shiftOrbitOf X Y a f)
            (shiftOrbitOf Y Z (-a) g)) 0 =
              shiftHomComp' (neg_add_cancel a) f
                ((shiftOrbitOf Y Z (-a) g) (-a))
        rw [shiftOrbitCompHom_of_of]
        have hleft :
            (shiftOrbitOf X Z ((-a) + a)
              (shiftHomComp f g)) 0 =
                shiftHomComp' (neg_add_cancel a) f g := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Z d) 0
              (DirectSum.lof k A (fun d ↦ ShiftHom X Z d) ((-a) + a)
                (shiftHomComp f g)) = _
          rw [DirectSum.component.of]
          have hdeg : -a + a = (0 : A) := neg_add_cancel a
          simp only [dif_pos hdeg]
          exact eq_of_heq ((eqRec_heq _ _).trans
            (shiftHomComp_heq_shiftHomComp' (neg_add_cancel a) f g))
        have hright : (shiftOrbitOf Y Z (-a) g) (-a) = g := by
          change DirectSum.component k A (fun d ↦ ShiftHom Y Z d) (-a)
              (DirectSum.lof k A (fun d ↦ ShiftHom Y Z d) (-a) g) = g
          rw [DirectSum.component.of]
          simp
        rw [hleft, hright]
      · change
          (shiftOrbitCompHom (shiftOrbitOf X Y a f)
            (shiftOrbitOf Y Z b g)) 0 =
              shiftHomComp' (neg_add_cancel a) f
                ((shiftOrbitOf Y Z b g) (-a))
        rw [shiftOrbitCompHom_of_of]
        have hdeg : b + a ≠ (0 : A) := by
          intro hzero
          apply hba
          exact (eq_neg_of_add_eq_zero_left hzero)
        have hleft :
            (shiftOrbitOf X Z (b + a) (shiftHomComp f g)) 0 = 0 := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Z d) 0
              (DirectSum.lof k A (fun d ↦ ShiftHom X Z d) (b + a)
                (shiftHomComp f g)) = 0
          rw [DirectSum.component.of]
          simp [hdeg]
        rw [hleft]
        have hright : (shiftOrbitOf Y Z b g) (-a) = 0 := by
          change DirectSum.component k A (fun d ↦ ShiftHom Y Z d) (-a)
              (DirectSum.lof k A (fun d ↦ ShiftHom Y Z d) b g) = 0
          rw [DirectSum.component.of]
          simp [hba]
        rw [hright]
        simp [shiftHomComp']
  | add r s hr hs =>
      rw [map_add]
      change
        (shiftOrbitCompHom (shiftOrbitOf X Y a f) r) 0 +
            (shiftOrbitCompHom (shiftOrbitOf X Y a f) s) 0 =
          shiftHomComp' (neg_add_cancel a) f (r (-a) + s (-a))
      rw [hr, hs]
      simp [shiftHomComp', Functor.map_add, Preadditive.comp_add]

include k in
set_option backward.isDefEq.respectTransparency false in
/-- A retraction in the shift-orbit category has a split-monic homogeneous
component when the source endomorphism ring is local. -/
theorem exists_isSplitMono_shiftOrbitHom_component_of_retraction
    {X Y : C} (hlocal : IsLocalRing (End X))
    (q : ShiftOrbitHom A X Y) (r : ShiftOrbitHom A Y X)
    (hqr : shiftOrbitCompHom q r = shiftOrbitId X) :
    ∃ a : A, IsSplitMono (q a) := by
  classical
  let z : X⟦(0 : A)⟧ ⟶ X := (shiftFunctorZero C A).hom.app X
  let ev0 : ShiftOrbitHom A X X →ₗ[k] ShiftHom X X (0 : A) :=
    DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
  let c (a : A) : End X :=
    ev0 (shiftOrbitCompHom (shiftOrbitOf X Y a (q a)) r) ≫ z
  let cr : ShiftOrbitHom A X Y →+ ShiftOrbitHom A X X :=
    AddMonoidHom.flip shiftOrbitCompHom r
  have hdecomp :
      ∑ a ∈ q.support, shiftOrbitOf X Y a (q a) = q := by
    change ∑ a ∈ q.support, DFinsupp.single a (q a) = q
    exact DFinsupp.sum_single
  have hconv :
      ∑ a ∈ q.support,
          shiftOrbitCompHom (shiftOrbitOf X Y a (q a)) r =
        shiftOrbitId X := by
    calc
      ∑ a ∈ q.support,
          shiftOrbitCompHom (shiftOrbitOf X Y a (q a)) r =
          cr (∑ a ∈ q.support, shiftOrbitOf X Y a (q a)) := by
            change ∑ a ∈ q.support,
                cr (shiftOrbitOf X Y a (q a)) = cr _
            rw [map_sum]
      _ = cr q := by rw [hdecomp]
      _ = shiftOrbitId X := hqr
  have hsum : ∑ a ∈ q.support, c a = 𝟙 X := by
    calc
      ∑ a ∈ q.support, c a =
          (∑ a ∈ q.support,
            ev0 (shiftOrbitCompHom
              (shiftOrbitOf X Y a (q a)) r)) ≫ z := by
                dsimp only [c]
                rw [Preadditive.sum_comp]
      _ = ev0 (∑ a ∈ q.support,
          shiftOrbitCompHom (shiftOrbitOf X Y a (q a)) r) ≫ z := by
            rw [map_sum]
      _ = ev0 (shiftOrbitId X) ≫ z := by rw [hconv]
      _ = 𝟙 X := by
        have hid : ev0 (shiftOrbitId X) = shiftHomId X := by
          dsimp only [ev0, shiftOrbitId]
          change DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
              (DirectSum.lof k A (fun d ↦ ShiftHom X X d) 0
                (shiftHomId X)) = shiftHomId X
          rw [DirectSum.component.of]
          simp
        rw [hid]
        simp [z, shiftHomId]
  letI : IsLocalRing (End X) := hlocal
  have hunit : IsUnit (∑ a ∈ q.support, c a) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨a, _ha, haunit⟩ :=
    IsLocalRing.exists_of_isUnit_sum (s := q.support) (f := c) hunit
  let b : Y⟦a⟧ ⟶ X :=
    (shiftFunctor C a).map (r (-a)) ≫
      (shiftFunctorAdd' C (-a) a 0 (neg_add_cancel a)).inv.app X ≫ z
  have hc : c a = q a ≫ b := by
    dsimp only [c, ev0]
    have hcomponent :
        DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
            (shiftOrbitCompHom (shiftOrbitOf X Y a (q a)) r) =
          shiftHomComp' (neg_add_cancel a) (q a) (r (-a)) := by
      exact shiftOrbitComp_of_left_component_zero
        (k := k) a (q a) r
    rw [hcomponent]
    simp [b, z, shiftHomComp', Category.assoc]
  have habI : IsIso (q a ≫ b) := by
    apply (isUnit_iff_isIso (q a ≫ b)).1
    simpa only [hc] using haunit
  letI : IsIso (q a ≫ b) := habI
  refine ⟨a, ?_⟩
  apply IsSplitMono.mk'
  exact
    { retraction := b ≫ inv (q a ≫ b)
      id := by rw [← Category.assoc, IsIso.hom_inv_id] }

include k in
/-- An isomorphism in the shift-orbit category has a split-monic homogeneous
component whenever the ordinary source endomorphism ring is local. -/
theorem exists_isSplitMono_shiftOrbitHom_component
    {X Y : C} (hlocal : IsLocalRing (End X))
    (q : ShiftOrbitHom A X Y)
    [IsIso
      (show (show ShiftOrbitCategory C A from X) ⟶
        (show ShiftOrbitCategory C A from Y) from q)] :
    ∃ a : A, IsSplitMono (q a) := by
  let r : ShiftOrbitHom A Y X :=
    inv (show (show ShiftOrbitCategory C A from X) ⟶
      (show ShiftOrbitCategory C A from Y) from q)
  apply exists_isSplitMono_shiftOrbitHom_component_of_retraction
    (k := k) hlocal q r
  change (show (show ShiftOrbitCategory C A from X) ⟶
      (show ShiftOrbitCategory C A from Y) from q) ≫ r = 𝟙 _
  exact IsIso.hom_inv_id _

end MagnitudeConjecture.CoveringHom
