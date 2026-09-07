import MagnitudeConjecture.CategoryTheory.DeckShiftUniverseLift
import MagnitudeConjecture.LinearAlgebra.DirectSumFubini

/-!
# Reindexing shift-orbit categories across a universe lift

Universe lifting a deck group changes only the universe of the degree index.
This file reindexes the resulting finite-support direct sums and records that
the reindexing preserves the orbit-category identity and composition.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w w' uK

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable {k : Type uK} [CommRing k] [CategoryTheory.Linear k C]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Reindex an orbit Hom direct sum from the universe-lifted deck group back
to the original deck group. -/
noncomputable def uliftShiftOrbitLinearEquiv (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    ShiftOrbitHom (Additive (ULift.{w'} G)) X Y ≃ₗ[k]
      ShiftOrbitHom (Additive G) X Y := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  change
    DirectSum (Additive (ULift.{w'} G))
        (fun a ↦ X ⟶ (D.core.F (additiveULiftDown a)).obj Y) ≃ₗ[k]
      DirectSum (Additive G) (fun a ↦ X ⟶ (D.core.F a).obj Y)
  let e := (additiveULiftEquiv.{w, w'} (G := G)).toEquiv
  let M : Additive G → Type v :=
    fun a ↦ X ⟶ (D.core.F a).obj Y
  let reindex :
      DirectSum (Additive (ULift.{w'} G)) (fun a ↦ M (e a)) ≃ₗ[k]
        DirectSum (Additive G) (fun b ↦ M (e (e.symm b))) :=
    DirectSum.lequivCongrLeft k e
  let castFibers :
      DirectSum (Additive G) (fun b ↦ M (e (e.symm b))) ≃ₗ[k]
        DirectSum (Additive G) M :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun b ↦
      LinearEquiv.cast (R := k) (M := M) (e.apply_symm_apply b)
  exact reindex.trans castFibers

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
@[simp]
theorem uliftShiftOrbitLinearEquiv_shiftOrbitLof
    (X Y : C) (a : Additive (ULift.{w'} G))
    (f : letI := D.ulift.{u, v, w, w'}.hasShift
      ShiftHom X Y a) :
    letI := D.hasShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    D.uliftShiftOrbitLinearEquiv (k := k) X Y
        (shiftOrbitLof (k := k) X Y a f) =
      shiftOrbitLof (k := k) X Y (additiveULiftDown a) f := by
  letI := D.hasShift
  letI := D.ulift.{u, v, w, w'}.hasShift
  classical
  rw [shiftOrbitLof_apply, shiftOrbitLof_apply,
    shiftOrbitOf_eq_directSumOf, shiftOrbitOf_eq_directSumOf]
  let e := (additiveULiftEquiv.{w, w'} (G := G)).toEquiv
  let M : Additive G → Type v :=
    fun b ↦ X ⟶ (D.core.F b).obj Y
  change D.uliftShiftOrbitLinearEquiv (k := k) X Y
      (DirectSum.of (fun b ↦ M (e b)) a f) =
    DirectSum.of M (e a) f
  unfold uliftShiftOrbitLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  exact MagnitudeConjecture.DirectSumFubini.reindexCastLinearEquiv_of
    (T := M) e a f

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
@[simp]
theorem uliftShiftOrbitLinearEquiv_shiftOrbitOf
    (X Y : C) (a : Additive (ULift.{w'} G))
    (f : letI := D.ulift.{u, v, w, w'}.hasShift
      ShiftHom X Y a) :
    letI := D.hasShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    D.uliftShiftOrbitLinearEquiv (k := k) X Y
        (shiftOrbitOf X Y a f) =
      shiftOrbitOf X Y (additiveULiftDown a) f := by
  letI := D.hasShift
  letI := D.ulift.{u, v, w, w'}.hasShift
  simpa only [shiftOrbitLof_apply] using
    D.uliftShiftOrbitLinearEquiv_shiftOrbitLof
      (k := k) X Y a f

omit [∀ a : Additive G, (D.core.F a).Linear k] in
private theorem uliftShiftOrbitLinearEquiv_comp_of_of
    {X Y Z : C} (a b : Additive (ULift.{w'} G))
    (f : letI := D.ulift.{u, v, w, w'}.hasShift
      ShiftHom X Y a)
    (g : letI := D.ulift.{u, v, w, w'}.hasShift
      ShiftHom Y Z b) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    D.uliftShiftOrbitLinearEquiv (k := k) X Z
        (shiftOrbitCompHom
          (shiftOrbitOf X Y a f) (shiftOrbitOf Y Z b g)) =
      shiftOrbitCompHom
        (D.uliftShiftOrbitLinearEquiv (k := k) X Y
          (shiftOrbitOf X Y a f))
        (D.uliftShiftOrbitLinearEquiv (k := k) Y Z
          (shiftOrbitOf Y Z b g)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  rw [shiftOrbitCompHom_of_of,
    D.uliftShiftOrbitLinearEquiv_shiftOrbitOf,
    D.uliftShiftOrbitLinearEquiv_shiftOrbitOf,
    D.uliftShiftOrbitLinearEquiv_shiftOrbitOf,
    shiftOrbitCompHom_of_of]
  rfl

omit [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k] in
theorem uliftShiftOrbitLinearEquiv_id (X : C) :
    letI := D.hasShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    D.uliftShiftOrbitLinearEquiv (k := k) X X
        (shiftOrbitId X) = shiftOrbitId X := by
  letI := D.hasShift
  letI := D.ulift.{u, v, w, w'}.hasShift
  change D.uliftShiftOrbitLinearEquiv (k := k) X X
      (shiftOrbitLof (k := k) X X 0 (shiftHomId X)) =
    shiftOrbitLof (k := k) X X 0 (shiftHomId X)
  rw [D.uliftShiftOrbitLinearEquiv_shiftOrbitLof]
  rfl

omit [∀ a : Additive G, (D.core.F a).Linear k] in
theorem uliftShiftOrbitLinearEquiv_comp
    {X Y Z : C}
    (f : letI := D.ulift.{u, v, w, w'}.hasShift
      letI := D.ulift.{u, v, w, w'}.additiveShift
      ShiftOrbitHom (Additive (ULift.{w'} G)) X Y)
    (g : letI := D.ulift.{u, v, w, w'}.hasShift
      letI := D.ulift.{u, v, w, w'}.additiveShift
      ShiftOrbitHom (Additive (ULift.{w'} G)) Y Z) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    D.uliftShiftOrbitLinearEquiv (k := k) X Z
        (shiftOrbitCompHom f g) =
      shiftOrbitCompHom
        (D.uliftShiftOrbitLinearEquiv (k := k) X Y f)
        (D.uliftShiftOrbitLinearEquiv (k := k) Y Z g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro b gb
      simpa only [shiftOrbitOf_eq_directSumOf] using
        D.uliftShiftOrbitLinearEquiv_comp_of_of
          (k := k) a b fa gb
    · intro g₁ g₂ hg₁ hg₂
      simpa only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using
        congrArg₂ (.+.) hg₁ hg₂
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using
      congrArg₂ (.+.) hf₁ hf₂

/-- Identity on objects and degree reindexing on morphisms gives the canonical
functor from the lifted shift-orbit category to the original one. -/
noncomputable def uliftShiftOrbitFunctor :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    ShiftOrbitCategory C (Additive (ULift.{w'} G)) ⥤
      ShiftOrbitCategory C (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  exact
    { obj := fun X ↦ X
      map := fun {X Y} f ↦
        D.uliftShiftOrbitLinearEquiv (k := k) X Y f
      map_id := D.uliftShiftOrbitLinearEquiv_id (k := k)
      map_comp := D.uliftShiftOrbitLinearEquiv_comp (k := k) }

instance uliftShiftOrbitFunctor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftShiftOrbitFunctor (k := k)).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro X Y f g
  exact (D.uliftShiftOrbitLinearEquiv
    (k := k) (show C from X) (show C from Y)).map_add f g

instance uliftShiftOrbitFunctor_linear :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftShiftOrbitFunctor (k := k)).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro X Y f r
  exact (D.uliftShiftOrbitLinearEquiv
    (k := k) (show C from X) (show C from Y)).map_smul r f

instance uliftShiftOrbitFunctor_full :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftShiftOrbitFunctor (k := k)).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro X Y f
  exact ⟨(D.uliftShiftOrbitLinearEquiv
    (k := k) (show C from X) (show C from Y)).symm f,
      (D.uliftShiftOrbitLinearEquiv
        (k := k) (show C from X) (show C from Y)).apply_symm_apply f⟩

instance uliftShiftOrbitFunctor_faithful :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftShiftOrbitFunctor (k := k)).Faithful := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro X Y
  exact (D.uliftShiftOrbitLinearEquiv
    (k := k) (show C from X) (show C from Y)).injective

/-- Reindexing the deck group across `ULift` does not change the concrete
shift-orbit category. -/
noncomputable def uliftShiftOrbitEquivalence :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    ShiftOrbitCategory C (Additive (ULift.{w'} G)) ≌
      ShiftOrbitCategory C (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  let F := D.uliftShiftOrbitFunctor (k := k)
  letI : F.IsEquivalence :=
    { full := inferInstance
      faithful := inferInstance
      essSurj := ⟨fun X ↦ ⟨X, ⟨Iso.refl X⟩⟩⟩ }
  exact F.asEquivalence

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
