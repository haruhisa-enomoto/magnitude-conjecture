import MagnitudeConjecture.CategoryTheory.CoherentDeckShiftRestriction

/-!
# Functors between subgroup shift-orbit categories

A coherent deck action of `G` restricts to every subgroup `N`.  Extending a
finitely supported `N`-graded orbit morphism by zero outside `N` gives a
canonical additive functor from the `N` shift-orbit category to the `G`
shift-orbit category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

private abbrev subgroupDegree (N : Subgroup G) :
    Additive N → Additive G :=
  fun a ↦ Additive.ofMul (a.toMul : G)

@[simp]
private theorem subgroupDegree_zero (N : Subgroup G) :
    subgroupDegree N 0 = 0 := rfl

@[simp]
private theorem subgroupDegree_add (N : Subgroup G)
    (a b : Additive N) :
    subgroupDegree N (a + b) = subgroupDegree N a + subgroupDegree N b :=
  rfl

private def subgroupShiftHom (N : Subgroup G) (X Y : C)
    (a : Additive N) (f :
      letI := (D.restrict N).hasShift
      ShiftHom X Y a) :
    letI := D.hasShift
    ShiftHom X Y (subgroupDegree N a) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  change X ⟶ (D.core.F (subgroupDegree N a)).obj Y
  change X ⟶ ((D.restrict N).core.F a).obj Y at f
  exact f

private def subgroupShiftHomAddHom (N : Subgroup G) (X Y : C)
    (a : Additive N) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    ShiftHom X Y a →+ ShiftHom X Y (subgroupDegree N a) where
  toFun := D.subgroupShiftHom N X Y a
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Extend a finitely supported `N`-orbit morphism by zero to a `G`-orbit
morphism. -/
noncomputable def shiftOrbitSubgroupMap (N : Subgroup G) (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitHom (Additive N) X Y →+
      ShiftOrbitHom (Additive G) X Y := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive N) := Classical.decEq _
  letI : DecidableEq (Additive G) := Classical.decEq _
  exact DirectSum.toAddMonoid fun a ↦
    (shiftOrbitOf X Y (subgroupDegree N a)).comp
      (D.subgroupShiftHomAddHom N X Y a)

@[simp]
theorem shiftOrbitSubgroupMap_of (N : Subgroup G)
    (X Y : C) (a : Additive N) (f :
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftHom X Y a) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N X Y (shiftOrbitOf X Y a f) =
      shiftOrbitOf X Y (subgroupDegree N a)
        (D.subgroupShiftHom N X Y a f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive N) := Classical.decEq _
  letI : DecidableEq (Additive G) := Classical.decEq _
  unfold shiftOrbitSubgroupMap shiftOrbitOf
  let φ : ∀ a : Additive N,
      ShiftHom X Y a →+ ShiftOrbitHom (Additive G) X Y :=
    fun a ↦ (shiftOrbitOf X Y (subgroupDegree N a)).comp
      (D.subgroupShiftHomAddHom N X Y a)
  change DirectSum.toAddMonoid φ
      (DirectSum.of (fun a : Additive N ↦ ShiftHom X Y a) a f) = φ a f
  exact DirectSum.toAddMonoid_of φ a f

theorem shiftOrbitSubgroupMap_id (N : Subgroup G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N X X (shiftOrbitId X) = shiftOrbitId X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive N) := Classical.decEq _
  letI : DecidableEq (Additive G) := Classical.decEq _
  rw [shiftOrbitId, D.shiftOrbitSubgroupMap_of]
  rfl

theorem shiftOrbitSubgroupMap_comp (N : Subgroup G)
    {X Y Z : C}
    (f : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) X Y)
    (g : letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      ShiftOrbitHom (Additive N) Y Z) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.shiftOrbitSubgroupMap N X Z (shiftOrbitCompHom f g) =
      shiftOrbitCompHom (D.shiftOrbitSubgroupMap N X Y f)
        (D.shiftOrbitSubgroupMap N Y Z g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : DecidableEq (Additive N) := Classical.decEq _
  letI : DecidableEq (Additive G) := Classical.decEq _
  refine DirectSum.induction_on f ?_ ?_ ?_
  · simp
  · intro a fa
    refine DirectSum.induction_on g ?_ ?_ ?_
    · simp
    · intro b gb
      change D.shiftOrbitSubgroupMap N X Z
          (shiftOrbitCompHom
            (shiftOrbitOf (C := C) (A := Additive N) X Y a fa)
            (shiftOrbitOf (C := C) (A := Additive N) Y Z b gb)) =
        shiftOrbitCompHom
          (D.shiftOrbitSubgroupMap N X Y
            (shiftOrbitOf (C := C) (A := Additive N) X Y a fa))
          (D.shiftOrbitSubgroupMap N Y Z
            (shiftOrbitOf (C := C) (A := Additive N) Y Z b gb))
      rw [shiftOrbitCompHom_of_of, D.shiftOrbitSubgroupMap_of,
        D.shiftOrbitSubgroupMap_of, D.shiftOrbitSubgroupMap_of,
        shiftOrbitCompHom_of_of]
      rfl
    · intro g₁ g₂ hg₁ hg₂
      simpa only [map_add, AddMonoidHom.add_apply] using
        congrArg₂ (.+.) hg₁ hg₂
  · intro f₁ f₂ hf₁ hf₂
    simpa only [map_add, AddMonoidHom.add_apply] using
      congrArg₂ (.+.) hf₁ hf₂

/-- The canonical inclusion of the subgroup shift-orbit category into the
ambient shift-orbit category. -/
noncomputable def shiftOrbitSubgroupFunctor (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftOrbitCategory C (Additive N) ⥤
      ShiftOrbitCategory C (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { obj := fun X ↦ X
      map := fun {X Y} f ↦ D.shiftOrbitSubgroupMap N X Y f
      map_id := D.shiftOrbitSubgroupMap_id N
      map_comp := D.shiftOrbitSubgroupMap_comp N }

instance shiftOrbitSubgroupFunctor_additive (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitSubgroupFunctor N).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  constructor
  intro X Y f g
  exact (D.shiftOrbitSubgroupMap N (show C from X) (show C from Y)).map_add f g

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
