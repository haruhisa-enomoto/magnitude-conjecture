import MagnitudeConjecture.CategoryTheory.ShiftOrbitDecomposition

/-!
# Componentwise factorization in shift-orbit categories

This file gives the finite-support assembly used in Gabriel's almost-split
push-down argument.  If every homogeneous component of a shift-orbit
morphism factors through an ordinary map, then the whole orbit morphism
factors through its degree-zero inclusion.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A : Type w} [AddGroup A] [HasShift C A]

omit [Preadditive C] in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of an ordinary map in degree zero with a homogeneous map is
ordinary categorical composition. -/
theorem shiftHomComp'_zero_left
    {X Y Z : C} {a : A} (f : X ⟶ Y) (g : ShiftHom Y Z a) :
    shiftHomComp' (add_zero a) (shiftHomZero (A := A) f) g = f ≫ g := by
  simpa [shiftHomComp', shiftHomZero, CategoryTheory.ShiftedHom.comp] using
    CategoryTheory.ShiftedHom.mk₀_comp (0 : A) rfl f g

variable [∀ a : A, (shiftFunctor C a).Additive]

set_option backward.isDefEq.respectTransparency false in
/-- In the shift-orbit category, composing an ordinary degree-zero map with
a homogeneous morphism is ordinary categorical composition. -/
theorem shiftOrbitComp_zero_left_of
    {X Y Z : C} {a : A} (f : X ⟶ Y) (g : ShiftHom Y Z a) :
    shiftOrbitCompHom
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f))
        (shiftOrbitOf Y Z a g) =
      shiftOrbitOf X Z a (f ≫ g) := by
  classical
  rw [shiftOrbitCompHom_of_of]
  change DirectSum.of (fun d : A ↦ ShiftHom X Z d) (a + 0)
      (shiftHomComp (shiftHomZero (A := A) f) g) =
    DirectSum.of (fun d : A ↦ ShiftHom X Z d) a (f ≫ g)
  apply DFinsupp.single_eq_of_sigma_eq
  apply Sigma.ext (add_zero a)
  exact
    (shiftHomComp_heq_shiftHomComp' (add_zero a)
      (shiftHomZero (A := A) f) g).trans
      (heq_of_eq (shiftHomComp'_zero_left f g))

/-- Componentwise factorizations through an ordinary morphism assemble into
a factorization of a finite-support shift-orbit morphism. -/
theorem exists_shiftOrbit_factor_of_components
    {X Y Z : C} (f : X ⟶ Y) (q : ShiftOrbitHom A X Z)
    (hfac : ∀ a : A, ∃ c : ShiftHom Y Z a,
      shiftOrbitCompHom
          (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f))
          (shiftOrbitOf Y Z a c) =
        shiftOrbitOf X Z a (q a)) :
    ∃ c : ShiftOrbitHom A Y Z,
      shiftOrbitCompHom
          (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) c = q := by
  classical
  let c : ShiftOrbitHom A Y Z :=
    ∑ a ∈ q.support, shiftOrbitOf Y Z a (Classical.choose (hfac a))
  refine ⟨c, ?_⟩
  calc
    shiftOrbitCompHom
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) c =
        ∑ a ∈ q.support,
          shiftOrbitCompHom
            (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f))
            (shiftOrbitOf Y Z a (Classical.choose (hfac a))) := by
              simp only [c, map_sum]
    _ = ∑ a ∈ q.support, shiftOrbitOf X Z a (q a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Classical.choose_spec (hfac a)
    _ = q := by
      change ∑ a ∈ q.support, DFinsupp.single a (q a) = q
      exact DFinsupp.sum_single

section SplitReflection

variable {k : Type*} [Field k] [CategoryTheory.Linear k C]

/-- The identity-degree component after precomposition by an ordinary map is
ordinary composition. -/
theorem shiftOrbitComp_zero_left_component_zero
    {X Y Z : C} (f : X ⟶ Y) (r : ShiftOrbitHom A Y Z) :
    (shiftOrbitCompHom
      (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) r) 0 =
      shiftHomZero (A := A)
        (f ≫ (shiftHomZeroLinearEquiv (k := k) (A := A) Y Z).symm (r 0)) := by
  classical
  let E₀ := shiftHomZeroLinearEquiv (k := k) (A := A) Y Z
  induction r using DirectSum.induction_on with
  | zero =>
      simp only [map_zero]
      change (0 : ShiftHom X Z (0 : A)) =
        shiftHomZero (A := A) (f ≫ E₀.symm 0)
      rw [map_zero, CategoryTheory.Limits.comp_zero]
      exact (shiftHomZeroLinearEquiv
        (k := k) (A := A) X Z).map_zero.symm
  | of a g =>
      change (shiftOrbitCompHom
        (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f))
        (shiftOrbitOf Y Z a g)) 0 =
          shiftHomZero (A := A) (f ≫ E₀.symm ((shiftOrbitOf Y Z a g) 0))
      by_cases ha : a = 0
      · subst a
        have hg : g = shiftHomZero (A := A) (E₀.symm g) :=
          (E₀.apply_symm_apply g).symm
        rw [hg, shiftOrbitComp_zero_zero]
        have hcomponent : (shiftOrbitOf X Z 0
            (shiftHomZero (A := A) (f ≫ E₀.symm g))) 0 =
            shiftHomZero (A := A) (f ≫ E₀.symm g) := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Z d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom X Z d) 0
              (shiftHomZero (A := A) (f ≫ E₀.symm g))) = _
          rw [DirectSum.component.of]
          simp
        rw [hcomponent]
        congr 2
        have hcomponent' : (shiftOrbitOf Y Z 0
            (shiftHomZero (A := A) (E₀.symm g))) 0 =
            shiftHomZero (A := A) (E₀.symm g) := by
          change DirectSum.component k A (fun d ↦ ShiftHom Y Z d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom Y Z d) 0
              (shiftHomZero (A := A) (E₀.symm g))) = _
          rw [DirectSum.component.of]
          simp
        rw [hcomponent']
        exact (E₀.symm_apply_apply (E₀.symm g)).symm
      · rw [shiftOrbitCompHom_of_of]
        have hleft : (shiftOrbitOf X Z (a + 0)
            (shiftHomComp (shiftHomZero (A := A) f) g)) 0 = 0 := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Z d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom X Z d) (a + 0)
              (shiftHomComp (shiftHomZero (A := A) f) g)) = 0
          rw [DirectSum.component.of]
          simp [ha]
        rw [hleft]
        have hright : (shiftOrbitOf Y Z a g) 0 = 0 := by
          change DirectSum.component k A (fun d ↦ ShiftHom Y Z d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom Y Z d) a g) = 0
          rw [DirectSum.component.of]
          simp [ha]
        rw [hright, map_zero, CategoryTheory.Limits.comp_zero]
        exact (shiftHomZeroLinearEquiv
          (k := k) (A := A) X Z).map_zero.symm
  | add r s hr hs =>
      rw [map_add]
      change (shiftOrbitCompHom
          (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) r) 0 +
          (shiftOrbitCompHom
            (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) s) 0 =
        shiftHomZero (A := A)
          (f ≫ E₀.symm (r 0 + s 0))
      rw [hr, hs]
      rw [map_add, Preadditive.comp_add]
      exact (shiftHomZeroLinearEquiv
        (k := k) (A := A) X Z).map_add _ _ |>.symm

/-- The identity-degree component after postcomposition by an ordinary map is
ordinary categorical composition. -/
theorem shiftOrbitComp_zero_right_component_zero
    {X Y Z : C} (r : ShiftOrbitHom A X Y) (f : Y ⟶ Z) :
    (shiftOrbitCompHom r
      (shiftOrbitOf Y Z 0 (shiftHomZero (A := A) f))) 0 =
      shiftHomZero (A := A)
        ((shiftHomZeroLinearEquiv (k := k) (A := A) X Y).symm (r 0) ≫ f) := by
  classical
  let E₀ := shiftHomZeroLinearEquiv (k := k) (A := A) X Y
  induction r using DirectSum.induction_on with
  | zero =>
      simp only [map_zero]
      change (0 : ShiftHom X Z (0 : A)) =
        shiftHomZero (A := A) (E₀.symm 0 ≫ f)
      rw [map_zero, CategoryTheory.Limits.zero_comp]
      exact (shiftHomZeroLinearEquiv
        (k := k) (A := A) X Z).map_zero.symm
  | of a g =>
      change (shiftOrbitCompHom
        (shiftOrbitOf X Y a g)
        (shiftOrbitOf Y Z 0 (shiftHomZero (A := A) f))) 0 =
          shiftHomZero (A := A) (E₀.symm ((shiftOrbitOf X Y a g) 0) ≫ f)
      by_cases ha : a = 0
      · subst a
        have hg : g = shiftHomZero (A := A) (E₀.symm g) :=
          (E₀.apply_symm_apply g).symm
        rw [hg, shiftOrbitComp_zero_zero]
        have hcomponent : (shiftOrbitOf X Z 0
            (shiftHomZero (A := A) (E₀.symm g ≫ f))) 0 =
            shiftHomZero (A := A) (E₀.symm g ≫ f) := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Z d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom X Z d) 0
              (shiftHomZero (A := A) (E₀.symm g ≫ f))) = _
          rw [DirectSum.component.of]
          simp
        rw [hcomponent]
        congr 2
        have hcomponent' : (shiftOrbitOf X Y 0
            (shiftHomZero (A := A) (E₀.symm g))) 0 =
            shiftHomZero (A := A) (E₀.symm g) := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Y d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom X Y d) 0
              (shiftHomZero (A := A) (E₀.symm g))) = _
          rw [DirectSum.component.of]
          simp
        rw [hcomponent']
        exact (E₀.symm_apply_apply (E₀.symm g)).symm
      · rw [shiftOrbitCompHom_of_of]
        have hleft : (shiftOrbitOf X Z (0 + a)
            (shiftHomComp g (shiftHomZero (A := A) f))) 0 = 0 := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Z d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom X Z d) (0 + a)
              (shiftHomComp g (shiftHomZero (A := A) f))) = 0
          rw [DirectSum.component.of]
          simp [ha]
        rw [hleft]
        have hright : (shiftOrbitOf X Y a g) 0 = 0 := by
          change DirectSum.component k A (fun d ↦ ShiftHom X Y d) 0
            (DirectSum.lof k A (fun d ↦ ShiftHom X Y d) a g) = 0
          rw [DirectSum.component.of]
          simp [ha]
        rw [hright, map_zero, CategoryTheory.Limits.zero_comp]
        exact (shiftHomZeroLinearEquiv
          (k := k) (A := A) X Z).map_zero.symm
  | add r s hr hs =>
      rw [map_add]
      change (shiftOrbitCompHom r
          (shiftOrbitOf Y Z 0 (shiftHomZero (A := A) f))) 0 +
          (shiftOrbitCompHom s
            (shiftOrbitOf Y Z 0 (shiftHomZero (A := A) f))) 0 =
        shiftHomZero (A := A)
          (E₀.symm (r 0 + s 0) ≫ f)
      rw [hr, hs]
      rw [map_add, Preadditive.add_comp]
      exact (shiftHomZeroLinearEquiv
        (k := k) (A := A) X Z).map_add _ _ |>.symm

/-- The degree-zero orbit inclusion reflects split monomorphisms. -/
theorem isSplitMono_of_shiftOrbit_zero_isSplitMono
    (k : Type*) [Field k] [CategoryTheory.Linear k C]
    {X Y : C} (f : X ⟶ Y)
    (hsplit : IsSplitMono
      (show (show ShiftOrbitCategory C A from X) ⟶
          (show ShiftOrbitCategory C A from Y) from
        shiftOrbitOf X Y 0 (shiftHomZero (A := A) f))) :
    IsSplitMono f := by
  classical
  let q : (show ShiftOrbitCategory C A from X) ⟶
      (show ShiftOrbitCategory C A from Y) :=
    shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)
  letI : IsSplitMono q := hsplit
  let r : ShiftOrbitHom A Y X := retraction q
  let c := (shiftHomZeroLinearEquiv (k := k) (A := A) Y X).symm (r 0)
  apply IsSplitMono.mk'
  refine ⟨c, ?_⟩
  have h := congrArg (fun z : ShiftOrbitHom A X X ↦ z 0)
    (IsSplitMono.id q)
  change (shiftOrbitCompHom
      (shiftOrbitOf X Y 0 (shiftHomZero (A := A) f)) r) 0 =
    (shiftOrbitId X) 0 at h
  rw [shiftOrbitComp_zero_left_component_zero (k := k)] at h
  have hid : (shiftOrbitId X) 0 = shiftHomId (A := A) X := by
    change DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
      (DirectSum.lof k A (fun d ↦ ShiftHom X X d) 0
        (shiftHomId (A := A) X)) = _
    rw [DirectSum.component.of]
    simp
  rw [hid] at h
  change shiftHomZero (A := A) (f ≫ c) = shiftHomId (A := A) X at h
  rw [← shiftHomZero_id (A := A)] at h
  exact (shiftHomZeroLinearEquiv (k := k) (A := A) X X).injective h

end SplitReflection

end MagnitudeConjecture.CoveringHom
