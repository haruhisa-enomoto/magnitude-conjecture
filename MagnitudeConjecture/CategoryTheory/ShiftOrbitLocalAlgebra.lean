import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.ShiftOrbitDecomposition
import MagnitudeConjecture.LinearAlgebra.LocalAlgebraResidue

/-!
# Local residue of a shift-orbit endomorphism algebra

For an indecomposable object with trivial shift stabilizer, taking the
ordinary degree-zero component of a finite-support shift-orbit endomorphism
and then passing to the residue field is multiplicative.  Products returning
to degree zero through a nonzero shift factor through a nonisomorphic
indecomposable and therefore have zero residue.

This is the local-algebra mechanism in Gabriel's assertion that a pushed
endomorphism is nilpotent exactly when its identity component is nilpotent.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable [CategoryTheory.Limits.HasBinaryBiproducts C]
variable [IsIdempotentComplete C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- The residue scalar of the ordinary degree-zero component of a shift-orbit
endomorphism. -/
noncomputable def shiftOrbitResidueLinearMap (X : C)
    [FiniteDimensional k (End X)] [IsLocalRing (End X)] :
    ShiftOrbitHom A X X →ₗ[k] k :=
  (LocalAlgebraResidue.residueLinearMap k (End X)).comp
    ((shiftHomZeroLinearEquiv (k := k) (A := A) X X).symm.toLinearMap.comp
      (DirectSum.component k A (fun a ↦ ShiftHom X X a) 0))

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [CategoryTheory.Limits.HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
@[simp]
theorem shiftOrbitResidueLinearMap_of_ne
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)]
    {a : A} (ha : a ≠ 0) (f : ShiftHom X X a) :
    shiftOrbitResidueLinearMap (k := k) (A := A) X
      (shiftOrbitOf X X a f) = 0 := by
  classical
  have hcomponent :
      DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
          (shiftOrbitOf X X a f) = 0 := by
    change DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
      (DirectSum.lof k A (fun d ↦ ShiftHom X X d) a f) = 0
    rw [DirectSum.component.of]
    simp [ha]
  change LocalAlgebraResidue.residueScalar k
    (End.of ((shiftHomZeroLinearEquiv (k := k) (A := A) X X).symm
      (DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
        (shiftOrbitOf X X a f)))) = 0
  rw [hcomponent, map_zero]
  exact LocalAlgebraResidue.residueScalar_zero (k := k) (E := End X)

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [CategoryTheory.Limits.HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
@[simp]
theorem shiftOrbitResidueLinearMap_of_zero
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)]
    (f : ShiftHom X X (0 : A)) :
    shiftOrbitResidueLinearMap (k := k) (A := A) X
      (shiftOrbitOf X X 0 f) =
        LocalAlgebraResidue.residueScalar k
          (End.of ((shiftHomZeroLinearEquiv
            (k := k) (A := A) X X).symm f)) := by
  classical
  have hcomponent :
      DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
          (shiftOrbitOf X X 0 f) = f := by
    change DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
      (DirectSum.lof k A (fun d ↦ ShiftHom X X d) 0 f) = f
    rw [DirectSum.component.of]
    simp
  change LocalAlgebraResidue.residueScalar k
    (End.of ((shiftHomZeroLinearEquiv (k := k) (A := A) X X).symm
      (DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
        (shiftOrbitOf X X 0 f)))) = _
  rw [hcomponent]

omit [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous product returning to degree zero through a nonzero shift
has zero residue. -/
theorem residueScalar_shiftHomComp'_eq_zero
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)]
    (hX : Indecomposable X)
    (htrivial : ∀ a : A, Nonempty (X ≅ X⟦a⟧) → a = 0)
    {a b : A} (ha : a ≠ 0) (hba : b + a = 0)
    (f : ShiftHom X X a) (g : ShiftHom X X b) :
    LocalAlgebraResidue.residueScalar k
        (End.of ((shiftHomZeroLinearEquiv
          (k := k) (A := A) X X).symm
            (shiftHomComp' hba f g))) = 0 := by
  let c : X⟦a⟧ ⟶ X :=
    (shiftFunctor C a).map g ≫
      (shiftFunctorAdd' C b a 0 hba).inv.app X ≫
        (shiftFunctorZero C A).hom.app X
  have hfactor :
      (shiftHomZeroLinearEquiv (k := k) (A := A) X X).symm
          (shiftHomComp' hba f g) = f ≫ c := by
    dsimp [shiftHomZeroLinearEquiv, shiftHomComp',
      CategoryTheory.ShiftedHom.homEquiv, c]
    simp only [Category.assoc]
    simp [shiftFunctorZero']
  have hshift : Indecomposable (X⟦a⟧) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor C a) X).mpr hX
  have hnonunit : ¬ IsUnit (End.of (f ≫ c)) := by
    intro hunit
    haveI : IsIso (f ≫ c) := (isUnit_iff_isIso (f ≫ c)).mp hunit
    haveI : IsSplitMono f := by
      apply IsSplitMono.mk'
      exact
        { retraction := c ≫ inv (f ≫ c)
          id := by rw [← Category.assoc, IsIso.hom_inv_id] }
    haveI : IsIso f :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        hshift f hX.1
    exact ha (htrivial a ⟨asIso f⟩)
  have hker : End.of (f ≫ c) ∈ LinearMap.ker
      (LocalAlgebraResidue.residueLinearMap k (End X)) :=
    (LocalAlgebraResidue.mem_ker_residueLinearMap_iff
      (k := k) (E := End X) (End.of (f ≫ c))).mpr hnonunit
  rw [hfactor]
  exact hker

omit [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- The shift-orbit residue of a homogeneous product through a nonzero shift
vanishes. -/
theorem shiftOrbitResidueLinearMap_comp_of_ne_of_add_eq_zero
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)]
    (hX : Indecomposable X)
    (htrivial : ∀ a : A, Nonempty (X ≅ X⟦a⟧) → a = 0)
    {a b : A} (ha : a ≠ 0) (hba : b + a = 0)
    (f : ShiftHom X X a) (g : ShiftHom X X b) :
    shiftOrbitResidueLinearMap (k := k) (A := A) X
      (shiftOrbitOf X X (b + a) (shiftHomComp f g)) = 0 := by
  classical
  have hcomponent :
      DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
          (shiftOrbitOf X X (b + a) (shiftHomComp f g)) =
        shiftHomComp' hba f g := by
    change DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
      (DirectSum.lof k A (fun d ↦ ShiftHom X X d) (b + a)
        (shiftHomComp f g)) = shiftHomComp' hba f g
    rw [DirectSum.component.of]
    simp only [dif_pos hba]
    exact eq_of_heq ((eqRec_heq _ _).trans
      (shiftHomComp_heq_shiftHomComp' hba f g))
  change LocalAlgebraResidue.residueScalar k
    (End.of ((shiftHomZeroLinearEquiv (k := k) (A := A) X X).symm
      (DirectSum.component k A (fun d ↦ ShiftHom X X d) 0
        (shiftOrbitOf X X (b + a) (shiftHomComp f g))))) = 0
  rw [hcomponent]
  exact residueScalar_shiftHomComp'_eq_zero
    (k := k) (A := A) X hX htrivial ha hba f g

omit [∀ a : A, (shiftFunctor C a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero residue is multiplicative for shift-orbit convolution
when the base object is indecomposable with trivial shift stabilizer. -/
theorem shiftOrbitResidueLinearMap_comp
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)]
    (hX : Indecomposable X)
    (htrivial : ∀ a : A, Nonempty (X ≅ X⟦a⟧) → a = 0)
    (q r : ShiftOrbitHom A X X) :
    shiftOrbitResidueLinearMap (k := k) (A := A) X
        (shiftOrbitCompHom q r) =
      shiftOrbitResidueLinearMap (k := k) (A := A) X q *
        shiftOrbitResidueLinearMap (k := k) (A := A) X r := by
  classical
  refine DirectSum.induction_on q ?_ ?_ ?_
  · simp
  · intro a f
    refine DirectSum.induction_on r ?_ ?_ ?_
    · simp
    · intro b g
      change shiftOrbitResidueLinearMap (k := k) (A := A) X
          (shiftOrbitCompHom
            (shiftOrbitOf X X a f) (shiftOrbitOf X X b g)) =
        shiftOrbitResidueLinearMap (k := k) (A := A) X
            (shiftOrbitOf X X a f) *
          shiftOrbitResidueLinearMap (k := k) (A := A) X
            (shiftOrbitOf X X b g)
      by_cases ha : a = 0
      · subst a
        by_cases hb : b = 0
        · subst b
          let E₀ := shiftHomZeroLinearEquiv
            (k := k) (A := A) X X
          have hf : f = shiftHomZero (A := A) (E₀.symm f) :=
            (E₀.apply_symm_apply f).symm
          have hg : g = shiftHomZero (A := A) (E₀.symm g) :=
            (E₀.apply_symm_apply g).symm
          rw [hf, hg]
          rw [shiftOrbitComp_zero_zero]
          simp only [shiftOrbitResidueLinearMap_of_zero]
          change LocalAlgebraResidue.residueScalar k
              (End.of (E₀.symm (E₀ (E₀.symm f ≫ E₀.symm g)))) =
            LocalAlgebraResidue.residueScalar k
                (End.of (E₀.symm (E₀ (E₀.symm f)))) *
              LocalAlgebraResidue.residueScalar k
                (End.of (E₀.symm (E₀ (E₀.symm g))))
          simp only [LinearEquiv.symm_apply_apply]
          rw [show End.of (E₀.symm f ≫ E₀.symm g) =
              End.of (E₀.symm g) * End.of (E₀.symm f) by rfl,
            LocalAlgebraResidue.residueScalar_mul, mul_comm]
        · rw [shiftOrbitCompHom_of_of]
          rw [shiftOrbitResidueLinearMap_of_ne X (by simpa using hb)]
          rw [shiftOrbitResidueLinearMap_of_ne X hb]
          simp
      · rw [shiftOrbitResidueLinearMap_of_ne X ha]
        simp only [zero_mul]
        rw [shiftOrbitCompHom_of_of]
        by_cases hba : b + a = 0
        · exact shiftOrbitResidueLinearMap_comp_of_ne_of_add_eq_zero
            (k := k) (A := A) X hX htrivial ha hba f g
        · exact shiftOrbitResidueLinearMap_of_ne X hba _
    · intro r₁ r₂ hr₁ hr₂
      simpa only [map_add, AddMonoidHom.add_apply, mul_add] using
        congrArg₂ (.+.) hr₁ hr₂
  · intro q₁ q₂ hq₁ hq₂
    simpa only [map_add, AddMonoidHom.add_apply, add_mul] using
      congrArg₂ (.+.) hq₁ hq₂

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k]
  [CategoryTheory.Limits.HasBinaryBiproducts C]
  [IsIdempotentComplete C] in
/-- The residue of the shift-orbit identity is one. -/
theorem shiftOrbitResidueLinearMap_one
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)] :
    shiftOrbitResidueLinearMap (k := k) (A := A) X (shiftOrbitId X) = 1 := by
  rw [shiftOrbitId, shiftOrbitResidueLinearMap_of_zero]
  rw [← shiftHomZero_id (A := A) X]
  let E₀ := shiftHomZeroLinearEquiv (k := k) (A := A) X X
  change LocalAlgebraResidue.residueScalar k
    (End.of (E₀.symm (E₀ (𝟙 X)))) = 1
  rw [LinearEquiv.symm_apply_apply]
  change LocalAlgebraResidue.residueScalar k (1 : End X) = 1
  simpa using LocalAlgebraResidue.residueScalar_algebraMap
    (k := k) (E := End X) 1

/-- The degree-zero residue is a `k`-algebra homomorphism on the shift-orbit
endomorphism ring. -/
noncomputable def shiftOrbitResidueAlgHom
    (X : C) [FiniteDimensional k (End X)] [IsLocalRing (End X)]
    (hX : Indecomposable X)
    (htrivial : ∀ a : A, Nonempty (X ≅ X⟦a⟧) → a = 0) :
    End (show ShiftOrbitCategory C A from X) →ₐ[k] k where
  toFun := shiftOrbitResidueLinearMap (k := k) (A := A) X
  map_zero' := (shiftOrbitResidueLinearMap (k := k) (A := A) X).map_zero
  map_one' := shiftOrbitResidueLinearMap_one (k := k) (A := A) X
  map_add' := (shiftOrbitResidueLinearMap (k := k) (A := A) X).map_add
  map_mul' q r := by
    change shiftOrbitResidueLinearMap (k := k) (A := A) X
        (shiftOrbitCompHom r q) =
      shiftOrbitResidueLinearMap (k := k) (A := A) X q *
        shiftOrbitResidueLinearMap (k := k) (A := A) X r
    rw [shiftOrbitResidueLinearMap_comp X hX htrivial]
    exact mul_comm _ _
  commutes' c := by
    change shiftOrbitResidueLinearMap (k := k) (A := A) X
      (c • shiftOrbitId X) = c
    rw [map_smul, shiftOrbitResidueLinearMap_one]
    simp

end MagnitudeConjecture.CoveringHom
