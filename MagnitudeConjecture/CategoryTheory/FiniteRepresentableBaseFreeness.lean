import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleTrivialStabilizer
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.RepresentableDeckShift

/-!
# Base-category freeness from finite representables

The manuscript proves trivial deck stabilizers for nonzero finite-support
modules.  Applying that statement to the finite representable of an object
recovers freeness on isomorphism classes of category objects.  This removes a
separate base-category freeness hypothesis from finite-cover applications.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [IsMulTorsionFree G]
variable [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]

/-- If every representable is finite-dimensional and every object has local
endomorphism ring, then the torsion-free free object action is also free on
categorical isomorphism classes.  The proof detects an object isomorphism on
its nonzero finite representable and invokes finite-support stabilizer
freeness. -/
theorem isFreeOnIsomorphismClasses_of_finiteRepresentables
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    IsFreeOnIsomorphismClasses (C := C) (G := G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro g X hX
  let M := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
  have hM : Indecomposable M :=
    finiteDimensionalLinearCoyoneda_indecomposable hP hlocal X
  let a : Additive G := Additive.ofMul g⁻¹
  obtain ⟨e⟩ := hX
  let eObj : X ≅ (shiftFunctor C a).obj X :=
    e ≪≫ eqToIso (by rw [inv_inv]) ≪≫ (D.objIso g⁻¹ X).symm
  let L := finiteDimensionalLinearCoyonedaFunctor (k := k) hP
  let eRepShift :
      (shiftFunctor
          (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) a).obj
          (L.obj (Opposite.op X)) ≅
        L.obj (Opposite.op X) :=
    D.finiteDimensionalLinearCoyonedaShiftIso (k := k) hP a X ≪≫
      L.mapIso eObj.op
  have ha : a = 0 :=
    D.finiteDimensionalModule_trivialStabilizer (k := k) M hM.1 a
      ⟨eRepShift.symm⟩
  have hginv : g⁻¹ = 1 := by
    simpa [a] using congrArg Additive.toMul ha
  exact inv_eq_one.mp hginv

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
