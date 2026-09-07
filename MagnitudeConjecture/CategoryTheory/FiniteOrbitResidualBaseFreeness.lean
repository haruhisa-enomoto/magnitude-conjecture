import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownResidualFreeness
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamPresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.RepresentableDeckShift

/-!
# Freeness of the residual action on the strict subgroup-orbit category

An isomorphism stabilizing a strict subgroup orbit also stabilizes its finite
representable module.  That representable is the subgroup push-down of an
indecomposable ambient representable, so module-level residual freeness forces
the residual group element to be trivial.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [IsMulTorsionFree G]
variable [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The residual quotient acts freely on isomorphism classes of objects of
the strict subgroup-orbit skeleton.  The proof passes through finite
representable modules and hence does not require the quotient group to be
torsion-free. -/
theorem deckOrbitResidual_isFreeOnIsomorphismClasses
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    IsFreeOnIsomorphismClasses
      (C := DeckOrbitSkeleton C N) (G := G ⧸ N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := (D.restrict N).isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := (D.restrict N).finiteDimensionalModuleCategoryHasShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  let R := D.deckOrbitResidualCoherentDeckShift N
  letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
  intro q Q hq
  induction Q using Quotient.inductionOn with
  | _ X =>
      let M := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
      have hM : Indecomposable M :=
        finiteDimensionalLinearCoyoneda_indecomposable hP hlocal X
      let P := (D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
        (k := k)
      let hPdown := (D.restrict N).orbitSkeletonLinearCoyonedaFinite
        (k := k) hP
      let Q : DeckOrbitSkeleton C N :=
        (Quotient.mk'' X : MulAction.orbitRel.Quotient N C)
      let L := finiteDimensionalLinearCoyonedaFunctor (k := k) hPdown
      let eP :=
        (D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
          (k := k) X (hP X)
      let a : Additive (G ⧸ N) := Additive.ofMul q⁻¹
      obtain ⟨e⟩ := hq
      let eObj : Q ≅ (shiftFunctor (DeckOrbitSkeleton C N) a).obj Q :=
        e ≪≫ eqToIso (by rw [inv_inv]) ≪≫ (R.objIso q⁻¹ Q).symm
      let eRepShift :
          (shiftFunctor
              (FiniteDimensionalModuleCategory.{u, v, v, v}
                (C := DeckOrbitSkeleton C N) k) a).obj
              (L.obj (Opposite.op Q)) ≅
            L.obj (Opposite.op Q) :=
        R.finiteDimensionalLinearCoyonedaShiftIso
            (k := k) hPdown a Q ≪≫
          L.mapIso eObj.op
      have hstab : Nonempty
          (P.obj M ≅
            (shiftFunctor
              (FiniteDimensionalModuleCategory.{u, v, v, v}
                (C := DeckOrbitSkeleton C N) k) a).obj (P.obj M)) :=
        ⟨eP ≪≫ eRepShift.symm ≪≫
          (shiftFunctor
            (FiniteDimensionalModuleCategory.{u, v, v, v}
              (C := DeckOrbitSkeleton C N) k) a).mapIso eP.symm⟩
      have ha : a = 0 :=
        D.finiteDimensionalModuleOrbitSkeletonPushdown_residual_trivialStabilizer
          (k := k) M hM N a hstab
      have hqinv : q⁻¹ = 1 := by
        simpa [a] using congrArg Additive.toMul ha
      exact inv_eq_one.mp hqinv

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
