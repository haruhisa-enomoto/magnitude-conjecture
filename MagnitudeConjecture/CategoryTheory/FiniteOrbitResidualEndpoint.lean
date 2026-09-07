import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerPushdown
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerFiniteSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownDensity
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownResidualFreeness
import MagnitudeConjecture.CategoryTheory.FiniteOrbitResidualBaseFreeness
import MagnitudeConjecture.CategoryTheory.FiniteOrbitResidualLabelFreeness
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownShift
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownExactLocalDensity
import MagnitudeConjecture.Combinatorics.FiniteOrbitCarrier

/-!
# Residual finite-push-down endpoint

The strict orbit-tower equivalence identifies the direct quotient with the
successive quotient by a normal subgroup and its residual quotient.  This
file connects density for direct finite push-down to the residual finite
push-down: every label of the transported direct skeleton is represented by
the residual push-down of a subgroup push-down.

The residual coherent deck shift and the shift transported through the orbit
tower are propositionally equal but expensive to normalize inside module
category types.  The finite residual push-down is therefore kept abstract at
the theorem boundary and identified with the coherent construction by an
explicit equality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

universe u₁ u₂ v uK w

variable {k : Type uK} [Field k]
variable {C : Type u₁} [Category.{v} C] [Preadditive C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]
variable {G : Type w} [Group G]
variable (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
variable (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := D))
variable (P : FiniteDimensionalModuleCategory.{u₁, v, uK, v} (C := C) k ⥤
  FiniteDimensionalModuleCategory.{u₂, v, uK, v} (C := D) k)
variable (hIndec : ∀ i : Fin S.n, Indecomposable (P.obj (S.obj i)))

/-- The target-skeleton label representing the push-down of a source label. -/
noncomputable def pushdownLabel (i : Fin S.n) : Fin T.n :=
  Classical.choose (T.complete (P.obj (S.obj i)) (hIndec i))

/-- Chosen isomorphism from a pushed source label to its target-skeleton
representative. -/
noncomputable def pushdownLabelIso (i : Fin S.n) :
    P.obj (S.obj i) ≅ T.obj (S.pushdownLabel T P hIndec i) :=
  Classical.choice
    (Classical.choose_spec (T.complete (P.obj (S.obj i)) (hIndec i)))

/-- The pushed-label classifier is invariant when push-down identifies every
translated source object with the original one. -/
theorem pushdownLabel_invariant
    [MulAction G (Fin S.n)]
    (hshift : ∀ (g : G) (i : Fin S.n),
      Nonempty (P.obj (S.obj (g • i)) ≅ P.obj (S.obj i))) :
    ∀ (g : G) (i : Fin S.n),
      S.pushdownLabel T P hIndec (g • i) =
        S.pushdownLabel T P hIndec i := by
  intro g i
  apply T.skeletal
  obtain ⟨e⟩ := hshift g i
  exact ⟨(S.pushdownLabelIso T P hIndec (g • i)).symm ≪≫ e ≪≫
    S.pushdownLabelIso T P hIndec i⟩

/-- Essential coverage of target labels makes the pushed-label classifier
surjective when the push-down functor reflects indecomposability. -/
theorem pushdownLabel_surjective
    [P.Additive] [P.Faithful]
    (coverage : ∀ j : Fin T.n,
      ∃ X : FiniteDimensionalModuleCategory.{u₁, v, uK, v} (C := C) k,
        Nonempty (P.obj X ≅ T.obj j)) :
    Function.Surjective (S.pushdownLabel T P hIndec) := by
  intro j
  obtain ⟨X, ⟨eX⟩⟩ := coverage j
  have hPX : Indecomposable (P.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eX).2
      (T.indecomposable j)
  have hX : Indecomposable X :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P X hPX
  obtain ⟨i, ⟨eI⟩⟩ := S.complete X hX
  refine ⟨i, ?_⟩
  apply T.skeletal
  exact ⟨(S.pushdownLabelIso T P hIndec i).symm ≪≫
    (P.mapIso eI).symm ≪≫ eX⟩

/-- If isomorphic push-downs reflect to a common source orbit, then the fibres
of the pushed-label classifier are exactly source-label orbits. -/
theorem pushdownLabel_fiber
    [MulAction G (Fin S.n)]
    (hreflect : ∀ i j : Fin S.n,
      Nonempty (P.obj (S.obj i) ≅ P.obj (S.obj j)) →
        ∃ g : G, g • j = i) :
    ∀ i j, S.pushdownLabel T P hIndec i =
        S.pushdownLabel T P hIndec j →
      ∃ g : G, g • j = i := by
  intro i j hij
  apply hreflect i j
  exact ⟨S.pushdownLabelIso T P hIndec i ≪≫
    eqToIso (congrArg T.obj hij) ≪≫
    (S.pushdownLabelIso T P hIndec j).symm⟩

end MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G]
variable [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The Auslander--Reiten surplus of the finite module category over the
strict deck-orbit skeleton.  This is the literal downstairs endpoint quantity
used in the covering average. -/
noncomputable def finiteOrbitSurplus
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) : ℤ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let S := D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep
  exact @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
    (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      S.toFiniteRightTauCategoryData)
    S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _)

/-- View the canonical finite-orbit indecomposable skeleton through an
extensionally chosen shift instance equal to the coherent deck shift. -/
noncomputable def finiteOrbitModuleIndecomposableSkeleton_of_hasShift_eq
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI := H
    letI := hadd
    letI := hlinear
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := DeckOrbitSkeleton C G) := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  exact D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep

/-- View the canonical finite-orbit surplus through an extensionally chosen
shift instance equal to the coherent deck shift. -/
noncomputable def finiteOrbitSurplus_of_hasShift_eq
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) : ℤ := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  exact D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep

/-- Transporting the finite-orbit surplus across an equal shift instance
does not change its value. -/
theorem finiteOrbitSurplus_of_hasShift_eq_eq
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI := H
    letI := hadd
    letI := hlinear
    D.finiteOrbitSurplus_of_hasShift_eq
        (k := k) H hadd hlinear hH hP hI hlocal hfree hrep =
      D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
  cases hH
  rfl

/-- The transported finite-orbit surplus is the literal surplus of the
transported canonical skeleton. -/
theorem finiteOrbitSurplus_of_hasShift_eq_eq_skeleton
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (hEnough : letI := H
      letI := hadd
      letI := hlinear
      EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)) :
    letI := H
    letI := hadd
    letI := hlinear
    letI := hEnough
    let S := D.finiteOrbitModuleIndecomposableSkeleton_of_hasShift_eq
      (k := k) H hadd hlinear hH hP hI hlocal hfree hrep
    D.finiteOrbitSurplus_of_hasShift_eq
        (k := k) H hadd hlinear hH hP hI hlocal hfree hrep =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.toFiniteRightTauCategoryData)
        S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  cases hH
  rfl

/-- The finite-orbit surplus depends on a coherent deck shift only through
its coherent shift core; changing the chosen object-action comparison does
not change the resulting complete-skeleton invariant. -/
theorem finiteOrbitSurplus_eq_of_core_eq
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (E : CoherentDeckShift C G)
    (hcore : D.core = E.core)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI : ∀ a : Additive G, (E.core.F a).Additive := by
      rw [← hcore]
      infer_instance
    letI : ∀ a : Additive G, (E.core.F a).Linear k := by
      rw [← hcore]
      infer_instance
    D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep =
      E.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
  rcases E with ⟨Ecore, EobjIso⟩
  dsimp at hcore ⊢
  subst Ecore
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let S := D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep
  let E' : CoherentDeckShift C G :=
    { core := D.core
      objIso := EobjIso }
  let T := E'.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep
  change
    @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.toFiniteRightTauCategoryData)
        S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _)
  let e :
      FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k ≌
        FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k :=
    CategoryTheory.Equivalence.refl
  letI : e.functor.Additive := by
    dsimp only [e, CategoryTheory.Equivalence.refl]
    infer_instance
  exact T.surplus_eq_of_equivalence e S

/-- Exact finite push-down identifies the local-density sum over the source
label orbits with the total local density of any covered target skeleton. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_orbitSum_eq_of_hasShift_eq
    [IsAlgClosed k]
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (T : letI := H
      letI := hadd
      letI := hlinear
      FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
    (hEnoughSource : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    (hEnoughTarget : letI := H
      letI := hadd
      letI := hlinear
      EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k))
    (hShiftFree :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
      S.IsShiftFreeOnLabels (G := G))
    (coverage :
      letI := H
      letI := hadd
      letI := hlinear
      let P := D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
        (k := k) H hadd hlinear hH
      ∀ j : Fin T.n,
        ∃ X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Nonempty (P.obj X ≅ T.obj j)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    letI := S.labelMulAction (G := G)
    letI := S.labelOrbitFintype (G := G)
    letI := H
    letI := hadd
    letI := hlinear
    (∑ q : MulAction.orbitRel.Quotient G (Fin S.n),
        MagnitudeConjecture.CoveringAction.orbitInvariantDescend
          S.rightTauLocalDensity S.rightTauLocalDensity_smul q) =
      ∑ j : Fin T.n, T.rightTauLocalDensity j := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := hEnoughSource
  letI := S.labelMulAction (G := G)
  letI := S.labelOrbitFintype (G := G)
  letI := H
  letI := hadd
  letI := hlinear
  letI := hEnoughTarget
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
    (k := k) H hadd hlinear hH
  letI : P.Additive :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_additive
      (k := k) H hadd hlinear hH
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_faithful
      (k := k) H hadd hlinear hH
  let htrivial := S.indecomposable_trivialStabilizer_of_isShiftFreeOnLabels
    hShiftFree
  let hIndec : ∀ i : Fin S.n, Indecomposable (P.obj (S.obj i)) := fun i ↦
    D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_indecomposable_of_trivial_stabilizer
      (k := k) H hadd hlinear hH (S.obj i) (S.indecomposable i)
        (htrivial (S.obj i) (S.indecomposable i))
  let c := S.pushdownLabel T P hIndec
  have hc_invariant : ∀ (g : G) (i : Fin S.n), c (g • i) = c i := by
    apply S.pushdownLabel_invariant T P hIndec
    intro g i
    let a : Additive G := Additive.ofMul g⁻¹
    exact ⟨P.mapIso (S.shiftLabelIso g i).symm ≪≫
      D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_shiftIso
        (k := k) H hadd hlinear hH (S.obj i) a⟩
  have hc_surjective : Function.Surjective c := by
    apply S.pushdownLabel_surjective T P hIndec
    exact coverage
  have hc_fiber : ∀ i j, c i = c j → ∃ g : G, g • j = i := by
    apply S.pushdownLabel_fiber T P hIndec
    intro i j hij
    obtain ⟨a, ⟨e⟩⟩ :=
      D.exists_shift_iso_of_pushdown_iso_of_hasShift_eq
        (k := k) H hadd hlinear hH (S.obj i) (S.obj j)
          (S.indecomposable i) (S.indecomposable j)
          (htrivial (S.obj i) (S.indecomposable i)) hij
    let g : G := a.toMul⁻¹
    refine ⟨g, ?_⟩
    change S.shiftLabel g j = i
    apply S.skeletal
    have hga : Additive.ofMul g⁻¹ = a := by
      apply Additive.toMul.injective
      simp [g]
    let eDegree :
        (shiftFunctor
          (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
          (Additive.ofMul g⁻¹)).obj (S.obj j) ≅
        (shiftFunctor
          (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) a).obj
          (S.obj j) :=
      eqToIso (congrArg
        (fun b : Additive G ↦
          (shiftFunctor
            (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) b).obj
              (S.obj j)) hga)
    exact ⟨(S.shiftLabelIso g j).symm ≪≫ eDegree ≪≫ e.symm⟩
  have hvalue : ∀ i : Fin S.n,
      S.rightTauLocalDensity i = T.rightTauLocalDensity (c i) := by
    intro i
    exact
      D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_rightTauLocalDensity_eq_of_indec_trivialStabilizers
        H hadd hlinear hH hP hI hlocal hfree htrivial S T i (c i)
          (S.pushdownLabelIso T P hIndec i)
  exact MagnitudeConjecture.CoveringAction.sum_orbitInvariantDescend_eq_sum_of_orbitClassifier
    c hc_invariant hc_surjective hc_fiber S.rightTauLocalDensity
      S.rightTauLocalDensity_smul T.rightTauLocalDensity hvalue

/-- Exact finite push-down scales the total source local density by the order
of the deck group.  This is the integral endpoint equation consumed by the
finite covering telescope. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_sum_eq_card_mul_of_hasShift_eq
    [IsAlgClosed k] [Fintype G]
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (T : letI := H
      letI := hadd
      letI := hlinear
      FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
    (hEnoughSource : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    (hEnoughTarget : letI := H
      letI := hadd
      letI := hlinear
      EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k))
    (hShiftFree :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
      S.IsShiftFreeOnLabels (G := G))
    (coverage :
      letI := H
      letI := hadd
      letI := hlinear
      let P := D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
        (k := k) H hadd hlinear hH
      ∀ j : Fin T.n,
        ∃ X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Nonempty (P.obj X ≅ T.obj j)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    letI := H
    letI := hadd
    letI := hlinear
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
      (Fintype.card G : ℤ) * ∑ j : Fin T.n, T.rightTauLocalDensity j := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := hEnoughSource
  letI := S.labelMulAction (G := G)
  letI := S.labelOrbitFintype (G := G)
  letI := H
  letI := hadd
  letI := hlinear
  letI := hEnoughTarget
  rw [S.sum_occurrenceLocalDensity_eq_card_mul_orbitSum hShiftFree,
    D.finiteDimensionalModuleOrbitSkeletonPushdown_orbitSum_eq_of_hasShift_eq
      H hadd hlinear hH hP hI hlocal hfree S T hEnoughSource hEnoughTarget
        hShiftFree coverage]

/-- Every object of the transported direct indecomposable skeleton is in the
essential image of residual finite push-down.  The equality argument is the
controlled boundary between the tower's transported residual shift and the
coherent shift used to construct finite push-down. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_deckOrbitTowerCoverage
    (hDensity : FiniteOrbitPushdownDensity.{u, v, v, v, v} (k := k) D)
    (N : Subgroup G) [N.Normal]
    (S : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G)) :
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
    let R := D.deckOrbitResidualCoherentDeckShift N
    ∀ P : FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C N) k ⥤
        FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) k,
      P = R.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
        (k := k) (D.deckOrbitResidualHasShift N)
        (D.deckOrbitResidualAdditiveShift N)
        (D.deckOrbitResidualLinearShift (k := k) N)
        (D.deckOrbitResidualCoherentDeckShift_hasShift_eq N).symm →
      ∀ j : Fin S.n,
        ∃ X : FiniteDimensionalModuleCategory.{u, v, v, v}
            (C := DeckOrbitSkeleton C N) k,
          Nonempty
            (P.obj X ≅
              (D.deckOrbitTowerFiniteDimensionalModuleEquivalence
                (k := k) N).functor.obj (S.obj j)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := (D.restrict N).isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := (D.restrict N).finiteDimensionalModuleCategoryHasShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  intro R P hP j
  let PN :=
    (D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, v, v, v}
      (k := k)
  let E :=
    (D.deckOrbitTowerFiniteDimensionalModuleEquivalence (k := k) N).functor
  obtain ⟨M, ⟨eM⟩⟩ := hDensity.essSurj.mem_essImage (S.obj j)
  let J := (IsFiniteDimensionalModule
    (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) k).ι
  let eTail := J.mapIso (E.mapIso eM)
  let eLinear :=
    (D.linearModuleOrbitSkeletonPushdownTowerIso (k := k) N).app M.obj ≪≫
      eTail
  let eFinite :=
    R.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_isoMk
      (k := k) (D.deckOrbitResidualHasShift N)
      (D.deckOrbitResidualAdditiveShift N)
      (D.deckOrbitResidualLinearShift (k := k) N)
      (D.deckOrbitResidualCoherentDeckShift_hasShift_eq N).symm (PN.obj M)
      eLinear
  refine ⟨PN.obj M, ?_⟩
  rw [hP]
  exact ⟨eFinite⟩

set_option maxHeartbeats 2000000 in
/-- Passing from a finite-index subgroup orbit to the full orbit scales the
literal finite-orbit Auslander--Reiten surplus by the residual covering
degree. -/
theorem finiteOrbitSurplus_restrict_eq_card_mul
    [IsAlgClosed k] [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G) :
    let N' : Subgroup G := N
    letI : Finite (MulAction.orbitRel.Quotient N' C) :=
      MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
    letI : Fintype (G ⧸ N') := Fintype.ofFinite _
    (D.restrict N').finiteOrbitSurplus
        (k := k) hP hI hlocal (hfree.restrict N') hrep =
      (Fintype.card (G ⧸ N') : ℤ) *
        D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
  let N' : Subgroup G := N
  letI : Finite (MulAction.orbitRel.Quotient N' C) :=
    MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Fintype (G ⧸ N') := Fintype.ofFinite _
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  let hfreeN : IsFreeOnIsomorphismClasses (C := C) (G := N') :=
    hfree.restrict N'
  let S := (D.restrict N').finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfreeN hrep
  let T := D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep
  let hPN := (D.restrict N').orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hIN := (D.restrict N').orbitSkeletonDualLinearYonedaFinite (k := k) hI
  let hlocalN := (D.restrict N').orbitSkeleton_end_isLocalRing
    (k := k) hP hlocal hfreeN
  letI : MulAction (G ⧸ N') (DeckOrbitSkeleton C N') :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N'
  letI := D.deckOrbitResidualHasShift N'
  letI := D.deckOrbitResidualAdditiveShift N'
  letI := D.deckOrbitResidualLinearShift (k := k) N'
  let R := D.deckOrbitResidualCoherentDeckShift N'
  letI : ∀ a : Additive (G ⧸ N'), (R.core.F a).Additive := inferInstance
  letI : ∀ a : Additive (G ⧸ N'), (R.core.F a).Linear k := inferInstance
  let TT := D.deckOrbitTowerIndecomposableSkeleton (k := k) N' T
  let hPDirect := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hPTower := R.orbitSkeletonLinearCoyonedaFinite (k := k) hPN
  let hEnoughSource : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C N') k) :=
    enoughProjectives_of_finiteRepresentables hPN
  let hEnoughTarget : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N') (G ⧸ N')) k) :=
    enoughProjectives_of_finiteRepresentables hPTower
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C N') k) := hEnoughSource
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPDirect
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N') (G ⧸ N')) k) :=
    hEnoughTarget
  let hShiftFree :=
    D.finiteOrbitModuleIndecomposableSkeleton_residual_isShiftFreeOnLabels
      (k := k) hP hI hlocal hfree hrep N
  let hDensity := D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
    (k := k) hP hI hlocal hfree hrep
  let hCoverage :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_deckOrbitTowerCoverage
      (k := k) hDensity N' T
        (R.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
          (k := k) (D.deckOrbitResidualHasShift N')
          (D.deckOrbitResidualAdditiveShift N')
          (D.deckOrbitResidualLinearShift (k := k) N')
          (D.deckOrbitResidualCoherentDeckShift_hasShift_eq N').symm) rfl
  have hscale :=
    R.finiteDimensionalModuleOrbitSkeletonPushdown_sum_eq_card_mul_of_hasShift_eq
      (D.deckOrbitResidualHasShift N')
      (D.deckOrbitResidualAdditiveShift N')
      (D.deckOrbitResidualLinearShift (k := k) N')
      (D.deckOrbitResidualCoherentDeckShift_hasShift_eq N').symm
      hPN hIN hlocalN
      (D.deckOrbitResidual_isFreeOnIsomorphismClasses
        (k := k) hP hlocal N')
      S TT hEnoughSource hEnoughTarget hShiftFree hCoverage
  change
    @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.toFiniteRightTauCategoryData)
        S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      (Fintype.card (G ⧸ N') : ℤ) *
        @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _)
  rw [← S.sum_rightTauLocalDensity_eq_surplus,
    ← T.sum_rightTauLocalDensity_eq_surplus]
  calc
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
        (Fintype.card (G ⧸ N') : ℤ) *
          ∑ j : Fin TT.n, TT.rightTauLocalDensity j := hscale
    _ = (Fintype.card (G ⧸ N') : ℤ) *
          ∑ j : Fin T.n, T.rightTauLocalDensity j := by
      rw [D.sum_rightTauLocalDensity_eq_deckOrbitTower N' T TT]

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
