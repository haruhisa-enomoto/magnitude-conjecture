import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplus
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageEndpoints
import MagnitudeConjecture.CategoryTheory.StandardCoveringCategoryAlgebraDefs

/-!
# The category algebra of a finite standard covering quotient

The finite covering average is formulated intrinsically on the strict deck-
orbit category.  This file identifies its endpoint surpluses with the literal
right-module surpluses of the finite category algebra and of the primitive
quotient belonging to one orbit object.  This is the algebra-facing bridge
used by the manuscript's standard-deletion corollary.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.StandardCovering

open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.ObjectDeletion

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable {G : Type u} [Group G] [MulAction G C] [IsCancelSMul G C]

noncomputable instance orbitCategoryAlgebra_finiteDimensional
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    FiniteDimensional k (orbitCategoryAlgebra (k := k) D hP) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (orbitFiniteCovariantRepresentables (k := k) D hP)

noncomputable instance orbitCategoryAlgebra_opposite_isNoetherian
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    IsNoetherianRing (orbitCategoryAlgebra (k := k) D hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The orbit object downstairs represented by an upstairs object. -/
noncomputable abbrev orbitObject
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (x : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (Quotient.mk'' x : MulAction.orbitRel.Quotient G C)

/-- The canonical category-algebra idempotent belonging to one orbit
object. -/
noncomputable abbrev orbitCategoryProjector
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (x : C) : orbitCategoryAlgebra (k := k) D hP := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  exact finiteCategoryProjectiveGenerator.canonicalProjector
    (orbitFiniteCovariantRepresentables (k := k) D hP)
    (orbitObject (k := k) D x)

/-- The orbit-object projector is primitive. -/
theorem orbitCategoryProjectorPrimitive
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (x : C) :
    RightModule.PrimitiveIdempotentData
      (orbitCategoryProjector (k := k) D hP x) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hlocalDown :=
    D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal hfree
  exact finiteCategoryProjectiveGenerator.canonicalProjector_primitive
    hPdown hlocalDown (orbitObject (k := k) D x)

/-- The covering-average initial endpoint is the ambient surplus of every
complete right-module skeleton of the finite orbit-category algebra. -/
theorem finiteOrbitSurplus_eq_orbitCategoryAlgebra_ambientARSurplus
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k
      (orbitCategoryAlgebra (k := k) D hP)) :
    D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep =
      S.ambientARSurplus := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let T := D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep
  change
    @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      S.ambientARSurplus
  exact finiteCategoryProjectiveGenerator.categorySkeleton_surplus_eq_ambientARSurplus
    hPdown T S

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The covering-average terminal endpoint is the actual surplus of the
primitive quotient of the orbit-category algebra.  No directedness of the
downstairs algebra is used. -/
theorem fullOrbitDeletionFiniteOrbitSurplus_eq_primitiveQuotient_ambientARSurplus
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (Salg : RightModule.FiniteIndecomposableSkeleton k
      (orbitCategoryAlgebra (k := k) D hP))
    (x : C) :
    let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
    let P := orbitCategoryProjectorPrimitive
      (k := k) D hP hlocal hfree x
    letI : IsNoetherianRing
        (RightModule.primitiveQuotientAlgebra
          (orbitCategoryProjector (k := k) D hP x))ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    fullOrbitDeletionFiniteOrbitSurplus
        (k := k) D hC hP hI hlocal hrep x =
      (Salg.primitiveQuotientFiniteIndecomposableSkeleton P).ambientARSurplus := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let U := MulAction.orbit G x
  let hUG := fullOrbit_actionInvariant (G := G) x
  letI : ObjectProperty.IsClosedUnderIsomorphisms U :=
    isClosedUnderIsomorphisms_of_skeletal hC U
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D U hUG
  letI := rawHasShift (k := k) U hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C U) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) U hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C U) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) U hShift a
  letI := deletionHasShift (k := k) U hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C U) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) U hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C U) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) U hShift a
  letI := deletionMulAction (k := k) U hUG
  haveI : IsCancelSMul G (DeletionCategory (k := k) C U) :=
    deletionIsCancelSMul (k := k) U hUG
  let DG := CoherentDeckShift.deletionCoherentDeckShift (k := k) D U hUG
  let hDGHas : DG.hasShift = deletionHasShift (k := k) U hShift :=
    CoherentDeckShift.deletionCoherentDeckShift_hasShift_eq
      (k := k) D U hUG
  letI : ∀ a : Additive G, (DG.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D U hUG a
  letI : ∀ a : Additive G, (DG.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D U hUG a
  letI : Finite
      (MulAction.orbitRel.Quotient G
        (DeletionCategory (k := k) C U)) :=
    finite_deletionOrbitQuotient (k := k) C U hUG
  letI : Finite
      (DeckOrbitSkeleton (DeletionCategory (k := k) C U) G) := by
    change Finite
      (MulAction.orbitRel.Quotient G
        (DeletionCategory (k := k) C U))
    infer_instance
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  let hPdel := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP U X
  let hIdel := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI U X
  let hlocalDel := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal U X
  let hrepDel := isLocallyRepresentationFinite_deletion
    (k := k) C U hrep
  let hfreeDel := DG.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hPdel hlocalDel
  let hPfullDown := DG.orbitSkeletonLinearCoyonedaFinite (k := k) hPdel
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := DeckOrbitSkeleton (DeletionCategory (k := k) C U) G) k) :=
    enoughProjectives_of_finiteRepresentables hPfullDown
  let Full := DG.finiteOrbitModuleIndecomposableSkeleton_of_hasShift_eq
    (k := k) (deletionHasShift (k := k) U hShift)
      (fun a ↦ deletionShift_additive (k := k) U hShift a)
      (fun a ↦ deletionShift_linear (k := k) U hShift a)
      hDGHas.symm hPdel hIdel hlocalDel hfreeDel hrepDel
  let q : DeckOrbitSkeleton C G := orbitObject (k := k) D x
  let DownDeletion :=
    DeletionCategory (k := k) (DeckOrbitSkeleton C G) ({q} : Set _)
  let eDeck := deckOrbitDeletionCommEquivalence (k := k) D U hUG
  letI : eDeck.functor.Additive :=
    deckOrbitDeletionCommEquivalence_functor_additive
      (k := k) D U hUG
  letI : eDeck.functor.Linear k :=
    deckOrbitDeletionCommEquivalence_functor_linear
      (k := k) D U hUG
  let eEq : DeletionCategory (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) U) ≌ DownDeletion :=
    deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet_orbit (G := G) x)
  letI : eEq.functor.Additive := inferInstance
  letI : eEq.functor.Linear k := inferInstance
  let eBase :
      DeckOrbitSkeleton (DeletionCategory (k := k) C U) G ≌
        DownDeletion :=
    eDeck.trans eEq
  letI : eBase.functor.Additive := by
    change (eDeck.functor ⋙ eEq.functor).Additive
    infer_instance
  letI : eBase.functor.Linear k := by
    change (eDeck.functor ⋙ eEq.functor).Linear k
    infer_instance
  letI : Finite DownDeletion :=
    Finite.of_injective
      (fun X : DownDeletion ↦ X.obj.as)
      (fun X Y h ↦ by
        apply ObjectProperty.FullSubcategory.ext
        apply CategoryTheory.Quotient.ext
        exact h)
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hlocalDown :=
    D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal
      (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
        (k := k) hP hlocal)
  let hPdownDeletion := fun Y ↦
    deletion_linearCoyoneda_isFiniteDimensional
      (k := k) (DeckOrbitSkeleton C G) hPdown ({q} : Set _) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := DownDeletion) k) :=
    enoughProjectives_of_finiteRepresentables hPdownDeletion
  let eBaseSymm := eBase.symm
  letI : eBaseSymm.functor.Additive := by
    change eBase.inverse.Additive
    infer_instance
  letI : eBaseSymm.functor.Linear k := by
    change eBase.inverse.Linear k
    infer_instance
  let E := finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) eBaseSymm
  letI : E.functor.Additive :=
    finiteDimensionalModuleCongrEquivalenceOfFinite_functor_additive
      (k := k) eBaseSymm
  let Tdeleted := Full.mapEquivalence E
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let P := orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra
        (orbitCategoryProjector (k := k) D hP x))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  calc
    fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D hC hP hI hlocal hrep x =
        DG.finiteOrbitSurplus
          (k := k) hPdel hIdel hlocalDel hfreeDel hrepDel := by
      rfl
    _ = DG.finiteOrbitSurplus_of_hasShift_eq
          (k := k) (deletionHasShift (k := k) U hShift)
            (fun a ↦ deletionShift_additive (k := k) U hShift a)
            (fun a ↦ deletionShift_linear (k := k) U hShift a)
            hDGHas.symm hPdel hIdel hlocalDel hfreeDel hrepDel :=
      (DG.finiteOrbitSurplus_of_hasShift_eq_eq
        (k := k) (deletionHasShift (k := k) U hShift)
          (fun a ↦ deletionShift_additive (k := k) U hShift a)
          (fun a ↦ deletionShift_linear (k := k) U hShift a)
          hDGHas.symm hPdel hIdel hlocalDel hfreeDel hrepDel).symm
    _ = @ARCount.surplus (Fin Full.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            Full.toFiniteRightTauCategoryData)
          Full.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) :=
      DG.finiteOrbitSurplus_of_hasShift_eq_eq_skeleton
        (k := k) (deletionHasShift (k := k) U hShift)
          (fun a ↦ deletionShift_additive (k := k) U hShift a)
          (fun a ↦ deletionShift_linear (k := k) U hShift a)
          hDGHas.symm hPdel hIdel hlocalDel hfreeDel hrepDel
          (by infer_instance)
    _ = @ARCount.surplus (Fin Tdeleted.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            Tdeleted.toFiniteRightTauCategoryData)
          Tdeleted.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) :=
      (Full.surplus_mapEquivalence E).symm
    _ = (Salg.primitiveQuotientFiniteIndecomposableSkeleton P).ambientARSurplus :=
      finiteCategoryProjectiveGenerator.deletionCategorySkeleton_surplus_eq_primitiveQuotientFinite_ambientARSurplus
        hPdown hlocalDown Salg q Tdeleted

/-- Manuscript-facing primitive-deletion monotonicity for the category
algebra of an admissible residually finite covering. -/
theorem primitiveQuotient_ambientARSurplus_le_ambientARSurplus_of_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (Salg : RightModule.FiniteIndecomposableSkeleton k
      (orbitCategoryAlgebra
        (k := k) D H.locallyBounded.finiteCovariantRepresentables))
    (x : C) :
    let hP := H.locallyBounded.finiteCovariantRepresentables
    let hlocal := H.locallyBounded.localEndomorphismRings
    let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
    let P := orbitCategoryProjectorPrimitive
      (k := k) D hP hlocal hfree x
    letI : IsNoetherianRing
        (RightModule.primitiveQuotientAlgebra
          (orbitCategoryProjector (k := k) D hP x))ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    (Salg.primitiveQuotientFiniteIndecomposableSkeleton P).ambientARSurplus ≤
      Salg.ambientARSurplus := by
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hI := H.locallyBounded.finiteDualCorepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let hrep := H.locallyRepresentationFinite
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let P := orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra
        (orbitCategoryProjector (k := k) D hP x))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hInitial :=
    finiteOrbitSurplus_eq_orbitCategoryAlgebra_ambientARSurplus
      (k := k) D hP hI hlocal hfree hrep Salg
  have hTerminal :=
    fullOrbitDeletionFiniteOrbitSurplus_eq_primitiveQuotient_ambientARSurplus
      (k := k) D H.locallyBounded.skeletal hP hI hlocal hrep Salg x
  calc
    (Salg.primitiveQuotientFiniteIndecomposableSkeleton P).ambientARSurplus =
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D H.locallyBounded.skeletal hP hI hlocal hrep x :=
      hTerminal.symm
    _ ≤ D.finiteOrbitSurplus
          (k := k) hP hI hlocal hfree hrep :=
      fullOrbitDeletionFiniteOrbitSurplus_le_finiteOrbitSurplus_of_residuallyFinite_admissible
        (k := k) D H x
    _ = Salg.ambientARSurplus := hInitial

/-- Equality in the category-algebra primitive deletion forces the
manuscript's one-dimensional fibre conclusion on the universal cover. -/
theorem finrank_obj_eq_one_of_ambientARSurplus_eq_primitiveQuotient_of_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (Salg : RightModule.FiniteIndecomposableSkeleton k
      (orbitCategoryAlgebra
        (k := k) D H.locallyBounded.finiteCovariantRepresentables))
    (x : C)
    (hEquality :
      let hP := H.locallyBounded.finiteCovariantRepresentables
      let hlocal := H.locallyBounded.localEndomorphismRings
      let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
        (k := k) hP hlocal
      let P := orbitCategoryProjectorPrimitive
        (k := k) D hP hlocal hfree x
      letI : IsNoetherianRing
          (RightModule.primitiveQuotientAlgebra
            (orbitCategoryProjector (k := k) D hP x))ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      Salg.ambientARSurplus =
        (Salg.primitiveQuotientFiniteIndecomposableSkeleton P).ambientARSurplus)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hI := H.locallyBounded.finiteDualCorepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let hrep := H.locallyRepresentationFinite
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let P := orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra
        (orbitCategoryProjector (k := k) D hP x))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hInitial :=
    finiteOrbitSurplus_eq_orbitCategoryAlgebra_ambientARSurplus
      (k := k) D hP hI hlocal hfree hrep Salg
  have hTerminal :=
    fullOrbitDeletionFiniteOrbitSurplus_eq_primitiveQuotient_ambientARSurplus
      (k := k) D H.locallyBounded.skeletal hP hI hlocal hrep Salg x
  have hCoverEquality :
      D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep =
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D H.locallyBounded.skeletal hP hI hlocal hrep x :=
    hInitial.trans (hEquality.trans hTerminal.symm)
  exact
    finrank_obj_eq_one_of_finiteOrbitSurplus_eq_fullOrbitDeletion_of_residuallyFinite_admissible
      (k := k) D H x hCoverEquality M hM hMx

end MagnitudeConjecture.StandardCovering
