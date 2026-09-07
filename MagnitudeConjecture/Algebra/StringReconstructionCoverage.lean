import MagnitudeConjecture.Algebra.StringDetectorReflection
import MagnitudeConjecture.Algebra.StringHookCohookFiniteIrreducible

/-!
# Finite string-sum coverage from string detectors

The finite detector reconstruction writes every finite-dimensional module as
a biproduct of coefficient-valued literal string modules.  A finite
coefficient space is a biproduct of copies of the ground field, so the
reconstruction flattens to a finite biproduct of literal string modules.

This is the direct object-coverage input for hook and cohook irreducibility;
it does not pass through a separate string-or-band classification theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

namespace DetectorIndex

variable [Fintype (DetectorIndex S)]

/-- The multiplicity with which the detector representative `i` occurs in
the reconstruction of `N`. -/
def reconstructionMultiplicity
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (i : DetectorIndex S) : ℕ :=
  Module.finrank k (i.finiteDetectorFunctor.obj N)

/-- One label for each literal string copy occurring in the detector
reconstruction. -/
abbrev ReconstructionCopyIndex
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :=
  Σ i : DetectorIndex S, Fin (reconstructionMultiplicity N i)

/-- A numerical enumeration of all literal string copies in the detector
reconstruction. -/
def reconstructionCopyEquiv
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :
    Fin (Fintype.card (ReconstructionCopyIndex (S := S) N)) ≃
      ReconstructionCopyIndex (S := S) N :=
  (Fintype.equivFin (ReconstructionCopyIndex (S := S) N)).symm

/-- The literal word carried by a numerical reconstruction-copy label. -/
def reconstructionWord
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (j : Fin (Fintype.card (ReconstructionCopyIndex (S := S) N))) :
    Word P.toPresentation.relations :=
  (reconstructionCopyEquiv (S := S) N j).1.endpointWord.word

/-- A coefficient-valued reconstruction summand is a finite biproduct of
copies of its literal string module. -/
def reconstructionSummandIsoBiproduct
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (i : DetectorIndex S) :
    reconstructionSummand (S := S) N i ≅
      ⨁ fun _ : Fin (reconstructionMultiplicity N i) ↦
        i.endpointWord.word.finiteRightModule P.monomial := by
  let V := i.finiteDetectorFunctor.obj N
  let copies := fun _ : Fin (Module.finrank k V) ↦ FGModuleCat.of k k
  exact
    i.finiteStringEmbeddingFunctor.mapIso
        (MagnitudeConjecture.FiniteVectorSpace.isoBiproductUnit V) ≪≫
      i.finiteStringEmbeddingFunctor.mapBiproduct copies ≪≫
      biproduct.mapIso (fun _ ↦
        i.endpointWord.word.scalarFiniteRightModuleUnitIso P.monomial)

/-- The complete reconstruction source is a single finite biproduct of
literal string modules, with nested detector/coefficient indices flattened
and enumerated by a `Fin` type. -/
def reconstructionSourceIsoFiniteStringBiproduct
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :
    reconstructionSource (S := S) N ≅
      ⨁ fun j : Fin (Fintype.card (ReconstructionCopyIndex (S := S) N)) ↦
        (reconstructionWord (S := S) N j).finiteRightModule P.monomial := by
  let I := fun i : DetectorIndex S ↦ Fin (reconstructionMultiplicity N i)
  let G := fun (i : DetectorIndex S) (_ : I i) ↦
    i.endpointWord.word.finiteRightModule P.monomial
  let flat : (Σ i, I i) →
      MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k :=
    fun p ↦ G p.1 p.2
  let e : Fin (Fintype.card (Σ i, I i)) ≃ (Σ i, I i) :=
    (Fintype.equivFin (Σ i, I i)).symm
  let flattened : reconstructionSource (S := S) N ≅
      ⨁ fun j ↦ flat (e j) :=
      biproduct.mapIso (fun i ↦
        reconstructionSummandIsoBiproduct (S := S) N i) ≪≫
      biproductBiproductIso I G ≪≫
      (biproduct.whiskerEquiv e
        (fun j ↦ Iso.refl (flat (e j)))).symm
  simpa [I, G, flat, e, reconstructionWord, reconstructionCopyEquiv,
    ReconstructionCopyIndex] using flattened

/-- The detector reconstruction identifies a finite-dimensional module
itself with a finite biproduct of literal string modules. -/
def reconstructionIsoFiniteStringBiproduct
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)]
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :
    N ≅
      ⨁ fun j : Fin (Fintype.card (ReconstructionCopyIndex (S := S) N)) ↦
        (reconstructionWord (S := S) N j).finiteRightModule P.monomial := by
  letI : IsIso (reconstructionEvaluation (S := S) N) :=
    isIso_reconstructionEvaluation (S := S) N
  exact
    (asIso (reconstructionEvaluation (S := S) N)).symm ≪≫
      reconstructionSourceIsoFiniteStringBiproduct (S := S) N

/-- Every finite-dimensional module is a finite biproduct of literal string
modules.  This follows directly from the detector reconstruction theorem. -/
theorem everyFiniteModuleIsFiniteStringSum
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)] :
    Word.EveryFiniteModuleIsFiniteStringSum P.monomial := by
  intro N
  let n := Fintype.card (ReconstructionCopyIndex (S := S) N)
  let M : Fin n → Word P.toPresentation.relations :=
    reconstructionWord (S := S) N
  let eFinite : N ≅ ⨁ fun j : Fin n ↦
      (M j).finiteRightModule P.monomial :=
    reconstructionIsoFiniteStringBiproduct S N
  let J : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k ⥤
      ((Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k) :=
    (MagnitudeConjecture.CoveringHom.IsFiniteDimensionalModule
        (C := (Category P.toPresentation.relations)ᵒᵖ) k).ι ⋙
      (MagnitudeConjecture.CoveringHom.IsLinearModule
        (C := (Category P.toPresentation.relations)ᵒᵖ) k).ι
  letI : PreservesBiproduct
      (fun j : Fin n ↦ (M j).finiteRightModule P.monomial) J :=
    preservesBiproduct_of_preservesProduct J
  refine ⟨n, M, ⟨?_⟩⟩
  exact J.mapIso eFinite ≪≫
    J.mapBiproduct (fun j : Fin n ↦
      (M j).finiteRightModule P.monomial)

end DetectorIndex

namespace Word

/-- The canonical right-hook projection is irreducible once the finite
detector family exists. -/
theorem HookExtension.finiteModuleMap_isIrreducible
    {C D : Word P.toPresentation.relations} (hook : HookExtension C D)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)] :
    IsIrreducibleMorphism (hook.finiteModuleMap P.monomial) :=
  hook.finiteModuleMap_isIrreducible_of_finiteStringSum P.monomial
    (DetectorIndex.everyFiniteModuleIsFiniteStringSum S)

/-- The canonical right-cohook inclusion is irreducible once the finite
detector family exists. -/
theorem CohookExtension.finiteModuleMap_isIrreducible
    {C D : Word P.toPresentation.relations} (cohook : CohookExtension C D)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)] :
    IsIrreducibleMorphism (cohook.finiteModuleMap P.monomial) :=
  cohook.finiteModuleMap_isIrreducible_of_finiteStringSum P.monomial
    (DetectorIndex.everyFiniteModuleIsFiniteStringSum S)

/-- The canonical left-hook projection is irreducible once the finite
detector family exists. -/
theorem LeftHookExtension.finiteModuleMap_isIrreducible
    {C : Word P.toPresentation.relations} (hook : LeftHookExtension C)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)] :
    IsIrreducibleMorphism (hook.finiteModuleMap P.monomial) :=
  hook.finiteModuleMap_isIrreducible_of_finiteStringSum P.monomial
    (DetectorIndex.everyFiniteModuleIsFiniteStringSum S)

/-- The canonical left-cohook inclusion is irreducible once the finite
detector family exists. -/
theorem LeftCohookExtension.finiteModuleMap_isIrreducible
    {C : Word P.toPresentation.relations} (cohook : LeftCohookExtension C)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    [Fintype (DetectorIndex S)] :
    IsIrreducibleMorphism (cohook.finiteModuleMap P.monomial) :=
  cohook.finiteModuleMap_isIrreducible_of_finiteStringSum P.monomial
    (DetectorIndex.everyFiniteModuleIsFiniteStringSum S)

/-- A finite complete indecomposable skeleton makes the right-hook
projection irreducible, with detector finiteness discharged internally. -/
theorem HookExtension.finiteModuleMap_isIrreducible_of_finiteIndecomposableSkeleton
    {C D : Word P.toPresentation.relations} (hook : HookExtension C D)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : DetectorIndex.FiniteIndecomposableSkeleton (P := P)) :
    IsIrreducibleMorphism (hook.finiteModuleMap P.monomial) := by
  letI : Finite (DetectorIndex S) :=
    DetectorIndex.finite_of_finiteIndecomposableSkeleton T
  letI : Fintype (DetectorIndex S) := Fintype.ofFinite _
  exact hook.finiteModuleMap_isIrreducible S

/-- A finite complete indecomposable skeleton makes the right-cohook
inclusion irreducible, with detector finiteness discharged internally. -/
theorem CohookExtension.finiteModuleMap_isIrreducible_of_finiteIndecomposableSkeleton
    {C D : Word P.toPresentation.relations} (cohook : CohookExtension C D)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : DetectorIndex.FiniteIndecomposableSkeleton (P := P)) :
    IsIrreducibleMorphism (cohook.finiteModuleMap P.monomial) := by
  letI : Finite (DetectorIndex S) :=
    DetectorIndex.finite_of_finiteIndecomposableSkeleton T
  letI : Fintype (DetectorIndex S) := Fintype.ofFinite _
  exact cohook.finiteModuleMap_isIrreducible S

/-- A finite complete indecomposable skeleton makes the left-hook projection
irreducible, with detector finiteness discharged internally. -/
theorem LeftHookExtension.finiteModuleMap_isIrreducible_of_finiteIndecomposableSkeleton
    {C : Word P.toPresentation.relations} (hook : LeftHookExtension C)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : DetectorIndex.FiniteIndecomposableSkeleton (P := P)) :
    IsIrreducibleMorphism (hook.finiteModuleMap P.monomial) := by
  letI : Finite (DetectorIndex S) :=
    DetectorIndex.finite_of_finiteIndecomposableSkeleton T
  letI : Fintype (DetectorIndex S) := Fintype.ofFinite _
  exact hook.finiteModuleMap_isIrreducible S

/-- A finite complete indecomposable skeleton makes the left-cohook inclusion
irreducible, with detector finiteness discharged internally. -/
theorem LeftCohookExtension.finiteModuleMap_isIrreducible_of_finiteIndecomposableSkeleton
    {C : Word P.toPresentation.relations} (cohook : LeftCohookExtension C)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : DetectorIndex.FiniteIndecomposableSkeleton (P := P)) :
    IsIrreducibleMorphism (cohook.finiteModuleMap P.monomial) := by
  letI : Finite (DetectorIndex S) :=
    DetectorIndex.finite_of_finiteIndecomposableSkeleton T
  letI : Fintype (DetectorIndex S) := Fintype.ofFinite _
  exact cohook.finiteModuleMap_isIrreducible S

end Word

end MagnitudeConjecture.BoundQuiver.StringWord
