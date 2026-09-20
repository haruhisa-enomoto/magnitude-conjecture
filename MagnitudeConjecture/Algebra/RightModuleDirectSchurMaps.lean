import MagnitudeConjecture.Algebra.RightModuleDirectPosetGrading

/-! # Maps between the selected representatives of Schur poset spaces -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData

/-- Transport a poset-space map to the selected factor representatives. -/
def directFactorSchurMap
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    {X Y : PosetSpace.Obj k B.ProjectivePoset}
    (hX : PosetSpace.IsSchur k B.ProjectivePoset X)
    (hY : PosetSpace.IsSchur k B.ProjectivePoset Y) (f : X ⟶ Y) :
    S.factorObject (S.primitiveKilledLabels D) (B.directFactorSchurLabel X hX) ⟶
      S.factorObject (S.primitiveKilledLabels D) (B.directFactorSchurLabel Y hY) :=
  (B.directFactorSchurIso X hX).inv ≫ B.directPosetSpaceEquivalence.inverse.map f ≫
    (B.directFactorSchurIso Y hY).hom

/-- Composition of maps survives the choice of representatives. -/
theorem directFactorSchurMap_comp
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    {X Y Z : PosetSpace.Obj k B.ProjectivePoset}
    (hX : PosetSpace.IsSchur k B.ProjectivePoset X)
    (hY : PosetSpace.IsSchur k B.ProjectivePoset Y)
    (hZ : PosetSpace.IsSchur k B.ProjectivePoset Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    B.directFactorSchurMap hX hZ (f ≫ g) =
      B.directFactorSchurMap hX hY f ≫ B.directFactorSchurMap hY hZ g := by
  simp [directFactorSchurMap, Functor.map_comp]

/-- Nonzero maps remain nonzero after transport. -/
theorem directFactorSchurMap_ne_zero
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    {X Y : PosetSpace.Obj k B.ProjectivePoset}
    (hX : PosetSpace.IsSchur k B.ProjectivePoset X)
    (hY : PosetSpace.IsSchur k B.ProjectivePoset Y) (f : X ⟶ Y) (hf : f ≠ 0) :
    B.directFactorSchurMap hX hY f ≠ 0 := by
  let E := B.directPosetSpaceEquivalence
  letI : E.functor.Linear k := by
    change B.projectivePosetData.representableData.functor.Linear k
    infer_instance
  letI : E.inverse.Linear k := E.inverseLinear k
  intro hz
  have hmap : E.inverse.map f = 0 := by
    have h := congrArg (fun g ↦ (B.directFactorSchurIso X hX).hom ≫ g ≫
      (B.directFactorSchurIso Y hY).inv) hz
    simpa [directFactorSchurMap] using h
  apply hf
  apply E.inverse.map_injective
  simpa using hmap

/-- Nonisomorphic Schur spaces have distinct selected factor labels. -/
theorem directFactorSchurLabel_ne_of_not_iso
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    {X Y : PosetSpace.Obj k B.ProjectivePoset}
    (hX : PosetSpace.IsSchur k B.ProjectivePoset X)
    (hY : PosetSpace.IsSchur k B.ProjectivePoset Y) (hne : ¬ Nonempty (X ≅ Y)) :
    B.directFactorSchurLabel X hX ≠ B.directFactorSchurLabel Y hY := by
  intro heq
  let E := B.directPosetSpaceEquivalence
  let ep : E.inverse.obj X ≅ E.inverse.obj Y :=
    (B.directFactorSchurIso X hX).trans
      ((eqToIso (congrArg (S.factorObject (S.primitiveKilledLabels D)) heq)).trans
        (B.directFactorSchurIso Y hY).symm)
  apply hne
  exact ⟨(E.counitIso.app X).symm.trans ((E.functor.mapIso ep).trans (E.counitIso.app Y))⟩

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
