import MagnitudeConjecture.Algebra.StringDetectorOffDiagonal
import MagnitudeConjecture.Algebra.StringEmbeddingFunctor
import MagnitudeConjecture.CategoryTheory.FGModuleCatLinearFunctor

/-!
# Finite-dimensional string detector and embedding functors

This file restricts Butler--Ringel's finite-string functors to the categories
used by finite reconstruction.  A detector of a finite-dimensional
module is finite-dimensional, and a finite coefficient space copied along a
finite string again gives a finite-dimensional module.

For the chosen representatives of inversion classes, the coordinate
calculation gives the natural finite-string orthogonality identities

`F_i S_i ≅ id` and `F_i S_j ≅ 0` for `i ≠ j`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace EndpointWord

variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- A detector of a finite-dimensional module is a finite-dimensional vector
space. -/
theorem detectorSpace_finiteDimensional
    (C : EndpointWord S u₀ t)
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :
    FiniteDimensional k (DetectorSpace N.obj.obj C) := by
  infer_instance

/-- The detector restricted to finite-dimensional modules and bundled with a
finite-dimensional target. -/
def finiteDetectorFunctor (C : EndpointWord S u₀ t) :
    MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k ⥤
      FGModuleCat.{u} k where
  obj N := ⟨C.detectorFunctor.obj N.obj,
    C.detectorSpace_finiteDimensional N⟩
  map {M N} f := ⟨C.detectorFunctor.map f.hom⟩
  map_id N := by
    apply ObjectProperty.hom_ext
    exact C.detectorFunctor.map_id N.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact C.detectorFunctor.map_comp f.hom g.hom

instance finiteDetectorFunctor_additive (C : EndpointWord S u₀ t) :
    C.finiteDetectorFunctor.Additive where
  map_add {M N} f g := by
    apply ObjectProperty.hom_ext
    exact Functor.map_add C.detectorFunctor
      (f := f.hom) (g := g.hom)

instance finiteDetectorFunctor_linear (C : EndpointWord S u₀ t) :
    C.finiteDetectorFunctor.Linear k where
  map_smul {M N} f r := by
    apply ObjectProperty.hom_ext
    exact Functor.map_smul C.detectorFunctor r f.hom

@[simp]
theorem finiteDetectorFunctor_obj_carrier
    (C : EndpointWord S u₀ t)
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :
    ((C.finiteDetectorFunctor.obj N : FGModuleCat.{u} k) : Type u) =
      DetectorSpace N.obj.obj C :=
  rfl

end EndpointWord

namespace DetectorIndex

variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

local instance : DecidableEq (DetectorIndex S) := Classical.decEq _

/-- The finite detector attached to a chosen inversion-class index. -/
def finiteDetectorFunctor (i : DetectorIndex S) :
    MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k ⥤
      FGModuleCat.{u} k :=
  i.endpointWord.finiteDetectorFunctor

/-- The finite string embedding attached to the chosen representative of an
inversion class. -/
def finiteStringEmbeddingFunctor (i : DetectorIndex S) :
    FGModuleCat.{u} k ⥤
      MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k :=
  i.endpointWord.word.finiteStringEmbeddingFunctor P.monomial

instance finiteStringEmbeddingFunctor_additive (i : DetectorIndex S) :
    i.finiteStringEmbeddingFunctor.Additive := by
  unfold finiteStringEmbeddingFunctor
  infer_instance

instance finiteStringEmbeddingFunctor_linear (i : DetectorIndex S) :
    i.finiteStringEmbeddingFunctor.Linear k := by
  unfold finiteStringEmbeddingFunctor
  infer_instance

instance finiteDetectorFunctor_additive (i : DetectorIndex S) :
    i.finiteDetectorFunctor.Additive := by
  unfold finiteDetectorFunctor
  infer_instance

instance finiteDetectorFunctor_linear (i : DetectorIndex S) :
    i.finiteDetectorFunctor.Linear k := by
  unfold finiteDetectorFunctor
  infer_instance

/-- The composite `F_i S_j` on finite-dimensional coefficient spaces. -/
def finiteDetectorEmbeddingFunctor (i j : DetectorIndex S) :
    FGModuleCat.{u} k ⥤ FGModuleCat.{u} k :=
  j.finiteStringEmbeddingFunctor ⋙ i.finiteDetectorFunctor

instance finiteDetectorEmbeddingFunctor_additive
    (i j : DetectorIndex S) :
    (finiteDetectorEmbeddingFunctor i j).Additive := by
  unfold finiteDetectorEmbeddingFunctor
  infer_instance

instance finiteDetectorEmbeddingFunctor_linear
    (i j : DetectorIndex S) :
    (finiteDetectorEmbeddingFunctor i j).Linear k := by
  unfold finiteDetectorEmbeddingFunctor
  infer_instance

/-- The finite detector and embedding functors satisfy the finite-string part
of Butler--Ringel's orthogonality formula on the one-dimensional coefficient
space. -/
theorem finrank_finiteDetectorFunctor_finiteStringEmbeddingFunctor_unit
    (i j : DetectorIndex S) :
    Module.finrank k
        ((i.finiteDetectorFunctor.obj
          (j.finiteStringEmbeddingFunctor.obj (FGModuleCat.of k k)) :
            FGModuleCat.{u} k) : Type u) =
      if i = j then 1 else 0 := by
  let eModule :=
    j.endpointWord.word.scalarFiniteRightModuleUnitIso P.monomial
  let eDetector := i.finiteDetectorFunctor.mapIso eModule
  exact (FGModuleCat.isoToLinearEquiv eDetector).finrank_eq.trans
    (finrank_detectorSpace_rightModule_endpointWord i j)

/-- The full finite-string orthogonality formula: on every finite coefficient
space `V`, `F_i S_j(V)` has dimension `dim V` on the matching inversion class
and dimension zero off that class. -/
theorem finrank_finiteDetectorEmbeddingFunctor
    (i j : DetectorIndex S) (V : FGModuleCat.{u} k) :
    Module.finrank k ((finiteDetectorEmbeddingFunctor i j).obj V) =
      if i = j then Module.finrank k V else 0 := by
  rw [MagnitudeConjecture.FiniteVectorSpace.finrank_map_eq_mul]
  change Module.finrank k V *
      Module.finrank k
        (i.finiteDetectorFunctor.obj
          (j.finiteStringEmbeddingFunctor.obj (FGModuleCat.of k k))) = _
  rw [finrank_finiteDetectorFunctor_finiteStringEmbeddingFunctor_unit]
  by_cases hij : i = j <;> simp [hij]

/-- The diagonal detector-embedding composite on the ground field is
canonically one-dimensional, with coordinate given by the target position of
the literal string. -/
def finiteDetectorEmbeddingFunctorUnitIso (i : DetectorIndex S) :
    (finiteDetectorEmbeddingFunctor i i).obj (FGModuleCat.of k k) ≅
      FGModuleCat.of k k := by
  letI : FiniteDimensional k
      (EndpointWord.DetectorSpace
        (i.endpointWord.word.rightModule P.monomial) i.endpointWord) :=
    i.endpointWord.detectorSpace_finiteDimensional
      (i.endpointWord.word.finiteRightModule P.monomial)
  exact
    i.finiteDetectorFunctor.mapIso
        (i.endpointWord.word.scalarFiniteRightModuleUnitIso P.monomial) ≪≫
      i.endpointWord.detectorTargetEquiv.toFGModuleCatIso

/-- Butler--Ringel's diagonal identity as a natural isomorphism:
`F_i S_i ≅ id` on finite-dimensional coefficient spaces. -/
def finiteDetectorEmbeddingFunctorSelfIso (i : DetectorIndex S) :
    finiteDetectorEmbeddingFunctor i i ≅ 𝟭 (FGModuleCat.{u} k) :=
  (MagnitudeConjecture.FiniteVectorSpace.functorEvaluationNatIso
      (finiteDetectorEmbeddingFunctor i i)).symm ≪≫
    (MonoidalCategory.tensoringLeft (FGModuleCat.{u} k)).mapIso
      (finiteDetectorEmbeddingFunctorUnitIso i) ≪≫
    MonoidalCategory.leftUnitorNatIso (FGModuleCat.{u} k)

/-- Off the diagonal, `F_i S_j(V)` is the zero vector space. -/
theorem finiteDetectorEmbeddingFunctor_subsingleton_of_ne
    {i j : DetectorIndex S} (hij : i ≠ j) (V : FGModuleCat.{u} k) :
    Subsingleton ((finiteDetectorEmbeddingFunctor i j).obj V) := by
  apply (Module.finrank_zero_iff
    (R := k)
    (M := ((finiteDetectorEmbeddingFunctor i j).obj V : Type u))).mp
  simpa [hij] using finrank_finiteDetectorEmbeddingFunctor i j V

/-- Off the diagonal, the detector-embedding composite is naturally the zero
functor. -/
def finiteDetectorEmbeddingFunctorZeroIsoOfNe
    {i j : DetectorIndex S} (hij : i ≠ j) :
    finiteDetectorEmbeddingFunctor i j ≅
      (Functor.const (FGModuleCat.{u} k)).obj
        (FGModuleCat.of k PUnit.{u + 1}) :=
  NatIso.ofComponents
    (fun V ↦
      { hom := 0
        inv := 0
        hom_inv_id := by
          letI : Subsingleton
              ((finiteDetectorEmbeddingFunctor i j).obj V : Type u) :=
            finiteDetectorEmbeddingFunctor_subsingleton_of_ne hij V
          apply ObjectProperty.hom_ext
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact Subsingleton.elim _ _
        inv_hom_id := by
          letI : Subsingleton
              (((Functor.const (FGModuleCat.{u} k)).obj
                (FGModuleCat.of k PUnit.{u + 1})).obj V : Type u) := by
            change Subsingleton PUnit.{u + 1}
            infer_instance
          apply ObjectProperty.hom_ext
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact Subsingleton.elim _ _ })
    (fun {V W} f ↦ by
      letI : Subsingleton
          (((Functor.const (FGModuleCat.{u} k)).obj
            (FGModuleCat.of k PUnit.{u + 1})).obj W : Type u) := by
        change Subsingleton PUnit.{u + 1}
        infer_instance
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _)

end DetectorIndex

end MagnitudeConjecture.BoundQuiver.StringWord
