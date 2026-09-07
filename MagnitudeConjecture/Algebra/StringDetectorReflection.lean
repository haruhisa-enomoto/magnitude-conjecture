import MagnitudeConjecture.Algebra.StringDetectorReversal
import MagnitudeConjecture.Algebra.StringFiniteDetectorFunctor
import MagnitudeConjecture.Algebra.StringDetectorReconstruction
import MagnitudeConjecture.LinearAlgebra.FiniteFiltration

/-!
# Reflection from a finite string-detector filtration

At every displayed vertex, the two endpoint-word filtrations form a finite
lexicographic grid.  Its successive quotients are pair detectors; invalid
pairs vanish, while valid pairs are naturally ordinary string detectors.
Reversal invariance then shows that the finite inversion-class family detects
every layer.  The successive-quotient theorem makes every vertex component
bijective and hence reflects module isomorphisms.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization}

namespace EndpointWord

open MagnitudeConjecture.LinearAlgebra.FiniteFiltration

variable {M N :
  (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}

/-- The concrete ordered pair-grid filtration reflects bijectivity as soon as
every literal endpoint detector map is bijective. -/
theorem app_bijective_of_endpointDetectorLinearMap_bijective
    [Finite (DetectorIndex S)]
    {f : M ⟶ N} [M.Additive] [N.Additive]
    (hdetector : ∀ {x : Q} {t : Bool} (C : EndpointWord S x t),
      Function.Bijective (detectorLinearMap f C))
    (x : Q) :
    Function.Bijective
      (f.app (Opposite.op (obj P.toPresentation.relations x))).hom := by
  let FM := orderedGridFiltration
    (P := P) (S := S) (u₀ := x) (t := false) M
  let FN := orderedGridFiltration
    (P := P) (S := S) (u₀ := x) (t := false) N
  let hcompatible := orderedGridFiltration_compatible
    (P := P) (S := S) (u₀ := x) (t := false) f
  exact Filtration.map_bijective_of_gradedMap_bijective
    (f.app (Opposite.op (obj P.toPresentation.relations x))).hom
    FM FN hcompatible
    (orderedGridFiltration_gradedMap_bijective
      (P := P) (S := S) (u₀ := x) (t := false) f hdetector)

/-- Literal endpoint detectors jointly reflect isomorphisms through the
ordered pair-grid filtration. -/
theorem isIso_of_endpointDetectorLinearMap_bijective
    [Finite (DetectorIndex S)]
    {f : M ⟶ N} [M.Additive] [N.Additive]
    (hdetector : ∀ {x : Q} {t : Bool} (C : EndpointWord S x t),
      Function.Bijective (detectorLinearMap f C)) :
    IsIso f := by
  letI appIso (X : (Category P.toPresentation.relations)ᵒᵖ) :
      IsIso (f.app X) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.app X)).mpr
    change Function.Bijective
      (f.app (Opposite.op
        (obj P.toPresentation.relations X.unop.as))).hom
    exact app_bijective_of_endpointDetectorLinearMap_bijective
      hdetector X.unop.as
  exact NatIso.isIso_of_isIso_app f

/-- The chosen finite detector indices jointly reflect isomorphisms.  Reversal
invariance supplies every literal endpoint detector required by the grid. -/
theorem isIso_of_detectorIndexLinearMap_bijective
    [Finite (DetectorIndex S)]
    {f : M ⟶ N} [M.Additive] [N.Additive]
    (hdetector : ∀ i : DetectorIndex S,
      Function.Bijective (detectorLinearMap f i.endpointWord)) :
    IsIso f :=
  isIso_of_endpointDetectorLinearMap_bijective
    (fun C ↦ detectorLinearMap_bijective_of_detectorIndex f hdetector C)

end EndpointWord

namespace DetectorIndex

variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

/-- On finite-dimensional modules, the finite family of chosen string
detectors jointly reflects isomorphisms. -/
theorem isIso_of_finiteDetectorFunctor_map
    [Finite (DetectorIndex S)]
    {M N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k}
    (f : M ⟶ N)
    (hdetector : ∀ i : DetectorIndex S,
      IsIso (i.finiteDetectorFunctor.map f)) :
    IsIso f := by
  have hbijective (i : DetectorIndex S) :
      Function.Bijective
        (EndpointWord.detectorLinearMap f.hom.hom i.endpointWord) := by
    have hi := hdetector i
    have hiHom : IsIso (i.finiteDetectorFunctor.map f).hom :=
      (ObjectProperty.isIso_hom_iff
        (i.finiteDetectorFunctor.map f)).mpr hi
    exact (ConcreteCategory.isIso_iff_bijective
      (i.finiteDetectorFunctor.map f).hom).mp hiHom
  have hraw : IsIso f.hom.hom :=
    EndpointWord.isIso_of_detectorIndexLinearMap_bijective hbijective
  letI : IsIso f.hom.hom := hraw
  letI : IsIso f.hom :=
    (ObjectProperty.isIso_hom_iff f.hom).mp inferInstance
  exact (ObjectProperty.isIso_hom_iff f).mp inferInstance

/-- Every finite-dimensional module over a representation-finite string
algebra is isomorphic to the finite direct sum reconstructed from all of its
string detectors. -/
theorem isIso_reconstructionEvaluation
    [Fintype (DetectorIndex S)]
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k) :
    IsIso (reconstructionEvaluation (S := S) N) := by
  let f := reconstructionEvaluation (S := S) N
  exact isIso_of_finiteDetectorFunctor_map f
    (fun i ↦
      isIso_finiteDetectorFunctor_map_reconstructionEvaluation
        (S := S) N i)

end DetectorIndex

end MagnitudeConjecture.BoundQuiver.StringWord
