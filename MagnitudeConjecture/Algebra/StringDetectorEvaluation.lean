import MagnitudeConjecture.Algebra.StringDetectorTrajectory
import MagnitudeConjecture.Algebra.StringDetectorSelfEvaluation
import MagnitudeConjecture.Algebra.StringFiniteDetectorFunctor

/-!
# Evaluation of a detector-generated string summand

The coherent trajectory construction gives an objectwise module morphism
`S_C(F_C(N)) → N`.  This file begins the reconstruction argument by computing
the matching detector of that morphism.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

namespace Word

/-- The linear map from the ground field selecting one coefficient vector. -/
def coefficientPointMap (V : ModuleCat.{u} k) (v : V) :
    ModuleCat.of k k ⟶ V :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton k V v)

@[simp]
theorem coefficientPointMap_apply
    (V : ModuleCat.{u} k) (v : V) (c : k) :
    coefficientPointMap V v c = c • v :=
  rfl

/-- Insert one coefficient vector uniformly along a literal string module. -/
def coefficientRightModuleMap
    (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) (v : V) :
    C.rightModule hmono ⟶ C.scalarRightModule hmono V :=
  ((C.scalarRightLinearModuleUnitIso hmono).inv ≫
    (C.stringEmbeddingFunctor hmono).map (coefficientPointMap V v)).hom

@[simp]
theorem coefficientRightModuleMap_app_obj_apply
    (C : Word R) (hmono : IsMonomial R)
    (V : ModuleCat.{u} k) (v : V) (x : Q) (w : C.Space x) :
    (C.coefficientRightModuleMap hmono V v).app
        (Opposite.op (obj R x)) w = w ⊗ₜ[k] v := by
  change (ModuleCat.of k (C.Space x) ◁ coefficientPointMap V v)
      ((ρ_ (ModuleCat.of k (C.Space x))).inv w) = w ⊗ₜ[k] v
  rw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    coefficientPointMap_apply, one_smul]

end Word

namespace EndpointWord

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}
variable {u₀ : Q} {t : Bool}

/-- Detector maps respect composition, stated on individual detector
classes. -/
theorem detectorLinearMap_comp_apply
    {L M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : L ⟶ M) (g : M ⟶ N)
    (C : EndpointWord S u₀ t) (q : DetectorSpace L C) :
    detectorLinearMap (f ≫ g) C q =
      detectorLinearMap g C (detectorLinearMap f C q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ q => rfl

/-- The detector class in `F_C(S_C(F_C(N)))` obtained by inserting `q` into
the distinguished target class of the literal string module. -/
def coherentDetectorEvaluationSourceClass
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) (q : DetectorSpace N C) :
    DetectorSpace
      (C.word.scalarRightModule P.monomial
        (ModuleCat.of k (DetectorSpace N C))) C :=
  detectorLinearMap
    (C.word.coefficientRightModuleMap P.monomial
      (ModuleCat.of k (DetectorSpace N C)) q) C
    C.targetDetectorClass

/-- At the target position, coherent detector evaluation is the chosen
numerator representative of the detector class. -/
theorem coherentDetectorPositionMap_targetPosition
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) (q : DetectorSpace N C) :
    C.coherentDetectorPositionMap N C.word.targetPosition q =
      (detectorRepresentative N C q :
        N.obj (Opposite.op (obj P.toPresentation.relations u₀))) := by
  change C.word.coherentPositionMap N (upperBoundarySubspace N C)
      C.word.targetPosition (detectorUpperRepresentative N C q) = _
  rw [C.word.coherentPositionMap_targetPosition]
  rfl

/-- Inserting a detector class in the literal target basis and then applying
coherent evaluation recovers its chosen numerator representative. -/
theorem coefficientRightModuleMap_comp_coherentDetectorModuleMap_targetBasis
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t) (q : DetectorSpace N C) :
    (((C.word.coefficientRightModuleMap P.monomial
          (ModuleCat.of k (DetectorSpace N C)) q) ≫
        C.coherentDetectorModuleMap N P.monomial).app
          (Opposite.op (obj P.toPresentation.relations u₀)))
        (Finsupp.single C.word.targetPosition (1 : k)) =
      (detectorRepresentative N C q :
        N.obj (Opposite.op (obj P.toPresentation.relations u₀))) := by
  rw [NatTrans.comp_app, ModuleCat.comp_apply,
    C.word.coefficientRightModuleMap_app_obj_apply]
  change C.coherentDetectorTensorMap N u₀
      (Finsupp.single C.word.targetPosition (1 : k) ⊗ₜ[k] q) = _
  rw [C.coherentDetectorTensorMap_single_tmul, one_smul]
  exact C.coherentDetectorPositionMap_targetPosition N q

/-- The matching detector sends the composite from the literal string module
through the `q` coefficient line and coherent evaluation to `q` itself. -/
theorem detectorLinearMap_coefficientRightModuleMap_comp_evaluation
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t) (q : DetectorSpace N C) :
    detectorLinearMap
        (C.word.coefficientRightModuleMap P.monomial
            (ModuleCat.of k (DetectorSpace N C)) q ≫
          C.coherentDetectorModuleMap N P.monomial) C
        C.targetDetectorClass = q := by
  rw [show C.targetDetectorClass =
      Submodule.Quotient.mk C.targetNumeratorElement from rfl,
    detectorLinearMap_mk]
  have hnumerator :
      detectorNumeratorMap
          (C.word.coefficientRightModuleMap P.monomial
              (ModuleCat.of k (DetectorSpace N C)) q ≫
            C.coherentDetectorModuleMap N P.monomial) C
          C.targetNumeratorElement = detectorRepresentative N C q := by
    apply Subtype.ext
    exact C.coefficientRightModuleMap_comp_coherentDetectorModuleMap_targetBasis
      N q
  rw [hnumerator]
  exact LinearMap.congr_fun
    (detectorQuotientMap_comp_detectorRepresentative N C) q

/-- Applying the matching detector to coherent evaluation is onto.  The
explicit preimage of `q` is the distinguished literal target class with
coefficient `q`. -/
theorem detectorLinearMap_coherentDetectorModuleMap_sourceClass
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t) (q : DetectorSpace N C) :
    detectorLinearMap (C.coherentDetectorModuleMap N P.monomial) C
        (C.coherentDetectorEvaluationSourceClass N q) = q := by
  rw [coherentDetectorEvaluationSourceClass,
    ← detectorLinearMap_comp_apply
      (C.word.coefficientRightModuleMap P.monomial
        (ModuleCat.of k (DetectorSpace N C)) q)
      (C.coherentDetectorModuleMap N P.monomial) C C.targetDetectorClass]
  exact C.detectorLinearMap_coefficientRightModuleMap_comp_evaluation N q

theorem detectorLinearMap_coherentDetectorModuleMap_surjective
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] [N.Linear k]
    (C : EndpointWord S u₀ t) :
    Function.Surjective
      (detectorLinearMap (C.coherentDetectorModuleMap N P.monomial) C) := by
  intro q
  exact ⟨C.coherentDetectorEvaluationSourceClass N q,
    C.detectorLinearMap_coherentDetectorModuleMap_sourceClass N q⟩

/-- Coherent detector evaluation bundled in the finite-dimensional module
category. -/
def coherentFiniteDetectorEvaluation
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (C : EndpointWord S u₀ t) :
    (C.word.finiteStringEmbeddingFunctor P.monomial).obj
        (C.finiteDetectorFunctor.obj N) ⟶ N :=
  ⟨⟨C.coherentDetectorModuleMap N.obj.obj P.monomial⟩⟩

/-- The underlying linear map obtained by applying the matching finite
detector to coherent evaluation is the detector quotient map computed above. -/
theorem finiteDetectorFunctor_map_coherentFiniteDetectorEvaluation_hom
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (C : EndpointWord S u₀ t) :
    (C.finiteDetectorFunctor.map
        (C.coherentFiniteDetectorEvaluation N)).hom.hom =
      detectorLinearMap
        (C.coherentDetectorModuleMap N.obj.obj P.monomial) C :=
  rfl

/-- The matching finite detector sends coherent evaluation onto the original
detector coefficient space. -/
theorem finiteDetectorFunctor_map_coherentFiniteDetectorEvaluation_surjective
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (C : EndpointWord S u₀ t) :
    Function.Surjective
      (C.finiteDetectorFunctor.map
        (C.coherentFiniteDetectorEvaluation N)).hom.hom := by
  rw [C.finiteDetectorFunctor_map_coherentFiniteDetectorEvaluation_hom N]
  exact C.detectorLinearMap_coherentDetectorModuleMap_surjective N.obj.obj

end EndpointWord

namespace DetectorIndex

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

/-- Coherent evaluation for the chosen representative of one detector
inversion class. -/
def coherentFiniteDetectorEvaluation
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (i : DetectorIndex S) :
    i.finiteStringEmbeddingFunctor.obj (i.finiteDetectorFunctor.obj N) ⟶ N :=
  i.endpointWord.coherentFiniteDetectorEvaluation N

/-- The matching detector of coherent evaluation is an isomorphism.  Its
surjectivity is the explicit trajectory computation; injectivity follows
because `F_i S_i ≅ id` makes source and target finite-dimensional spaces have
the same dimension. -/
theorem isIso_finiteDetectorFunctor_map_coherentFiniteDetectorEvaluation
    (N : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category P.toPresentation.relations)ᵒᵖ) k)
    (i : DetectorIndex S) :
    IsIso (i.finiteDetectorFunctor.map
      (i.coherentFiniteDetectorEvaluation N)) := by
  let f := i.finiteDetectorFunctor.map
    (i.coherentFiniteDetectorEvaluation N)
  have hsurjective : Function.Surjective f.hom.hom :=
    i.endpointWord.finiteDetectorFunctor_map_coherentFiniteDetectorEvaluation_surjective N
  have hfinrank :
      Module.finrank k
          (((finiteDetectorEmbeddingFunctor i i).obj
            (i.finiteDetectorFunctor.obj N) : FGModuleCat.{u} k) : Type u) =
        Module.finrank k
          ((i.finiteDetectorFunctor.obj N : FGModuleCat.{u} k) : Type u) :=
    (FGModuleCat.isoToLinearEquiv
      ((finiteDetectorEmbeddingFunctorSelfIso i).app
        (i.finiteDetectorFunctor.obj N))).finrank_eq
  have hbijective : Function.Bijective f.hom.hom := ⟨
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).2
        hsurjective,
      hsurjective⟩
  let e := (LinearEquiv.ofBijective f.hom.hom hbijective).toFGModuleCatIso
  have heq : e.hom = f := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    rfl
  change IsIso f
  rw [← heq]
  infer_instance

end DetectorIndex

end MagnitudeConjecture.BoundQuiver.StringWord
