import MagnitudeConjecture.Algebra.StringProjectiveRadicalDecomposition
import MagnitudeConjecture.Algebra.StringQuotientSkeletal
import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleTauAssembly
import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauOneMiddle

/-!
# Incoming AR multiplicity at string projectives

The projective-boundary minimal right almost-split map has source the
Jacobson radical.  For a string presentation that radical has one
indecomposable uniserial summand for every displayed arrow ending at the
vertex.  Hence the incoming Auslander--Reiten arity at the corresponding
projective is the literal incoming-arrow count.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance quotientCategoryAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance quotientCategoryAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  exact IsNoetherianRing.of_finite k _

noncomputable local instance arCountQuotientFGHasFiniteBiproducts
    (P : StringPresentation k A Q) :
    HasFiniteBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

noncomputable local instance arCountQuotientFGHasBinaryBiproducts
    (P : StringPresentation k A Q) :
    HasBinaryBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- A represented canonical projective is nonzero, witnessed by its trivial
path basis vector. -/
theorem representedVertexModule_nontrivial
    (P : StringPresentation k A Q) (y : Q) :
    Nontrivial (P.representedVertexModule y) := by
  let b := P.representedVertexPathBasis y
  let p₀ := P.nilVertexPath y
  exact ⟨b p₀, 0, b.ne_zero p₀⟩

/-- A represented canonical projective is categorically projective. -/
theorem representedVertexModule_projective
    (P : StringPresentation k A Q) (y : Q) :
    Projective (P.representedVertexModule y) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let e := P.vertexRightIdealRepresentedLinearEquiv y
  have hProjector : IsIdempotentElem (P.vertexProjector y) := by
    rw [IsIdempotentElem, End.mul_def]
    simp [vertexProjector, Category.assoc]
  letI : Module.Projective P.quotientCategoryAlgebraᵐᵒᵖ
      (RightModule.rightIdeal (P.vertexProjector y)) :=
    RightModule.rightIdeal_moduleProjective hProjector
  have hModule : Module.Projective P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) :=
    Module.Projective.of_equiv' e
  exact fgProjective_of_moduleProjective
    (P.representedVertexModule y) hModule

/-- The ordinary module endomorphism ring of a represented canonical
projective is local. -/
theorem representedVertexModuleEnd_isLocalRing
    (P : StringPresentation k A Q) (y : Q) :
    IsLocalRing
      (Module.End P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y)) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let X := P.quotientRepresentable (obj P.toPresentation.relations y)
  let F := CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor hP
  letI : IsLocalRing (End X) :=
    CoveringHom.finiteDimensionalLinearCoyoneda_end_isLocalRing
      hP (fun Z ↦ P.quotientEnd_isLocalRing Z)
        (obj P.toPresentation.relations y)
  letI : IsLocalRing (End (F.obj X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (CategoryTheory.Functor.endRingEquivOfFullyFaithful F X)
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (RightModule.FiniteIndecomposableSkeleton.fgEndModuleEndRingEquiv
      (P.representedVertexModule y))

/-- A represented canonical projective is indecomposable. -/
theorem representedVertexModule_indecomposable
    (P : StringPresentation k A Q) (y : Q) :
    Indecomposable (P.representedVertexModule y) := by
  letI : IsLocalRing
      (Module.End P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y)) :=
    P.representedVertexModuleEnd_isLocalRing y
  letI : IsLocalRing (End (P.representedVertexModule y)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (RightModule.FiniteIndecomposableSkeleton.fgEndModuleEndRingEquiv
        (P.representedVertexModule y)).symm
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end
    (P.representedVertexModule y)

/-- The literal inclusion of the represented projective's radical. -/
def representedVertexRadicalInclusion
    (P : StringPresentation k A Q) (y : Q) :
    P.representedVertexRadicalFGObj y ⟶
      P.representedVertexModule y := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact fgModuleRadicalInclusion (P.representedVertexModule y)

/-- The radical inclusion at a represented string projective is right almost
split. -/
theorem representedVertexRadicalInclusion_isRightAlmostSplit
    (P : StringPresentation k A Q) (y : Q) :
    IsRightAlmostSplit (P.representedVertexRadicalInclusion y) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Nontrivial (P.representedVertexModule y) :=
    P.representedVertexModule_nontrivial y
  letI : IsLocalRing
      (Module.End P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y)) :=
    P.representedVertexModuleEnd_isLocalRing y
  exact fgModuleRadicalInclusion_isRightAlmostSplit
    (P.representedVertexModule y)
      (P.representedVertexModule_projective y)

/-- The radical inclusion at a represented string projective is right
minimal. -/
theorem representedVertexRadicalInclusion_isRightMinimal
    (P : StringPresentation k A Q) (y : Q) :
    IsRightMinimal (P.representedVertexRadicalInclusion y) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact fgModuleRadicalInclusion_isRightMinimal
    (P.representedVertexModule y)

private def representedVertexSkeletonIndex
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (y : Q) : Fin S.n :=
  Classical.choose
    (S.fgObj_complete (P.representedVertexModule y)
      (P.representedVertexModule_indecomposable y))

/-- The represented canonical projective is the chosen skeleton object at its
unique label. -/
def representedVertexSkeletonIso
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (y : Q) :
    P.representedVertexModule y ≅
      S.fgObj (P.representedVertexSkeletonIndex S y) :=
  Classical.choice
    (Classical.choose_spec
      (S.fgObj_complete (P.representedVertexModule y)
        (P.representedVertexModule_indecomposable y)))

/-- The unique indecomposable-projective label corresponding to a
displayed vertex. -/
def representedVertexProjectiveLabel
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (y : Q) : S.ProjectiveLabel where
  label := P.representedVertexSkeletonIndex S y
  projective := Projective.of_iso (P.representedVertexSkeletonIso S y)
    (P.representedVertexModule_projective y)

/-- An isomorphism between represented canonical projectives remembers the
displayed vertex. -/
theorem eq_of_representedVertexModule_iso
    (P : StringPresentation k A Q) {x y : Q}
    (eModule : P.representedVertexModule x ≅
      P.representedVertexModule y) :
    x = y := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let F := CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor hP
  let eRepresentable :
      P.quotientRepresentable (obj P.toPresentation.relations x) ≅
        P.quotientRepresentable (obj P.toPresentation.relations y) :=
    F.preimageIso eModule
  let J := CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP
  letI : J.Full := by
    dsimp [J, CoveringHom.finiteDimensionalLinearCoyonedaFunctor,
      CoveringHom.linearCoyonedaLinearModuleFunctor]
    infer_instance
  letI : J.Faithful := by
    dsimp [J, CoveringHom.finiteDimensionalLinearCoyonedaFunctor,
      CoveringHom.linearCoyonedaLinearModuleFunctor]
    infer_instance
  let eOpposite := J.preimageIso eRepresentable
  exact P.eq_of_quotientVertex_iso eOpposite.unop.symm

/-- Distinct displayed vertices have distinct projective labels. -/
theorem representedVertexProjectiveLabel_injective
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Function.Injective (P.representedVertexProjectiveLabel S) := by
  intro x y hxy
  have hlabel :
      (P.representedVertexProjectiveLabel S x).label =
        (P.representedVertexProjectiveLabel S y).label :=
    congrArg RightModule.FiniteIndecomposableSkeleton.ProjectiveLabel.label hxy
  let eModule : P.representedVertexModule x ≅
      P.representedVertexModule y :=
    (P.representedVertexSkeletonIso S x).trans
      ((eqToIso (congrArg S.fgObj hlabel)).trans
        (P.representedVertexSkeletonIso S y).symm)
  exact P.eq_of_representedVertexModule_iso eModule

/-- Every indecomposable projective label is represented by a displayed
vertex. -/
theorem representedVertexProjectiveLabel_surjective
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Function.Surjective (P.representedVertexProjectiveLabel S) := by
  intro p
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let hlocal : ∀ X : Category P.toPresentation.relations,
      IsLocalRing (End X) := fun X ↦ P.quotientEnd_isLocalRing X
  let E := CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence hP
  letI : E.functor.Additive :=
    CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor_additive hP
  letI : E.inverse.Additive := inferInstance
  let M := E.inverse.obj (S.fgObj p.label)
  have hMind : Indecomposable M :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse (S.fgObj p.label)).2 (S.fgObj_indecomposable p.label)
  letI : Projective M :=
    (E.symm.map_projective_iff (S.fgObj p.label)).2 p.projective
  obtain ⟨X, ⟨eX⟩⟩ :=
    CoveringHom.indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      hP hlocal M hMind
  let y := P.quotientObjectEquiv X
  let eObj : obj P.toPresentation.relations y ≅ X :=
    eqToIso (P.quotientObjectEquiv.symm_apply_apply X)
  let J := CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP
  let eRepresentable :
      P.quotientRepresentable (obj P.toPresentation.relations y) ≅ M :=
    (J.mapIso eObj.symm.op).trans eX
  let eTarget : P.representedVertexModule y ≅ S.fgObj p.label :=
    (E.functor.mapIso eRepresentable).trans
      (E.counitIso.app (S.fgObj p.label))
  have hlabel : (P.representedVertexProjectiveLabel S y).label = p.label :=
    S.fgObj_skeletal ⟨
      (P.representedVertexSkeletonIso S y).symm.trans eTarget⟩
  refine ⟨y, ?_⟩
  let q := P.representedVertexProjectiveLabel S y
  have hlabel' : q.label = p.label := hlabel
  change q = p
  rcases hq : q with ⟨j, hj⟩
  rcases hp : p with ⟨i, hi⟩
  rw [hq, hp] at hlabel'
  change j = i at hlabel'
  subst i
  rfl

/-- Displayed vertices are equivalent to the projective labels of any
duplicate-free module skeleton. -/
def representedVertexProjectiveEquiv
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Q ≃ S.ProjectiveLabel :=
  Equiv.ofBijective (P.representedVertexProjectiveLabel S)
    ⟨P.representedVertexProjectiveLabel_injective S,
      P.representedVertexProjectiveLabel_surjective S⟩

/-- The incoming AR arity at the projective represented by `y` is the
number of displayed quiver arrows ending at `y`. -/
theorem rightMiddleArity_representedVertexProjectiveLabel
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) (y : Q) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (P.representedVertexProjectiveLabel S y).label =
      Nat.card (DisplayedIncomingArrow y) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : HasFiniteBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasBinaryBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let p := P.representedVertexProjectiveLabel S y
  let e := P.representedVertexSkeletonIso S y
  let f := P.representedVertexRadicalInclusion y ≫ e.hom
  have hf : IsRightAlmostSplit f :=
    (P.representedVertexRadicalInclusion_isRightAlmostSplit y).postcomp_iso e
  have hfmin : IsRightMinimal f :=
    IsRightMinimal.postcomp_iso e
      (P.representedVertexRadicalInclusion_isRightMinimal y)
  have harity :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T p.label (P.representedVertexRadicalDecomposition y) hf hfmin
  simpa [T, p] using harity

/-- Incoming right-mesh arity is at most two at every projective string
module as well: the radical of its represented vertex projective has one
indecomposable summand for each displayed incoming arrow. -/
theorem rightMiddleArity_le_two_of_projective
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (i : Fin S.n) (hi : S.finiteTauCategoryData.IsProjective i) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2 := by
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory P.quotientCategoryAlgebra) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      P.quotientCategoryAlgebraᵐᵒᵖ
  let p : S.ProjectiveLabel := ⟨i,
    (FiniteTauMatrix.isProjective_iff_projective_obj
      S.finiteTauCategoryData.toFiniteRightTauCategoryData i).1 hi⟩
  obtain ⟨y, hy⟩ := P.representedVertexProjectiveLabel_surjective S p
  have hlabel : (P.representedVertexProjectiveLabel S y).label = i :=
    congrArg RightModule.FiniteIndecomposableSkeleton.ProjectiveLabel.label hy
  calc
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData i =
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData
          (P.representedVertexProjectiveLabel S y).label := by rw [hlabel]
    _ = Nat.card (DisplayedIncomingArrow y) :=
      P.rightMiddleArity_representedVertexProjectiveLabel S y
    _ ≤ 2 := P.arrows_ending_le_two y

/-- The literal type of all displayed arrows, grouped by their target
vertex. -/
abbrev DisplayedArrow (Q : Type u) [Quiver.{u} Q] :=
  Σ y : Q, DisplayedIncomingArrow y

/-- The manuscript's `ell`: the total incoming AR-arrow multiplicity at
indecomposable projective targets. -/
def projectiveTargetArrowCount
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) : ℕ :=
  ∑ p : S.ProjectiveLabel,
    FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p.label

/-- The generic finite-tau projective incoming count is the same sum as the
string-projective target count, merely indexed by the tau-projective subtype
instead of structured projective labels. -/
theorem projectiveIncomingArity_eq_projectiveTargetArrowCount
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    FiniteTauMatrix.projectiveIncomingArity S.finiteTauCategoryData =
      P.projectiveTargetArrowCount S := by
  classical
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory P.quotientCategoryAlgebra) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      P.quotientCategoryAlgebraᵐᵒᵖ
  let hprojective (i : Fin S.n) :
      T.IsProjective i ↔ Projective (S.fgObj i) :=
    FiniteTauMatrix.isProjective_iff_projective_obj T i
  let E : {i : Fin S.n // T.IsProjective i} ≃ S.ProjectiveLabel :=
    { toFun := fun i ↦ ⟨i.1, (hprojective i.1).1 i.2⟩
      invFun := fun p ↦ ⟨p.label, (hprojective p.label).2 p.projective⟩
      left_inv := fun i ↦ Subtype.ext rfl
      right_inv := by
        intro p
        rcases p with ⟨i, hi⟩
        rfl }
  have hsubtype :
      (∑ i : Fin S.n,
        if T.IsProjective i then
          FiniteTauMatrix.rightMiddleArity T i
        else 0) =
      ∑ i : {i : Fin S.n // T.IsProjective i},
        FiniteTauMatrix.rightMiddleArity T i.1 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      T.IsProjective
      (fun i : Fin S.n ↦
        if T.IsProjective i then
          FiniteTauMatrix.rightMiddleArity T i
        else 0)
    have hpositive :
        (∑ i : {i : Fin S.n // T.IsProjective i},
          if T.IsProjective i.1 then
            FiniteTauMatrix.rightMiddleArity T i.1
          else 0) =
          ∑ i : {i : Fin S.n // T.IsProjective i},
            FiniteTauMatrix.rightMiddleArity T i.1 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [if_pos i.2]
    have hcomplement :
        (∑ i : {i : Fin S.n // ¬ T.IsProjective i},
          if T.IsProjective i.1 then
            FiniteTauMatrix.rightMiddleArity T i.1
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg i.2]
    calc
      (∑ i : Fin S.n,
          if T.IsProjective i then
            FiniteTauMatrix.rightMiddleArity T i
          else 0) =
          (∑ i : {i : Fin S.n // T.IsProjective i},
            if T.IsProjective i.1 then
              FiniteTauMatrix.rightMiddleArity T i.1
            else 0) +
          ∑ i : {i : Fin S.n // ¬ T.IsProjective i},
            if T.IsProjective i.1 then
              FiniteTauMatrix.rightMiddleArity T i.1
            else 0 := hsplit.symm
      _ = ∑ i : {i : Fin S.n // T.IsProjective i},
          FiniteTauMatrix.rightMiddleArity T i.1 := by
        rw [hpositive, hcomplement, add_zero]
  rw [FiniteTauMatrix.projectiveIncomingArity, projectiveTargetArrowCount]
  rw [hsubtype]
  simpa [E] using E.sum_comp (fun p : S.ProjectiveLabel ↦
    FiniteTauMatrix.rightMiddleArity T p.label)

/-- For a string presentation, the number of AR arrows ending at projective
modules is the number of displayed quiver arrows. -/
theorem projectiveTargetArrowCount_eq_natCard_displayedArrow
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    P.projectiveTargetArrowCount S = Nat.card (DisplayedArrow Q) := by
  classical
  let E := P.representedVertexProjectiveEquiv S
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  rw [projectiveTargetArrowCount]
  calc
    (∑ p : S.ProjectiveLabel,
        FiniteTauMatrix.rightMiddleArity T p.label) =
        ∑ y : Q,
          FiniteTauMatrix.rightMiddleArity T (E y).label :=
      (E.sum_comp (fun p : S.ProjectiveLabel ↦
        FiniteTauMatrix.rightMiddleArity T p.label)).symm
    _ = ∑ y : Q, Nat.card (DisplayedIncomingArrow y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact P.rightMiddleArity_representedVertexProjectiveLabel S y
    _ = Nat.card (DisplayedArrow Q) := Nat.card_sigma.symm

noncomputable local instance stringTauProjectiveDecidablePred
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    DecidablePred S.finiteTauCategoryData.IsProjective :=
  Classical.decPred _

/-- Under the two-middle bound, the AR surplus of a representation-finite
string presentation is `E₁ - |Q₁|`.  This is the exact numerical reduction
used in the frozen manuscript before the Butler--Ringel bijection identifies
the two terms. -/
theorem surplus_eq_oneMiddleMeshCount_sub_natCard_displayedArrow
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (hbound : ∀ Y : Fin S.n,
      ¬ S.finiteTauCategoryData.IsProjective Y →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData Y ≤ 2) :
    ARCount.surplus
        (FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData)
        S.finiteTauCategoryData.IsProjective =
      (FiniteTauMatrix.oneMiddleMeshCount S.finiteTauCategoryData : ℤ) -
        Nat.card (DisplayedArrow Q) := by
  classical
  rw [FiniteTauMatrix.surplus_eq_oneMiddleMeshCount_sub_projectiveIncomingArity
      S.finiteTauCategoryData hbound,
    P.projectiveIncomingArity_eq_projectiveTargetArrowCount S,
    P.projectiveTargetArrowCount_eq_natCard_displayedArrow S]

end StringPresentation

end MagnitudeConjecture.BoundQuiver
