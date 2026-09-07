import MagnitudeConjecture.Algebra.SpecialBiserialSoclePairingEssentiality
import MagnitudeConjecture.Algebra.UniserialModule
import MagnitudeConjecture.Algebra.RightModuleInjectiveSocle
import MagnitudeConjecture.Algebra.StringProjectiveARCount
import MagnitudeConjecture.Algebra.StringArrowCokernelBranch
import MagnitudeConjecture.Algebra.RightModuleIdealQuotientSkeleton
import MagnitudeConjecture.CategoryTheory.UniserialObject

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

private abbrev quotientRepresentable
    (P : SpecialBiserialPresentation k A Q)
    (X : Category P.toPresentation.relations) :=
  (CoveringHom.finiteDimensionalLinearCoyonedaFunctor
      (finiteRepresentablesOfAdmissible P.toPresentation.admissible)).obj
    (Opposite.op X)

private abbrev quotientCategoryAlgebra
    (P : SpecialBiserialPresentation k A Q) :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    (finiteRepresentablesOfAdmissible P.toPresentation.admissible)

private abbrev representedVertexModule
    (P : SpecialBiserialPresentation k A Q) (z : Q) :=
  (CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor
    (finiteRepresentablesOfAdmissible P.toPresentation.admissible)).obj
      (P.quotientRepresentable (obj P.toPresentation.relations z))

private def arrowRepresentableMap
    (P : SpecialBiserialPresentation k A Q) {y z : Q} (a : y ⟶ z) :
    P.quotientRepresentable (obj P.toPresentation.relations y) ⟶
      P.quotientRepresentable (obj P.toPresentation.relations z) :=
  (CoveringHom.finiteDimensionalLinearCoyonedaFunctor
      (finiteRepresentablesOfAdmissible P.toPresentation.admissible)).map
    (arrowMap P.toPresentation.relations a).op

private def representedArrowElement
    (P : SpecialBiserialPresentation k A Q) {y z : Q} (a : y ⟶ z) :
    P.representedVertexModule z :=
  biproduct.π P.quotientRepresentable
      (obj P.toPresentation.relations y) ≫
    P.arrowRepresentableMap a

private theorem eq_zero_of_mem_lengthComponent_one_of_quotient_mem_tail_two
    {R : RelationFamily k Q} (hR : IsAdmissible R)
    {X Y : LinearPathCategory.Category k Q} (f : X ⟶ Y)
    (hf : f ∈ LinearPathCategory.lengthComponent X Y 1)
    (hq :
      LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X Y f ∈
        hR.quotientHomLengthTail X Y 2) :
    f = 0 := by
  rcases hq with ⟨g, hg, hgf⟩
  have hdiffKer : f - g ∈ LinearMap.ker
      (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X Y) := by
    rw [LinearMap.mem_ker, map_sub, ← hgf, sub_self]
  have hdiffIdeal : f - g ∈
      QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.generatedHomSubmodule
        k R X Y := by
    rw [← LinearPathCategory.HomogeneousQuotient.ker_quotientHomLinearMap]
    exact hdiffKer
  have hdiffTail : f - g ∈ LinearPathCategory.lengthTail X Y 2 :=
    hR.relationIdeal_le_lengthTail_two X Y hdiffIdeal
  have hfTail : f ∈ LinearPathCategory.lengthTail X Y 2 := by
    rw [show f = (f - g) + g by abel]
    exact Submodule.add_mem _ hdiffTail hg
  exact eq_zero_of_mem_lengthComponent_one_of_mem_lengthTail_two hf hfTail

private theorem arrowMap_comp_ne_arrowMap_of_ne
    (P : SpecialBiserialPresentation k A Q)
    {y w z : Q} (a : y ⟶ z) (b : w ⟶ z)
    (hab : (⟨y, a⟩ : Σ t : Q, t ⟶ z) ≠ ⟨w, b⟩)
    (g : obj P.toPresentation.relations w ⟶
      obj P.toPresentation.relations y) :
    arrowMap P.toPresentation.relations b ≫ g ≠
      arrowMap P.toPresentation.relations a := by
  classical
  let R := P.toPresentation.relations
  let hR := P.toPresentation.admissible
  have haComponent : LinearPathCategory.pathHom a.toPath ∈
      LinearPathCategory.lengthComponent
        (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) 1 :=
    (LinearPathCategory.pathHom_mem_lengthComponent_iff a.toPath 1).2 (by
      change a.toPath.length = 1
      simp)
  have hbTail : arrowMap R b ∈ hR.quotientHomLengthTail
      (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q w) 1 := by
    refine ⟨LinearPathCategory.pathHom b.toPath, ?_, rfl⟩
    exact (LinearPathCategory.pathHom_mem_lengthTail_iff b.toPath 1).2 (by
      change 1 ≤ b.toPath.length
      simp)
  intro hcomp
  by_cases hyw : y = w
  · subst w
    have hab' : a ≠ b := by
      intro hab'
      apply hab
      subst b
      rfl
    obtain ⟨c, s, hs, hg⟩ :=
      hR.exists_eq_smul_one_add_mem_quotientHomLengthTail_one
        (LinearPathCategory.obj k Q y) (End.of g)
    have hbsTail : arrowMap R b ≫ End.asHom s ∈
        hR.quotientHomLengthTail
          (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) 2 := by
      simpa using hR.comp_mem_quotientHomLengthTail hbTail hs
    let pa : LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q y :=
      LinearPathCategory.pathHom a.toPath
    let pb : LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q y :=
      LinearPathCategory.pathHom b.toPath
    let f : LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q y :=
      pa - c • pb
    have hfComponent : f ∈ LinearPathCategory.lengthComponent
        (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) 1 := by
      apply Submodule.sub_mem
      · exact haComponent
      · apply Submodule.smul_mem
        exact (LinearPathCategory.pathHom_mem_lengthComponent_iff b.toPath 1).2
          (by
            change b.toPath.length = 1
            simp)
    have hfImage :
        LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
            (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) f =
          arrowMap R a - c • arrowMap R b := by
      calc
        LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
              (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) f =
            LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
                (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) pa -
              c • LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
                (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) pb := by
          simp only [f, map_sub, map_smul]
        _ = arrowMap R a - c • arrowMap R b := by
          rfl
    have hfQuotient :
        LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
          (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) f =
          arrowMap R b ≫ End.asHom s := by
      calc
        _ = arrowMap R a - c • arrowMap R b := hfImage
        _ = arrowMap R b ≫ End.asHom s := by
          have hg' : g = c • 𝟙 (obj R y) + End.asHom s := by
            exact congrArg End.asHom hg
          rw [← hcomp, hg', Preadditive.comp_add,
            CategoryTheory.Linear.comp_smul, Category.comp_id]
          abel
    have hfTail :
        LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
            (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) f ∈
          hR.quotientHomLengthTail
            (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) 2 := by
      rw [hfQuotient]
      exact hbsTail
    have hfzero :=
      eq_zero_of_mem_lengthComponent_one_of_quotient_mem_tail_two
        hR f hfComponent hfTail
    have hlinear : arrowMap R a - c • arrowMap R b = 0 := by
      rw [← hfImage, hfzero, map_zero]
    let coeff : (y ⟶ z) →₀ k :=
      Finsupp.single a 1 - Finsupp.single b c
    have hcomb : Finsupp.linearCombination k (fun d : y ⟶ z ↦ arrowMap R d)
        coeff = 0 := by
      simp only [coeff, map_sub, Finsupp.linearCombination_single,
        one_smul, hlinear]
    have hcoeffZero : coeff = 0 :=
      (arrowMap_linearIndependent hR y z).finsuppLinearCombination_injective
        (by simpa using hcomb)
    have haValue := congrArg (fun d : (y ⟶ z) →₀ k ↦ d a) hcoeffZero
    simp [coeff, hab'] at haValue
  · have hgTail : g ∈ hR.quotientHomLengthTail
        (LinearPathCategory.obj k Q w) (LinearPathCategory.obj k Q y) 1 := by
      rw [hR.quotientHomLengthTail_one_eq_top_of_vertex_ne]
      · exact Submodule.mem_top
      · exact hyw
    have hbgTail : arrowMap R b ≫ g ∈
        hR.quotientHomLengthTail
          (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) 2 := by
      simpa using hR.comp_mem_quotientHomLengthTail hbTail hgTail
    have haTail : arrowMap R a ∈ hR.quotientHomLengthTail
        (LinearPathCategory.obj k Q z) (LinearPathCategory.obj k Q y) 2 := by
      rw [← hcomp]
      exact hbgTail
    have hazero :=
      eq_zero_of_mem_lengthComponent_one_of_quotient_mem_tail_two
        hR (LinearPathCategory.pathHom a.toPath) haComponent haTail
    exact (LinearPathCategory.homPathBasis
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q y)).ne_zero a.toPath hazero

private theorem smul_representedArrowElement_ne_of_ne
    (P : SpecialBiserialPresentation k A Q)
    {y w z : Q} (a : y ⟶ z) (b : w ⟶ z)
    (hab : (⟨y, a⟩ : Σ t : Q, t ⟶ z) ≠ ⟨w, b⟩)
    (c : P.quotientCategoryAlgebraᵐᵒᵖ) :
    c • P.representedArrowElement b ≠ P.representedArrowElement a := by
  intro hsmul
  let h : P.quotientRepresentable (obj P.toPresentation.relations y) ⟶
      P.quotientRepresentable (obj P.toPresentation.relations w) :=
    biproduct.ι P.quotientRepresentable
        (obj P.toPresentation.relations y) ≫
      End.asHom c.unop ≫
      biproduct.π P.quotientRepresentable
        (obj P.toPresentation.relations w)
  have hfactor : h ≫ P.arrowRepresentableMap b =
      P.arrowRepresentableMap a := by
    have hsmul' := congrArg
      (fun q : P.representedVertexModule z ↦
        biproduct.ι P.quotientRepresentable
            (obj P.toPresentation.relations y) ≫ q) hsmul
    change
      biproduct.ι P.quotientRepresentable
            (obj P.toPresentation.relations y) ≫
          End.asHom c.unop ≫
          biproduct.π P.quotientRepresentable
            (obj P.toPresentation.relations w) ≫
          P.arrowRepresentableMap b =
        biproduct.ι P.quotientRepresentable
            (obj P.toPresentation.relations y) ≫
          biproduct.π P.quotientRepresentable
            (obj P.toPresentation.relations y) ≫
          P.arrowRepresentableMap a at hsmul'
    simpa [h, Category.assoc] using hsmul'
  let g : obj P.toPresentation.relations w ⟶
      obj P.toPresentation.relations y :=
    ((h.hom.hom.app (obj P.toPresentation.relations y)).hom)
      (𝟙 (obj P.toPresentation.relations y))
  have hcomp : arrowMap P.toPresentation.relations b ≫ g =
      arrowMap P.toPresentation.relations a := by
    have happ := congrArg
      (fun q : P.quotientRepresentable (obj P.toPresentation.relations y) ⟶
          P.quotientRepresentable (obj P.toPresentation.relations z) ↦
        ((q.hom.hom.app (obj P.toPresentation.relations y)).hom)
          (𝟙 (obj P.toPresentation.relations y))) hfactor
    exact happ
  exact P.arrowMap_comp_ne_arrowMap_of_ne a b hab g hcomp

theorem relationSourceRepresentedModule_not_uniserial
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    ¬ IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule z) := by
  intro huni
  obtain ⟨q, hqp⟩ := p.exists_ne P r hr
  let dp := P.relationSurvivingSupportFinalDecomposition r hr p
  let dq := P.relationSurvivingSupportFinalDecomposition r hr q
  have hpqArrow : (⟨dp.middle, dp.arrow⟩ : Σ t : Q, t ⟶ z) ≠
      ⟨dq.middle, dq.arrow⟩ := by
    intro harrow
    apply hqp
    exact (P.relationSurvivingSupportFinalArrow_injective r hr harrow).symm
  rcases huni.smul_comparable
      (P.representedArrowElement dp.arrow)
      (P.representedArrowElement dq.arrow) with hpdq | hqdp
  · obtain ⟨c, hc⟩ := hpdq
    exact P.smul_representedArrowElement_ne_of_ne
      dq.arrow dp.arrow hpqArrow.symm c hc
  · obtain ⟨c, hc⟩ := hqdp
    exact P.smul_representedArrowElement_ne_of_ne
      dp.arrow dq.arrow hpqArrow c hc

end MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

namespace MagnitudeConjecture

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

include k in
theorem submodule_inf_ne_bot_of_injective_indecomposable
    (I : FGModuleCat.{u} Bᵐᵒᵖ) [Injective I]
    (hI : Indecomposable I)
    (U V : Submodule Bᵐᵒᵖ I) (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    U ⊓ V ≠ ⊥ := by
  have hlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := B) I
  letI : IsArtinian Bᵐᵒᵖ I :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  have hsocle : IsSimpleModule Bᵐᵒᵖ (moduleSocle Bᵐᵒᵖ I) :=
    moduleSocle_isSimple_of_injective_indecomposable (k := k) I hI
  have hUSne : U ⊓ moduleSocle Bᵐᵒᵖ I ≠ ⊥ :=
    inf_moduleSocle_ne_bot U hU
  have hVSne : V ⊓ moduleSocle Bᵐᵒᵖ I ≠ ⊥ :=
    inf_moduleSocle_ne_bot V hV
  have hUS : U ⊓ moduleSocle Bᵐᵒᵖ I = moduleSocle Bᵐᵒᵖ I :=
    (isSimpleModule_iff_isAtom.mp hsocle).le_iff_eq hUSne |>.mp inf_le_right
  have hVS : V ⊓ moduleSocle Bᵐᵒᵖ I = moduleSocle Bᵐᵒᵖ I :=
    (isSimpleModule_iff_isAtom.mp hsocle).le_iff_eq hVSne |>.mp inf_le_right
  have hsocleU : moduleSocle Bᵐᵒᵖ I ≤ U := by
    rw [← hUS]
    exact inf_le_left
  have hsocleV : moduleSocle Bᵐᵒᵖ I ≤ V := by
    rw [← hVS]
    exact inf_le_left
  intro hUV
  have hsocleBot : moduleSocle Bᵐᵒᵖ I ≤ ⊥ := by
    rw [← hUV]
    exact le_inf hsocleU hsocleV
  exact (isSimpleModule_iff_isAtom.mp hsocle).ne_bot
    (le_antisymm hsocleBot bot_le)

/-- Module-theoretic uniseriality is reflected by the finitely generated
module category. -/
theorem isUniserialModule_of_fgModuleCat_isUniserialObject
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (N : FGModuleCat.{u} R) (hN : IsUniserialObject N) :
    IsUniserialModule R N := by
  letI : (ModuleCat.isFG R).IsClosedUnderSubobjects := {
    prop_of_mono := by
      intro X Y f _ hY
      letI : Module.Finite R Y := hY
      exact Module.Finite.of_injective f.hom
        ((ModuleCat.mono_iff_injective f).mp inferInstance) }
  letI : (ModuleCat.isFG R).ContainsZero := {
    exists_zero := ⟨ModuleCat.of R PUnit,
      ModuleCat.isZero_of_subsingleton _, by
      change Module.Finite R PUnit
      infer_instance⟩ }
  have hAmbient : IsUniserialObject (ModuleCat.of R N) :=
    IsUniserialObject.congrOrderIso hN
      (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
        (ModuleCat.isFG R) N)
  exact IsUniserialModule.iff_moduleCat.mpr hAmbient

end MagnitudeConjecture

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- For a module annihilated by an ideal, uniseriality over the quotient is
exactly uniseriality over the ambient algebra. -/
theorem idealQuotientFGObj_isUniserial_iff_ambient
    (I : TwoSidedIdeal A) (M : IdealQuotientSubcategory I) :
    IsUniserialModule (idealQuotientAlgebra I)ᵐᵒᵖ
        ((idealQuotientEquivalence (k := k) I).functor.obj M) ↔
      IsUniserialModule Aᵐᵒᵖ M.obj := by
  letI : IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let E := idealQuotientEquivalence (k := k) I
  let Q := IdealQuotientProperty I
  letI : Q.Nonempty := ObjectProperty.nonempty_of_prop M.property
  letI : Q.ContainsZero := inferInstance
  constructor
  · intro hQuotient
    have hQuotientObject : IsUniserialObject (E.functor.obj M) :=
      IsUniserialModule.toFGModuleCatIsUniserialObject _ hQuotient
    have hSubcategory : IsUniserialObject M :=
      IsUniserialObject.of_map_equivalence E hQuotientObject
    have hAmbientObject : IsUniserialObject M.obj :=
      IsUniserialObject.congrOrderIso hSubcategory
        (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
          Q M)
    exact isUniserialModule_of_fgModuleCat_isUniserialObject M.obj
      hAmbientObject
  · intro hAmbient
    have hAmbientObject : IsUniserialObject M.obj :=
      IsUniserialModule.toFGModuleCatIsUniserialObject M.obj hAmbient
    have hSubcategory : IsUniserialObject M :=
      IsUniserialObject.congrOrderIso hAmbientObject
        (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
          Q M).symm
    have hQuotientObject : IsUniserialObject (E.functor.obj M) :=
      IsUniserialObject.map_equivalence hSubcategory E
    exact isUniserialModule_of_fgModuleCat_isUniserialObject
      (E.functor.obj M) hQuotientObject

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

theorem representedVertexModule_isUniserial_of_injective
    (P : StringPresentation k A Q) (y : Q)
    (hInjective : Injective (P.representedVertexModule y)) :
    IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := by
  classical
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Injective (P.representedVertexModule y) := hInjective
  have hIndecomposable : Indecomposable (P.representedVertexModule y) :=
    P.representedVertexModule_indecomposable y
  by_contra hnotUniserial
  have hnotSubsingleton : ¬ Subsingleton (DisplayedIncomingArrow y) := by
    intro hSubsingleton
    letI : Subsingleton (DisplayedIncomingArrow y) := hSubsingleton
    have hfamily : IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
        (∀ a : DisplayedIncomingArrow y,
          LinearMap.range (P.representedArrowLinearMap a.2)) := by
      apply isUniserialModule_pi_of_subsingleton
      intro a
      exact P.representedArrowLinearRange_isUniserial a.2
    have hradical : IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
        (Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
          (P.representedVertexModule y)) :=
      IsUniserialModule.congr
        (P.incomingArrowRangeFamilyRadicalLinearEquiv y) hfamily
    exact hnotUniserial (IsUniserialModule.of_simpleTop_of_jacobson
      (P.representedVertexModule_top_isSimple y) hradical)
  have hexists : ∃ a b : DisplayedIncomingArrow y, a ≠ b := by
    by_contra hnone
    apply hnotSubsingleton
    constructor
    intro a b
    by_contra hab
    exact hnone ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hexists
  let U : Submodule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) :=
    LinearMap.range (P.representedArrowLinearMap a.2)
  let V : Submodule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) :=
    LinearMap.range (P.representedArrowLinearMap b.2)
  have hU : U ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp
      (P.representedArrowLinearRange_nontrivial a.2)
  have hV : V ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp
      (P.representedArrowLinearRange_nontrivial b.2)
  have hUV : U ⊓ V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    let ga : ∀ d : DisplayedIncomingArrow y,
        LinearMap.range (P.representedArrowLinearMap d.2) :=
      Pi.single a (⟨x, hx.1⟩ : U)
    let gb : ∀ d : DisplayedIncomingArrow y,
        LinearMap.range (P.representedArrowLinearMap d.2) :=
      Pi.single b (⟨x, hx.2⟩ : V)
    have hga : P.incomingArrowRangeSumLinearMap y ga = x := by
      change (∑ d, (ga d).1) = x
      rw [Finset.sum_eq_single a]
      · simp [ga]
      · intro d _ hda
        simp [ga, hda]
      · simp
    have hgb : P.incomingArrowRangeSumLinearMap y gb = x := by
      change (∑ d, (gb d).1) = x
      rw [Finset.sum_eq_single b]
      · simp [gb]
      · intro d _ hdb
        simp [gb, hdb]
      · simp
    have hgab : ga = gb :=
      P.incomingArrowRangeSumLinearMap_injective y (hga.trans hgb.symm)
    have ha := congrFun hgab a
    have hxa : x = 0 := by
      have haVal := congrArg Subtype.val ha
      simpa [ga, gb, hab] using haVal
    exact hxa
  exact submodule_inf_ne_bot_of_injective_indecomposable
    (k := k) (P.representedVertexModule y) hIndecomposable U V hU hV hUV

/-- Every indecomposable projective-injective module over the category algebra
of a string presentation is uniserial. -/
theorem projectiveInjectiveIndecomposable_isUniserial
    (P : StringPresentation k A Q)
    (M : FGModuleCat.{u} P.quotientCategoryAlgebraᵐᵒᵖ)
    [Projective M] [Injective M]
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      P.quotientCategoryAlgebraᵐᵒᵖ M) :
    IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ M := by
  classical
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hMCat : Indecomposable M :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := P.quotientCategoryAlgebra) M).1 hM
  let hlocal : ∀ X : Category P.toPresentation.relations,
      IsLocalRing (End X) := fun X ↦ P.quotientEnd_isLocalRing X
  let E := CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence hP
  letI : E.functor.Additive :=
    CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor_additive hP
  letI : E.inverse.Additive := inferInstance
  let N := E.inverse.obj M
  letI : Projective N :=
    (E.symm.map_projective_iff M).2 inferInstance
  have hN : Indecomposable N :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse M).2 hMCat
  obtain ⟨X, ⟨eX⟩⟩ :=
    CoveringHom.indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      hP hlocal N hN
  let y := P.quotientObjectEquiv X
  let eObj : obj P.toPresentation.relations y ≅ X :=
    eqToIso (P.quotientObjectEquiv.symm_apply_apply X)
  let J := CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP
  let eRepresentable :
      P.quotientRepresentable (obj P.toPresentation.relations y) ≅ N :=
    (J.mapIso eObj.symm.op).trans eX
  let eTarget : P.representedVertexModule y ≅ M :=
    (E.functor.mapIso eRepresentable).trans (E.counitIso.app M)
  have hRepresentedInjective : Injective (P.representedVertexModule y) :=
    Injective.of_iso eTarget.symm (inferInstance : Injective M)
  exact IsUniserialModule.congr
    (FGModuleCat.isoToLinearEquiv eTarget)
    (P.representedVertexModule_isUniserial_of_injective y
      hRepresentedInjective)

end MagnitudeConjecture.BoundQuiver.StringPresentation
