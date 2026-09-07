import MagnitudeConjecture.Algebra.RightModuleRegularDecomposition
import MagnitudeConjecture.Algebra.RightModuleSupportCoordinate

/-!
# Directed boundary vanishings in middle-support quotients

This file formalizes the two directed-triangle vanishings used in the
manuscript's Ringel support argument.  All modules and morphisms live in the
literal quotient supported on the middle term of the chosen almost-split
sequence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

omit [IsNoetherianRing Bᵐᵒᵖ] in
private theorem fg_hom_sum_apply {J : Type*} [Fintype J]
    {X Y : FGModuleCat.{u} B} (f : J → (X ⟶ Y)) (x : X) :
    ((∑ j, f j).hom.hom) x = ∑ j, (f j).hom.hom x := by
  have h : (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h, ModuleCat.hom_sum]
  exact LinearMap.sum_apply _ _ x

/-- The regular left module as a literal finitely generated object. -/
abbrev leftRegularFGObj : FGModuleCat.{u} B := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite k B
  exact FGModuleCat.of B B

/-- The literal inclusion `Be → B` of left ideals. -/
def leftIdealInclusion (e : B) :
    leftIdealFGObj (k := k) e ⟶ leftRegularFGObj (B := B) := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite k B
  letI : IsNoetherian B B := inferInstance
  letI : Module.Finite B (leftIdeal e) := inferInstance
  exact FGModuleCat.ofHom (leftIdeal e).subtype

/-- Right multiplication by `e`, as the projection `B → Be` of left
ideals. -/
def leftIdealProjection (e : B) :
    leftRegularFGObj (B := B) ⟶ leftIdealFGObj (k := k) e := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite k B
  letI : IsNoetherian B B := inferInstance
  letI : Module.Finite B (leftIdeal e) := inferInstance
  exact FGModuleCat.ofHom <|
    (leftRegularRightMul e).codRestrict
      (leftIdeal e) fun y ↦ ⟨y, rfl⟩

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem leftIdealInclusion_apply_val
    (e : B) (y : leftIdealFGObj (k := k) e) :
    (leftIdealInclusion (k := k) e).hom.hom y = y.1 :=
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem leftIdealProjection_apply_val
    (e : B) (y : leftRegularFGObj (B := B)) :
    ((leftIdealProjection (k := k) e).hom.hom y).1 = y * e :=
  rfl

/-- The standard injective cogenerator `D(B)`. -/
abbrev injectiveCogeneratorFGObj : FinitelyGeneratedCategory B :=
    (Contragredient.dualFunctor k B).obj
    (Opposite.op (leftRegularFGObj (B := B)))

/-- Dualizing `B → Be` gives the canonical inclusion `D(Be) → D(B)`. -/
def primitiveInjectiveInclusion (e : B) :
    primitiveInjectiveFGObj (k := k) e ⟶
      injectiveCogeneratorFGObj (k := k) (B := B) :=
  (Contragredient.dualFunctor k B).map (leftIdealProjection (k := k) e).op

/-- Dualizing `Be → B` gives the canonical projection `D(B) → D(Be)`. -/
def primitiveInjectiveProjection (e : B) :
    injectiveCogeneratorFGObj (k := k) (B := B) ⟶
      primitiveInjectiveFGObj (k := k) e :=
  (Contragredient.dualFunctor k B).map (leftIdealInclusion (k := k) e).op

omit [IsNoetherianRing Bᵐᵒᵖ] in
@[simp]
theorem primitiveInjectiveProjection_comp_inclusion_apply
    (e : B) (φ : injectiveCogeneratorFGObj (k := k) (B := B))
    (b : B) :
    (Contragredient.forwardInnerDualEquiv k B
      (leftRegularFGObj (B := B))
        ((primitiveInjectiveProjection (k := k) e ≫
          primitiveInjectiveInclusion (k := k) e).hom.hom φ)) b =
      (Contragredient.forwardInnerDualEquiv k B
        (leftRegularFGObj (B := B)) φ) (b * e) :=
  rfl

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- Decompose the regular support module into the right ideals belonging to
the surviving primitive idempotents. -/
def supportRegularDecompositionMap
    (X : RightModule.FinitelyGeneratedCategory A) :
    RightModule.rightRegularFGObj (B := P.SupportAlgebra X) ⟶
      ⨁ fun p : SupportedProjectiveLabel (S := S) X ↦
        RightModule.rightIdealFGObj (P.supportedIdempotent X p) :=
  biproduct.lift fun p ↦
    RightModule.rightIdealProjection (P.supportedIdempotent X p)

/-- Assemble the supported primitive right ideals back into the regular
support module. -/
def supportRegularAssemblyMap
    (X : RightModule.FinitelyGeneratedCategory A) :
    (⨁ fun p : SupportedProjectiveLabel (S := S) X ↦
      RightModule.rightIdealFGObj (P.supportedIdempotent X p)) ⟶
      RightModule.rightRegularFGObj (B := P.SupportAlgebra X) :=
  biproduct.desc fun p ↦
    RightModule.rightIdealInclusion (P.supportedIdempotent X p)

/-- Completeness of the quotient idempotents makes regular decomposition
followed by assembly the identity. -/
theorem supportRegularDecompositionMap_comp_assemblyMap
    (X : RightModule.FinitelyGeneratedCategory A) :
    P.supportRegularDecompositionMap X ≫
      P.supportRegularAssemblyMap X = 𝟙 _ := by
  classical
  rw [supportRegularDecompositionMap, supportRegularAssemblyMap,
    biproduct.lift_desc]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [RightModule.fg_hom_sum_apply]
  change (∑ p : SupportedProjectiveLabel (S := S) X,
      P.supportedIdempotent X p * y) = y
  calc
    _ = ∑ p : SupportedProjectiveLabel (S := S) X,
        P.supportedIdempotent X p * y := by
          rfl
    _ = y := by
      rw [← Finset.sum_mul,
        (P.supportedIdempotents_complete X).complete, one_mul]

/-- The regular decomposition map is split monic. -/
theorem supportRegularDecompositionMap_isSplitMono
    (X : RightModule.FinitelyGeneratedCategory A) :
    IsSplitMono (P.supportRegularDecompositionMap X) :=
  IsSplitMono.mk'
    { retraction := P.supportRegularAssemblyMap X
      id := P.supportRegularDecompositionMap_comp_assemblyMap X }

/-- Assemble the primitive injectives belonging to the surviving quotient
idempotents into the standard injective cogenerator `D(B)`. -/
def supportInjectiveAssemblyMap
    (X : RightModule.FinitelyGeneratedCategory A) :
    (⨁ fun p : SupportedProjectiveLabel (S := S) X ↦
        RightModule.primitiveInjectiveFGObj (k := k)
          (P.supportedIdempotent X p)) ⟶
      RightModule.injectiveCogeneratorFGObj (k := k)
        (B := P.SupportAlgebra X) :=
  biproduct.desc fun p ↦
    RightModule.primitiveInjectiveInclusion (k := k)
      (P.supportedIdempotent X p)

/-- Restrict a functional on the support algebra to all primitive left
ideals. -/
def supportInjectiveDecompositionMap
    (X : RightModule.FinitelyGeneratedCategory A) :
    RightModule.injectiveCogeneratorFGObj (k := k)
        (B := P.SupportAlgebra X) ⟶
      ⨁ fun p : SupportedProjectiveLabel (S := S) X ↦
        RightModule.primitiveInjectiveFGObj (k := k)
          (P.supportedIdempotent X p) :=
  biproduct.lift fun p ↦
    RightModule.primitiveInjectiveProjection (k := k)
      (P.supportedIdempotent X p)

/-- Restriction followed by assembly is the identity on `D(B)`. -/
theorem supportInjectiveDecompositionMap_comp_assemblyMap
    (X : RightModule.FinitelyGeneratedCategory A) :
    P.supportInjectiveDecompositionMap X ≫
      P.supportInjectiveAssemblyMap X = 𝟙 _ := by
  classical
  rw [supportInjectiveDecompositionMap, supportInjectiveAssemblyMap,
    biproduct.lift_desc]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rw [RightModule.fg_hom_sum_apply]
  apply (Contragredient.forwardInnerDualEquiv k (P.SupportAlgebra X)
    (RightModule.leftRegularFGObj (B := P.SupportAlgebra X))).injective
  apply DFunLike.ext _ _
  intro b
  simp only [map_sum, LinearMap.sum_apply,
    RightModule.primitiveInjectiveProjection_comp_inclusion_apply]
  let ψ := Contragredient.forwardInnerDualEquiv k (P.SupportAlgebra X)
    (RightModule.leftRegularFGObj (B := P.SupportAlgebra X)) φ
  change (∑ p : SupportedProjectiveLabel (S := S) X,
      ψ (b * P.supportedIdempotent X p)) = ψ b
  rw [← map_sum, ← Finset.mul_sum,
    (P.supportedIdempotents_complete X).complete, mul_one]

/-- Assembly of the surviving primitive injectives is split epic. -/
theorem supportInjectiveAssemblyMap_isSplitEpi
    (X : RightModule.FinitelyGeneratedCategory A) :
    IsSplitEpi (P.supportInjectiveAssemblyMap X) :=
  IsSplitEpi.mk'
    { section_ := P.supportInjectiveDecompositionMap X
      id := P.supportInjectiveDecompositionMap_comp_assemblyMap X }

/-- The ambient epimorphism remains epic after restriction to the full
middle-support subcategory. -/
theorem rightSequenceSupportMap_epi
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Epi (rightSequenceSupportMap (S := S) z) := by
  let B := S.minimalRightAlmostSplitAt z.1
  have hBEpi : Epi B.map :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
  letI : Epi B.map := hBEpi
  apply (Preadditive.epi_iff_cancel_zero _).2
  intro Z g hg
  apply ObjectProperty.hom_ext
  apply (Preadditive.epi_iff_cancel_zero B.map).1 hBEpi Z.obj g.hom
  have hg' := congrArg (fun q ↦ q.hom) hg
  exact hg'

/-- The transported middle-support almost-split map is still epic. -/
theorem rightSequenceSupportSkeletonMap_epi
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Epi (P.rightSequenceSupportSkeletonMap hA z) := by
  letI : Epi (rightSequenceSupportMap (S := S) z) :=
    rightSequenceSupportMap_epi (S := S) z
  dsimp only [rightSequenceSupportSkeletonMap,
    rightSequenceSupportAlgebraMap]
  infer_instance

/-- The endpoint remains nonprojective in the literal middle-support
quotient. -/
theorem rightSequenceSupportTarget_not_projective
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    ¬ Projective
      ((P.supportAlgebraSkeleton hA
        (S.minimalRightAlmostSplitAt z.1).middle).almostSplitSkeleton.obj
          (P.rightSequenceSupportTargetLabel hA z)) := by
  intro hprojective
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  letI : Projective
      ((P.supportAlgebraSkeleton hA
        (S.minimalRightAlmostSplitAt z.1).middle).almostSplitSkeleton.obj
          (P.rightSequenceSupportTargetLabel hA z)) := hprojective
  letI : Epi B.map := P.rightSequenceSupportSkeletonMap_epi hA z
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 _) B.map
  apply B.rightAlmostSplit.not_isSplitEpi
  exact IsSplitEpi.mk' { section_ := s, id := hs }

/-- Every supported primitive-projective skeleton object maps nontrivially
to the actual middle object of the transported sequence. -/
theorem exists_ne_zero_hom_from_supportProjective_to_rightMiddle
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (p : SupportedProjectiveLabel (S := S)
      (S.minimalRightAlmostSplitAt z.1).middle) :
    ∃ f : (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            (P.supportProjectiveCoordinate hA
              (S.minimalRightAlmostSplitAt z.1).middle p.1 p.2).label ⟶
        (P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z).middle,
      f ≠ 0 := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let Dp := P.supportPrimitiveIdempotentData X p.1 p.2
  obtain ⟨f, hf⟩ := P.exists_ne_zero_hom_from_supportedRightIdeal X p
  let e := T.primitiveSourceIso Dp
  refine ⟨e.inv ≫ f, ?_⟩
  intro hzero
  exact hf (zero_of_epi_comp e.inv hzero)

/-- The actual middle object maps nontrivially to every supported
primitive-injective skeleton object. -/
theorem exists_ne_zero_hom_from_rightMiddle_to_supportInjective
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (p : SupportedProjectiveLabel (S := S)
      (S.minimalRightAlmostSplitAt z.1).middle) :
    ∃ f :
        (P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z).middle ⟶
          (P.supportAlgebraSkeleton hA
            (S.minimalRightAlmostSplitAt z.1).middle).fgObj
              ((P.supportAlgebraSkeleton hA
                (S.minimalRightAlmostSplitAt z.1).middle).primitiveSinkLabel
                  (P.supportPrimitiveIdempotentData
                    (S.minimalRightAlmostSplitAt z.1).middle p.1 p.2)),
      f ≠ 0 := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let Dp := P.supportPrimitiveIdempotentData X p.1 p.2
  obtain ⟨f, hf⟩ :=
    P.exists_ne_zero_hom_to_supportedPrimitiveInjective X p
  let e := T.primitiveSinkIso Dp
  refine ⟨f ≫ e.hom, ?_⟩
  intro hzero
  exact hf (zero_of_comp_mono e.hom hzero)

/-- The supported endpoint has no nonzero map to any surviving primitive
projective.  A hypothetical map closes a directed triangle with one
irreducible component of the transported right almost-split map. -/
theorem hom_from_rightTarget_to_supportProjective_eq_zero
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (p : SupportedProjectiveLabel (S := S)
      (S.minimalRightAlmostSplitAt z.1).middle)
    (q : (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            (P.rightSequenceSupportTargetLabel hA z) ⟶
        (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            (P.supportProjectiveCoordinate hA
              (S.minimalRightAlmostSplitAt z.1).middle p.1 p.2).label) :
    q = 0 := by
  classical
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  let HT := P.supportAlgebraSkeleton_hasAcyclicNonzeroNonisomorphisms H hA X
  by_contra hq
  obtain ⟨f, hf⟩ :=
    P.exists_ne_zero_hom_from_supportProjective_to_rightMiddle hA z p
  have hcomponent : ∃ t : B.index,
      f ≫ B.decomposition.hom ≫
          biproduct.π
            (fun j ↦ T.almostSplitSkeleton.obj (B.label j)) t ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    apply (cancel_mono B.decomposition.hom).1
    apply biproduct.hom_ext
    intro t
    simpa only [Category.assoc, zero_comp] using hall t
  obtain ⟨t, ht⟩ := hcomponent
  have hirr : HasIrreducibleMorphism
      (T.almostSplitSkeleton.obj (B.label t))
      (T.almostSplitSkeleton.obj
        (P.rightSequenceSupportTargetLabel hA z)) :=
    ⟨B.component T.almostSplitSkeleton t,
      B.component_irreducible T.almostSplitSkeleton t⟩
  exact HasAcyclicNonzeroNonisomorphisms.no_nonzero_triangle_of_irreducible
    T HT
    hirr
    q hq
    (f ≫ B.decomposition.hom ≫
      biproduct.π
        (fun j ↦ T.almostSplitSkeleton.obj (B.label j)) t) ht

/-- The supported endpoint has no nonzero map to the regular support
module.  This is the finite aggregation of the primitive-projective
vanishing over the complete quotient idempotent family. -/
theorem hom_from_rightTarget_to_supportRegular_eq_zero
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (q : (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            (P.rightSequenceSupportTargetLabel hA z) ⟶
        RightModule.rightRegularFGObj
          (B := P.SupportAlgebra
            (S.minimalRightAlmostSplitAt z.1).middle)) :
    q = 0 := by
  classical
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let d := P.supportRegularDecompositionMap X
  letI : IsSplitMono d := P.supportRegularDecompositionMap_isSplitMono X
  apply (cancel_mono d).1
  apply biproduct.hom_ext
  intro p
  simp only [d, supportRegularDecompositionMap, Category.assoc,
    biproduct.lift_π, zero_comp]
  let Dp := P.supportPrimitiveIdempotentData X p.1 p.2
  let e := T.primitiveSourceIso Dp
  have hzero := P.hom_from_rightTarget_to_supportProjective_eq_zero
    hA H z p (q ≫ RightModule.rightIdealProjection
      (P.supportedIdempotent X p) ≫ e.hom)
  have hzero' := hzero
  change (q ≫ RightModule.rightIdealProjection
    (P.supportedIdempotent X p)) ≫ e.hom = 0 at hzero'
  exact zero_of_comp_mono e.hom hzero'

/-- The support-skeleton label selected for the kernel of the transported
right almost-split map. -/
def rightSequenceSupportKernelLabel
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Fin (P.supportAlgebraSkeleton hA
      (S.minimalRightAlmostSplitAt z.1).middle).n := by
  let T := P.supportAlgebraSkeleton hA
    (S.minimalRightAlmostSplitAt z.1).middle
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  exact Classical.choose
    (T.almostSplitSkeleton.complete (kernel B.map)
      (B.kernel_ar_sequence T.almostSplitSkeleton
        (P.rightSequenceSupportTarget_not_projective hA z)).2.2.1)

/-- The kernel is represented by its selected support-skeleton label. -/
def rightSequenceSupportKernelIso
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    kernel (P.rightSequenceSupportMinimalRightAlmostSplitDecomposition
        hA z).map ≅
      (P.supportAlgebraSkeleton hA
        (S.minimalRightAlmostSplitAt z.1).middle).almostSplitSkeleton.obj
          (P.rightSequenceSupportKernelLabel hA z) := by
  let T := P.supportAlgebraSkeleton hA
    (S.minimalRightAlmostSplitAt z.1).middle
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  exact Classical.choice (Classical.choose_spec
    (T.almostSplitSkeleton.complete (kernel B.map)
      (B.kernel_ar_sequence T.almostSplitSkeleton
        (P.rightSequenceSupportTarget_not_projective hA z)).2.2.1))

/-- The kernel inclusion, transported to its selected skeleton object and
equipped with the actual middle decomposition, is minimal left almost
split. -/
def rightSequenceSupportMinimalLeftAlmostSplitDecomposition
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (P.supportAlgebraSkeleton hA
      (S.minimalRightAlmostSplitAt z.1).middle).almostSplitSkeleton
        |>.MinimalLeftAlmostSplitDecomposition
          (P.rightSequenceSupportKernelLabel hA z) := by
  let T := P.supportAlgebraSkeleton hA
    (S.minimalRightAlmostSplitAt z.1).middle
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  let hAR := B.kernel_ar_sequence T.almostSplitSkeleton
    (P.rightSequenceSupportTarget_not_projective hA z)
  let e := P.rightSequenceSupportKernelIso hA z
  exact
    { middle := B.middle
      finiteLength := B.finiteLength
      map := e.inv ≫ kernel.ι B.map
      leftAlmostSplit := hAR.1.precomp_iso e.symm
      leftMinimal := hAR.2.1.precomp_iso e.symm
      index := B.index
      label := B.label
      decomposition := B.decomposition }

/-- No surviving primitive injective maps nontrivially to the kernel of the
transported sequence.  A hypothetical map closes a directed triangle with
one irreducible component of the kernel's minimal left almost-split map. -/
theorem hom_from_supportInjective_to_rightKernel_eq_zero
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (p : SupportedProjectiveLabel (S := S)
      (S.minimalRightAlmostSplitAt z.1).middle)
    (q : (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            ((P.supportAlgebraSkeleton hA
              (S.minimalRightAlmostSplitAt z.1).middle).primitiveSinkLabel
                (P.supportPrimitiveIdempotentData
                  (S.minimalRightAlmostSplitAt z.1).middle p.1 p.2)) ⟶
        (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            (P.rightSequenceSupportKernelLabel hA z)) :
    q = 0 := by
  classical
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  let L :=
    P.rightSequenceSupportMinimalLeftAlmostSplitDecomposition hA z
  let HT := P.supportAlgebraSkeleton_hasAcyclicNonzeroNonisomorphisms H hA X
  by_contra hq
  obtain ⟨f, hf⟩ :=
    P.exists_ne_zero_hom_from_rightMiddle_to_supportInjective hA z p
  have hcomponent : ∃ t : B.index,
      biproduct.ι
          (fun j ↦ T.almostSplitSkeleton.obj (B.label j)) t ≫
        B.decomposition.inv ≫ f ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    apply (cancel_epi B.decomposition.inv).1
    apply biproduct.hom_ext'
    intro t
    simpa only [Category.assoc, comp_zero] using hall t
  obtain ⟨t, ht⟩ := hcomponent
  have hirr : HasIrreducibleMorphism
      (T.almostSplitSkeleton.obj
        (P.rightSequenceSupportKernelLabel hA z))
      (T.almostSplitSkeleton.obj (B.label t)) :=
    ⟨L.component T.almostSplitSkeleton t,
      L.component_irreducible T.almostSplitSkeleton t⟩
  exact HasAcyclicNonzeroNonisomorphisms.no_nonzero_triangle_of_irreducible
    T HT hirr
    (biproduct.ι
        (fun j ↦ T.almostSplitSkeleton.obj (B.label j)) t ≫
      B.decomposition.inv ≫ f) ht
    q hq

/-- The injective cogenerator of the support algebra has no nonzero map to
the kernel.  This is the finite aggregation of the primitive-injective
vanishing over the complete quotient idempotent family. -/
theorem hom_from_supportInjectiveCogenerator_to_rightKernel_eq_zero
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (q : RightModule.injectiveCogeneratorFGObj (k := k)
          (B := P.SupportAlgebra
            (S.minimalRightAlmostSplitAt z.1).middle) ⟶
        (P.supportAlgebraSkeleton hA
          (S.minimalRightAlmostSplitAt z.1).middle).fgObj
            (P.rightSequenceSupportKernelLabel hA z)) :
    q = 0 := by
  classical
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let c := P.supportInjectiveAssemblyMap X
  letI : IsSplitEpi c := P.supportInjectiveAssemblyMap_isSplitEpi X
  apply (cancel_epi c).1
  apply biproduct.hom_ext'
  intro p
  let Dp := P.supportPrimitiveIdempotentData X p.1 p.2
  let e := T.primitiveSinkIso Dp
  have hzero := P.hom_from_supportInjective_to_rightKernel_eq_zero
    hA H z p (e.inv ≫
      RightModule.primitiveInjectiveInclusion (k := k)
        (P.supportedIdempotent X p) ≫ q)
  have hzero' := hzero
  change e.inv ≫
    (RightModule.primitiveInjectiveInclusion (k := k)
      (P.supportedIdempotent X p) ≫ q) = 0 at hzero'
  have hinclusion := zero_of_epi_comp e.inv hzero'
  dsimp only [c, supportInjectiveAssemblyMap]
  rw [← Category.assoc, biproduct.ι_desc, comp_zero]
  exact hinclusion

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
