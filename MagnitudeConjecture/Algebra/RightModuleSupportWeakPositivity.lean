import MagnitudeConjecture.Algebra.RightModuleWeakPositivity
import MagnitudeConjecture.Algebra.RightModuleSupportCoordinate

/-!
# Sincerity detection in a literal support algebra

An ambient indecomposable whose projective support is the whole chosen
support quotient supplies the two map-detection properties used in Ringel's
global-dimension cycle argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

set_option maxHeartbeats 800000 in
/-- A supported indecomposable with the full chosen support detects the maps
from the injective cogenerator and into finite projectives that occur in
Ringel's proof of global dimension at most two. -/
theorem supportLabel_sincereDetectionData
    (hA : RightModule.IsRepresentationFinite k A)
    (X M : RightModule.FinitelyGeneratedCategory A)
    (hsub : S.projectiveSupport M ⊆ S.projectiveSupport X)
    (hM : Indecomposable M.obj)
    (hfull : S.projectiveSupport M = S.projectiveSupport X) :
    let T := P.supportAlgebraSkeleton hA X
    T.SincereDetectionData (P.supportLabel hA X M hsub hM) := by
  classical
  let T := P.supportAlgebraSkeleton hA X
  let w := P.supportLabel hA X M hsub hM
  let eW := P.supportFGObjIsoSkeletonFG hA X M hsub hM
  constructor
  · intro Y q hq
    let c := P.supportInjectiveAssemblyMap X
    letI : IsSplitEpi c := P.supportInjectiveAssemblyMap_isSplitEpi X
    have hcq : c ≫ q ≠ 0 := by
      intro hzero
      exact hq (zero_of_epi_comp c hzero)
    have hcomponent : ∃ p : SupportedProjectiveLabel (S := S) X,
        biproduct.ι
            (fun p : SupportedProjectiveLabel (S := S) X ↦
              RightModule.primitiveInjectiveFGObj (k := k)
                (P.supportedIdempotent X p)) p ≫ c ≫ q ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hcq
      apply biproduct.hom_ext'
      intro p
      simpa only [Category.assoc, comp_zero] using hall p
    obtain ⟨p, hp⟩ := hcomponent
    have hpM : p.1 ∈ S.projectiveSupport M := by
      rw [hfull]
      exact p.2
    let Dp : RightModule.PrimitiveIdempotentData
        (P.supportedIdempotent X p) := by
      simpa only [supportedIdempotent] using
        P.supportPrimitiveIdempotentData X p.1 p.2
    let eI := T.primitiveSinkIso Dp
    obtain ⟨fRaw, hfRaw⟩ :=
      P.exists_ne_zero_hom_from_supportFGObj_to_supportedPrimitiveInjective
        X M hsub p.1 p.2 hpM
    let f₀ : P.supportFGObj X M hsub ⟶
        RightModule.primitiveInjectiveFGObj (k := k)
          (P.supportedIdempotent X p) := by
      simpa only [supportedIdempotent] using fRaw
    have hf₀ : f₀ ≠ 0 := by
      intro hzero
      apply hfRaw
      simpa [f₀, supportedIdempotent] using hzero
    have hιc :
        biproduct.ι
            (fun p : SupportedProjectiveLabel (S := S) X ↦
              RightModule.primitiveInjectiveFGObj (k := k)
                (P.supportedIdempotent X p)) p ≫ c =
          RightModule.primitiveInjectiveInclusion (k := k)
            (P.supportedIdempotent X p) := by
      simp [c, supportInjectiveAssemblyMap]
    let g₀ : RightModule.primitiveInjectiveFGObj (k := k)
        (P.supportedIdempotent X p) ⟶ Y :=
      RightModule.primitiveInjectiveInclusion (k := k)
          (P.supportedIdempotent X p) ≫ q
    have hg₀ : g₀ ≠ 0 := by
      dsimp only [g₀]
      intro hzero
      apply hp
      rw [← Category.assoc, hιc, hzero]
    let f : T.fgObj w ⟶ T.fgObj (T.primitiveSinkLabel Dp) :=
      eW.inv ≫ f₀ ≫ eI.hom
    have hf : f ≠ 0 := by
      intro hzero
      apply hf₀
      apply zero_of_epi_comp eW.inv
      apply zero_of_comp_mono eI.hom
      simpa [f, Category.assoc] using hzero
    let g : T.fgObj (T.primitiveSinkLabel Dp) ⟶ Y :=
      eI.inv ≫ g₀
    have hg : g ≠ 0 := by
      intro hzero
      apply hg₀
      exact zero_of_epi_comp eI.inv hzero
    exact ⟨T.primitiveSinkLabel Dp, ⟨f, hf⟩, g, hg⟩
  · intro Q _hQProjective Y i hi
    letI : Module.Finite (P.SupportAlgebra X)ᵐᵒᵖ
        (P.SupportAlgebra X) :=
      Module.Finite.equiv
        (RightModule.rightRegularLinearEquiv (A := P.SupportAlgebra X))
    letI : Module.Projective (P.SupportAlgebra X)ᵐᵒᵖ Q :=
      moduleProjective_of_fgProjective Q (inferInstance : Projective Q)
    let frame := RightModule.finiteProjectiveFrame
      (P.SupportAlgebra X)ᵐᵒᵖ Q
    let phi (t : Fin frame.n) : Q ⟶
        RightModule.rightRegularFGObj (B := P.SupportAlgebra X) :=
      FGModuleCat.ofHom
        ((RightModule.rightRegularLinearEquiv
          (A := P.SupportAlgebra X)).toLinearMap.comp (frame.phi t))
    have hphi : ∃ t : Fin frame.n, i ≫ phi t ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hi
      apply FGModuleCat.hom_ext
      ext y
      change i.hom.hom y = 0
      rw [← frame.total (i.hom.hom y)]
      apply Finset.sum_eq_zero
      intro t _ht
      have ht := DFunLike.congr_fun
        (congrArg (fun f ↦ f.hom.hom) (hall t)) y
      have ht' : frame.phi t (i.hom.hom y) = 0 := by
        apply (RightModule.rightRegularLinearEquiv
          (A := P.SupportAlgebra X)).injective
        change (RightModule.rightRegularLinearEquiv
          (A := P.SupportAlgebra X)) (frame.phi t (i.hom.hom y)) = 0 at ht
        exact ht
      rw [ht', zero_smul]
    obtain ⟨t, ht⟩ := hphi
    let d := P.supportRegularDecompositionMap X
    letI : IsSplitMono d := P.supportRegularDecompositionMap_isSplitMono X
    have htd : i ≫ phi t ≫ d ≠ 0 := by
      intro hzero
      apply ht
      exact zero_of_comp_mono d (by simpa [Category.assoc] using hzero)
    have hcomponent : ∃ p : SupportedProjectiveLabel (S := S) X,
        i ≫ phi t ≫ d ≫
          biproduct.π
            (fun p : SupportedProjectiveLabel (S := S) X ↦
              RightModule.rightIdealFGObj (P.supportedIdempotent X p)) p ≠ 0 := by
      by_contra hall
      push Not at hall
      apply htd
      apply biproduct.hom_ext
      intro p
      simpa only [Category.assoc, comp_zero, zero_comp] using hall p
    obtain ⟨p, hp⟩ := hcomponent
    have hpM : p.1 ∈ S.projectiveSupport M := by
      rw [hfull]
      exact p.2
    let Dp : RightModule.PrimitiveIdempotentData
        (P.supportedIdempotent X p) := by
      simpa only [supportedIdempotent] using
        P.supportPrimitiveIdempotentData X p.1 p.2
    let eP := T.primitiveSourceIso Dp
    obtain ⟨gRaw, hgRaw⟩ :=
      P.exists_ne_zero_hom_from_supportedRightIdeal_to_supportFGObj
        X M hsub p.1 p.2 hpM
    let g₀ : RightModule.rightIdealFGObj (P.supportedIdempotent X p) ⟶
        P.supportFGObj X M hsub := by
      simpa only [supportedIdempotent] using gRaw
    have hg₀ : g₀ ≠ 0 := by
      intro hzero
      apply hgRaw
      simpa [g₀, supportedIdempotent] using hzero
    let a₀ : Y ⟶ RightModule.rightIdealFGObj
        (P.supportedIdempotent X p) :=
      i ≫ phi t ≫ d ≫
        biproduct.π
          (fun p : SupportedProjectiveLabel (S := S) X ↦
            RightModule.rightIdealFGObj (P.supportedIdempotent X p)) p
    have ha₀ : a₀ ≠ 0 := by
      exact hp
    let a : Y ⟶ T.fgObj (T.primitiveSourceLabel Dp) :=
      a₀ ≫ eP.hom
    have ha : a ≠ 0 := by
      intro hzero
      apply ha₀
      exact zero_of_comp_mono eP.hom hzero
    let b : T.fgObj (T.primitiveSourceLabel Dp) ⟶ T.fgObj w :=
      eP.inv ≫ g₀ ≫ eW.hom
    have hb : b ≠ 0 := by
      intro hzero
      apply hg₀
      apply zero_of_epi_comp eP.inv
      apply zero_of_comp_mono eW.hom
      simpa [b, Category.assoc] using hzero
    exact ⟨T.primitiveSourceLabel Dp, ⟨a, ha⟩, b, hb⟩

/-- The support algebra of a chosen right almost-split middle term contains
an actual selected indecomposable with the sincerity detection data. -/
theorem exists_rightSequenceSupport_sincereDetectionData
    (hA : RightModule.IsRepresentationFinite k A)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    let T := P.rightSequenceMiddleSupportSkeleton hA z
    ∃ w : Fin T.n, T.SincereDetectionData w := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  obtain ⟨w, hwfull, _hwterm⟩ :=
    S.exists_rightSequence_supportSincere_label z
  have hsub : S.projectiveSupport (S.fgObj w) ⊆
      S.projectiveSupport X := hwfull.le
  let wt := P.supportLabel hA X (S.fgObj w) hsub
    (S.obj_indecomposable w)
  refine ⟨wt, ?_⟩
  exact P.supportLabel_sincereDetectionData hA X (S.fgObj w) hsub
    (S.obj_indecomposable w) hwfull

/-- The Euler quadratic form of the literal middle-support algebra is
weakly positive, with no imported Ringel theorem assumption remaining. -/
theorem rightSequenceMiddleSupport_projectiveCartanInverse_weaklyPositive
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    let T := P.rightSequenceMiddleSupportSkeleton hA z
    ∀ x,
      CartanCoordinate.IsPositive x →
        1 ≤ CartanCoordinate.quadraticForm
          T.projectiveCartanInverse x := by
  let T := P.rightSequenceMiddleSupportSkeleton hA z
  obtain ⟨w, D⟩ :=
    P.exists_rightSequenceSupport_sincereDetectionData hA z
  exact T.projectiveCartanInverse_weaklyPositive_of_sincereDetection
    (P.rightSequenceMiddleSupportAcyclic hA H z) w D

/-- The two endpoints of a supported Auslander--Reiten sequence form the
literal positive-root/Coxeter pair required by the coordinate argument. -/
theorem rightSequenceSupportCartanRootPairData
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    let T := P.rightSequenceMiddleSupportSkeleton hA z
    T.SupportCartanRootPairData
      (P.rightSequenceMiddleSupportAcyclic hA H z)
      (P.rightSequenceSupportTargetLabel hA z)
      (P.rightSequenceSupportSourceLabel hA z) := by
  let T := P.rightSequenceMiddleSupportSkeleton hA z
  let HT := P.rightSequenceMiddleSupportAcyclic hA H z
  have hweak :=
    P.rightSequenceMiddleSupport_projectiveCartanInverse_weaklyPositive hA H z
  let D := T.supportWeaklyPositiveCartanData HT hweak
  have htarget := P.rightSequenceSupportTarget_quadraticForm_eq_one hA H z
  have hcoxeter := P.rightSequenceSupportSource_coxeter_translate hA H z
  refine
    { weaklyPositive := hweak
      source_root := htarget
      translated_root := ?_
      coxeter_translate := hcoxeter }
  rw [hcoxeter]
  exact (D.quadraticForm_coxeter
    (T.projectiveHomVector
      (P.rightSequenceSupportTargetLabel hA z))).trans htarget

/-- The literal middle-support Cartan package is available directly from
representation-finiteness, directedness, and algebraic closedness. -/
def middleSupportCartanData
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : RightModule.PrimitiveIdempotentData e) :
    S.MiddleSupportCartanData D :=
  P.middleSupportCartanDataOfRootPairs hA H D fun z ↦
    P.rightSequenceSupportCartanRootPairData hA H z

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
