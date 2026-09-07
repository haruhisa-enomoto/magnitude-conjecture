import MagnitudeConjecture.Algebra.RightModuleStableRepresentable
import MagnitudeConjecture.Algebra.RightModuleRepresentableImage
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleRejection
import MagnitudeConjecture.Algebra.RightModuleHoshinoTorsion
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecompositionUniqueness
import MagnitudeConjecture.CategoryTheory.AlmostSplitPullback
import QuotientSubmoduleEquidistribution.CategoryTheory.SplitMorphismComplement

/-!
# Two-arm successors for stable representables

This file formalizes the local step in Auslander--Reiten's proof of
Corollary 3.8.  A stable generator carries one incoming irreducible arm that
is already zero.  In a right almost-split middle term of arity at most two,
that arm splits off and leaves at most one nonzero indecomposable complement.
The opposite component of the almost-split kernel supplies the killed arm at
the next stage.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

private theorem finiteIndecomposableDecomposition_n_pos
    {X : RightModule.FinitelyGeneratedCategory A}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X)
    (hX : ¬ IsZero X) :
    0 < d.n := by
  by_contra hn
  have hnzero : d.n = 0 := Nat.eq_zero_of_not_pos hn
  have hsum : IsZero (⨁ d.summand) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact Fin.elim0 (hnzero ▸ i)
  exact hX (hsum.of_iso d.isoBiproduct)

include k in
/-- A nonzero finitely generated module admitting a displayed
indecomposable decomposition with at most one occurrence is indecomposable. -/
theorem finiteIndecomposableDecomposition_indecomposable_of_n_le_one
    {X : RightModule.FinitelyGeneratedCategory A}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X)
    (hd : d.n ≤ 1) (hX : ¬ IsZero X) :
    Indecomposable X := by
  refine ⟨hX, ?_⟩
  intro Y Z e
  by_cases hY : IsZero Y
  · exact Or.inl hY
  by_cases hZ : IsZero Z
  · exact Or.inr hZ
  letI : Module.Finite k Y :=
    RightModule.finite_over_field_of_finitelyGenerated k A Y
  letI : Module.Finite k Z :=
    RightModule.finite_over_field_of_finitelyGenerated k A Z
  obtain ⟨dY⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) Y
  obtain ⟨dZ⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) Z
  let dSum := dY.biprod dZ
  have hlocal (i : Fin d.n) : IsLocalRing (End (d.summand i)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (d.summand i) (d.indecomposable i)
  have hcount : d.n = dY.n + dZ.n :=
    d.n_eq_of_iso dSum hlocal e
  have hYpos : 0 < dY.n :=
    finiteIndecomposableDecomposition_n_pos dY hY
  have hZpos : 0 < dZ.n :=
    finiteIndecomposableDecomposition_n_pos dZ hZ
  omega

/-- The complementary component of a minimal right almost-split map is
irreducible once the complement is identified with a chosen indecomposable. -/
theorem splitMonoComplement_rightComponent_isIrreducible
    {x i : S.IndecCategory}
    {E : RightModule.FinitelyGeneratedCategory A}
    (f : E ⟶ S.fgObj i) (hf : IsRightAlmostSplit f)
    (hfmin : IsRightMinimal f)
    (t : S.fgObj x ⟶ E) [IsSplitMono t]
    (d : SplitMonoComplement t)
    (j : S.IndecCategory) (e : S.fgObj j ≅ d.complement) :
    IsIrreducibleMorphism (e.hom ≫ d.inclusion ≫ f) := by
  let inc : S.fgObj j ⟶ E := e.hom ≫ d.inclusion
  let proj : E ⟶ S.fgObj j := d.projection ≫ e.inv
  let g : S.fgObj j ⟶ S.fgObj i := inc ≫ f
  have hincproj : inc ≫ proj = 𝟙 (S.fgObj j) := by
    dsimp only [inc, proj]
    calc
      (e.hom ≫ d.inclusion) ≫ (d.projection ≫ e.inv) =
          e.hom ≫ (d.inclusion ≫ d.projection) ≫ e.inv := by
            simp only [Category.assoc]
      _ = e.hom ≫ e.inv := by rw [d.inclusion_projection]; simp
      _ = 𝟙 (S.fgObj j) := e.hom_inv_id
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    obtain ⟨se⟩ := hg.exists_splitEpi
    apply hf.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := se.section_ ≫ inc
        id := by simpa only [g, Category.assoc] using se.id }
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    letI : IsSplitMono g := hg
    letI : IsIso g :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        (S.fgObj_indecomposable i) g (S.fgObj_indecomposable j).1
    exact hnotepi inferInstance
  change IsIrreducibleMorphism g
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  obtain ⟨q, hq⟩ := hf.factors b hb
  let u : E ⟶ E := 𝟙 E + proj ≫ (a ≫ q - inc)
  have huf : u ≫ f = f := by
    dsimp only [u]
    rw [Preadditive.add_comp, Category.id_comp,
      Category.assoc, Preadditive.sub_comp]
    have haq : (a ≫ q) ≫ f = g := by
      rw [Category.assoc, hq, hab]
    rw [haq]
    change f + proj ≫ (g - g) = f
    simp
  have hincu : inc ≫ u = a ≫ q := by
    dsimp only [u]
    rw [Preadditive.comp_add, Category.comp_id,
      ← Category.assoc, hincproj, Category.id_comp]
    abel
  letI : IsIso u := hfmin u huf
  exact Or.inl (IsSplitMono.mk'
    { retraction := q ≫ inv u ≫ proj
      id := by
        calc
          a ≫ (q ≫ inv u ≫ proj) =
              (a ≫ q) ≫ inv u ≫ proj := by
                simp only [Category.assoc]
          _ = (inc ≫ u) ≫ inv u ≫ proj := by rw [hincu]
          _ = 𝟙 (S.fgObj j) := by
                simp only [Category.assoc, IsIso.hom_inv_id_assoc,
                  hincproj] })

/-- Dually, projecting a minimal left almost-split map to the same
indecomposable complement gives the killed irreducible arm for the next
stable generator. -/
theorem splitMonoComplement_leftComponent_isIrreducible
    {source x : S.IndecCategory}
    {E : RightModule.FinitelyGeneratedCategory A}
    (a : S.fgObj source ⟶ E) (ha : IsLeftAlmostSplit a)
    (hamin : IsLeftMinimal a)
    (t : S.fgObj x ⟶ E) [IsSplitMono t]
    (d : SplitMonoComplement t)
    (j : S.IndecCategory) (e : S.fgObj j ≅ d.complement) :
    IsIrreducibleMorphism (a ≫ d.projection ≫ e.inv) := by
  let inc : S.fgObj j ⟶ E := e.hom ≫ d.inclusion
  let proj : E ⟶ S.fgObj j := d.projection ≫ e.inv
  let g : S.fgObj source ⟶ S.fgObj j := a ≫ proj
  have hincproj : inc ≫ proj = 𝟙 (S.fgObj j) := by
    dsimp only [inc, proj]
    calc
      (e.hom ≫ d.inclusion) ≫ (d.projection ≫ e.inv) =
          e.hom ≫ (d.inclusion ≫ d.projection) ≫ e.inv := by
            simp only [Category.assoc]
      _ = e.hom ≫ e.inv := by rw [d.inclusion_projection]; simp
      _ = 𝟙 (S.fgObj j) := e.hom_inv_id
  have hnotmono : ¬ IsSplitMono g := by
    intro hg
    obtain ⟨sm⟩ := hg.exists_splitMono
    apply ha.not_isSplitMono
    exact IsSplitMono.mk'
      { retraction := proj ≫ sm.retraction
        id := by simpa only [g, Category.assoc] using sm.id }
  have hnotepi : ¬ IsSplitEpi g := by
    intro hg
    letI : IsSplitEpi g := hg
    letI : IsIso g :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
        (S.fgObj_indecomposable source) g (S.fgObj_indecomposable j).1
    exact hnotmono inferInstance
  change IsIrreducibleMorphism g
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M p q hpq
  by_cases hp : IsSplitMono p
  · exact Or.inl hp
  obtain ⟨r, hr⟩ := ha.factors p hp
  let v : E ⟶ E := 𝟙 E + (r ≫ q - proj) ≫ inc
  have hav : a ≫ v = a := by
    dsimp only [v]
    rw [Preadditive.comp_add, Category.comp_id,
      ← Category.assoc, Preadditive.comp_sub]
    have hrq : a ≫ (r ≫ q) = g := by
      rw [← Category.assoc, hr, hpq]
    rw [hrq]
    change a + (g - g) ≫ inc = a
    simp
  have hvproj : v ≫ proj = r ≫ q := by
    dsimp only [v]
    rw [Preadditive.add_comp, Category.id_comp,
      Category.assoc, hincproj, Category.comp_id]
    abel
  letI : IsIso v := hamin v hav
  exact Or.inr (IsSplitEpi.mk'
    { section_ := inc ≫ inv v ≫ r
      id := by
        calc
          (inc ≫ inv v ≫ r) ≫ q =
              inc ≫ inv v ≫ (r ≫ q) := by
                simp only [Category.assoc]
          _ = inc ≫ inv v ≫ (v ≫ proj) := by rw [← hvproj]
          _ = 𝟙 (S.fgObj j) := by
                simp only [IsIso.inv_hom_id_assoc, hincproj] })

/-- A cyclic stable image is on the Auslander--Reiten chain when one
irreducible incoming arrow is already killed in the stable quotient. -/
def IsStableChainGenerator
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) : Prop :=
  ∃ (x : S.IndecCategory) (d : S.fgObj x ⟶ S.fgObj i),
    IsIrreducibleMorphism d ∧
      S.finiteRestrictedContravariantRepresentableMap d ≫
      S.finiteRestrictedToProjectiveStableMap i h = 0

/-- A cyclic image of an arbitrary finite functor is on the
Auslander--Reiten chain when one irreducible incoming arm is killed by its
generating map. -/
def IsRepresentableChainGenerator
    {G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (i : S.IndecCategory)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G) : Prop :=
  ∃ (x : S.IndecCategory) (d : S.fgObj x ⟶ S.fgObj i),
    IsIrreducibleMorphism d ∧
      S.finiteRestrictedContravariantRepresentableMap d ≫ p = 0

/-- If the radical of a cyclic stable image is nonzero, the two-arm bound
makes the source label of an irreducible incoming arm killed by the generator
unique.  One killed arm splits from the right almost-split middle; its
complement is the nonzero radical-generating arm, so a second killed arm cannot
split through that complement. -/
theorem killedIrreducible_source_eq_of_nonzero_stableImageRadical
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hRzero : ¬ IsZero
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
            S.finiteProjectiveStableImagePresentation i h) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)))
    (x : S.IndecCategory) (d : S.fgObj x ⟶ S.fgObj i)
    (hd : IsIrreducibleMorphism d)
    (hdzero : S.finiteRestrictedContravariantRepresentableMap d ≫
      S.finiteRestrictedToProjectiveStableMap i h = 0)
    (x' : S.IndecCategory) (d' : S.fgObj x' ⟶ S.fgObj i)
    (hd' : IsIrreducibleMorphism d')
    (hdzero' : S.finiteRestrictedContravariantRepresentableMap d' ≫
      S.finiteRestrictedToProjectiveStableMap i h = 0) :
    x' = x := by
  let R := imageSubobject
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
      S.finiteProjectiveStableImagePresentation i h)
  let B := S.minimalRightAlmostSplitAt i
  let b : B.middle ⟶ S.fgObj i := B.map
  obtain ⟨t, ht⟩ := B.rightAlmostSplit.factors d hd.not_isSplitEpi
  have htSplit : IsSplitMono t :=
    (hd.factorization t b ht).resolve_right B.rightAlmostSplit.not_isSplitEpi
  letI : IsSplitMono t := htSplit
  let D := splitMonoComplement t
  let qComp :=
    S.finiteRestrictedContravariantRepresentableMap (D.inclusion ≫ b) ≫
      S.finiteProjectiveStableImagePresentation i h
  have hdPresentation :
      S.finiteRestrictedContravariantRepresentableMap d ≫
          S.finiteProjectiveStableImagePresentation i h = 0 := by
    apply (cancel_mono (S.finiteProjectiveStableImageInclusion i h)).1
    rw [Category.assoc,
      S.finiteProjectiveStableImagePresentation_comp_inclusion,
      hdzero, zero_comp]
  have htPresentation :
      S.finiteRestrictedContravariantRepresentableMap (t ≫ b) ≫
          S.finiteProjectiveStableImagePresentation i h = 0 := by
    change t ≫ b = d at ht
    rw [ht]
    exact hdPresentation
  have hwhole :=
    S.finiteRestrictedContravariantRepresentableMap_comp_eq_complement
      t D b (S.finiteProjectiveStableImagePresentation i h) htPresentation
  change S.finiteRestrictedContravariantRepresentableMap b ≫
      S.finiteProjectiveStableImagePresentation i h =
    S.finiteRestrictedContravariantRepresentableMap D.projection ≫ qComp at hwhole
  have hRas : R = imageSubobject
      (S.finiteRestrictedContravariantRepresentableMap b ≫
        S.finiteProjectiveStableImagePresentation i h) :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      i b B.rightAlmostSplit
        (S.finiteProjectiveStableImagePresentation i h)
  have hDnonzero : ¬ IsZero D.complement := by
    intro hD
    have hIncl : D.inclusion = 0 := hD.eq_of_src _ _
    have hqComp : qComp = 0 := by
      dsimp only [qComp]
      rw [hIncl, zero_comp,
        S.finiteRestrictedContravariantRepresentableMap_zero, zero_comp]
    apply hRzero
    change IsZero (R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k)
    rw [hRas, hwhole, hqComp, comp_zero, imageSubobject_zero]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  let dB := S.minimalRightAlmostSplitAtDecomposition i
  letI : Module.Finite k D.complement :=
    RightModule.finite_over_field_of_finitelyGenerated k A D.complement
  obtain ⟨dD⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) D.complement
  let dOldOne :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (S.fgObj x) (S.fgObj_indecomposable x)
  let dSplit := dOldOne.biprod dD
  let eSplit : B.middle ≅ S.fgObj x ⊞ D.complement :=
    D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hlocalB (r : Fin dB.n) : IsLocalRing (End (dB.summand r)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (dB.summand r) (dB.indecomposable r)
  have hcount : dB.n = 1 + dD.n :=
    dB.n_eq_of_iso dSplit hlocalB eSplit
  have harityEq : FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData i = dB.n :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      S.finiteTauCategoryData.toFiniteRightTauCategoryData i dB
        B.rightAlmostSplit B.rightMinimal
  have hiNonprojective : ¬ Projective (S.fgObj i) := by
    intro hi
    have hiModule : Module.Projective Aᵐᵒᵖ (S.fgObj i) :=
      MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj i) hi
    letI : Module.Projective Aᵐᵒᵖ (S.fgObj i) := hiModule
    have hiObj : Projective (S.fgObj i).obj := inferInstance
    exact hstable
      (S.finiteRestrictedMap_comp_stableQuotient_eq_zero h hiObj)
  have hDle : dD.n ≤ 1 := by
    have hBle : dB.n ≤ 2 := by
      rw [← harityEq]
      exact harity i hiNonprojective
    omega
  have hDindec : Indecomposable D.complement :=
    finiteIndecomposableDecomposition_indecomposable_of_n_le_one
      (k := k) dD hDle hDnonzero
  obtain ⟨t', ht'⟩ := B.rightAlmostSplit.factors d' hd'.not_isSplitEpi
  have ht'Split : IsSplitMono t' :=
    (hd'.factorization t' b ht').resolve_right B.rightAlmostSplit.not_isSplitEpi
  let tSplit : S.fgObj x' ⟶ S.fgObj x ⊞ D.complement := t' ≫ eSplit.hom
  letI : IsSplitMono tSplit := by
    dsimp only [tSplit]
    letI : IsSplitMono t' := ht'Split
    infer_instance
  letI : IsLocalRing (End (S.fgObj x')) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (S.fgObj x') (S.fgObj_indecomposable x')
  rcases
      MagnitudeConjecture.CategoryTheory.splitMono_fst_or_snd_of_splitMono_to_biprod
        tSplit with hleft | hright
  · let left : S.fgObj x' ⟶ S.fgObj x := tSplit ≫ biprod.fst
    letI : IsSplitMono left := hleft
    let hleftIso : IsIso left :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        (S.fgObj_indecomposable x) left (S.fgObj_indecomposable x').1
    exact S.fgObj_skeletal ⟨@asIso _ _ _ _ left hleftIso⟩
  · let right : S.fgObj x' ⟶ D.complement := tSplit ≫ biprod.snd
    letI : IsSplitMono right := hright
    let rightIso : IsIso right :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        hDindec right (S.fgObj_indecomposable x').1
    letI : IsIso right := rightIso
    have heSplitFst : eSplit.hom ≫ biprod.fst = retraction t :=
      D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso_hom_comp
        (BinaryBiproduct.isLimit _ _) (Discrete.mk WalkingPair.left)
    have heSplitSnd : eSplit.hom ≫ biprod.snd = D.projection :=
      D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso_hom_comp
        (BinaryBiproduct.isLimit _ _) (Discrete.mk WalkingPair.right)
    let left : S.fgObj x' ⟶ S.fgObj x := t' ≫ retraction t
    have hright : right = t' ≫ D.projection := by
      dsimp only [right, tSplit]
      rw [Category.assoc, heSplitSnd]
    have ht'Decomp : t' = left ≫ t + right ≫ D.inclusion := by
      dsimp only [left]
      rw [hright]
      calc
        t' = t' ≫ 𝟙 B.middle := by rw [Category.comp_id]
        _ = t' ≫ (retraction t ≫ t + D.projection ≫ D.inclusion) := by
          rw [D.total]
        _ = _ := by simp only [Preadditive.comp_add, Category.assoc]
    have hd'Presentation :
        S.finiteRestrictedContravariantRepresentableMap d' ≫
            S.finiteProjectiveStableImagePresentation i h = 0 := by
      apply (cancel_mono (S.finiteProjectiveStableImageInclusion i h)).1
      rw [Category.assoc,
        S.finiteProjectiveStableImagePresentation_comp_inclusion,
        hdzero', zero_comp]
    have ht'Presentation :
        S.finiteRestrictedContravariantRepresentableMap (t' ≫ b) ≫
            S.finiteProjectiveStableImagePresentation i h = 0 := by
      change t' ≫ b = d' at ht'
      rw [ht']
      exact hd'Presentation
    have ht'b : t' ≫ b =
        left ≫ (t ≫ b) + right ≫ (D.inclusion ≫ b) := by
      rw [ht'Decomp, Preadditive.add_comp]
      simp only [Category.assoc]
    have hrightQ :
        S.finiteRestrictedContravariantRepresentableMap right ≫ qComp = 0 := by
      rw [ht'b,
        S.finiteRestrictedContravariantRepresentableMap_add,
        Preadditive.add_comp,
        S.finiteRestrictedContravariantRepresentableMap_comp,
        S.finiteRestrictedContravariantRepresentableMap_comp,
        Category.assoc, htPresentation, comp_zero, zero_add] at ht'Presentation
      rw [S.finiteRestrictedContravariantRepresentableMap_comp,
        S.finiteRestrictedContravariantRepresentableMap_comp] at ht'Presentation
      rw [← S.finiteRestrictedContravariantRepresentableMap_comp
        tSplit biprod.snd] at ht'Presentation
      change S.finiteRestrictedContravariantRepresentableMap right ≫ qComp = 0
        at ht'Presentation
      exact ht'Presentation
    have hmapRightIso : IsIso
        (S.finiteRestrictedContravariantRepresentableMap right) := by
      infer_instance
    letI : IsIso (S.finiteRestrictedContravariantRepresentableMap right) :=
      hmapRightIso
    have hqComp : qComp = 0 := by
      apply (cancel_epi
        (S.finiteRestrictedContravariantRepresentableMap right)).1
      simpa only [comp_zero] using hrightQ
    exfalso
    apply hRzero
    change IsZero (R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k)
    rw [hRas, hwhole, hqComp, comp_zero, imageSubobject_zero]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

/-- The two-arm successor step depends only on a cyclic representable image,
not on the stable-representable origin of its ambient finite functor. -/
theorem exists_representableChainGenerator_radicalSuccessor
    (harity : ∀ (i : S.IndecCategory),
      ¬ Projective (S.fgObj i) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2)
    {G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (i : S.IndecCategory)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
    (hgood : S.IsRepresentableChainGenerator i p)
    (hp : p ≠ 0)
    (hiNonprojective : ¬ Projective (S.fgObj i))
    (hRzero : ¬ IsZero
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
            S.finiteRepresentableImagePresentation i p) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k))) :
    ∃ (j : S.IndecCategory)
      (q : S.finiteRestrictedContravariantRepresentable (S.fgObj j) ⟶ G),
      S.IsRepresentableChainGenerator j q ∧ q ≠ 0 ∧
        Nonempty
          ((imageSubobject
                (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
                  S.finiteRepresentableImagePresentation i p) :
              CoveringHom.FiniteDimensionalModuleCategory
                (C := S.IndecCategoryᵒᵖ) k) ≅
            S.finiteRepresentableImage j q) := by
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let R := imageSubobject
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
      S.finiteRepresentableImagePresentation i p)
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    ⟨i, hiNonprojective⟩
  let B := S.minimalRightAlmostSplitAt i
  let b : B.middle ⟶ S.fgObj i := B.map
  have hbAlmostSplit : IsRightAlmostSplit b := B.rightAlmostSplit
  have hbMinimal : IsRightMinimal b := B.rightMinimal
  obtain ⟨x, dOld, hdOld, hOldZero⟩ := hgood
  obtain ⟨t, ht⟩ := hbAlmostSplit.factors dOld hdOld.not_isSplitEpi
  have htSplit : IsSplitMono t :=
    (hdOld.factorization t b ht).resolve_right
      hbAlmostSplit.not_isSplitEpi
  letI : IsSplitMono t := htSplit
  let D := splitMonoComplement t
  let qComp :=
    S.finiteRestrictedContravariantRepresentableMap
        (D.inclusion ≫ b) ≫
      S.finiteRepresentableImagePresentation i p
  have hOldPresentation :
      S.finiteRestrictedContravariantRepresentableMap dOld ≫
          S.finiteRepresentableImagePresentation i p = 0 := by
    apply (cancel_mono (S.finiteRepresentableImageInclusion i p)).1
    rw [Category.assoc,
      S.finiteRepresentableImagePresentation_comp_inclusion,
      hOldZero, zero_comp]
  have htPresentation :
      S.finiteRestrictedContravariantRepresentableMap (t ≫ b) ≫
          S.finiteRepresentableImagePresentation i p = 0 := by
    rw [ht]
    exact hOldPresentation
  have hwhole :=
    S.finiteRestrictedContravariantRepresentableMap_comp_eq_complement
      t D b (S.finiteRepresentableImagePresentation i p) htPresentation
  let mapProjection :=
    S.finiteRestrictedContravariantRepresentableMap D.projection
  letI : IsSplitEpi mapProjection := by
    apply IsSplitEpi.mk'
    refine
      { section_ :=
          S.finiteRestrictedContravariantRepresentableMap D.inclusion
        id := ?_ }
    dsimp only [mapProjection]
    rw [← S.finiteRestrictedContravariantRepresentableMap_comp,
      D.inclusion_projection,
      S.finiteRestrictedContravariantRepresentableMap_id]
  have hRas : R = imageSubobject
      (S.finiteRestrictedContravariantRepresentableMap b ≫
        S.finiteRepresentableImagePresentation i p) :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      i b hbAlmostSplit (S.finiteRepresentableImagePresentation i p)
  have hRcomp : R = imageSubobject qComp := by
    rw [hRas, hwhole]
    exact imageSubobject_comp_eq_of_epi mapProjection qComp
  have hDnonzero : ¬ IsZero D.complement := by
    intro hD
    have hIncl : D.inclusion = 0 := hD.eq_of_src _ _
    have hbranchzero : D.inclusion ≫ b =
        (0 : D.complement ⟶ S.fgObj i) := by
      simpa only [hIncl, zero_comp]
    have hqComp : qComp = 0 := by
      dsimp only [qComp]
      rw [hbranchzero,
        S.finiteRestrictedContravariantRepresentableMap_zero, zero_comp]
    apply hRzero
    change IsZero (R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k)
    rw [hRcomp, hqComp, imageSubobject_zero]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  let dB := S.minimalRightAlmostSplitAtDecomposition i
  letI : Module.Finite k D.complement :=
    RightModule.finite_over_field_of_finitelyGenerated k A D.complement
  obtain ⟨dD⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) D.complement
  let dOldOne :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (S.fgObj x) (S.fgObj_indecomposable x)
  let dSplit := dOldOne.biprod dD
  let eSplit : B.middle ≅ S.fgObj x ⊞ D.complement :=
    D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hlocalB (r : Fin dB.n) : IsLocalRing (End (dB.summand r)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (dB.summand r) (dB.indecomposable r)
  have hcount : dB.n = 1 + dD.n :=
    dB.n_eq_of_iso dSplit hlocalB eSplit
  have harityEq : FiniteTauMatrix.rightMiddleArity T i = dB.n :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T i dB B.rightAlmostSplit B.rightMinimal
  have hDle : dD.n ≤ 1 := by
    have hBle : dB.n ≤ 2 := by
      rw [← harityEq]
      exact harity i hiNonprojective
    omega
  have hDindec : Indecomposable D.complement :=
    finiteIndecomposableDecomposition_indecomposable_of_n_le_one
      (k := k) dD hDle hDnonzero
  obtain ⟨j, ⟨eD⟩⟩ := S.fgObj_complete D.complement hDindec
  let e : S.fgObj j ≅ D.complement := eD.symm
  let path : S.fgObj j ⟶ S.fgObj i :=
    e.hom ≫ D.inclusion ≫ b
  let q : S.finiteRestrictedContravariantRepresentable (S.fgObj j) ⟶ G :=
    S.finiteRestrictedContravariantRepresentableMap path ≫ p
  let qJ := S.finiteRestrictedContravariantRepresentableMap e.hom ≫ qComp
  let m := S.finiteRepresentableImageInclusion i p
  letI : Mono m := by
    dsimp only [m]
    infer_instance
  have hpresentation :
      S.finiteRepresentableImagePresentation i p ≫ m = p :=
    S.finiteRepresentableImagePresentation_comp_inclusion i p
  have hqJm : qJ ≫ m = q := by
    calc
      qJ ≫ m =
          S.finiteRestrictedContravariantRepresentableMap e.hom ≫
            S.finiteRestrictedContravariantRepresentableMap
                (D.inclusion ≫ b) ≫ p := by
          dsimp only [qJ, qComp]
          simp only [Category.assoc, hpresentation]
      _ = S.finiteRestrictedContravariantRepresentableMap path ≫ p := by
          dsimp only [path]
          rw [← Category.assoc,
            ← S.finiteRestrictedContravariantRepresentableMap_comp]
      _ = q := rfl
  have hqJImage : imageSubobject qJ = imageSubobject qComp := by
    dsimp only [qJ]
    exact imageSubobject_iso_comp _ _
  let eR : (R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k) ≅
      (imageSubobject qJ : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
    eqToIso (congrArg
      (fun Q : Subobject (S.finiteRepresentableImage i p) ↦
        (Q : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k))
      (hRcomp.trans hqJImage.symm))
  have hq : q ≠ 0 := by
    intro hzero
    have hqJzero : qJ = 0 := by
      apply (cancel_mono m).1
      rw [hqJm, hzero, zero_comp]
    apply hRzero
    have hImageZero : IsZero
        ((imageSubobject qJ : Subobject (S.finiteRepresentableImage i p)) :
          CoveringHom.FiniteDimensionalModuleCategory
            (C := S.IndecCategoryᵒᵖ) k) := by
      apply IsZero.of_mono_eq_zero (imageSubobject qJ).arrow
      apply (cancel_epi (factorThruImageSubobject qJ)).1
      rw [imageSubobject_arrow_comp, comp_zero]
      exact hqJzero
    exact hImageZero.of_iso eR
  have hright : IsIrreducibleMorphism path :=
    S.splitMonoComplement_rightComponent_isIrreducible
      b hbAlmostSplit hbMinimal t D j e
  let a : S.fgObj (S.rightTranslationLabel z) ⟶ B.middle :=
    S.rightKernelMap z
  let c : S.fgObj (S.rightTranslationLabel z) ⟶ S.fgObj j :=
    a ≫ D.projection ≫ e.inv
  have hleft : IsIrreducibleMorphism c :=
    S.splitMonoComplement_leftComponent_isIrreducible
      a (S.rightKernelMap_leftAlmostSplit z)
        (S.rightKernelMap_leftMinimal z) t D j e
  have haB : a ≫ b = 0 := by
    dsimp only [a, rightKernelMap]
    change ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map) ≫
      B.map = 0
    simp
  have hsum :
      a ≫ retraction t ≫ t ≫ b +
          a ≫ D.projection ≫ D.inclusion ≫ b = 0 := by
    calc
      a ≫ retraction t ≫ t ≫ b +
          a ≫ D.projection ≫ D.inclusion ≫ b =
          a ≫ (retraction t ≫ t +
            D.projection ≫ D.inclusion) ≫ b := by
              simp only [Preadditive.comp_add, Preadditive.add_comp,
                Category.assoc]
      _ = a ≫ b := by
        rw [D.total]
        simp only [Category.id_comp, Category.comp_id]
      _ = 0 := haB
  have hcpath : c ≫ path =
      -(a ≫ retraction t ≫ (t ≫ b)) := by
    have hrelation :
        a ≫ D.projection ≫ D.inclusion ≫ b =
          -(a ≫ retraction t ≫ t ≫ b) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa only [add_comm] using hsum
    dsimp only [c, path]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hrelation
  have htP :
      S.finiteRestrictedContravariantRepresentableMap (t ≫ b) ≫ p = 0 := by
    rw [ht]
    exact hOldZero
  have hnextZero :
      S.finiteRestrictedContravariantRepresentableMap c ≫ q = 0 := by
    dsimp only [q]
    rw [← Category.assoc,
      ← S.finiteRestrictedContravariantRepresentableMap_comp, hcpath,
      S.finiteRestrictedContravariantRepresentableMap_neg]
    rw [S.finiteRestrictedContravariantRepresentableMap_comp,
      S.finiteRestrictedContravariantRepresentableMap_comp]
    simp only [Preadditive.neg_comp, neg_eq_zero, Category.assoc,
      htP, comp_zero]
  refine ⟨j, q, ⟨S.rightTranslationLabel z, c, hleft, hnextZero⟩,
    hq, ?_⟩
  let eMono := imageSubobjectCompMonoIso qJ m
  let eTarget :
      (imageSubobject (qJ ≫ m) :
          CoveringHom.FiniteDimensionalModuleCategory
            (C := S.IndecCategoryᵒᵖ) k) ≅
        S.finiteRepresentableImage j q :=
    eqToIso (by rw [hqJm]; rfl)
  exact ⟨eR ≪≫ eMono ≪≫ eTarget⟩

/-- If nonzero maps into a fixed finite functor can only be generated at
nonprojective module labels, the two-arm bound makes every chain-generated
cyclic image uniserial. -/
theorem finiteRepresentableImage_isUniserial_of_twoArm
    (harity : ∀ (i : S.IndecCategory),
      ¬ Projective (S.fgObj i) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2)
    {G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (hsupport : ∀ (i : S.IndecCategory)
      (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G),
      p ≠ 0 → ¬ Projective (S.fgObj i))
    (i : S.IndecCategory)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
    (hgood : S.IsRepresentableChainGenerator i p)
    (hp : p ≠ 0) :
    IsUniserialObject (S.finiteRepresentableImage i p) := by
  exact S.finiteRepresentableImage_isUniserial_of_closedRadicalSuccessors
    S.IsRepresentableChainGenerator
    (fun i p hgood hp hRzero ↦
      S.exists_representableChainGenerator_radicalSuccessor
        harity i p hgood hp (hsupport i p hp) hRzero)
    i p hgood hp

/-- The local Auslander--Reiten successor step.  Under a two-summand bound
on right almost-split middles, every nonzero radical stage of a chain
generator is another cyclic stable image carrying its next killed arm. -/
theorem exists_stableChainGenerator_radicalSuccessor
    (harity : ∀ (i : S.IndecCategory),
      ¬ Projective (S.fgObj i) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2)
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hgood : S.IsStableChainGenerator i h)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hRzero : ¬ IsZero
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
            S.finiteProjectiveStableImagePresentation i h) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k))) :
    ∃ (j : S.IndecCategory) (g : S.fgObj j ⟶ C),
      S.IsStableChainGenerator j g ∧
        S.finiteRestrictedToProjectiveStableMap j g ≠ 0 ∧
        Nonempty
          ((imageSubobject
                (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
                  S.finiteProjectiveStableImagePresentation i h) :
              CoveringHom.FiniteDimensionalModuleCategory
                (C := S.IndecCategoryᵒᵖ) k) ≅
            S.finiteProjectiveStableImage j g) := by
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let R := imageSubobject
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
      S.finiteProjectiveStableImagePresentation i h)
  have hiNonprojective : ¬ Projective (S.fgObj i) := by
    intro hi
    have hiModule : Module.Projective Aᵐᵒᵖ (S.fgObj i) :=
      MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj i) hi
    letI : Module.Projective Aᵐᵒᵖ (S.fgObj i) := hiModule
    have hiObj : Projective (S.fgObj i).obj := inferInstance
    exact hstable
      (S.finiteRestrictedMap_comp_stableQuotient_eq_zero h hiObj)
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    ⟨i, hiNonprojective⟩
  let B := S.minimalRightAlmostSplitAt i
  let b : B.middle ⟶ S.fgObj i := B.map
  have hbAlmostSplit : IsRightAlmostSplit b := B.rightAlmostSplit
  have hbMinimal : IsRightMinimal b := B.rightMinimal
  obtain ⟨x, dOld, hdOld, hOldZero⟩ := hgood
  obtain ⟨t, ht⟩ := hbAlmostSplit.factors dOld hdOld.not_isSplitEpi
  have htSplit : IsSplitMono t :=
    (hdOld.factorization t b ht).resolve_right
      hbAlmostSplit.not_isSplitEpi
  letI : IsSplitMono t := htSplit
  let D := splitMonoComplement t
  let qComp :=
    S.finiteRestrictedContravariantRepresentableMap
        (D.inclusion ≫ b) ≫
      S.finiteProjectiveStableImagePresentation i h
  have hOldPresentation :
      S.finiteRestrictedContravariantRepresentableMap dOld ≫
          S.finiteProjectiveStableImagePresentation i h = 0 := by
    change
      S.finiteRestrictedContravariantRepresentableMap dOld ≫
          factorThruImageSubobject
            (S.finiteRestrictedToProjectiveStableMap i h) = 0
    apply (cancel_mono
      (imageSubobject
        (S.finiteRestrictedToProjectiveStableMap i h)).arrow).1
    rw [Category.assoc, imageSubobject_arrow_comp, hOldZero, zero_comp]
  have htPresentation :
      S.finiteRestrictedContravariantRepresentableMap (t ≫ b) ≫
          S.finiteProjectiveStableImagePresentation i h = 0 := by
    rw [ht]
    exact hOldPresentation
  have hwhole :=
    S.finiteRestrictedContravariantRepresentableMap_comp_eq_complement
      t D b (S.finiteProjectiveStableImagePresentation i h)
        htPresentation
  let mapProjection :=
    S.finiteRestrictedContravariantRepresentableMap D.projection
  letI : IsSplitEpi mapProjection := by
    apply IsSplitEpi.mk'
    refine
      { section_ :=
          S.finiteRestrictedContravariantRepresentableMap D.inclusion
        id := ?_ }
    dsimp only [mapProjection]
    rw [← S.finiteRestrictedContravariantRepresentableMap_comp,
      D.inclusion_projection,
      S.finiteRestrictedContravariantRepresentableMap_id]
  have hRas : R = imageSubobject
      (S.finiteRestrictedContravariantRepresentableMap b ≫
        S.finiteProjectiveStableImagePresentation i h) :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      i b hbAlmostSplit
        (S.finiteProjectiveStableImagePresentation i h)
  have hRcomp : R = imageSubobject qComp := by
    rw [hRas, hwhole]
    exact imageSubobject_comp_eq_of_epi mapProjection qComp
  have hDnonzero : ¬ IsZero D.complement := by
    intro hD
    have hIncl : D.inclusion = 0 := hD.eq_of_src _ _
    have hbranchzero : D.inclusion ≫ b =
        (0 : D.complement ⟶ S.fgObj i) := by
      simpa only [hIncl, zero_comp]
    have hqComp : qComp = 0 := by
      dsimp only [qComp]
      rw [hbranchzero,
        S.finiteRestrictedContravariantRepresentableMap_zero, zero_comp]
    apply hRzero
    change IsZero (R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k)
    rw [hRcomp, hqComp, imageSubobject_zero]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  let dB := S.minimalRightAlmostSplitAtDecomposition i
  letI : Module.Finite k D.complement :=
    RightModule.finite_over_field_of_finitelyGenerated k A D.complement
  obtain ⟨dD⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) D.complement
  let dOldOne :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (S.fgObj x) (S.fgObj_indecomposable x)
  let dSplit := dOldOne.biprod dD
  let eSplit : B.middle ≅ S.fgObj x ⊞ D.complement :=
    D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hlocalB (r : Fin dB.n) : IsLocalRing (End (dB.summand r)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (dB.summand r) (dB.indecomposable r)
  have hcount : dB.n = 1 + dD.n :=
    dB.n_eq_of_iso dSplit hlocalB eSplit
  have harityEq : FiniteTauMatrix.rightMiddleArity T i = dB.n :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T i dB B.rightAlmostSplit B.rightMinimal
  have hDle : dD.n ≤ 1 := by
    have hBle : dB.n ≤ 2 := by
      rw [← harityEq]
      exact harity i hiNonprojective
    omega
  have hDindec : Indecomposable D.complement :=
    finiteIndecomposableDecomposition_indecomposable_of_n_le_one
      (k := k) dD hDle hDnonzero
  obtain ⟨j, ⟨eD⟩⟩ := S.fgObj_complete D.complement hDindec
  let e : S.fgObj j ≅ D.complement := eD.symm
  let path : S.fgObj j ⟶ S.fgObj i :=
    e.hom ≫ D.inclusion ≫ b
  let g : S.fgObj j ⟶ C := path ≫ h
  let qJ := S.finiteRestrictedContravariantRepresentableMap e.hom ≫ qComp
  let m := S.finiteProjectiveStableImageInclusion i h
  letI : Mono m := by
    dsimp only [m]
    infer_instance
  have hpresentation :
      S.finiteProjectiveStableImagePresentation i h ≫ m =
        S.finiteRestrictedToProjectiveStableMap i h := by
    exact S.finiteProjectiveStableImagePresentation_comp_inclusion i h
  have hqJm : qJ ≫ m =
      S.finiteRestrictedToProjectiveStableMap j g := by
    calc
      qJ ≫ m =
          S.finiteRestrictedContravariantRepresentableMap e.hom ≫
            S.finiteRestrictedContravariantRepresentableMap
                (D.inclusion ≫ b) ≫
              S.finiteRestrictedToProjectiveStableMap i h := by
          dsimp only [qJ, qComp]
          simp only [Category.assoc, hpresentation]
      _ = S.finiteRestrictedContravariantRepresentableMap
              (e.hom ≫ D.inclusion ≫ b) ≫
            S.finiteRestrictedToProjectiveStableMap i h := by
          rw [← Category.assoc,
            ← S.finiteRestrictedContravariantRepresentableMap_comp]
      _ = S.finiteRestrictedToProjectiveStableMap j
              ((e.hom ≫ D.inclusion ≫ b) ≫ h) :=
          S.finiteRestrictedContravariantRepresentableMap_comp_stableMap
            (e.hom ≫ D.inclusion ≫ b) h
      _ = S.finiteRestrictedToProjectiveStableMap j g := rfl
  have hqJImage : imageSubobject qJ = imageSubobject qComp := by
    dsimp only [qJ]
    exact imageSubobject_iso_comp _ _
  let eR : (R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k) ≅
      (imageSubobject qJ : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
    eqToIso (congrArg
      (fun Q : Subobject (S.finiteProjectiveStableImage i h) ↦
        (Q : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k))
      (hRcomp.trans hqJImage.symm))
  have hnextStable :
      S.finiteRestrictedToProjectiveStableMap j g ≠ 0 := by
    intro hzero
    have hqJzero : qJ = 0 := by
      apply (cancel_mono m).1
      rw [hqJm, hzero, zero_comp]
    apply hRzero
    have hImageZero : IsZero
        ((imageSubobject qJ : Subobject
            (S.finiteProjectiveStableImage i h)) :
          CoveringHom.FiniteDimensionalModuleCategory
            (C := S.IndecCategoryᵒᵖ) k) := by
      apply IsZero.of_mono_eq_zero (imageSubobject qJ).arrow
      apply (cancel_epi (factorThruImageSubobject qJ)).1
      rw [imageSubobject_arrow_comp, comp_zero]
      exact hqJzero
    exact hImageZero.of_iso eR
  have hright : IsIrreducibleMorphism path :=
    S.splitMonoComplement_rightComponent_isIrreducible
      b hbAlmostSplit hbMinimal t D j e
  let a : S.fgObj (S.rightTranslationLabel z) ⟶ B.middle :=
    S.rightKernelMap z
  let c : S.fgObj (S.rightTranslationLabel z) ⟶ S.fgObj j :=
    a ≫ D.projection ≫ e.inv
  have hleft : IsIrreducibleMorphism c :=
    S.splitMonoComplement_leftComponent_isIrreducible
      a (S.rightKernelMap_leftAlmostSplit z)
        (S.rightKernelMap_leftMinimal z) t D j e
  have haB : a ≫ b = 0 := by
    dsimp only [a, rightKernelMap]
    change ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map) ≫
      B.map = 0
    simp
  have hsum :
      a ≫ retraction t ≫ t ≫ b +
          a ≫ D.projection ≫ D.inclusion ≫ b = 0 := by
    calc
      a ≫ retraction t ≫ t ≫ b +
          a ≫ D.projection ≫ D.inclusion ≫ b =
          a ≫ (retraction t ≫ t +
            D.projection ≫ D.inclusion) ≫ b := by
              simp only [Preadditive.comp_add, Preadditive.add_comp,
                Category.assoc]
      _ = a ≫ b := by
        rw [D.total]
        simp only [Category.id_comp, Category.comp_id]
      _ = 0 := haB
  have hcpath : c ≫ path =
      -(a ≫ retraction t ≫ (t ≫ b)) := by
    have hrelation :
        a ≫ D.projection ≫ D.inclusion ≫ b =
          -(a ≫ retraction t ≫ t ≫ b) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa only [add_comm] using hsum
    dsimp only [c, path]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hrelation
  have htStable :
      S.finiteRestrictedContravariantRepresentableMap (t ≫ b) ≫
          S.finiteRestrictedToProjectiveStableMap i h = 0 := by
    rw [ht]
    exact hOldZero
  have hnextZero :
      S.finiteRestrictedContravariantRepresentableMap c ≫
          S.finiteRestrictedToProjectiveStableMap j g = 0 := by
    rw [← S.finiteRestrictedContravariantRepresentableMap_comp_stableMap
      path h]
    rw [← Category.assoc,
      ← S.finiteRestrictedContravariantRepresentableMap_comp, hcpath,
      S.finiteRestrictedContravariantRepresentableMap_neg]
    rw [S.finiteRestrictedContravariantRepresentableMap_comp,
      S.finiteRestrictedContravariantRepresentableMap_comp]
    simp only [Preadditive.neg_comp, neg_eq_zero, Category.assoc,
      htStable, comp_zero]
  refine ⟨j, g, ⟨S.rightTranslationLabel z, c, hleft, hnextZero⟩,
    hnextStable, ?_⟩
  let eMono := imageSubobjectCompMonoIso qJ m
  let eTarget :
      (imageSubobject (qJ ≫ m) :
          CoveringHom.FiniteDimensionalModuleCategory
            (C := S.IndecCategoryᵒᵖ) k) ≅
        S.finiteProjectiveStableImage j g :=
    eqToIso (by rw [hqJm]; rfl)
  exact ⟨eR ≪≫ eMono ≪≫ eTarget⟩

/-- Under the two-arm bound, every nonzero cyclic stable image already on the
Auslander--Reiten chain is uniserial. -/
theorem finiteProjectiveStableImage_isUniserial_of_twoArm
    (harity : ∀ (i : S.IndecCategory),
      ¬ Projective (S.fgObj i) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2)
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hgood : S.IsStableChainGenerator i h)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    IsUniserialObject (S.finiteProjectiveStableImage i h) := by
  exact S.finiteProjectiveStableImage_isUniserial_of_closedRadicalSuccessors
    S.IsStableChainGenerator
    (fun i h hgood hstable hRzero ↦
      S.exists_stableChainGenerator_radicalSuccessor
        harity i h hgood hstable hRzero)
    i h hgood hstable

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
