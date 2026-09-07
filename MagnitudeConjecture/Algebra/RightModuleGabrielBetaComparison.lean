import MagnitudeConjecture.Algebra.RightModuleBetaD4Boundary
import MagnitudeConjecture.Algebra.FiniteModuleDecomposition
import MagnitudeConjecture.Algebra.RightModuleInjectiveSocleQuotient
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecompositionUniqueness

/-!
# Gabriel's direct comparison of the two beta bounds

This file develops the local module argument excluding the injective `D4`
boundary fork forced by a failure of the opposite beta bound.  The first
step identifies the chosen minimal left almost-split middle term out of the
injective center with its socle quotient.  The three arms of the fork then
force that quotient to have at least three indecomposable summands.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

include k in
/-- A nonzero quotient of a finite module with simple top is
indecomposable. -/
theorem indecomposable_of_epi_from_simpleTop
    (P Y : RightModule.FinitelyGeneratedCategory A)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hY : ¬ IsZero Y)
    (f : P ⟶ Y) [Epi f] : Indecomposable Y := by
  have hsurjective : Function.Surjective f.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
  have hkerNeTop : f.hom.hom.ker ≠ ⊤ := by
    intro hker
    have hfLinear : f.hom.hom = 0 := LinearMap.ker_eq_top.mp hker
    have hfZero : f = 0 := by
      apply FGModuleCat.hom_ext
      exact hfLinear
    exact hY (IsZero.of_epi_eq_zero f hfZero)
  have hkerRad : f.hom.hom.ker ≤ Module.jacobson Aᵐᵒᵖ P :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
      hPtop hkerNeTop
  let Q : RightModule.FinitelyGeneratedCategory A :=
    RightModule.quotientFGObj P f.hom.hom.ker
  have hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q) :=
    isSimpleModule_top_quotient_of_le_jacobson
      f.hom.hom.ker hkerRad hPtop
  have hQ : Indecomposable Q :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := A) Q).1
      (IsUniserialModule.isIndecomposableModule_of_simpleTop hQtop)
  let e : Q ≅ Y :=
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ (f.hom.hom.quotKerEquivOfSurjective hsurjective)
  exact (CategoryTheory.indecomposable_iff_of_iso e).1 hQ

include k in
/-- An irreducible epimorphism from a finite module with simple top has
simple kernel.  This is the elementary local-module lemma in Gabriel's
boundary argument. -/
theorem simple_kernel_of_irreducible_epi_from_simpleTop
    (P Y : RightModule.FinitelyGeneratedCategory A)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hY : Indecomposable Y)
    (f : P ⟶ Y) (hf : IsIrreducibleMorphism f) [Epi f] :
    IsSimpleModule Aᵐᵒᵖ f.hom.hom.ker := by
  apply isSimpleModule_iff_isAtom.mpr
  have hkerNeBot : f.hom.hom.ker ≠ ⊥ := by
    intro hker
    have hinjective : Function.Injective f.hom.hom :=
      LinearMap.ker_eq_bot.mp hker
    letI : Mono f :=
      (IndecomposableSkeleton.fg_mono_iff_injective f).2 hinjective
    letI : IsIso f := isIso_of_mono_of_epi f
    exact hf.not_isSplitMono inferInstance
  refine ⟨hkerNeBot, ?_⟩
  intro L hLlt
  by_contra hLNeBot
  have hkerNeTop : f.hom.hom.ker ≠ ⊤ := by
    intro hker
    have hfLinear : f.hom.hom = 0 := LinearMap.ker_eq_top.mp hker
    have hfZero : f = 0 := by
      apply FGModuleCat.hom_ext
      exact hfLinear
    exact hY.1 (IsZero.of_epi_eq_zero f hfZero)
  have hLrad : L ≤ Module.jacobson Aᵐᵒᵖ P :=
    (hLlt.le.trans <|
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
        hPtop hkerNeTop)
  let Q : RightModule.FinitelyGeneratedCategory A :=
    RightModule.quotientFGObj P L
  let qLinear : P →ₗ[Aᵐᵒᵖ] Q := RightModule.quotientFGMkQ P L
  let q : P ⟶ Q := FGModuleCat.ofHom qLinear
  let hLinear : Q →ₗ[Aᵐᵒᵖ] Y :=
    RightModule.quotientFGLift P Y L f.hom.hom hLlt.le
  let h : Q ⟶ Y := FGModuleCat.ofHom hLinear
  have hqh : q ≫ h = f := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact RightModule.quotientFGLift_apply_mkQ
      P Y L f.hom.hom hLlt.le x
  have hqNotSplit : ¬ IsSplitMono q := by
    intro hsplit
    letI : IsSplitMono q := hsplit
    have hqInjective : Function.Injective q.hom.hom :=
      (IndecomposableSkeleton.fg_mono_iff_injective q).1 inferInstance
    have hqKer : q.hom.hom.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr hqInjective
    apply hLNeBot
    rw [← Submodule.ker_mkQ L]
    exact hqKer
  have hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q) :=
    isSimpleModule_top_quotient_of_le_jacobson L hLrad hPtop
  have hQ : Indecomposable Q :=
    (RightModule.FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := A) Q).1
      (IsUniserialModule.isIndecomposableModule_of_simpleTop hQtop)
  have hhSplit : IsSplitEpi h :=
    (hf.factorization q h hqh).resolve_left hqNotSplit
  letI : IsSplitEpi h := hhSplit
  letI : IsIso h :=
    CategoryTheory.isIso_of_isSplitEpi_from_indecomposable hQ h hY.1
  have hhInjective : Function.Injective h.hom.hom :=
    (IndecomposableSkeleton.fg_mono_iff_injective h).1 inferInstance
  have hkerLeL : f.hom.hom.ker ≤ L := by
    intro x hx
    have hxComp : h.hom.hom (q.hom.hom x) = 0 := by
      have := congrArg (fun g ↦ g.hom.hom x) hqh
      simpa using this.trans hx
    have hxQ : q.hom.hom x = 0 := hhInjective <|
      hxComp.trans h.hom.hom.map_zero.symm
    exact (Submodule.Quotient.mk_eq_zero L).mp hxQ
  have hLeq : L = f.hom.hom.ker :=
    le_antisymm hLlt.le hkerLeL
  exact hLlt.ne hLeq

end MagnitudeConjecture

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The chosen minimal left almost-split middle term out of the injective
center of a boundary fork is its canonical socle quotient. -/
def InjectiveNonprojectiveD4Fork.leftMiddleIsoSocleQuotient
    (F : S.InjectiveNonprojectiveD4Fork) :
    (S.minimalLeftAlmostSplitAt F.center.1).middle ≅
      moduleSocleQuotientFGObj (S.fgObj F.center.1) := by
  let B := S.minimalLeftAlmostSplitAt F.center.1
  let I := S.fgObj F.center.1
  letI : Injective I := F.center_injective
  exact Classical.choose <| exists_leftAlmostSplit_middleIso
    B.leftAlmostSplit B.leftMinimal
      (moduleSocleQuotientProjection_isLeftAlmostSplit
        (k := k) I (S.fgObj_indecomposable F.center.1))
      (moduleSocleQuotientProjection_isLeftMinimal I)

/-- The comparison isomorphism intertwines the chosen minimal left
almost-split map with the canonical socle-quotient projection. -/
theorem InjectiveNonprojectiveD4Fork.leftMiddleIsoSocleQuotient_hom
    (F : S.InjectiveNonprojectiveD4Fork) :
    (S.minimalLeftAlmostSplitAt F.center.1).map ≫
        (F.leftMiddleIsoSocleQuotient S).hom =
      moduleSocleQuotientProjection (S.fgObj F.center.1) := by
  let B := S.minimalLeftAlmostSplitAt F.center.1
  let I := S.fgObj F.center.1
  letI : Injective I := F.center_injective
  exact Classical.choose_spec <| exists_leftAlmostSplit_middleIso
    B.leftAlmostSplit B.leftMinimal
      (moduleSocleQuotientProjection_isLeftAlmostSplit
        (k := k) I (S.fgObj_indecomposable F.center.1))
      (moduleSocleQuotientProjection_isLeftMinimal I)

/-- The factor of a fork arm through the canonical quotient by the
injective center's socle. -/
def InjectiveNonprojectiveD4Fork.outgoingSocleFactor
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    moduleSocleQuotientFGObj (S.fgObj F.center.1) ⟶
      S.fgObj (F.target j).1 := by
  let I := S.fgObj F.center.1
  letI : Injective I := F.center_injective
  exact Classical.choose <|
    (moduleSocleQuotientProjection_isLeftAlmostSplit
      (k := k) I (S.fgObj_indecomposable F.center.1)).factors
        (F.outgoingMap S j)
        (S.standardFormArrowMap_isIrreducible (F.arrow j)).not_isSplitMono

/-- Factoring a fork arm through the socle quotient recovers that arm. -/
theorem InjectiveNonprojectiveD4Fork.projection_comp_outgoingSocleFactor
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    moduleSocleQuotientProjection (S.fgObj F.center.1) ≫
        F.outgoingSocleFactor S j =
      F.outgoingMap S j := by
  let I := S.fgObj F.center.1
  letI : Injective I := F.center_injective
  exact Classical.choose_spec <|
    (moduleSocleQuotientProjection_isLeftAlmostSplit
      (k := k) I (S.fgObj_indecomposable F.center.1)).factors
        (F.outgoingMap S j)
        (S.standardFormArrowMap_isIrreducible (F.arrow j)).not_isSplitMono

/-- The factor of an irreducible fork arm through the socle quotient is a
split epimorphism. -/
theorem InjectiveNonprojectiveD4Fork.outgoingSocleFactor_isSplitEpi
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    IsSplitEpi (F.outgoingSocleFactor S j) := by
  let I := S.fgObj F.center.1
  letI : Injective I := F.center_injective
  let q := moduleSocleQuotientProjection I
  have hqAS := moduleSocleQuotientProjection_isLeftAlmostSplit
    (k := k) I (S.fgObj_indecomposable F.center.1)
  exact ((S.standardFormArrowMap_isIrreducible (F.arrow j)).factorization
    q (F.outgoingSocleFactor S j)
      (F.projection_comp_outgoingSocleFactor S j)).resolve_left
        hqAS.not_isSplitMono

/-- The displayed decomposition of the chosen minimal left almost-split
middle term, reindexed by a finite ordinal. -/
def minimalLeftMiddleDecomposition (i : Fin S.n) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (S.minimalLeftAlmostSplitAt i).middle := by
  classical
  let B := S.minimalLeftAlmostSplitAt i
  let n := Fintype.card B.index
  let epsilon : B.index ≃ Fin n := Fintype.equivFin B.index
  let summand : Fin n → RightModule.FinitelyGeneratedCategory A :=
    fun j ↦ S.fgObj (B.label (epsilon.symm j))
  let eReindex :
      S.almostSplitSkeleton.sumOver B.index B.label ≅ ⨁ summand :=
    biproduct.whiskerEquiv epsilon
      (fun j ↦ eqToIso (by
        simp only [summand, Equiv.symm_apply_apply]
        rfl))
  exact {
    n := n
    summand := summand
    indecomposable := fun j ↦ S.fgObj_indecomposable _
    isoBiproduct := B.decomposition.trans eReindex }

/-- The finite right-mesh occurrence represented by a fork arm. -/
def InjectiveNonprojectiveD4Fork.rightArmOccurrence
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.StandardFormOccurrence (F.target j).1 F.center.1 :=
  S.standardFormArrowOccurrenceEquiv (F.target j).1 F.center.1
    (F.arrow j)

/-- The underlying middle index of a fork arm. -/
abbrev InjectiveNonprojectiveD4Fork.rightArmIndex
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :=
  (F.rightArmOccurrence S j).1

/-- The selected middle occurrence has the center label. -/
theorem InjectiveNonprojectiveD4Fork.rightArmLabel
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (F.target j).1 (F.rightArmIndex S j) =
      F.center.1 :=
  (F.rightArmOccurrence S j).2

/-- The selected finite-tau middle object is the skeletal center object. -/
theorem InjectiveNonprojectiveD4Fork.rightArmMiddleObj_eq_center
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.finiteTauCategoryData.obj
        (FiniteTauMatrix.rightMiddleLabel
          S.finiteTauCategoryData.toFiniteRightTauCategoryData
          (F.target j).1 (F.rightArmIndex S j)) =
      S.fgObj F.center.1 :=
  (congrArg S.finiteTauCategoryData.obj (F.rightArmLabel S j)).trans
    (S.finiteTauCategoryData_obj F.center.1)

/-- A fork target, viewed as a nonprojective standard-form vertex. -/
abbrev InjectiveNonprojectiveD4Fork.targetNonprojectiveVertex
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
  ⟨(F.target j).1, by
    simpa [standardFormProjectiveSet] using (F.target j).2⟩

/-- The standard-form translate of a fork target is its translated target. -/
theorem InjectiveNonprojectiveD4Fork.standardFormTau_target
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.standardFormTau (F.targetNonprojectiveVertex S j) =
      F.translatedTarget S j := by
  unfold standardFormTau targetNonprojectiveVertex translatedTarget
  congr 2

/-- The skeletal translated target is the finite-tau source object of the
right mesh ending at the fork target. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSourceObj_eq_tauPlus
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.fgObj (F.translatedTarget S j) =
      S.finiteTauCategoryData.obj
        (S.finiteTauCategoryData.tauPlus
          (S.standardFormFiniteTauNonprojective
            (F.targetNonprojectiveVertex S j))) := by
  let z := F.targetNonprojectiveVertex S j
  let zT := S.standardFormFiniteTauNonprojective z
  have hlabel : F.translatedTarget S j =
      S.finiteTauCategoryData.tauPlus zT :=
    (F.standardFormTau_target S j).symm.trans
      (S.finiteTauCategoryData_tauPlus_standardFormTau z).symm
  exact (congrArg S.fgObj hlabel).trans
    (S.finiteTauCategoryData_obj _).symm

/-- The direct sum of all right-mesh occurrences except the selected fork
arm. -/
abbrev InjectiveNonprojectiveD4Fork.rightArmComplement
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    RightModule.FinitelyGeneratedCategory A :=
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let G := fun r : Fin (FiniteTauMatrix.rightMiddleArity T (F.target j).1) ↦
    S.finiteTauCategoryData.obj
      (FiniteTauMatrix.rightMiddleLabel T (F.target j).1 r)
  ⨁ Subtype.restrict (fun r ↦ r ≠ F.rightArmIndex S j) G

/-- Split the selected injective-center occurrence from its right
almost-split middle term. -/
def InjectiveNonprojectiveD4Fork.rightArmMiddleSplitIso
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    (S.finiteTauCategoryData.rightMesh
        (S.fgObj (F.target j).1)).X₂ ≅
      F.rightArmComplement S j ⊞ S.fgObj F.center.1 := by
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let G := fun r : Fin (FiniteTauMatrix.rightMiddleArity T (F.target j).1) ↦
    S.finiteTauCategoryData.obj
      (FiniteTauMatrix.rightMiddleLabel T (F.target j).1 r)
  let eMiddle :
      (S.finiteTauCategoryData.rightMesh
          (S.fgObj (F.target j).1)).X₂ ≅ ⨁ G :=
    FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData (F.target j).1
  let eSplit := MagnitudeConjecture.CategoryTheory.biproductSplitAtIso
    G (F.rightArmIndex S j)
  let eCenter : G (F.rightArmIndex S j) ≅ S.fgObj F.center.1 :=
    eqToIso (F.rightArmMiddleObj_eq_center S j)
  let C := F.rightArmComplement S j
  let eMap : C ⊞ G (F.rightArmIndex S j) ≅
      C ⊞ S.fgObj F.center.1 :=
    biprod.mapIso (Iso.refl C) eCenter
  exact {
    hom := eMiddle.hom ≫ eSplit.hom ≫ eMap.hom
    inv := eMap.inv ≫ eSplit.inv ≫ eMiddle.inv
    hom_inv_id := by simp
    inv_hom_id := by simp }

/-- The right-mesh source after splitting off the selected arm. -/
def InjectiveNonprojectiveD4Fork.rightArmSource
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    S.fgObj (F.translatedTarget S j) ⟶
      F.rightArmComplement S j ⊞ S.fgObj F.center.1 :=
  eqToHom (congrArg S.fgObj (F.standardFormTau_target S j).symm) ≫
    S.standardFormRightSource (F.targetNonprojectiveVertex S j) ≫
      (F.rightArmMiddleSplitIso S j).hom

/-- The right-mesh sink after splitting off the selected arm. -/
def InjectiveNonprojectiveD4Fork.rightArmSink
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.rightArmComplement S j ⊞ S.fgObj F.center.1 ⟶
      S.fgObj (F.target j).1 :=
  (F.rightArmMiddleSplitIso S j).inv ≫
    S.standardFormRightSink (F.target j).1

/-- The selected right component of the split mesh is the fork arm. -/
theorem InjectiveNonprojectiveD4Fork.rightArmMiddleSplitIso_inr_inv
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    biprod.inr ≫ (F.rightArmMiddleSplitIso S j).inv =
      eqToHom (F.rightArmMiddleObj_eq_center S j).symm ≫
        FiniteTauMatrix.rightMiddleInclusion
          S.finiteTauCategoryData (F.target j).1
            (F.rightArmIndex S j) := by
  dsimp only [rightArmMiddleSplitIso]
  simp only [biprod.mapIso_inv,
    MagnitudeConjecture.CategoryTheory.biproductSplitAtIso]
  rw [← Category.assoc, biprod.inr_map]
  simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
  simp only [biprod.inr_desc_assoc,
    FiniteTauMatrix.rightMiddleInclusion]
  congr

/-- Projection to the selected arm after splitting is the old middle
projection followed by the label identification. -/
theorem InjectiveNonprojectiveD4Fork.rightArmMiddleSplitIso_hom_snd
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    (F.rightArmMiddleSplitIso S j).hom ≫ biprod.snd =
      FiniteTauMatrix.rightMiddleProjection
          S.finiteTauCategoryData (F.target j).1
            (F.rightArmIndex S j) ≫
        eqToHom (F.rightArmMiddleObj_eq_center S j) := by
  dsimp only [rightArmMiddleSplitIso]
  simp only [MagnitudeConjecture.CategoryTheory.biproductSplitAtIso,
    biprod.mapIso_hom]
  unfold FiniteTauMatrix.rightMiddleProjection
  simp only [Category.assoc, biprod.map_snd,
    biprod.lift_snd_assoc]
  rfl

/-- The selected right component of the split mesh is the fork arm. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSink_inr
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    biprod.inr ≫ F.rightArmSink S j = F.outgoingMap S j := by
  rw [rightArmSink, ← Category.assoc,
    F.rightArmMiddleSplitIso_inr_inv S j]
  unfold outgoingMap standardFormArrowMap standardFormRightSink
  simp only [FiniteTauMatrix.rightMiddleComponent,
    S.finiteTauCategoryData_obj, Category.assoc]
  rfl

/-- The selected component of the split source is the finite-tau source
component, up to the displayed source and center identifications. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_snd
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.rightArmSource S j ≫ biprod.snd =
      eqToHom (F.rightArmSourceObj_eq_tauPlus S j) ≫
        FiniteTauMatrix.rightMiddleSourceComponent
          S.finiteTauCategoryData
          (S.standardFormFiniteTauNonprojective
            (F.targetNonprojectiveVertex S j))
          (F.rightArmIndex S j) ≫
        eqToHom (F.rightArmMiddleObj_eq_center S j) := by
  unfold rightArmSource standardFormRightSource
    FiniteTauMatrix.rightMiddleSourceComponent
  dsimp only [rightArmMiddleSplitIso]
  simp only [MagnitudeConjecture.CategoryTheory.biproductSplitAtIso,
    biprod.mapIso_hom, Category.assoc, biprod.map_snd,
    biprod.lift_snd_assoc]
  rfl

/-- The selected left component of the split mesh is irreducible. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_snd_irreducible
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    IsIrreducibleMorphism
      (F.rightArmSource S j ≫ biprod.snd) := by
  let z := F.targetNonprojectiveVertex S j
  let zT := S.standardFormFiniteTauNonprojective z
  let i := F.rightArmIndex S j
  have hi := FiniteTauMatrix.rightMiddleSourceComponent_isIrreducible
    S.finiteTauCategoryData zT i
  rw [F.rightArmSource_snd S j]
  exact (hi.postcomp_iso
    (eqToIso (F.rightArmMiddleObj_eq_center S j))).precomp_iso
      (eqToIso (F.rightArmSourceObj_eq_tauPlus S j))

/-- The split right-mesh source and sink have zero composite. -/
@[reassoc (attr := simp)]
theorem InjectiveNonprojectiveD4Fork.rightArmSource_comp_sink
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.rightArmSource S j ≫ F.rightArmSink S j = 0 := by
  unfold rightArmSource rightArmSink
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact S.standardFormRightSource_comp_rightSink
    (F.targetNonprojectiveVertex S j)

/-- The split right-mesh source remains monic. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_mono
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    Mono (F.rightArmSource S j) := by
  unfold rightArmSource
  haveI : Mono (S.standardFormRightSource
      (F.targetNonprojectiveVertex S j)) :=
    S.standardFormRightSource_mono (F.targetNonprojectiveVertex S j)
  infer_instance

/-- The split right-mesh source remains left almost split. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_isLeftAlmostSplit
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    IsLeftAlmostSplit (F.rightArmSource S j) := by
  let eSource : S.fgObj (F.translatedTarget S j) ≅
      S.fgObj (S.standardFormTau (F.targetNonprojectiveVertex S j)) :=
    eqToIso (congrArg S.fgObj (F.standardFormTau_target S j).symm)
  change IsLeftAlmostSplit
    (eSource.hom ≫
      S.standardFormRightSource (F.targetNonprojectiveVertex S j) ≫
        (F.rightArmMiddleSplitIso S j).hom)
  exact ((S.standardFormRightSource_isLeftAlmostSplit
    (F.targetNonprojectiveVertex S j)).precomp_iso eSource).postcomp_iso
      (F.rightArmMiddleSplitIso S j)

/-- The split right-mesh source remains left minimal. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_isLeftMinimal
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    IsLeftMinimal (F.rightArmSource S j) := by
  let eSource : S.fgObj (F.translatedTarget S j) ≅
      S.fgObj (S.standardFormTau (F.targetNonprojectiveVertex S j)) :=
    eqToIso (congrArg S.fgObj (F.standardFormTau_target S j).symm)
  change IsLeftMinimal
    (eSource.hom ≫
      S.standardFormRightSource (F.targetNonprojectiveVertex S j) ≫
        (F.rightArmMiddleSplitIso S j).hom)
  let f := eSource.hom ≫
    S.standardFormRightSource (F.targetNonprojectiveVertex S j)
  let e := F.rightArmMiddleSplitIso S j
  have hf : IsLeftMinimal f :=
    (S.standardFormRightSource_isLeftMinimal
      (F.targetNonprojectiveVertex S j)).precomp_iso eSource
  intro a ha
  let b := e.hom ≫ a ≫ e.inv
  have hb : f ≫ b = f := by
    have h := congrArg (fun q ↦ q ≫ e.inv) ha
    simpa only [f, e, b, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  letI : IsIso b := hf b hb
  let aIso :
      F.rightArmComplement S j ⊞ S.fgObj F.center.1 ≅
        F.rightArmComplement S j ⊞ S.fgObj F.center.1 :=
    e.symm.trans ((asIso b).trans e)
  have haIso : aIso.hom = a := by
    simp [aIso, b, Category.assoc]
  rw [← haIso]
  infer_instance

/-- The split right-mesh sink remains epic. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSink_epi
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    Epi (F.rightArmSink S j) := by
  have hSink : Epi (S.standardFormRightSink (F.target j).1) :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton (S.standardFormRightSink (F.target j).1)
        (S.standardFormRightSink_isRightAlmostSplit (F.target j).1)
        (F.target j).2
  letI : Epi (S.standardFormRightSink (F.target j).1) := hSink
  unfold rightArmSink
  infer_instance

/-- The split right-mesh source retains the weak-kernel factorization
property. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_factors_of_comp_sink_eq_zero
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3)
    {X : RightModule.FinitelyGeneratedCategory A}
    (q : X ⟶ F.rightArmComplement S j ⊞ S.fgObj F.center.1)
    (hq : q ≫ F.rightArmSink S j = 0) :
    ∃ t : X ⟶ S.fgObj (F.translatedTarget S j),
      t ≫ F.rightArmSource S j = q := by
  let eSource : S.fgObj (F.translatedTarget S j) ≅
      S.fgObj (S.standardFormTau (F.targetNonprojectiveVertex S j)) :=
    eqToIso (congrArg S.fgObj (F.standardFormTau_target S j).symm)
  have hqOld :
      (q ≫ (F.rightArmMiddleSplitIso S j).inv) ≫
          S.standardFormRightSink (F.target j).1 = 0 := by
    simpa only [rightArmSink, Category.assoc] using hq
  obtain ⟨t, ht⟩ :=
    S.standardFormRightSource_factors_of_comp_rightSink_eq_zero
      (F.targetNonprojectiveVertex S j)
      (q ≫ (F.rightArmMiddleSplitIso S j).inv) hqOld
  refine ⟨t ≫ eSource.inv, ?_⟩
  unfold rightArmSource
  change (t ≫ eSource.inv) ≫
      (eSource.hom ≫
        S.standardFormRightSource (F.targetNonprojectiveVertex S j) ≫
          (F.rightArmMiddleSplitIso S j).hom) = q
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ht]
  simp

/-- Exactness of the split right mesh on underlying module elements. -/
theorem InjectiveNonprojectiveD4Fork.rightArm_functionExact
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    Function.Exact (F.rightArmSource S j).hom.hom
      (F.rightArmSink S j).hom.hom := by
  let T : ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
    ShortComplex.mk (F.rightArmSource S j) (F.rightArmSink S j)
      (F.rightArmSource_comp_sink S j)
  letI : Mono (F.rightArmSource S j) := F.rightArmSource_mono S j
  have hKernel : IsLimit
      (KernelFork.ofι (F.rightArmSource S j)
        (F.rightArmSource_comp_sink S j)) := by
    apply KernelFork.IsLimit.ofι' _ _
    intro X q hq
    let hfactor :=
      F.rightArmSource_factors_of_comp_sink_eq_zero S j q hq
    exact ⟨Classical.choose hfactor, Classical.choose_spec hfactor⟩
  have hT : T.Exact := T.exact_of_f_is_kernel hKernel
  let U := forget₂ (RightModule.FinitelyGeneratedCategory A)
    (RightModule.Category A)
  have hTU : (T.map U).Exact := hT.map U
  have hfun : Function.Exact (T.map U).f (T.map U).g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hTU
  change Function.Exact (F.rightArmSource S j).hom.hom
    (F.rightArmSink S j).hom.hom at hfun
  exact hfun

/-- Exactness and epicity of the selected outgoing arm force the
complementary source component to be epic. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_fst_epi
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    Epi (F.rightArmSource S j ≫ biprod.fst) := by
  apply (IndecomposableSkeleton.fg_epi_iff_surjective _).2
  intro e
  let q := F.outgoingMap S j
  let g := biprod.inl ≫ F.rightArmSink S j
  have hqSurjective : Function.Surjective q.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective q).1
      (F.outgoingMap_epi S j)
  obtain ⟨i, hi⟩ := hqSurjective (-g.hom.hom e)
  let inl : F.rightArmComplement S j ⟶
      F.rightArmComplement S j ⊞ S.fgObj F.center.1 := biprod.inl
  let inr : S.fgObj F.center.1 ⟶
      F.rightArmComplement S j ⊞ S.fgObj F.center.1 := biprod.inr
  let z : (F.rightArmComplement S j ⊞ S.fgObj F.center.1).obj :=
    inl.hom.hom e + inr.hom.hom i
  have hz : (F.rightArmSink S j).hom.hom z = 0 := by
    dsimp only [z]
    rw [map_add]
    change (inl ≫ F.rightArmSink S j).hom.hom e +
      (inr ≫ F.rightArmSink S j).hom.hom i = 0
    change g.hom.hom e +
      (inr ≫ F.rightArmSink S j).hom.hom i = 0
    rw [F.rightArmSink_inr S j]
    rw [hi]
    exact add_neg_cancel _
  obtain ⟨p, hp⟩ := (F.rightArm_functionExact S j z).mp hz
  refine ⟨p, ?_⟩
  let fst : F.rightArmComplement S j ⊞ S.fgObj F.center.1 ⟶
      F.rightArmComplement S j := biprod.fst
  have hpFst := congrArg (fun w ↦ fst.hom.hom w) hp
  dsimp only [z] at hpFst
  rw [map_add] at hpFst
  have hInl : fst.hom.hom (inl.hom.hom e) = e := by
    change (inl ≫ fst).hom.hom e = e
    simp [inl, fst]
  have hInr : fst.hom.hom (inr.hom.hom i) = 0 := by
    change (inr ≫ fst).hom.hom i = 0
    simp [inr, fst]
  change fst.hom.hom ((F.rightArmSource S j).hom.hom p) = e
  rw [hpFst, hInl, hInr, add_zero]

/-- If the complementary middle object is nonzero, its source component
is irreducible. -/
theorem InjectiveNonprojectiveD4Fork.rightArmSource_fst_irreducible
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3)
    (hC : ¬ IsZero (F.rightArmComplement S j)) :
    IsIrreducibleMorphism (F.rightArmSource S j ≫ biprod.fst) := by
  let P := S.fgObj (F.translatedTarget S j)
  let C := F.rightArmComplement S j
  let E := C ⊞ S.fgObj F.center.1
  let s : P ⟶ E := F.rightArmSource S j
  let b : P ⟶ C := s ≫ biprod.fst
  let inc : C ⟶ E := biprod.inl
  let proj : E ⟶ C := biprod.fst
  have hincproj : inc ≫ proj = 𝟙 C := by simp [inc, proj]
  have hbNotSplitMono : ¬ IsSplitMono b := by
    intro hb
    apply (F.rightArmSource_isLeftAlmostSplit S j).not_isSplitMono
    obtain ⟨sm⟩ := hb.exists_splitMono
    exact IsSplitMono.mk'
      { retraction := proj ≫ sm.retraction
        id := by
          change s ≫ (proj ≫ sm.retraction) = 𝟙 P
          simpa only [b, Category.assoc] using sm.id }
  have hbNotSplitEpi : ¬ IsSplitEpi b := by
    intro hb
    letI : IsSplitEpi b := hb
    letI : IsIso b :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
        (S.fgObj_indecomposable (F.translatedTarget S j)) b hC
    exact hbNotSplitMono inferInstance
  refine ⟨hbNotSplitMono, hbNotSplitEpi, ?_⟩
  intro M a c hac
  by_cases ha : IsSplitMono a
  · exact Or.inl ha
  · obtain ⟨d, hd⟩ :=
      (F.rightArmSource_isLeftAlmostSplit S j).factors a ha
    let t : E ⟶ E := 𝟙 E + (d ≫ c - proj) ≫ inc
    have htfix : s ≫ t = s := by
      dsimp only [t]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, Preadditive.comp_sub]
      have hdc : s ≫ (d ≫ c) = b := by
        rw [← Category.assoc, hd, hac]
      rw [hdc]
      change s + (b - b) ≫ inc = s
      simp
    have htproj : t ≫ proj = d ≫ c := by
      dsimp only [t]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, hincproj, Category.comp_id]
      abel
    letI : IsIso t := F.rightArmSource_isLeftMinimal S j t htfix
    exact Or.inr (IsSplitEpi.mk'
      { section_ := inc ≫ inv t ≫ d
        id := by
          calc
            (inc ≫ inv t ≫ d) ≫ c =
                inc ≫ inv t ≫ (d ≫ c) := by simp only [Category.assoc]
            _ = inc ≫ inv t ≫ (t ≫ proj) := by rw [← htproj]
            _ = 𝟙 C := by
              simp only [IsIso.inv_hom_id_assoc, hincproj] })

/-- The two split components of the right-mesh relation. -/
theorem InjectiveNonprojectiveD4Fork.rightArm_component_relation
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    (F.rightArmSource S j ≫ biprod.fst) ≫
          (biprod.inl ≫ F.rightArmSink S j) +
        (F.rightArmSource S j ≫ biprod.snd) ≫
          F.outgoingMap S j =
      0 := by
  rw [← F.rightArmSink_inr S j]
  simp only [Category.assoc]
  calc
    F.rightArmSource S j ≫ biprod.fst ≫ biprod.inl ≫
          F.rightArmSink S j +
        F.rightArmSource S j ≫ biprod.snd ≫ biprod.inr ≫
          F.rightArmSink S j =
      F.rightArmSource S j ≫
          (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
            F.rightArmSink S j := by
        simp only [Preadditive.comp_add, Preadditive.add_comp,
          Category.assoc]
    _ = F.rightArmSource S j ≫ F.rightArmSink S j := by
      rw [biprod.total]
      simp
    _ = 0 := F.rightArmSource_comp_sink S j

/-- The literal kernel of the complementary source component. -/
abbrev InjectiveNonprojectiveD4Fork.rightArmComplementaryKernelObj
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    RightModule.FinitelyGeneratedCategory A :=
  RightModule.submoduleFGObj (S.fgObj (F.translatedTarget S j))
    (F.rightArmSource S j ≫ biprod.fst).hom.hom.ker

/-- The literal complementary-kernel submodule inclusion. -/
def InjectiveNonprojectiveD4Fork.rightArmComplementaryKernelInclusion
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.rightArmComplementaryKernelObj S j ⟶
      S.fgObj (F.translatedTarget S j) := by
  letI : Module.Finite Aᵐᵒᵖ (S.fgObj (F.translatedTarget S j)) :=
    (S.fgObj (F.translatedTarget S j)).property
  change FGModuleCat.of Aᵐᵒᵖ
      (F.rightArmSource S j ≫ biprod.fst).hom.hom.ker ⟶
    FGModuleCat.of Aᵐᵒᵖ (S.fgObj (F.translatedTarget S j))
  exact FGModuleCat.ofHom
    (F.rightArmSource S j ≫ biprod.fst).hom.hom.ker.subtype

/-- The complementary-kernel inclusion is killed by the complementary
source component. -/
@[reassoc (attr := simp)]
theorem InjectiveNonprojectiveD4Fork.rightArmComplementaryKernelInclusion_comp
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.rightArmComplementaryKernelInclusion S j ≫
        (F.rightArmSource S j ≫ biprod.fst) =
      0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (F.rightArmSource S j ≫ biprod.fst).hom.hom x.1 = 0
  exact x.2

/-- Exactness sends the kernel of the complementary source component to
the kernel left after splitting the chosen arm off the socle quotient. -/
def InjectiveNonprojectiveD4Fork.complementaryKernelToSocleFactorKernel
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.rightArmComplementaryKernelObj S j ⟶
      kernel (F.outgoingSocleFactor S j) := by
  let b := F.rightArmSource S j ≫ biprod.fst
  let u := F.rightArmSource S j ≫ biprod.snd
  let q := F.outgoingMap S j
  let pi := moduleSocleQuotientProjection (S.fgObj F.center.1)
  let h := F.outgoingSocleFactor S j
  let inc : F.rightArmComplementaryKernelObj S j ⟶
      S.fgObj (F.translatedTarget S j) :=
    F.rightArmComplementaryKernelInclusion S j
  let f : F.rightArmComplementaryKernelObj S j ⟶
      moduleSocleQuotientFGObj (S.fgObj F.center.1) :=
    inc ≫ u ≫ pi
  have hincb : inc ≫ b = 0 :=
    F.rightArmComplementaryKernelInclusion_comp S j
  have hrel := congrArg (fun t ↦ inc ≫ t)
    (F.rightArm_component_relation S j)
  have hincuq : inc ≫ u ≫ q = 0 := by
    change (inc ≫ b) ≫ (biprod.inl ≫ F.rightArmSink S j) +
      (inc ≫ u) ≫ q = 0 at hrel
    rw [hincb, zero_comp, zero_add] at hrel
    simpa only [Category.assoc] using hrel
  have hfh : f ≫ h = 0 := by
    change inc ≫ u ≫ (pi ≫ h) = 0
    rw [show pi ≫ h = q from
      F.projection_comp_outgoingSocleFactor S j]
    exact hincuq
  exact kernel.lift h f hfh

/-- The kernel lift is characterized by its composite with the canonical
kernel inclusion. -/
theorem InjectiveNonprojectiveD4Fork.complementaryKernelToSocleFactorKernel_comp_ι
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    F.complementaryKernelToSocleFactorKernel S j ≫
        kernel.ι (F.outgoingSocleFactor S j) =
      F.rightArmComplementaryKernelInclusion S j ≫
        (F.rightArmSource S j ≫ biprod.snd) ≫
          moduleSocleQuotientProjection (S.fgObj F.center.1) := by
  simp only [complementaryKernelToSocleFactorKernel, kernel.lift_ι]

/-- The exact right mesh makes the complementary-kernel map onto the
remaining socle-quotient kernel surjective. -/
theorem InjectiveNonprojectiveD4Fork.complementaryKernelToSocleFactorKernel_epi
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    Epi (F.complementaryKernelToSocleFactorKernel S j) := by
  apply (IndecomposableSkeleton.fg_epi_iff_surjective _).2
  intro x
  let pi := moduleSocleQuotientProjection (S.fgObj F.center.1)
  let h := F.outgoingSocleFactor S j
  let q := F.outgoingMap S j
  let s := F.rightArmSource S j
  let t := F.rightArmSink S j
  let b := s ≫ biprod.fst
  let u := s ≫ biprod.snd
  let inc := F.rightArmComplementaryKernelInclusion S j
  have hpiSurjective : Function.Surjective pi.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective pi).1
      (moduleSocleQuotientProjection_epi (S.fgObj F.center.1))
  obtain ⟨i, hi⟩ := hpiSurjective ((kernel.ι h).hom.hom x)
  have hxzero : h.hom.hom ((kernel.ι h).hom.hom x) = 0 := by
    have hcondition := congrArg (fun r ↦ r.hom.hom x)
      (kernel.condition h)
    exact hcondition
  have hiq : q.hom.hom i = 0 := by
    have hfactor := congrArg (fun r ↦ r.hom.hom i)
      (F.projection_comp_outgoingSocleFactor S j)
    calc
      q.hom.hom i = (pi ≫ h).hom.hom i := hfactor.symm
      _ = h.hom.hom (pi.hom.hom i) := rfl
      _ = h.hom.hom ((kernel.ι h).hom.hom x) :=
        congrArg h.hom.hom hi
      _ = 0 := hxzero
  let inr : S.fgObj F.center.1 ⟶
      F.rightArmComplement S j ⊞ S.fgObj F.center.1 := biprod.inr
  let z : (F.rightArmComplement S j ⊞ S.fgObj F.center.1).obj :=
    inr.hom.hom i
  have hz : t.hom.hom z = 0 := by
    have hcomponent := congrArg (fun r ↦ r.hom.hom i)
      (F.rightArmSink_inr S j)
    exact hcomponent.trans hiq
  obtain ⟨p, hp⟩ := (F.rightArm_functionExact S j z).mp hz
  let fst : F.rightArmComplement S j ⊞ S.fgObj F.center.1 ⟶
      F.rightArmComplement S j := biprod.fst
  let snd : F.rightArmComplement S j ⊞ S.fgObj F.center.1 ⟶
      S.fgObj F.center.1 := biprod.snd
  have hbp : b.hom.hom p = 0 := by
    have hpFst := congrArg (fun w ↦ fst.hom.hom w) hp
    have hInr : fst.hom.hom (inr.hom.hom i) = 0 := by
      change (inr ≫ fst).hom.hom i = 0
      simp [inr, fst]
    change fst.hom.hom (s.hom.hom p) = 0
    exact hpFst.trans hInr
  have hup : u.hom.hom p = i := by
    have hpSnd := congrArg (fun w ↦ snd.hom.hom w) hp
    have hInr : snd.hom.hom (inr.hom.hom i) = i := by
      change (inr ≫ snd).hom.hom i = i
      simp [inr, snd]
    change snd.hom.hom (s.hom.hom p) = i
    exact hpSnd.trans hInr
  let y : F.rightArmComplementaryKernelObj S j := ⟨p, hbp⟩
  refine ⟨y, ?_⟩
  let f := F.complementaryKernelToSocleFactorKernel S j
  have hkιInjective : Function.Injective
      (kernel.ι h).hom.hom :=
    (IndecomposableSkeleton.fg_mono_iff_injective (kernel.ι h)).1
      inferInstance
  apply hkιInjective
  have hmap := congrArg (fun r ↦ r.hom.hom y)
    (F.complementaryKernelToSocleFactorKernel_comp_ι S j)
  calc
    (kernel.ι h).hom.hom (f.hom.hom y) =
        (f ≫ kernel.ι h).hom.hom y := rfl
    _ =
        (inc ≫ u ≫ pi).hom.hom y := by
      simpa only [f, h, inc, u, pi] using hmap
    _ = pi.hom.hom (u.hom.hom p) := rfl
    _ = pi.hom.hom i := congrArg pi.hom.hom hup
    _ = (kernel.ι h).hom.hom x := hi

/-- If the translated arm is projective, the kernel of the complementary
source component has simple top.  For a zero complement it is the whole
projective; for a nonzero complement it is the simple kernel of an
irreducible epimorphism. -/
theorem InjectiveNonprojectiveD4Fork.complementaryKernel_simpleTop_of_projective
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3)
    (hp : Projective (S.fgObj (F.translatedTarget S j))) :
    IsSimpleModule Aᵐᵒᵖ
      (F.rightArmComplementaryKernelObj S j ⧸
        Module.jacobson Aᵐᵒᵖ
          (F.rightArmComplementaryKernelObj S j)) := by
  let P := S.fgObj (F.translatedTarget S j)
  let C := F.rightArmComplement S j
  let b : P ⟶ C := F.rightArmSource S j ≫ biprod.fst
  let L := F.rightArmComplementaryKernelObj S j
  let p : S.ProjectiveLabel := ⟨F.translatedTarget S j, hp⟩
  have hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P) :=
    S.projectiveSimpleTop_isSimpleModule p
  letI : Epi b := F.rightArmSource_fst_epi S j
  by_cases hC : IsZero C
  · have hbZero : b = 0 := hC.eq_of_tgt b 0
    have hkerTop : b.hom.hom.ker = ⊤ := by
      apply LinearMap.ker_eq_top.mpr
      rw [hbZero]
      rfl
    let e : L ≃ₗ[Aᵐᵒᵖ] P :=
      LinearEquiv.ofTop b.hom.hom.ker hkerTop
    exact isSimpleModule_top_congr e.symm hPtop
  · have hCind : Indecomposable C :=
      MagnitudeConjecture.indecomposable_of_epi_from_simpleTop
        (k := k) (A := A) P C hPtop hC b
    have hbIrr : IsIrreducibleMorphism b :=
      F.rightArmSource_fst_irreducible S j hC
    have hLsimple : IsSimpleModule Aᵐᵒᵖ b.hom.hom.ker :=
      MagnitudeConjecture.simple_kernel_of_irreducible_epi_from_simpleTop
        (k := k) (A := A) P C hPtop hCind b hbIrr
    letI : IsSimpleModule Aᵐᵒᵖ L := hLsimple
    have hJ : Module.jacobson Aᵐᵒᵖ L = ⊥ :=
      IsSimpleModule.jacobson_eq_bot Aᵐᵒᵖ L
    exact IsSimpleModule.congr
      ((Module.jacobson Aᵐᵒᵖ L).quotEquivOfEqBot hJ)

/-- The three fork arms inject into the summand occurrences of the chosen
minimal left almost-split middle term. -/
def InjectiveNonprojectiveD4Fork.leftMiddleOccurrence
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    (S.minimalLeftAlmostSplitAt F.center.1).index :=
  Classical.choose <|
    ((S.minimalLeftAlmostSplitAt F.center.1)
      |>.summandIrreducibleCorrespondence (F.target j).1).2
      ⟨F.outgoingMap S j,
        S.standardFormArrowMap_isIrreducible (F.arrow j)⟩

/-- Distinct fork arms give distinct summand occurrences. -/
theorem InjectiveNonprojectiveD4Fork.leftMiddleOccurrence_injective
    (F : S.InjectiveNonprojectiveD4Fork) :
    Function.Injective (F.leftMiddleOccurrence S) := by
  intro i j hij
  apply F.target_injective
  apply Subtype.ext
  have hi := Classical.choose_spec <|
    ((S.minimalLeftAlmostSplitAt F.center.1)
      |>.summandIrreducibleCorrespondence (F.target i).1).2
      ⟨F.outgoingMap S i,
        S.standardFormArrowMap_isIrreducible (F.arrow i)⟩
  have hj := Classical.choose_spec <|
    ((S.minimalLeftAlmostSplitAt F.center.1)
      |>.summandIrreducibleCorrespondence (F.target j).1).2
      ⟨F.outgoingMap S j,
        S.standardFormArrowMap_isIrreducible (F.arrow j)⟩
  exact hi.symm.trans <| (congrArg
    (S.minimalLeftAlmostSplitAt F.center.1).label hij).trans hj

/-- The chosen minimal left almost-split middle term out of the fork center
has at least three indecomposable summand occurrences. -/
theorem InjectiveNonprojectiveD4Fork.three_le_leftMiddle_card
    (F : S.InjectiveNonprojectiveD4Fork) :
    3 ≤ Fintype.card
      (S.minimalLeftAlmostSplitAt F.center.1).index := by
  exact Fintype.card_le_of_injective (F.leftMiddleOccurrence S)
    (F.leftMiddleOccurrence_injective S)

/-- The socle quotient of the injective center of a `D4` boundary fork is
not indecomposable.  This is the only decomposition consequence of the fork
needed in Gabriel's local argument. -/
theorem InjectiveNonprojectiveD4Fork.socleQuotient_not_indecomposable
    (F : S.InjectiveNonprojectiveD4Fork) :
    ¬ Indecomposable
      (moduleSocleQuotientFGObj (S.fgObj F.center.1)) := by
  intro hQ
  let dB := S.minimalLeftMiddleDecomposition F.center.1
  let Q := moduleSocleQuotientFGObj (S.fgObj F.center.1)
  let dQ :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      Q hQ
  have hcard : Fintype.card
      (S.minimalLeftAlmostSplitAt F.center.1).index = 1 := by
    have hn :=
      MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.n_eq_of_iso
        dB dQ (fun j ↦ S.fgObj_end_isLocalRing _) <|
          F.leftMiddleIsoSocleQuotient S
    exact hn
  have hthree := F.three_le_leftMiddle_card S
  omega

/-- A split fork-arm factor displays the socle quotient as the direct sum
of its kernel and the arm target. -/
def InjectiveNonprojectiveD4Fork.outgoingSocleFactorKernelSplitIso
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    moduleSocleQuotientFGObj (S.fgObj F.center.1) ≅
      kernel (F.outgoingSocleFactor S j) ⊞ S.fgObj (F.target j).1 := by
  let h := F.outgoingSocleFactor S j
  letI : IsSplitEpi h := F.outgoingSocleFactor_isSplitEpi S j
  let c : KernelFork h :=
    KernelFork.ofι (kernel.ι h) (kernel.condition h)
  let hc : IsLimit c := kernelIsKernel h
  let b := binaryBiconeOfIsSplitEpiOfKernel hc
  exact biprod.uniqueUpToIso (kernel h) (S.fgObj (F.target j).1)
    (isBilimitBinaryBiconeOfIsSplitEpiOfKernel hc)

/-- Removing any one fork arm leaves at least two indecomposable
occurrences in the kernel of the corresponding split factor from the
socle quotient. -/
theorem InjectiveNonprojectiveD4Fork.two_le_outgoingSocleFactorKernel_n
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3)
    (dK : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (kernel (F.outgoingSocleFactor S j))) :
    2 ≤ dK.n := by
  let dB := S.minimalLeftMiddleDecomposition F.center.1
  let dY :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (S.fgObj (F.target j).1) (S.fgObj_indecomposable (F.target j).1)
  let dSum := dK.biprod dY
  have hcount : dB.n = dSum.n :=
    dB.n_eq_of_iso dSum (fun i ↦ S.fgObj_end_isLocalRing _) <|
      (F.leftMiddleIsoSocleQuotient S).trans
        (F.outgoingSocleFactorKernelSplitIso S j)
  have hthree := F.three_le_leftMiddle_card S
  change Fintype.card
      (S.minimalLeftAlmostSplitAt F.center.1).index = dK.n + 1 at hcount
  omega

/-- The kernel left after splitting off one fork arm is nonzero and is not
indecomposable: it contains at least the other two indecomposable
occurrences. -/
theorem InjectiveNonprojectiveD4Fork.outgoingSocleFactorKernel_nonzero_and_not_indecomposable
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    (¬ IsZero (kernel (F.outgoingSocleFactor S j))) ∧
      ¬ Indecomposable (kernel (F.outgoingSocleFactor S j)) := by
  let K := kernel (F.outgoingSocleFactor S j)
  letI : Module.Finite k K :=
    RightModule.finite_over_field_of_finitelyGenerated k A K
  obtain ⟨dK⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) K
  have htwo : 2 ≤ dK.n := F.two_le_outgoingSocleFactorKernel_n S j dK
  have hlocal (i : Fin dK.n) : IsLocalRing (End (dK.summand i)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (dK.summand i) (dK.indecomposable i)
  constructor
  · intro hKzero
    let dZero :
        MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition K := {
      n := 0
      summand := fun i ↦ Fin.elim0 i
      indecomposable := fun i ↦ Fin.elim0 i
      isoBiproduct :=
        MagnitudeConjecture.CategoryTheory.zeroIsoEmptyBiproduct K hKzero }
    have hcount : dK.n = dZero.n :=
      dK.n_eq_of_iso dZero hlocal (Iso.refl K)
    change dK.n = 0 at hcount
    omega
  · intro hKind
    let dOne :=
      MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
        K hKind
    have hcount : dK.n = dOne.n :=
      dK.n_eq_of_iso dOne hlocal (Iso.refl K)
    change dK.n = 1 at hcount
    omega

/-- No translated arm of an injective `D4` boundary fork can be
projective.  The complementary kernel would otherwise be a simple-top
source surjecting onto an object with at least two indecomposable
occurrences. -/
theorem InjectiveNonprojectiveD4Fork.translatedTarget_not_projective
    (F : S.InjectiveNonprojectiveD4Fork) (j : Fin 3) :
    ¬ Projective (S.fgObj (F.translatedTarget S j)) := by
  intro hp
  let L := F.rightArmComplementaryKernelObj S j
  let K := kernel (F.outgoingSocleFactor S j)
  let f : L ⟶ K := F.complementaryKernelToSocleFactorKernel S j
  have hLtop : IsSimpleModule Aᵐᵒᵖ
      (L ⧸ Module.jacobson Aᵐᵒᵖ L) :=
    F.complementaryKernel_simpleTop_of_projective S j hp
  have hK :=
    F.outgoingSocleFactorKernel_nonzero_and_not_indecomposable S j
  letI : Epi f := F.complementaryKernelToSocleFactorKernel_epi S j
  have hKind : Indecomposable K :=
    MagnitudeConjecture.indecomposable_of_epi_from_simpleTop
      (k := k) (A := A) L K hLtop hK.1 f
  exact hK.2 hKind

/-- A right beta bound of two excludes the injective `D4` boundary fork. -/
theorem not_nonempty_injectiveNonprojectiveD4Fork_of_beta_le_two
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    ¬ Nonempty S.InjectiveNonprojectiveD4Fork := by
  rintro ⟨F⟩
  obtain ⟨j, hp⟩ := F.exists_projective_translatedTarget S hbeta
  exact F.translatedTarget_not_projective S j hp

/-- Gabriel's direct comparison: the right beta bound `≤ 2` forces the
opposite (left) beta bound `≤ 2`. -/
theorem leftBeta_le_two_of_beta_le_two
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    S.leftBeta ≤ 2 := by
  by_contra hleft
  exact S.not_nonempty_injectiveNonprojectiveD4Fork_of_beta_le_two hbeta
    (S.exists_injectiveNonprojectiveD4Fork_of_beta_le_two hbeta hleft)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
