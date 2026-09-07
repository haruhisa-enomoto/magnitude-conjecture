import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletion
import MagnitudeConjecture.CategoryTheory.LinearBiproduct
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The deleted-simple socle class

At a positive new mesh, the torsion-free quotient of the ambient
Auslander--Reiten middle has a simple submodule supported at the deleted
primitive idempotent.  This produces the manuscript's nonzero map from the
deleted simple and hence a nonzero connecting extension class.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

noncomputable local instance primitiveDeletedSocleHasExt :
    HasExt.{u} (FinitelyGeneratedCategory A) := by
  letI : EnoughProjectives (FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  exact CategoryTheory.hasExt_of_enoughProjectives _

namespace PrimitiveNewRightMeshEndpoint

variable {S} {e : A} {D : PrimitiveIdempotentData e}

/-- Maps from the primitive projective to an `AeA`-annihilated module are
zero. -/
theorem hom_primitiveSource_to_eq_zero
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M)
    (f : S.fgObj (S.primitiveSourceLabel D) ⟶ M) : f = 0 := by
  let E := S.primitiveSourceHomCoordinateEquiv D M
  apply E.injective
  have hcoordinate :
      Module.finrank k (idempotentCoordinate (k := k) e M) = 0 :=
    (finrank_idempotentCoordinate_eq_zero_iff D.idempotent M).2
      ((isAnnihilatedBy_primitiveIdeal_iff e M).1 hM)
  letI : FiniteDimensional k M :=
    finite_over_field_of_finitelyGenerated k A M
  have hall : ∀ x : idempotentCoordinate (k := k) e M, x = 0 :=
    (finrank_zero_iff_forall_zero).1 hcoordinate
  rw [hall (E f), map_zero]

/-- The primitive projective maps one-dimensionally to the ambient AR
middle at a new endpoint. -/
theorem ambientMiddle_primitiveSourceHom_finrank_eq_one
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶
        (S.minimalRightAlmostSplitAt N.label.1).middle) = 1 := by
  let p := S.primitiveSourceProjectiveLabel D
  have hmiddle := congrFun
    (S.projectiveHomVectorFGObj_middle_eq_add
      (S.ambientARShortComplex_shortExact N.ambientLabel)) p
  have hq : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶
        S.fgObj N.rightMarker.1) = 1 := by
    rw [← S.primitiveMultiplicity_eq_sourceHom D]
    exact N.rightMarker_primitiveMultiplicity_eq_one B
  have hN : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶ S.fgObj N.label.1) = 0 := by
    rw [← S.primitiveMultiplicity_eq_sourceHom D]
    exact
      (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero
        D N.label.1).1 N.label.2
  change
    (Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶
        (S.minimalRightAlmostSplitAt N.label.1).middle) : ℤ) =
      (Module.finrank k
        (S.fgObj (S.primitiveSourceLabel D) ⟶
          S.fgObj N.rightMarker.1) : ℤ) +
      (Module.finrank k
        (S.fgObj (S.primitiveSourceLabel D) ⟶
          S.fgObj N.label.1) : ℤ) at hmiddle
  rw [hq, hN] at hmiddle
  norm_num at hmiddle
  exact_mod_cast hmiddle

/-- In the fixed ambient decomposition of the AR middle, the sum of all
primitive coordinates is one. -/
theorem ambientMiddle_primitiveMultiplicity_sum_eq_one
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ∑ i : Fin
        (S.chosenLabelDecomposition
          (S.minimalRightAlmostSplitAt N.label.1).middle).n,
      S.primitiveMultiplicity D
        ((S.chosenLabelDecomposition
          (S.minimalRightAlmostSplitAt N.label.1).middle).label i) = 1 := by
  let V := (S.minimalRightAlmostSplitAt N.label.1).middle
  let c := S.chosenLabelDecomposition V
  rw [show (∑ i : Fin c.n,
      S.primitiveMultiplicity D (c.label i)) =
      ∑ i : Fin c.n, Module.finrank k
        (S.fgObj (S.primitiveSourceLabel D) ⟶ S.fgObj (c.label i)) by
    congr 1
    funext i
    exact S.primitiveMultiplicity_eq_sourceHom D (c.label i)]
  rw [← MagnitudeConjecture.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
    k (S.fgObj (S.primitiveSourceLabel D)) V
      (fun i : Fin c.n ↦ S.fgObj (c.label i)) c.iso]
  exact N.ambientMiddle_primitiveSourceHom_finrank_eq_one B

/-- Exactly one displayed ambient middle summand has nonzero primitive
coordinate, and that coordinate is one. -/
theorem exists_unique_ambientMiddle_primitiveSummand
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ∃ i : Fin
        (S.chosenLabelDecomposition
          (S.minimalRightAlmostSplitAt N.label.1).middle).n,
      ∀ j,
        S.primitiveMultiplicity D
          ((S.chosenLabelDecomposition
            (S.minimalRightAlmostSplitAt N.label.1).middle).label j) =
          if j = i then 1 else 0 := by
  classical
  let V := (S.minimalRightAlmostSplitAt N.label.1).middle
  let c := S.chosenLabelDecomposition V
  change ∃ i : Fin c.n, ∀ j : Fin c.n,
    S.primitiveMultiplicity D (c.label j) =
      if j = i then 1 else 0
  let d : Fin c.n →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm
      (fun i ↦ S.primitiveMultiplicity D (c.label i))
  have hd : d.sum (fun _ n ↦ n) = 1 := by
    simpa [d, Finsupp.sum_fintype] using
      N.ambientMiddle_primitiveMultiplicity_sum_eq_one B
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d).mp hd
  refine ⟨i, fun j ↦ ?_⟩
  have hj := congrFun
    (congrArg (fun z ↦ Finsupp.equivFunOnFinite z) hi) j
  by_cases hji : j = i
  · subst j
    simpa [d] using hj
  · have hij : i ≠ j := Ne.symm hji
    simpa [d, hji, hij] using hj

/-- The unique displayed ambient middle summand carrying the deleted
primitive coordinate. -/
def exceptionalMiddleIndex
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Fin
      (S.chosenLabelDecomposition
        (S.minimalRightAlmostSplitAt N.label.1).middle).n :=
  Classical.choose (N.exists_unique_ambientMiddle_primitiveSummand B)

/-- The primitive coordinate of every displayed middle summand, relative
to the exceptional index. -/
theorem exceptionalMiddleIndex_spec
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (j : Fin
      (S.chosenLabelDecomposition
        (S.minimalRightAlmostSplitAt N.label.1).middle).n) :
    S.primitiveMultiplicity D
      ((S.chosenLabelDecomposition
        (S.minimalRightAlmostSplitAt N.label.1).middle).label j) =
      if j = N.exceptionalMiddleIndex B then 1 else 0 :=
  Classical.choose_spec
    (N.exists_unique_ambientMiddle_primitiveSummand B) j

/-- The label of the unique ambient middle summand containing the deleted
primitive coordinate. -/
def exceptionalMiddleLabel
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) : Fin S.n :=
  (S.chosenLabelDecomposition
    (S.minimalRightAlmostSplitAt N.label.1).middle).label
      (N.exceptionalMiddleIndex B)

/-- The manuscript's exceptional middle summand `Y`. -/
abbrev exceptionalMiddleModule
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    FinitelyGeneratedCategory A :=
  S.fgObj (N.exceptionalMiddleLabel B)

/-- The exceptional summand has primitive coordinate one. -/
theorem exceptionalMiddle_primitiveMultiplicity_eq_one
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.primitiveMultiplicity D (N.exceptionalMiddleLabel B) = 1 := by
  simpa [exceptionalMiddleLabel] using
    N.exceptionalMiddleIndex_spec B (N.exceptionalMiddleIndex B)

/-- The exceptional summand is not an `A/AeA`-module. -/
theorem exceptionalMiddleLabel_not_mem
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.exceptionalMiddleLabel B ∉ S.primitiveKilledLabels D := by
  intro hmem
  have hzero :=
    (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D
      (N.exceptionalMiddleLabel B)).1 hmem
  rw [N.exceptionalMiddle_primitiveMultiplicity_eq_one B] at hzero
  norm_num at hzero

/-- Every other displayed ambient middle summand is an `A/AeA`-module. -/
theorem ambientMiddleLabel_mem_of_ne_exceptional
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (j : Fin
      (S.chosenLabelDecomposition
        (S.minimalRightAlmostSplitAt N.label.1).middle).n)
    (hj : j ≠ N.exceptionalMiddleIndex B) :
    (S.chosenLabelDecomposition
      (S.minimalRightAlmostSplitAt N.label.1).middle).label j ∈
        S.primitiveKilledLabels D := by
  apply
    (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero D _).2
  rw [N.exceptionalMiddleIndex_spec B j, if_neg hj]

/-- The direct sum of all displayed ambient middle summands except the
exceptional summand `Y`. -/
abbrev ambientMiddleComplement
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    FinitelyGeneratedCategory A :=
  let V := (S.minimalRightAlmostSplitAt N.label.1).middle
  let c := S.chosenLabelDecomposition V
  ⨁ fun j : {j : Fin c.n // j ≠ N.exceptionalMiddleIndex B} ↦
    S.fgObj (c.label j.1)

/-- The selected ambient decomposition splits the AR middle as
`V₀ ⊕ Y`. -/
def ambientMiddleSplitIso
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.minimalRightAlmostSplitAt N.label.1).middle ≅
      N.ambientMiddleComplement B ⊞ N.exceptionalMiddleModule B :=
  let V := (S.minimalRightAlmostSplitAt N.label.1).middle
  let c := S.chosenLabelDecomposition V
  let F := fun j : Fin c.n ↦ S.fgObj (c.label j)
  c.iso.trans
    (MagnitudeConjecture.CategoryTheory.biproductSplitAtIso F
      (N.exceptionalMiddleIndex B))

/-- Every summand of `V₀` is an `A/AeA`-module, so `V₀` itself is
annihilated by `AeA`. -/
theorem ambientMiddleComplement_isAnnihilatedBy
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    IsAnnihilatedBy (primitiveIdeal e) (N.ambientMiddleComplement B) := by
  let V := (S.minimalRightAlmostSplitAt N.label.1).middle
  let c := S.chosenLabelDecomposition V
  let i := N.exceptionalMiddleIndex B
  let J := {j : Fin c.n // j ≠ i}
  let F := fun j : J ↦ S.fgObj (c.label j.1)
  have hcoordinate : Module.finrank k
      (idempotentCoordinate (k := k) e (N.ambientMiddleComplement B)) = 0 := by
    rw [← (S.primitiveSourceHomCoordinateEquiv D
      (N.ambientMiddleComplement B)).finrank_eq]
    rw [MagnitudeConjecture.CategoryTheory.finrank_hom_eq_sum_of_iso_biproduct
      k (S.fgObj (S.primitiveSourceLabel D))
        (N.ambientMiddleComplement B) F (Iso.refl _)]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [← S.primitiveMultiplicity_eq_sourceHom D (c.label j.1)]
    simpa [i, j.2] using N.exceptionalMiddleIndex_spec B j.1
  exact (isAnnihilatedBy_primitiveIdeal_iff e _).2
    ((finrank_idempotentCoordinate_eq_zero_iff D.idempotent _).1
      hcoordinate)

/-- Applying primitive torsion to the manuscript split gives
`R(V) ≅ V₀ ⊕ R(Y)`: torsion fixes the killed complement and acts only on
the exceptional summand. -/
def primitiveTorsionAmbientMiddleSplitIso
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    primitiveTorsionFGObj e
        (S.minimalRightAlmostSplitAt N.label.1).middle ≅
      N.ambientMiddleComplement B ⊞
        primitiveTorsionFGObj e (N.exceptionalMiddleModule B) :=
  (primitiveTorsionFunctor e).mapIso (N.ambientMiddleSplitIso B) ≪≫
    primitiveTorsionBiprodIso e (N.ambientMiddleComplement B)
      (N.exceptionalMiddleModule B) ≪≫
    biprod.mapIso
      (primitiveTorsionIsoOfIsAnnihilated e
        (N.ambientMiddleComplement B)
        (N.ambientMiddleComplement_isAnnihilatedBy B))
      (Iso.refl _)

/-- The canonical inclusion of the exceptional summand into the selected
ambient decomposition. -/
def exceptionalMiddleInclusion
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.exceptionalMiddleModule B ⟶
      (S.minimalRightAlmostSplitAt N.label.1).middle :=
  let c := S.chosenLabelDecomposition
    (S.minimalRightAlmostSplitAt N.label.1).middle
  biproduct.ι (fun j : Fin c.n ↦ S.fgObj (c.label j))
      (N.exceptionalMiddleIndex B) ≫ c.iso.inv

/-- The exceptional summand inclusion is monic. -/
theorem exceptionalMiddleInclusion_mono
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Mono (N.exceptionalMiddleInclusion B) := by
  let c := S.chosenLabelDecomposition
    (S.minimalRightAlmostSplitAt N.label.1).middle
  let F := fun j : Fin c.n ↦ S.fgObj (c.label j)
  let i := N.exceptionalMiddleIndex B
  letI : IsSplitMono (biproduct.ι F i) := biproduct.ι_mono F i
  change Mono (biproduct.ι F i ≫ c.iso.inv)
  infer_instance

/-- Positivity forces `Hom_A(S_e,Y)=0` for the exceptional summand. -/
theorem hom_primitiveDeletedSimple_to_exceptionalMiddle_eq_zero
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive)
    (f : S.primitiveDeletedSimple D ⟶ N.exceptionalMiddleModule B) :
    f = 0 := by
  letI : Mono (N.exceptionalMiddleInclusion B) :=
    N.exceptionalMiddleInclusion_mono B
  apply (cancel_mono (N.exceptionalMiddleInclusion B)).1
  have hzero :=
    N.hom_primitiveDeletedSimple_to_ambientMiddle_eq_zero hpositive
      (f ≫ N.exceptionalMiddleInclusion B)
  calc
    f ≫ N.exceptionalMiddleInclusion B = 0 := hzero
    _ = 0 ≫ N.exceptionalMiddleInclusion B := zero_comp.symm

/-- A module receiving a one-dimensional Hom space from the primitive
projective has nonzero primitive torsion-free quotient. -/
theorem primitiveTorsionQuotient_nontrivial_of_sourceHom_finrank_eq_one
    (M : FinitelyGeneratedCategory A)
    (hfinrank : Module.finrank k
      (S.fgObj (S.primitiveSourceLabel D) ⟶ M) = 1) :
    Nontrivial (primitiveTorsionQuotientFGObj e M) := by
  letI : Nontrivial
      (S.fgObj (S.primitiveSourceLabel D) ⟶ M) :=
    Module.nontrivial_of_finrank_pos
      (hfinrank.symm ▸ Nat.zero_lt_one)
  obtain ⟨f, hf⟩ := exists_ne
    (0 : S.fgObj (S.primitiveSourceLabel D) ⟶ M)
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  let T : ShortComplex (FinitelyGeneratedCategory A) :=
    ShortComplex.mk (primitiveTorsionInclusion e M)
      (primitiveTorsionQuotientMk e M)
      (primitiveTorsionInclusion_comp_quotientMk e M)
  letI : Subsingleton T.X₃ := by
    change Subsingleton (primitiveTorsionQuotientFGObj e M)
    exact hsub
  have hT : T.ShortExact :=
    primitiveTorsionQuotient_fg_shortExact e M
  letI : Mono T.f := hT.mono_f
  have hcomp : f ≫ T.g = 0 := by
    apply FGModuleCat.hom_ext
    exact Subsingleton.elim _ _
  let lift : S.fgObj (S.primitiveSourceLabel D) ⟶ T.X₁ :=
    hT.exact.lift f hcomp
  have hlift : lift = 0 := by
    apply hom_primitiveSource_to_eq_zero (S := S) (D := D)
    exact primitiveTorsionFGObj_isAnnihilatedBy e M
  apply hf
  calc
    f = lift ≫ T.f := (hT.exact.lift_f f hcomp).symm
    _ = 0 := by rw [hlift, zero_comp]

/-- The exceptional summand's canonical torsion sequence
`0 -> R(Y) -> Y -> T_Y -> 0`. -/
def exceptionalMiddleTorsionShortComplex
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ShortComplex (FinitelyGeneratedCategory A) :=
  ShortComplex.mk
    (primitiveTorsionInclusion e (N.exceptionalMiddleModule B))
    (primitiveTorsionQuotientMk e (N.exceptionalMiddleModule B))
    (primitiveTorsionInclusion_comp_quotientMk e
      (N.exceptionalMiddleModule B))

/-- The exceptional summand's torsion sequence is short exact. -/
theorem exceptionalMiddleTorsionShortComplex_shortExact
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (N.exceptionalMiddleTorsionShortComplex B).ShortExact := by
  exact primitiveTorsionQuotient_fg_shortExact e
    (N.exceptionalMiddleModule B)

/-- The exceptional torsion-free quotient `T_Y` is nonzero. -/
theorem exceptionalMiddleTorsionQuotient_nontrivial
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    Nontrivial
      (primitiveTorsionQuotientFGObj e
        (N.exceptionalMiddleModule B)) := by
  apply primitiveTorsionQuotient_nontrivial_of_sourceHom_finrank_eq_one
    (S := S) (D := D)
  rw [← S.primitiveMultiplicity_eq_sourceHom D]
  exact N.exceptionalMiddle_primitiveMultiplicity_eq_one B

/-- The connecting map
`Hom_A(S_e,T_Y) -> Ext¹_A(S_e,R(Y))`. -/
def exceptionalPositiveConnectingLinear
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.primitiveDeletedSimple D ⟶
        primitiveTorsionQuotientFGObj e
          (N.exceptionalMiddleModule B)) →ₗ[k]
      Ext.{u} (S.primitiveDeletedSimple D)
        (primitiveTorsionFGObj e (N.exceptionalMiddleModule B)) 1 :=
  MagnitudeConjecture.InjectivePresentationExt.connectingLinear
    (k := k) (N.exceptionalMiddleTorsionShortComplex_shortExact B)
      (S.primitiveDeletedSimple D)

/-- At a positive mesh, the exceptional-summand connecting map is
injective. -/
theorem exceptionalPositiveConnectingLinear_injective
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    Function.Injective (N.exceptionalPositiveConnectingLinear B) := by
  letI : Subsingleton
      (S.primitiveDeletedSimple D ⟶
        (N.exceptionalMiddleTorsionShortComplex B).X₂) :=
    ⟨fun f g ↦ by
      rw [N.hom_primitiveDeletedSimple_to_exceptionalMiddle_eq_zero
          B hpositive f,
        N.hom_primitiveDeletedSimple_to_exceptionalMiddle_eq_zero
          B hpositive g]⟩
  exact
    MagnitudeConjecture.InjectivePresentationExt.connectingLinear_injective_of_subsingleton_hom_middle
      (k := k) (N.exceptionalMiddleTorsionShortComplex_shortExact B)
        (S.primitiveDeletedSimple D)

/-- A chosen simple submodule of a nonzero primitive torsion-free
quotient. -/
def primitiveTorsionQuotientSimpleSubmodule
    (M : FinitelyGeneratedCategory A)
    (hT : Nontrivial (primitiveTorsionQuotientFGObj e M)) :
    Submodule Aᵐᵒᵖ (primitiveTorsionQuotientFGObj e M) := by
  let T := primitiveTorsionQuotientFGObj e M
  letI : Nontrivial T := hT
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ T :=
    fgModule_isFiniteLength (k := k) (A := A) T
  letI : IsArtinian Aᵐᵒᵖ T :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  letI : IsAtomic (Submodule Aᵐᵒᵖ T) :=
    isAtomic_of_orderBot_wellFounded_lt
      ((isArtinian_iff Aᵐᵒᵖ T).mp inferInstance)
  exact Classical.choose
    (IsAtomic.exists_atom (Submodule Aᵐᵒᵖ T))

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The chosen torsion-free socle submodule is simple. -/
theorem primitiveTorsionQuotientSimpleSubmodule_isSimpleModule
    (M : FinitelyGeneratedCategory A)
    (hT : Nontrivial (primitiveTorsionQuotientFGObj e M)) :
    IsSimpleModule Aᵐᵒᵖ
      (primitiveTorsionQuotientSimpleSubmodule
        (k := k) (A := A) M hT) := by
  apply isSimpleModule_iff_isAtom.mpr
  let T := primitiveTorsionQuotientFGObj e M
  letI : Nontrivial T := hT
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ T :=
    fgModule_isFiniteLength (k := k) (A := A) T
  letI : IsArtinian Aᵐᵒᵖ T :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  letI : IsAtomic (Submodule Aᵐᵒᵖ T) :=
    isAtomic_of_orderBot_wellFounded_lt
      ((isArtinian_iff Aᵐᵒᵖ T).mp inferInstance)
  exact Classical.choose_spec
    (IsAtomic.exists_atom (Submodule Aᵐᵒᵖ T))

/-- The chosen simple submodule, bundled as a finitely generated ambient
right module. -/
def primitiveTorsionQuotientSimpleFGObj
    (M : FinitelyGeneratedCategory A)
    (hT : Nontrivial (primitiveTorsionQuotientFGObj e M)) :
    FinitelyGeneratedCategory A :=
  FGModuleCat.of Aᵐᵒᵖ
    (primitiveTorsionQuotientSimpleSubmodule
      (k := k) (A := A) M hT)

/-- The bundled socle object remains simple. -/
theorem primitiveTorsionQuotientSimpleFGObj_isSimpleModule
    (M : FinitelyGeneratedCategory A)
    (hT : Nontrivial (primitiveTorsionQuotientFGObj e M)) :
    IsSimpleModule Aᵐᵒᵖ
      (primitiveTorsionQuotientSimpleFGObj
        (k := k) (A := A) M hT) := by
  exact primitiveTorsionQuotientSimpleSubmodule_isSimpleModule
    (k := k) (A := A) M hT

/-- The chosen simple submodule cannot be an `A/AeA`-module, because the
torsion-free quotient has no nonzero `AeA`-annihilated submodule. -/
theorem primitiveTorsionQuotientSimpleFGObj_not_isAnnihilatedBy
    (M : FinitelyGeneratedCategory A)
    (he : IsIdempotentElem e)
    (hT : Nontrivial (primitiveTorsionQuotientFGObj e M)) :
    ¬ IsAnnihilatedBy (primitiveIdeal e)
      (primitiveTorsionQuotientSimpleFGObj
        (k := k) (A := A) M hT) := by
  intro hL
  let T := primitiveTorsionQuotientFGObj e M
  let L := primitiveTorsionQuotientSimpleSubmodule
    (k := k) (A := A) M hT
  have hact : ∀ x : primitiveTorsionQuotientSimpleFGObj
      (k := k) (A := A) M hT,
      (MulOpposite.op e) • x = 0 :=
    (isAnnihilatedBy_primitiveIdeal_iff e _).1 hL
  have hle : L ≤ primitiveTorsionSubmodule e T := by
    intro x hx
    change ∀ r : Aᵐᵒᵖ, (MulOpposite.op e * r) • x = 0
    intro r
    rw [mul_smul]
    exact congrArg Subtype.val
      (hact (r •
        (⟨x, hx⟩ : primitiveTorsionQuotientSimpleFGObj
          (k := k) (A := A) M hT)))
  have hbot : primitiveTorsionSubmodule e T = ⊥ :=
    primitiveTorsionQuotient_torsionSubmodule_eq_bot he M
  have hLbot : L = ⊥ := by
    apply le_bot_iff.mp
    rw [← hbot]
    exact hle
  have hAtom : IsAtom L :=
    isSimpleModule_iff_isAtom.mp
      (primitiveTorsionQuotientSimpleSubmodule_isSimpleModule
        (k := k) (A := A) M hT)
  exact hAtom.ne_bot hLbot

/-- The deleted simple occurs in the socle of the torsion-free quotient:
there is a nonzero map from `S_e`. -/
theorem exists_nonzero_hom_primitiveDeletedSimple_to_torsionQuotient
    (M : FinitelyGeneratedCategory A)
    (hT : Nontrivial (primitiveTorsionQuotientFGObj e M)) :
    ∃ f : S.primitiveDeletedSimple D ⟶
        primitiveTorsionQuotientFGObj e M,
      f ≠ 0 := by
  let T := primitiveTorsionQuotientFGObj e M
  let L := primitiveTorsionQuotientSimpleSubmodule
    (k := k) (A := A) M hT
  let Lfg := primitiveTorsionQuotientSimpleFGObj
    (k := k) (A := A) M hT
  letI : IsSimpleModule Aᵐᵒᵖ Lfg :=
    primitiveTorsionQuotientSimpleFGObj_isSimpleModule
      (k := k) (A := A) M hT
  have hnot : ¬ IsAnnihilatedBy (primitiveIdeal e) Lfg :=
    primitiveTorsionQuotientSimpleFGObj_not_isAnnihilatedBy
      (k := k) (A := A) M D.idempotent hT
  have hnotact : ¬ ∀ x : Lfg, (MulOpposite.op e) • x = 0 := by
    intro hact
    apply hnot
    exact (isAnnihilatedBy_primitiveIdeal_iff e Lfg).2 hact
  obtain ⟨x, hx⟩ := not_forall.mp hnotact
  let y : idempotentCoordinate (k := k) e Lfg :=
    ⟨(MulOpposite.op e) • x, ⟨x, rfl⟩⟩
  have hy : y ≠ 0 := by
    intro hzero
    apply hx
    exact congrArg Subtype.val hzero
  let f : S.fgObj (S.primitiveSourceLabel D) ⟶ Lfg :=
    (S.primitiveSourceHomCoordinateEquiv D Lfg).symm y
  have hf : f ≠ 0 := by
    intro hzero
    apply hy
    calc
      y = S.primitiveSourceHomCoordinateEquiv D Lfg f := by
        simp [f]
      _ = 0 := by rw [hzero, map_zero]
  have hjacTarget : Module.jacobson Aᵐᵒᵖ Lfg = ⊥ :=
    IsSimpleModule.jacobson_eq_bot Aᵐᵒᵖ Lfg
  have hjac :
      Module.jacobson Aᵐᵒᵖ
          (S.fgObj (S.primitiveSourceLabel D)) ≤
        LinearMap.ker f.hom.hom := by
    have hle := Module.le_comap_jacobson f.hom.hom
    rw [hjacTarget, Submodule.comap_bot] at hle
    exact hle
  let bar : S.primitiveDeletedSimple D ⟶ Lfg :=
    FGModuleCat.ofHom
      ((Module.jacobson Aᵐᵒᵖ
        (S.fgObj (S.primitiveSourceLabel D))).liftQ f.hom.hom
          hjac)
  have hbarcomp : S.primitiveDeletedSimpleProjection D ≫ bar = f := by
    apply FGModuleCat.hom_ext
    ext z
    rfl
  have hbar : bar ≠ 0 := by
    intro hzero
    apply hf
    rw [← hbarcomp, hzero, comp_zero]
  let inc : Lfg ⟶ T :=
    FGModuleCat.ofHom L.subtype
  refine ⟨bar ≫ inc, ?_⟩
  intro hzero
  apply hbar
  apply FGModuleCat.hom_ext
  ext z
  apply Subtype.val_injective
  have hz := DFunLike.congr_fun
    (congrArg (fun g ↦ g.hom.hom) hzero) z
  exact hz

/-- A fixed nonzero deleted-simple map into the exceptional torsion-free
quotient `T_Y`. -/
def exceptionalPrimitiveDeletedSocleMap
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.primitiveDeletedSimple D ⟶
      primitiveTorsionQuotientFGObj e
        (N.exceptionalMiddleModule B) :=
  Classical.choose
    (exists_nonzero_hom_primitiveDeletedSimple_to_torsionQuotient
      (S := S) (D := D) (N.exceptionalMiddleModule B)
        (N.exceptionalMiddleTorsionQuotient_nontrivial B))

/-- The fixed socle map is nonzero. -/
theorem exceptionalPrimitiveDeletedSocleMap_ne_zero
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.exceptionalPrimitiveDeletedSocleMap B ≠ 0 :=
  Classical.choose_spec
    (exists_nonzero_hom_primitiveDeletedSimple_to_torsionQuotient
      (S := S) (D := D) (N.exceptionalMiddleModule B)
        (N.exceptionalMiddleTorsionQuotient_nontrivial B))

/-- The extension class obtained by applying the torsion-sequence
connecting map to the fixed deleted-simple socle map. -/
def positiveConnectingClass
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D) :=
  N.exceptionalPositiveConnectingLinear B
    (N.exceptionalPrimitiveDeletedSocleMap B)

/-- At a positive new mesh, the selected connecting extension class is
nonzero. -/
theorem positiveConnectingClass_ne_zero
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    N.positiveConnectingClass B ≠ 0 := by
  intro hzero
  apply N.exceptionalPrimitiveDeletedSocleMap_ne_zero B
  apply N.exceptionalPositiveConnectingLinear_injective B hpositive
  rw [map_zero]
  exact hzero

/-- Some displayed indecomposable summand of `R(Y)` receives a nonzero
component of the positive connecting class. -/
theorem exists_positiveConnectingSummand
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
    let c := S.chosenLabelDecomposition RY
    ∃ i : Fin c.n,
      (Ext.addEquivBiproduct (S.primitiveDeletedSimple D)
        (biproduct.isBilimit
          (fun j : Fin c.n ↦ S.fgObj (c.label j))) 1)
        ((N.positiveConnectingClass B).comp
          (Ext.mk₀ c.iso.hom) (add_zero 1)) i ≠ 0 := by
  classical
  dsimp only
  let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
  let c := S.chosenLabelDecomposition RY
  let F := fun j : Fin c.n ↦ S.fgObj (c.label j)
  let xi := N.positiveConnectingClass B
  let eta : Ext.{u} (S.primitiveDeletedSimple D) (⨁ F) 1 :=
    xi.comp (Ext.mk₀ c.iso.hom) (add_zero 1)
  have heta : eta ≠ 0 := by
    intro hzero
    apply N.positiveConnectingClass_ne_zero B hpositive
    have hback := congrArg
      (fun z ↦ z.comp (Ext.mk₀ c.iso.inv) (add_zero 1)) hzero
    simpa [eta, xi, Ext.comp_assoc_of_second_deg_zero] using hback
  by_contra hall
  have hall' : ∀ i,
      (Ext.addEquivBiproduct (S.primitiveDeletedSimple D)
        (biproduct.isBilimit F) 1) eta i = 0 := by
    intro i
    exact not_ne_iff.mp ((not_exists.mp hall) i)
  apply heta
  apply (Ext.addEquivBiproduct
    (S.primitiveDeletedSimple D) (biproduct.isBilimit F) 1).injective
  funext i
  simpa [eta] using hall' i

/-- A fixed summand index of `R(Y)` on which the connecting class is
nonzero. -/
def positiveConnectingSummandIndex
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    Fin
      (S.chosenLabelDecomposition
        (primitiveTorsionFGObj e
          (N.exceptionalMiddleModule B))).n :=
  Classical.choose (N.exists_positiveConnectingSummand B hpositive)

/-- The nonzero Ext component at the fixed summand index. -/
theorem positiveConnectingSummand_ne_zero
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
    let c := S.chosenLabelDecomposition RY
    (Ext.addEquivBiproduct (S.primitiveDeletedSimple D)
      (biproduct.isBilimit
        (fun j : Fin c.n ↦ S.fgObj (c.label j))) 1)
      ((N.positiveConnectingClass B).comp
        (Ext.mk₀ c.iso.hom) (add_zero 1))
      (N.positiveConnectingSummandIndex B hpositive) ≠ 0 :=
  Classical.choose_spec (N.exists_positiveConnectingSummand B hpositive)

/-- The quotient label `Z` selected by the nonzero positive connecting
component. -/
def positiveSourceLabel
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) : S.PrimitiveQuotientLabel D := by
  let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
  let c := S.chosenLabelDecomposition RY
  let i := N.positiveConnectingSummandIndex B hpositive
  exact ⟨c.label i,
    S.chosenLabelDecomposition_label_mem_primitiveKilledLabels D RY
      (primitiveTorsionFGObj_isAnnihilatedBy e
        (N.exceptionalMiddleModule B)) i⟩

/-- The selected positive source is ambient noninjective, as witnessed by
its nonzero degree-one Ext component. -/
theorem positiveSourceLabel_not_injective
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    ¬ Injective (S.fgObj (N.positiveSourceLabel B hpositive).1) := by
  intro hInjective
  let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
  let c := S.chosenLabelDecomposition RY
  let i := N.positiveConnectingSummandIndex B hpositive
  change Injective (S.fgObj (c.label i)) at hInjective
  letI : Injective (S.fgObj (c.label i)) := hInjective
  apply N.positiveConnectingSummand_ne_zero B hpositive
  exact Ext.eq_zero_of_injective _

/-- The positive pair source bundled with the noninjectivity needed to form
its inverse Auslander--Reiten translate. -/
def positiveSourceNoninjectiveLabel
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
  ⟨(N.positiveSourceLabel B hpositive).1,
    N.positiveSourceLabel_not_injective B hpositive⟩

/-- The ambient label `τ_A⁻¹ Z` used to read the sign of the positive
gaining pair selected at a new mesh. -/
def positiveSourceLeftMarkerAmbientLabel
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) : Fin S.n :=
  ((S.rightTranslationEquiv).symm
    (N.positiveSourceNoninjectiveLabel B hpositive)).1

/-- The selected positive gaining-pair source has positive source marker:
there is a nonzero map `τ_A⁻¹ Z ⟶ S_e`. -/
theorem exists_nonzero_positiveSourceMarker [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    ∃ f : S.fgObj
        (N.positiveSourceLeftMarkerAmbientLabel B hpositive) ⟶
          S.primitiveDeletedSimple D,
      f ≠ 0 := by
  let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
  let c := S.chosenLabelDecomposition RY
  let i := N.positiveConnectingSummandIndex B hpositive
  let xi : Ext.{u} (S.primitiveDeletedSimple D)
      (S.fgObj (c.label i)) 1 :=
    (Ext.addEquivBiproduct (S.primitiveDeletedSimple D)
      (biproduct.isBilimit
        (fun j : Fin c.n ↦ S.fgObj (c.label j))) 1)
      ((N.positiveConnectingClass B).comp
        (Ext.mk₀ c.iso.hom) (add_zero 1)) i
  have hxi : xi ≠ 0 :=
    N.positiveConnectingSummand_ne_zero B hpositive
  exact S.exists_nonzero_hom_inverseTranslation_of_extOne_ne_zero
    H (N.positiveSourceNoninjectiveLabel B hpositive)
      (S.primitiveDeletedSimple D) xi hxi

/-- The selected label occurs with positive multiplicity in `R(Y)`. -/
theorem positiveSourceLabel_multiplicity_positive
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    0 < S.indecomposableMultiplicity
      (N.positiveSourceLabel B hpositive).1
      (primitiveTorsionFGObj e (N.exceptionalMiddleModule B)) := by
  let RY := primitiveTorsionFGObj e (N.exceptionalMiddleModule B)
  let c := S.chosenLabelDecomposition RY
  let i := N.positiveConnectingSummandIndex B hpositive
  rw [S.indecomposableMultiplicity_eq_of_decomposition
    (N.positiveSourceLabel B hpositive).1 RY c.iso]
  apply Finset.sum_pos'
  · intro j _hj
    exact Nat.zero_le _
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simp [positiveSourceLabel, RY, c, i]

/-- At a positive new mesh, the selected quotient label occurs strictly
more often in the relative middle `R(V)` than in the ambient AR middle
`V`. -/
theorem positiveSourceLabel_strict_multiplicity
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hpositive : N.IsPositive) :
    N.relativeArrowMultiplicity (N.positiveSourceLabel B hpositive) >
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (N.positiveSourceLabel B hpositive).1 N.label.1 := by
  let Z := N.positiveSourceLabel B hpositive
  let V := (S.minimalRightAlmostSplitAt N.label.1).middle
  let V₀ := N.ambientMiddleComplement B
  let Y := N.exceptionalMiddleModule B
  let RY := primitiveTorsionFGObj e Y
  have hRY : 0 < S.indecomposableMultiplicity Z.1 RY :=
    N.positiveSourceLabel_multiplicity_positive B hpositive
  have hYZ : N.exceptionalMiddleLabel B ≠ Z.1 := by
    intro h
    apply N.exceptionalMiddleLabel_not_mem B
    rw [h]
    exact Z.2
  have hY : S.indecomposableMultiplicity Z.1 Y = 0 := by
    rw [S.indecomposableMultiplicity_fgObj]
    simp [hYZ]
  have hambient : S.indecomposableMultiplicity Z.1 V =
      S.indecomposableMultiplicity Z.1 V₀ := by
    calc
      S.indecomposableMultiplicity Z.1 V =
          S.indecomposableMultiplicity Z.1 (V₀ ⊞ Y) :=
        S.indecomposableMultiplicity_iso_invariant Z.1
          (N.ambientMiddleSplitIso B)
      _ = S.indecomposableMultiplicity Z.1 V₀ +
          S.indecomposableMultiplicity Z.1 Y :=
        S.indecomposableMultiplicity_biprod Z.1 V₀ Y
      _ = S.indecomposableMultiplicity Z.1 V₀ := by rw [hY, Nat.add_zero]
  have hVambient : S.indecomposableMultiplicity Z.1 V =
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData Z.1 N.label.1 := by
    simpa only [V,
      S.meshRightAlmostSplitAt_eq_of_not_projective
        N.label.1 N.ambient_nonprojective] using
      S.indecomposableMultiplicity_meshRightMiddle Z.1 N.label.1
  change S.indecomposableMultiplicity Z.1 N.middleModule >
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData Z.1 N.label.1
  rw [← hVambient]
  calc
    S.indecomposableMultiplicity Z.1 N.middleModule =
        S.indecomposableMultiplicity Z.1 (V₀ ⊞ RY) :=
      S.indecomposableMultiplicity_iso_invariant Z.1
        (N.primitiveTorsionAmbientMiddleSplitIso B)
    _ = S.indecomposableMultiplicity Z.1 V₀ +
        S.indecomposableMultiplicity Z.1 RY :=
      S.indecomposableMultiplicity_biprod Z.1 V₀ RY
    _ > S.indecomposableMultiplicity Z.1 V₀ := by omega
    _ = S.indecomposableMultiplicity Z.1 V := hambient.symm

end PrimitiveNewRightMeshEndpoint

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
