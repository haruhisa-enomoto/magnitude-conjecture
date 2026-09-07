import MagnitudeConjecture.Algebra.RightModuleIyamaSaturation
import MagnitudeConjecture.Algebra.IdempotentSaturationProjective
import MagnitudeConjecture.Algebra.RightModuleNakayamaEmbedding
import MagnitudeConjecture.Algebra.RightModuleIyamaSubobjectReduction
import MagnitudeConjecture.Algebra.RightModuleIyamaBoundaryCover
import MagnitudeConjecture.Algebra.RightModuleIncidenceFullness
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# The saturated Auslander image of a represented subobject

Given a monomorphism from a poset space `Y` into a represented object, cover
`Y` by a represented boundary object and lift the composite into the factor
category.  Full-generator restricted Yoneda sends the lift to a map between
projective modules.  Its image `L` is enlarged by the boundary-idempotent
saturation constructed in `RightModuleIyamaSaturation`.

This is the literal module `M` in Iyama's proof of closure under subobjects.
The remaining homological layer proves that it is projective.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

namespace PrimitiveProjectivePosetData

/-- Lift the composite of the represented boundary cover with a map into a
represented object. -/
noncomputable def liftedSubobjectCoverMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.boundaryCoverObject Y ⟶ X :=
  Classical.choose
    ((R.representable_full H).map_surjective
      (R.representedBoundaryCoverMap H Y ≫ m))

/-- Restricted Yoneda sends the lifted cover to the requested composite. -/
theorem map_liftedSubobjectCoverMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.representableData.map (R.liftedSubobjectCoverMap H m) =
      R.representedBoundaryCoverMap H Y ≫ m :=
  Classical.choose_spec
    ((R.representable_full H).map_surjective
      (R.representedBoundaryCoverMap H Y ≫ m))

/-- The full-generator Auslander map induced by the lifted boundary cover. -/
def liftedSubobjectAuslanderMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    (S.factorAdditiveGenerator K ⟶ R.boundaryCoverObject Y) →ₗ[
      S.factorAuslanderRing K]
      (S.factorAdditiveGenerator K ⟶ X) :=
  ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map
    (R.liftedSubobjectCoverMap H m)).hom

/-- The raw image `L` of the lifted cover inside the represented Auslander
projective. -/
def liftedSubobjectImage
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    Submodule (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ X) :=
  LinearMap.range (R.liftedSubobjectAuslanderMap H m)

/-- Iyama's module `M`: the maximal boundary-invisible enlargement of the
lifted image `L`. -/
def saturatedSubobjectImage
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    Submodule (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ X) :=
  IdempotentSaturation.saturation
    (S.factorBoundaryIdempotent K)
    (R.liftedSubobjectImage H m)

/-- The raw lifted image is contained in its saturation. -/
theorem liftedSubobjectImage_le_saturatedSubobjectImage
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.liftedSubobjectImage H m ≤ R.saturatedSubobjectImage H m :=
  IdempotentSaturation.le_saturation _ _

/-- The image of the saturation in the quotient by `L` is annihilated by
the boundary idempotent. -/
theorem boundaryIdempotent_smul_mkQ_eq_zero_of_mem_saturatedSubobjectImage
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X)
    {x : S.factorAdditiveGenerator K ⟶ X}
    (hx : x ∈ R.saturatedSubobjectImage H m) :
    S.factorBoundaryIdempotent K •
        (R.liftedSubobjectImage H m).mkQ x = 0 :=
  IdempotentSaturation.smul_mkQ_eq_zero_of_mem_saturation _ _ hx

/-- Maximality of the actual saturated image among enlargements of `L` that
are invisible to the boundary idempotent. -/
theorem le_saturatedSubobjectImage_of_boundaryIdempotent_smul_mkQ_eq_zero
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X)
    (N : Submodule (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ X))
    (hN : ∀ x : S.factorAdditiveGenerator K ⟶ X, x ∈ N →
      S.factorBoundaryIdempotent K •
        (R.liftedSubobjectImage H m).mkQ x = 0) :
    N ≤ R.saturatedSubobjectImage H m :=
  IdempotentSaturation.le_saturation_of_smul_mkQ_eq_zero _ _ _ hN

/-- The quotient coordinate `M/L`, realized as the full idempotent-torsion
submodule of the ambient quotient. -/
abbrev saturatedSubobjectQuotientCoordinate
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :=
  IdempotentSaturation.torsionSubmodule
    (M := (S.factorAdditiveGenerator K ⟶ X) ⧸
      R.liftedSubobjectImage H m)
    (S.factorBoundaryIdempotent K)

/-- The quotient by Iyama's saturated image, bundled as a finitely generated
module over the factor Auslander algebra. -/
abbrev saturatedSubobjectAmbientQuotientFGObj
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    FGModuleCat.{u} (S.factorAuslanderRing K) :=
  FGModuleCat.of (S.factorAuslanderRing K)
    ((S.factorAdditiveGenerator K ⟶ X) ⧸
      R.saturatedSubobjectImage H m)

/-- Saturation removes all remaining boundary-idempotent torsion from the
ambient quotient `P/M`. -/
theorem torsionSubmodule_saturatedSubobjectAmbientQuotient_eq_bot
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    IdempotentSaturation.torsionSubmodule
        (M := (S.factorAdditiveGenerator K ⟶ X) ⧸
          R.saturatedSubobjectImage H m)
        (S.factorBoundaryIdempotent K) = ⊥ := by
  exact IdempotentSaturation.torsionSubmodule_quotient_saturation_eq_bot
    (S.factorBoundaryIdempotent_isIdempotentElem K)
    (R.liftedSubobjectImage H m)

/-- Every submodule of `P/M` invisible to the represented boundary
generator is zero.  This is the essentiality consequence of Iyama's maximal
saturation, stated without choosing an injective hull. -/
theorem submodule_eq_bot_of_hom_from_boundary_eq_zero
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X)
    (N : Submodule (S.factorAuslanderRing K)
      ((S.factorAdditiveGenerator K ⟶ X) ⧸
        R.saturatedSubobjectImage H m))
    (hzero : ∀ f :
      (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) →ₗ[
        S.factorAuslanderRing K] N,
      f = 0) :
    N = ⊥ := by
  let e := S.factorBoundaryIdempotent K
  have hann : ∀ z : N, e • z = 0 :=
    (S.factorProjectiveRepresentable_hom_eq_zero_iff K).1 hzero
  have hle : N ≤ IdempotentSaturation.torsionSubmodule
      (M := (S.factorAdditiveGenerator K ⟶ X) ⧸
        R.saturatedSubobjectImage H m) e := by
    apply IdempotentSaturation.le_torsionSubmodule e N
    intro z hz
    exact congrArg Subtype.val (hann ⟨z, hz⟩)
  rw [R.torsionSubmodule_saturatedSubobjectAmbientQuotient_eq_bot H m] at hle
  exact le_antisymm hle bot_le

/-- The finite Nakayama evaluation map from the saturated ambient quotient
to copies of the boundary Nakayama injective. -/
def saturatedSubobjectAmbientQuotientNakayamaMap
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    R.saturatedSubobjectAmbientQuotientFGObj H m →ₗ[
      S.factorAuslanderRing K]
      (Fin (Module.finrank k
          (S.factorBoundaryRepresentableFGObj K ⟶
            R.saturatedSubobjectAmbientQuotientFGObj H m)) →
        RightModule.projectiveNakayamaFGObj (k := k)
          (S.factorBoundaryRepresentableFGObj K)) :=
  RightModule.nakayamaEmbeddingMap (k := k)
    (S.factorBoundaryRepresentableFGObj K)
    (R.saturatedSubobjectAmbientQuotientFGObj H m)

/-- Maximal saturation makes the finite boundary Nakayama evaluation map
injective. -/
theorem saturatedSubobjectAmbientQuotientNakayamaMap_injective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    Function.Injective
      (R.saturatedSubobjectAmbientQuotientNakayamaMap H m) := by
  apply RightModule.nakayamaEmbeddingMap_injective (k := k)
  intro N hzero
  apply R.submodule_eq_bot_of_hom_from_boundary_eq_zero H m N
  intro f
  let f' : S.factorBoundaryRepresentableFGObj K ⟶
      FGModuleCat.of (S.factorAuslanderRing K) N :=
    FGModuleCat.ofHom f
  have hf' : f' = 0 := hzero f'
  apply LinearMap.ext
  intro p
  have hp := congrArg
    (fun q : S.factorBoundaryRepresentableFGObj K ⟶
        FGModuleCat.of (S.factorAuslanderRing K) N ↦ q.hom.hom p) hf'
  exact hp

/-- Iyama's boundary-Hom coordinate vanishes on `M/L`. -/
theorem hom_to_saturatedSubobjectQuotientCoordinate_eq_zero
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X) :
    ∀ f :
      (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) →ₗ[
        S.factorAuslanderRing K]
        R.saturatedSubobjectQuotientCoordinate H m,
      f = 0 := by
  apply (S.factorProjectiveRepresentable_hom_eq_zero_iff K).2
  intro x
  apply Subtype.ext
  exact IdempotentSaturation.smul_eq_zero_of_mem_torsionSubmodule _ x.2

/-- The final dimension shift in Iyama's proof, separated from the two
strict-tau inputs that construct the injective hull and control the global
dimension.  An embedding of `P/M` into a module of projective dimension at
most one has source of projective dimension at most one as soon as its
cokernel has projective dimension at most two. -/
theorem saturatedSubobjectQuotient_projectiveDimensionLE_one_of_injective
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X)
    {I : Type u} [AddCommGroup I] [Module (S.factorAuslanderRing K) I]
    (i : ((S.factorAdditiveGenerator K ⟶ X) ⧸
        R.saturatedSubobjectImage H m) →ₗ[S.factorAuslanderRing K] I)
    (hi : Function.Injective i)
    (hI : HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K) I) 1)
    (hcokernel : HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        (I ⧸ (LinearMap.range i))) 2) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        ((S.factorAdditiveGenerator K ⟶ X) ⧸
          R.saturatedSubobjectImage H m)) 1 :=
  IdempotentSaturation.projectiveDimensionLE_one_of_injective
    i hi hI hcokernel

/-- The saturated image is projective once the source's remaining quotient
projective-dimension bound is supplied. -/
theorem saturatedSubobjectImage_projective_of_quotient_projectiveDimensionLE_one
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X)
    (hquotient : HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        ((S.factorAdditiveGenerator K ⟶ X) ⧸
          R.saturatedSubobjectImage H m)) 1) :
    Projective
      (ModuleCat.of (S.factorAuslanderRing K)
        (R.saturatedSubobjectImage H m)) := by
  let G := S.factorAdditiveGenerator K
  have hRepresentableProjective :
      Projective ((preadditiveCoyonedaObj G).obj X) := by
    exact (S.factorAuslanderRepresentable_finiteProjective K X).2
  apply IdempotentSaturation.saturation_projective_of_quotient_projectiveDimensionLE_one
    (S.factorBoundaryIdempotent K) (R.liftedSubobjectImage H m)
  · change Projective ((preadditiveCoyonedaObj G).obj X)
    exact hRepresentableProjective
  · exact hquotient

/-- Once the quotient has projective dimension at most one, the saturated
module returns to a literal object of the factor category under the full
Auslander equivalence. -/
theorem exists_factorObject_representing_saturatedSubobjectImage
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {Y : PosetSpace.Obj k T} {X : S.FactorCategory K}
    (m : Y ⟶ R.representableData.obj X)
    (hquotient : HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        ((S.factorAdditiveGenerator K ⟶ X) ⧸
          R.saturatedSubobjectImage H m)) 1) :
    ∃ Z : S.FactorCategory K,
      Nonempty
        ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj Z ≅
          ModuleCat.of (S.factorAuslanderRing K)
            (R.saturatedSubobjectImage H m)) := by
  let G := S.factorAdditiveGenerator K
  have hProjective :
      Projective
        (ModuleCat.of (S.factorAuslanderRing K)
          (R.saturatedSubobjectImage H m)) :=
    R.saturatedSubobjectImage_projective_of_quotient_projectiveDimensionLE_one
      H m hquotient
  have hFinite : Module.Finite (S.factorAuslanderRing K)
      (R.saturatedSubobjectImage H m) := by
    letI : Module.Finite k (End (S.factorAdditiveGenerator K)) :=
      S.factorCategoryHomFinite K _ _
    letI : Module.Finite k (S.factorAuslanderRing K) := inferInstance
    letI : IsNoetherianRing (S.factorAuslanderRing K) :=
      IsNoetherianRing.of_finite k _
    letI : Module.Finite (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ X) :=
      (S.factorAuslanderRepresentable_finiteProjective K X).1
    infer_instance
  obtain ⟨Z, _, hZ⟩ :=
    CategoryTheory.exists_obj_homSelf_iso_of_finite_projective G
      (ModuleCat.of (S.factorAuslanderRing K)
        (R.saturatedSubobjectImage H m))
      ⟨hFinite, hProjective⟩
  exact ⟨Z, hZ⟩

end PrimitiveProjectivePosetData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
