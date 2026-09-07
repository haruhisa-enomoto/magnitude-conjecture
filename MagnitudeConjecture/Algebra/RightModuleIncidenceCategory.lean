import MagnitudeConjecture.Algebra.RightModulePrimitivePosetRealization
import MagnitudeConjecture.CategoryTheory.RepresentablePosetSpaceFullness
import MagnitudeConjecture.Combinatorics.PosetSpaceBoundary

/-!
# The primitive projective boundary is an incidence category

The root projective and the non-root projectives indexed by `T` form the
incidence category of the poset obtained by adjoining a new least element to
the dual of `T`.  This file records that statement without introducing a
second category: `boundaryLE q r` is exactly the condition for a morphism
from the boundary object indexed by `q` to the one indexed by `r`.

The normalized morphisms are the root identity, the chosen maps `P ⟶ P_t`,
and the normalized incidence maps `P_t ⟶ P_s`.  Every boundary morphism is a
unique scalar multiple of the corresponding normalized morphism, and all
off-incidence Hom spaces vanish.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.PosetSpace

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

/-- The root identity and each chosen `P ⟶ P_t` span the corresponding
root-to-boundary Hom space. -/
theorem boundaryUnit_spans
    (R : S.PrimitiveProjectivePosetData D T)
    (q : Option T)
    (a : R.representableData.source ⟶
      R.representableData.boundaryFamily q) :
    ∃ c : k, c • R.representableData.boundaryUnit q = a := by
  cases q with
  | none =>
      change ∃ c : k, c • 𝟙 R.representableData.source = a
      have hfinrank : Module.finrank k
          (R.representableData.source ⟶ R.representableData.source) = 1 :=
        (PrimitiveMultiplicityInput.factorHomFrom_finrank_eq_multiplicity
          (S := S) D D.source).trans
          (R.projective_multiplicity_eq_one D.sourceProjectiveLabel)
      have hid : (𝟙 R.representableData.source :
          R.representableData.source ⟶ R.representableData.source) ≠ 0 := by
        intro hzero
        exact S.factorObject_not_isZero K D.source
          ((IsZero.iff_id_eq_zero _).2 hzero)
      exact exists_smul_eq_of_finrank_eq_one hfinrank hid a
  | some t => exact R.exists_smul_unit_eq t a

/-- The normalized boundary morphism attached to an incidence relation. -/
def boundaryIncidenceMap
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) :
    R.representableData.boundaryFamily q ⟶
      R.representableData.boundaryFamily r := by
  cases q with
  | none =>
      cases r with
      | none => exact 𝟙 R.representableData.source
      | some s => exact R.unit s
  | some t =>
      cases r with
      | none => exact False.elim hqr
      | some s => exact R.incidenceMap hqr

@[reassoc]
theorem boundaryUnit_comp_boundaryIncidenceMap
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) :
    R.representableData.boundaryUnit q ≫
        R.boundaryIncidenceMap hqr =
      R.representableData.boundaryUnit r := by
  cases q with
  | none =>
      cases r with
      | none => simp [boundaryIncidenceMap,
          MagnitudeConjecture.PosetSpace.RepresentableData.boundaryUnit]
      | some s =>
          change 𝟙 R.representableData.source ≫ R.unit s = R.unit s
          simp
  | some t =>
      cases r with
      | none => exact False.elim hqr
      | some s => exact R.unit_comp_incidenceMap hqr

/-- Every normalized boundary incidence morphism is nonzero. -/
theorem boundaryIncidenceMap_ne_zero
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) :
    R.boundaryIncidenceMap hqr ≠ 0 := by
  intro hzero
  have hunit : R.representableData.boundaryUnit r = 0 := by
    rw [← R.boundaryUnit_comp_boundaryIncidenceMap hqr, hzero]
    simp
  cases r with
  | none =>
      exact S.factorObject_not_isZero K D.source
        ((IsZero.iff_id_eq_zero _).2 hunit)
  | some t => exact R.unit_ne_zero t hunit

/-- There are no morphisms from a non-root boundary projective back to the
root.  A nonzero such map together with `P ⟶ P_t` would give a directed
two-cycle between distinct surviving labels. -/
theorem projective_to_source_eq_zero
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (t : T) (f : R.projective t ⟶ R.representableData.source) :
    f = 0 := by
  by_contra hf
  have hlabel : R.label t = D.source :=
    H.factorObject_label_eq_of_two_way S K
      (R.label t) D.source f hf (R.unit t) (R.unit_ne_zero t)
  have hprojective :
      R.projectiveEquiv.symm (some t) = D.sourceProjectiveLabel := by
    apply Subtype.ext
    exact hlabel
  have hsome : some t = none := by
    calc
      some t = R.projectiveEquiv (R.projectiveEquiv.symm (some t)) :=
        (R.projectiveEquiv.apply_symm_apply (some t)).symm
      _ = R.projectiveEquiv D.sourceProjectiveLabel := by rw [hprojective]
      _ = none := R.source_eq_none
  exact Option.some_ne_none t hsome

/-- Off the augmented incidence relation, the corresponding boundary Hom
space is zero. -/
theorem boundaryHom_eq_zero_of_not_le
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {q r : Option T} (hqr : ¬ boundaryLE q r)
    (f : R.representableData.boundaryFamily q ⟶
      R.representableData.boundaryFamily r) :
    f = 0 := by
  cases q with
  | none => exact False.elim (hqr (by simp [boundaryLE]))
  | some t =>
      cases r with
      | none => exact R.projective_to_source_eq_zero H t f
      | some s => exact R.eq_zero_of_projectiveHom_of_not_le hqr f

/-- Every morphism along the augmented incidence relation is a scalar
multiple of its normalized incidence morphism. -/
theorem exists_smul_boundaryIncidenceMap_eq
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r)
    (f : R.representableData.boundaryFamily q ⟶
      R.representableData.boundaryFamily r) :
    ∃ c : k, c • R.boundaryIncidenceMap hqr = f := by
  cases q with
  | none =>
      cases r with
      | none =>
          simpa [boundaryIncidenceMap,
            MagnitudeConjecture.PosetSpace.RepresentableData.boundaryUnit]
            using R.boundaryUnit_spans none f
      | some s =>
          change ∃ c : k, c • R.unit s = f
          exact R.exists_smul_unit_eq s f
  | some t =>
      cases r with
      | none => exact False.elim hqr
      | some s => exact R.exists_smul_incidenceMap_eq hqr f

/-- The normalized boundary morphisms have literal incidence composition. -/
theorem boundaryIncidenceMap_comp
    (R : S.PrimitiveProjectivePosetData D T)
    {q r s : Option T}
    (hqr : boundaryLE q r) (hrs : boundaryLE r s) :
    R.boundaryIncidenceMap hqr ≫ R.boundaryIncidenceMap hrs =
      R.boundaryIncidenceMap (boundaryLE_trans hqr hrs) := by
  apply R.representableData.boundaryPrecomposition_injective
    (fun t X ↦ R.precomposition_injective t X) q
      (R.representableData.boundaryFamily s)
  simp only [MagnitudeConjecture.PosetSpace.RepresentableData.boundaryPrecomposition_apply]
  rw [← Category.assoc, R.boundaryUnit_comp_boundaryIncidenceMap hqr,
    R.boundaryUnit_comp_boundaryIncidenceMap hrs,
    R.boundaryUnit_comp_boundaryIncidenceMap]

/-- The normalized boundary morphism of a reflexive incidence relation is
the identity. -/
@[simp]
theorem boundaryIncidenceMap_refl
    (R : S.PrimitiveProjectivePosetData D T) (q : Option T) :
    R.boundaryIncidenceMap (boundaryLE_refl q) =
      𝟙 R.representableData.boundaryFamily q := by
  cases q with
  | none => rfl
  | some t =>
      exact (R.incidenceMap_unique (le_refl t) (𝟙 _)
        (Category.comp_id _)).symm

/-- Scalar multiples of a normalized boundary incidence morphism, as a
linear map from the coefficient field. -/
def boundaryIncidenceScalarLinearMap
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) :
    k →ₗ[k] (R.representableData.boundaryFamily q ⟶
      R.representableData.boundaryFamily r) where
  toFun c := c • R.boundaryIncidenceMap hqr
  map_add' c d := add_smul c d _
  map_smul' c d := by
    change (c * d) • R.boundaryIncidenceMap hqr =
      c • d • R.boundaryIncidenceMap hqr
    rw [smul_smul]

/-- Every on-incidence boundary Hom space is canonically one-dimensional,
with the normalized incidence morphism as basis vector. -/
def boundaryHomCoordinateEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) :
    (R.representableData.boundaryFamily q ⟶
      R.representableData.boundaryFamily r) ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (R.boundaryIncidenceScalarLinearMap hqr) ⟨by
    intro c d hcd
    change c • R.boundaryIncidenceMap hqr =
      d • R.boundaryIncidenceMap hqr at hcd
    have hzero : (c - d) • R.boundaryIncidenceMap hqr = 0 := by
      rw [sub_smul, hcd, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right
      (R.boundaryIncidenceMap_ne_zero hqr)),
    fun f ↦ R.exists_smul_boundaryIncidenceMap_eq hqr f⟩).symm

@[simp]
theorem boundaryHomCoordinateEquiv_symm_apply
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) (c : k) :
    (R.boundaryHomCoordinateEquiv hqr).symm c =
      c • R.boundaryIncidenceMap hqr :=
  rfl

@[simp]
theorem boundaryHomCoordinateEquiv_incidenceMap
    (R : S.PrimitiveProjectivePosetData D T)
    {q r : Option T} (hqr : boundaryLE q r) :
    R.boundaryHomCoordinateEquiv hqr (R.boundaryIncidenceMap hqr) = 1 := by
  apply (R.boundaryHomCoordinateEquiv hqr).symm.injective
  simp

/-- Boundary coordinates multiply under composition exactly as incidence
coefficients do. -/
theorem boundaryHomCoordinateEquiv_comp
    (R : S.PrimitiveProjectivePosetData D T)
    {q r s : Option T}
    (hqr : boundaryLE q r) (hrs : boundaryLE r s)
    (f : R.representableData.boundaryFamily q ⟶
      R.representableData.boundaryFamily r)
    (g : R.representableData.boundaryFamily r ⟶
      R.representableData.boundaryFamily s) :
    R.boundaryHomCoordinateEquiv (boundaryLE_trans hqr hrs) (f ≫ g) =
      R.boundaryHomCoordinateEquiv hqr f *
        R.boundaryHomCoordinateEquiv hrs g := by
  let c := R.boundaryHomCoordinateEquiv hqr f
  let d := R.boundaryHomCoordinateEquiv hrs g
  have hf : c • R.boundaryIncidenceMap hqr = f := by
    have h := (R.boundaryHomCoordinateEquiv hqr).symm_apply_apply f
    change c • R.boundaryIncidenceMap hqr = f at h
    exact h
  have hg : d • R.boundaryIncidenceMap hrs = g := by
    have h := (R.boundaryHomCoordinateEquiv hrs).symm_apply_apply g
    change d • R.boundaryIncidenceMap hrs = g at h
    exact h
  have hcomp : f ≫ g =
      (c * d) • R.boundaryIncidenceMap (boundaryLE_trans hqr hrs) := by
    rw [← hf, ← hg]
    simp only [Linear.comp_smul, Linear.smul_comp, smul_smul]
    rw [mul_comm d c, R.boundaryIncidenceMap_comp]
  rw [hcomp, LinearEquiv.map_smul,
    R.boundaryHomCoordinateEquiv_incidenceMap]
  simp [c, d]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData
