import MagnitudeConjecture.Algebra.RightModuleIncidenceCategory
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# The endomorphism algebra of the primitive boundary

The root-plus-projective boundary is indexed by the finite poset obtained by
adjoining a bottom element to `OrderDual T`.  Its opposite endomorphism ring
is therefore the ordinary incidence algebra of that augmented poset.  This is
the ring-level form of the incidence-category calculation.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MagnitudeConjecture.PosetSpace

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
variable {T : Type u} [Fintype T] [PartialOrder T]

private noncomputable instance boundaryIndexDecidableLE :
    DecidableLE (BoundaryIndex T) := Classical.decRel _

private noncomputable instance boundaryIndexDecidableLT :
    DecidableLT (BoundaryIndex T) := Classical.decRel _

/-- The boundary family reindexed by its actual augmented incidence poset. -/
abbrev incidenceBoundaryFamily
    (R : S.PrimitiveProjectivePosetData D T) (q : BoundaryIndex T) :
    S.FactorCategory K :=
  R.representableData.boundaryFamily q.toOption

/-- The biproduct of the incidence-indexed boundary family. -/
abbrev incidenceBoundaryGenerator
    (R : S.PrimitiveProjectivePosetData D T) : S.FactorCategory K :=
  ⨁ R.incidenceBoundaryFamily

private noncomputable instance boundaryIndexLocallyFiniteOrder :
    LocallyFiniteOrder (BoundaryIndex T) :=
  Fintype.toLocallyFiniteOrder

/-- Taking a `(q,r)` component is additive in the boundary endomorphism. -/
def boundaryEndComponentAddHom
    (R : S.PrimitiveProjectivePosetData D T)
    (q r : BoundaryIndex T) :
    End R.incidenceBoundaryGenerator →+
      (R.incidenceBoundaryFamily q ⟶ R.incidenceBoundaryFamily r) :=
  (Preadditive.leftComp _ (biproduct.ι R.incidenceBoundaryFamily q)).comp
    (Preadditive.rightComp _ (biproduct.π R.incidenceBoundaryFamily r))

/-- The `(q,r)` component of an endomorphism of the boundary generator. -/
def boundaryEndComponent
    (R : S.PrimitiveProjectivePosetData D T)
    (a : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) :
    R.incidenceBoundaryFamily q ⟶ R.incidenceBoundaryFamily r :=
  R.boundaryEndComponentAddHom q r a

theorem boundaryEndComponent_eq
    (R : S.PrimitiveProjectivePosetData D T)
    (a : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) :
    R.boundaryEndComponent a q r =
      biproduct.ι R.incidenceBoundaryFamily q ≫ a ≫
        biproduct.π R.incidenceBoundaryFamily r := by
  rfl

/-- Assemble a universe-polymorphic matrix of boundary morphisms.  Mathlib's
finite `biproduct.matrix` is intentionally small-universe, while the
representation-theoretic index type here lives in the algebra's universe. -/
def boundaryMatrix
    (R : S.PrimitiveProjectivePosetData D T)
    (m : ∀ q r, R.incidenceBoundaryFamily q ⟶
      R.incidenceBoundaryFamily r) :
    End R.incidenceBoundaryGenerator :=
  biproduct.desc fun q ↦ biproduct.lift fun r ↦ m q r

@[simp]
theorem boundaryEndComponent_boundaryMatrix
    (R : S.PrimitiveProjectivePosetData D T)
    (m : ∀ q r, R.incidenceBoundaryFamily q ⟶
      R.incidenceBoundaryFamily r)
    (q r : BoundaryIndex T) :
    R.boundaryEndComponent (R.boundaryMatrix m) q r = m q r := by
  rw [boundaryEndComponent_eq]
  simp [boundaryMatrix]

theorem boundaryMatrix_boundaryEndComponent
    (R : S.PrimitiveProjectivePosetData D T)
    (a : End R.incidenceBoundaryGenerator) :
    R.boundaryMatrix (R.boundaryEndComponent a) = a := by
  apply biproduct.hom_ext'
  intro q
  apply biproduct.hom_ext
  intro r
  simp [boundaryMatrix, boundaryEndComponent_eq, Category.assoc]

/-- The biproduct resolution of the identity, without Mathlib's small-index
restriction on the corresponding convenience theorem. -/
theorem boundaryBiproduct_total
    (R : S.PrimitiveProjectivePosetData D T) :
    (∑ z, biproduct.π R.incidenceBoundaryFamily z ≫
      biproduct.ι R.incidenceBoundaryFamily z) =
      𝟙 R.incidenceBoundaryGenerator := by
  classical
  apply biproduct.hom_ext'
  intro q
  simp only [Preadditive.comp_sum, ← Category.assoc, Category.comp_id]
  rw [Finset.sum_eq_single q]
  · simp
  · intro z _ hzq
    rw [biproduct.ι_π_ne _ hzq.symm, zero_comp]
  · simp

/-- Matrix multiplication for boundary endomorphisms, stated with a
universe-polymorphic finite sum. -/
theorem boundaryEndComponent_comp
    (R : S.PrimitiveProjectivePosetData D T)
    (a b : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) :
    R.boundaryEndComponent (a ≫ b) q r =
      ∑ z, R.boundaryEndComponent a q z ≫
        R.boundaryEndComponent b z r := by
  have htotal := R.boundaryBiproduct_total
  have hconjugated := congrArg
    (fun e ↦ biproduct.ι R.incidenceBoundaryFamily q ≫ a ≫ e ≫ b ≫
      biproduct.π R.incidenceBoundaryFamily r) htotal
  simp only [boundaryEndComponent_eq]
  simpa only [Category.assoc, Category.comp_id, Category.id_comp,
    Preadditive.comp_sum, Preadditive.sum_comp] using hconjugated.symm

/-- The scalar coordinate of one component of a boundary endomorphism. -/
def boundaryEndCoefficient
    (R : S.PrimitiveProjectivePosetData D T)
    (a : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) : k := by
  classical
  by_cases hqr : q ≤ r
  · exact R.boundaryHomCoordinateEquiv
      ((boundaryLE_toOption_iff_le q r).2 hqr)
      (R.boundaryEndComponent a q r)
  · exact 0

theorem boundaryEndCoefficient_add
    (R : S.PrimitiveProjectivePosetData D T)
    (a b : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) :
    R.boundaryEndCoefficient (a + b) q r =
      R.boundaryEndCoefficient a q r + R.boundaryEndCoefficient b q r := by
  classical
  by_cases hqr : q ≤ r
  · have hcomponent : R.boundaryEndComponent (a + b) q r =
        R.boundaryEndComponent a q r + R.boundaryEndComponent b q r :=
      map_add (R.boundaryEndComponentAddHom q r) a b
    simp [boundaryEndCoefficient, hqr, hcomponent]
  · simp [boundaryEndCoefficient, hqr]

/-- The coordinate of a composable pair of arbitrary matrix components.  If
an intermediate index lies outside the interval, the corresponding component
vanishes by acyclicity. -/
theorem boundaryEndCoordinate_component_comp
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (a b : End R.incidenceBoundaryGenerator) {q r : BoundaryIndex T}
    (hqr : q ≤ r) (z : BoundaryIndex T) :
    R.boundaryHomCoordinateEquiv
        ((boundaryLE_toOption_iff_le q r).2 hqr)
        (R.boundaryEndComponent a q z ≫ R.boundaryEndComponent b z r) =
      R.boundaryEndCoefficient a q z *
        R.boundaryEndCoefficient b z r := by
  classical
  by_cases hqz : q ≤ z
  · by_cases hzr : z ≤ r
    · simpa [boundaryEndCoefficient, hqz, hzr] using
        R.boundaryHomCoordinateEquiv_comp
          ((boundaryLE_toOption_iff_le q z).2 hqz)
          ((boundaryLE_toOption_iff_le z r).2 hzr)
          (R.boundaryEndComponent a q z) (R.boundaryEndComponent b z r)
    · have hbzero : R.boundaryEndComponent b z r = 0 :=
        R.boundaryHom_eq_zero_of_not_le H
          (fun h ↦ hzr ((boundaryLE_toOption_iff_le z r).1 h)) _
      simp [boundaryEndCoefficient, hqz, hzr, hbzero]
  · have hazero : R.boundaryEndComponent a q z = 0 :=
      R.boundaryHom_eq_zero_of_not_le H
        (fun h ↦ hqz ((boundaryLE_toOption_iff_le q z).1 h)) _
    simp [boundaryEndCoefficient, hqz, hazero]

theorem boundaryEndCoefficient_comp
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (a b : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) :
    R.boundaryEndCoefficient (a ≫ b) q r =
      ∑ z ∈ Finset.Icc q r,
        R.boundaryEndCoefficient a q z *
          R.boundaryEndCoefficient b z r := by
  classical
  by_cases hqr : q ≤ r
  · rw [boundaryEndCoefficient]
    simp only [hqr, ↓reduceDIte]
    rw [R.boundaryEndComponent_comp, map_sum]
    simp_rw [R.boundaryEndCoordinate_component_comp H a b hqr]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    simp only [Finset.mem_Icc] at hz
    rcases not_and_or.mp hz with hqz | hzr
    · simp [boundaryEndCoefficient, hqz]
    · simp [boundaryEndCoefficient, hzr]
  · rw [boundaryEndCoefficient]
    simp only [hqr, ↓reduceDIte]
    rw [Finset.Icc_eq_empty hqr, Finset.sum_empty]

/-- An endomorphism of the boundary biproduct gives its incidence matrix. -/
def boundaryEndToIncidence
    (R : S.PrimitiveProjectivePosetData D T)
    (a : End R.incidenceBoundaryGenerator) :
    IncidenceAlgebra k (BoundaryIndex T) where
  toFun := R.boundaryEndCoefficient a
  eq_zero_of_not_le' := by
    intro q r hqr
    simp [boundaryEndCoefficient, hqr]

/-- Reassemble an incidence matrix as an endomorphism of the boundary
biproduct. -/
def incidenceToBoundaryEnd
    (R : S.PrimitiveProjectivePosetData D T)
    (a : IncidenceAlgebra k (BoundaryIndex T)) :
    End R.incidenceBoundaryGenerator := by
  classical
  exact R.boundaryMatrix fun q r ↦
    if hqr : q ≤ r then
      (R.boundaryHomCoordinateEquiv
        ((boundaryLE_toOption_iff_le q r).2 hqr)).symm (a q r)
    else 0

@[simp]
theorem boundaryEndComponent_incidenceToBoundaryEnd
    (R : S.PrimitiveProjectivePosetData D T)
    (a : IncidenceAlgebra k (BoundaryIndex T)) (q r : BoundaryIndex T) :
    R.boundaryEndComponent (R.incidenceToBoundaryEnd a) q r =
      if hqr : q ≤ r then
        (R.boundaryHomCoordinateEquiv
          ((boundaryLE_toOption_iff_le q r).2 hqr)).symm (a q r)
      else 0 := by
  rw [incidenceToBoundaryEnd, boundaryEndComponent_boundaryMatrix]

@[simp]
theorem boundaryEndToIncidence_apply
    (R : S.PrimitiveProjectivePosetData D T)
    (a : End R.incidenceBoundaryGenerator) (q r : BoundaryIndex T) :
    R.boundaryEndToIncidence a q r = R.boundaryEndCoefficient a q r :=
  rfl

theorem boundaryEndToIncidence_incidenceToBoundaryEnd
    (R : S.PrimitiveProjectivePosetData D T)
    (a : IncidenceAlgebra k (BoundaryIndex T)) :
    R.boundaryEndToIncidence (R.incidenceToBoundaryEnd a) = a := by
  classical
  apply IncidenceAlgebra.ext
  intro q r hqr
  simp [boundaryEndToIncidence, boundaryEndCoefficient,
    incidenceToBoundaryEnd, hqr]

theorem incidenceToBoundaryEnd_boundaryEndToIncidence
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (a : End R.incidenceBoundaryGenerator) :
    R.incidenceToBoundaryEnd (R.boundaryEndToIncidence a) = a := by
  classical
  apply biproduct.hom_ext'
  intro q
  apply biproduct.hom_ext
  intro r
  simp only [Category.assoc]
  change R.boundaryEndComponent
      (R.incidenceToBoundaryEnd (R.boundaryEndToIncidence a)) q r =
    R.boundaryEndComponent a q r
  by_cases hqr : q ≤ r
  · simp [boundaryEndToIncidence, boundaryEndCoefficient, hqr]
  · rw [show R.boundaryEndComponent a q r = 0 by
      exact R.boundaryHom_eq_zero_of_not_le H
        (fun h ↦ hqr ((boundaryLE_toOption_iff_le q r).1 h)) _]
    simp [hqr]

theorem boundaryEndToIncidence_add
    (R : S.PrimitiveProjectivePosetData D T)
    (a b : End R.incidenceBoundaryGenerator) :
    R.boundaryEndToIncidence (a + b) =
      R.boundaryEndToIncidence a + R.boundaryEndToIncidence b := by
  classical
  apply IncidenceAlgebra.ext
  intro q r _
  exact R.boundaryEndCoefficient_add a b q r

theorem boundaryEndToIncidence_comp
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (a b : End R.incidenceBoundaryGenerator) :
    R.boundaryEndToIncidence (a ≫ b) =
      R.boundaryEndToIncidence a * R.boundaryEndToIncidence b := by
  classical
  apply IncidenceAlgebra.ext
  intro q r _
  rw [boundaryEndToIncidence_apply, IncidenceAlgebra.mul_apply]
  exact R.boundaryEndCoefficient_comp H a b q r

/-- The opposite endomorphism ring of the primitive boundary generator is
the incidence algebra of the augmented boundary poset.  The opposite is
essential: multiplication in `End` is reverse categorical composition. -/
def boundaryEndOppositeRingEquiv
    (R : S.PrimitiveProjectivePosetData D T)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    (End R.incidenceBoundaryGenerator)ᵐᵒᵖ ≃+*
      IncidenceAlgebra k (BoundaryIndex T) where
  toFun a := R.boundaryEndToIncidence a.unop
  invFun a := MulOpposite.op (R.incidenceToBoundaryEnd a)
  left_inv a := by
    apply MulOpposite.unop_injective
    simpa using R.incidenceToBoundaryEnd_boundaryEndToIncidence H a.unop
  right_inv a := R.boundaryEndToIncidence_incidenceToBoundaryEnd a
  map_add' a b := by
    simpa using R.boundaryEndToIncidence_add a.unop b.unop
  map_mul' a b := by
    rw [MulOpposite.unop_mul, End.mul_def]
    exact R.boundaryEndToIncidence_comp H a.unop b.unop

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.PrimitiveProjectivePosetData
