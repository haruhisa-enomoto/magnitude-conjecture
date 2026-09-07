import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundary
import MagnitudeConjecture.CategoryTheory.HomUnitEquations

/-!
# Iyama's zero-middle boundary for a primitive factor

The two Hom-unit equations identify the distinguished source and sink as the
only projective and injective boundary labels whose corresponding mesh has
zero middle term.  This is the literal `l⁺/l⁻` boundary condition used in
Iyama's projective-socle realization theorem.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.Iyama
open MagnitudeConjecture.FiniteTauMatrix

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

namespace PrimitiveDirectedBoundaryData

/-- The primitive multiplicity has categorical right-mesh defect one at the
distinguished source and zero at every other label. -/
theorem multiplicity_rightMeshDefect
    (D : S.PrimitiveMultiplicityInput K) (x : S.SurvivingLabel K) :
    rightMeshLabelWeightDefect
        (S.factorFiniteTauCategoryData K)
        (fun y ↦ (D.multiplicity y.1 : ℤ)) x =
      if x = D.source then 1 else 0 := by
  rw [rightMeshLabelWeightDefect_eq_meshColumnWeight]
  exact D.meshUnitEquations.1 x

/-- The primitive multiplicity has categorical left-mesh defect one at the
distinguished sink and zero at every other label. -/
theorem multiplicity_leftMeshDefect
    (D : S.PrimitiveMultiplicityInput K) (x : S.SurvivingLabel K) :
    leftMeshLabelWeightDefect
        (S.factorFiniteTauCategoryData K)
        (fun y ↦ (D.multiplicity y.1 : ℤ)) x =
      if x = D.sink then 1 else 0 := by
  let T := S.factorFiniteTauCategoryData K
  have hweight : (fun y : S.SurvivingLabel K ↦
      (D.multiplicity y.1 : ℤ)) = homToWeight (k := k) T D.sink :=
    funext D.weight_eq_to
  rw [hweight]
  exact leftMeshLabelWeightDefect_homToWeight T
    D.homMeshInverseData D.leftMesh_epi D.sink x

/-- Among the tau-projective boundary labels, the distinguished source is
exactly the one with zero right-mesh middle term. -/
theorem rightMiddle_isZero_iff_eq_source
    (B : S.PrimitiveDirectedBoundaryData D)
    (p : S.FactorProjectiveLabel K) :
    IsZero ((S.factorFiniteTauCategoryData K).thetaPlus p.1) ↔
      p.1 = D.source := by
  let T := S.factorFiniteTauCategoryData K
  let weight : S.SurvivingLabel K → ℤ :=
    fun x ↦ D.multiplicity x.1
  let W := T.additiveObjectWeightOfLabelWeight weight
  let R := T.rightMesh (T.obj p.1)
  have hpWeight : weight p.1 = 1 := by
    change (D.multiplicity p.1.1 : ℤ) = 1
    exact_mod_cast B.projective_multiplicity_eq_one p
  have hleft : W.weight R.X₁ = 0 :=
    W.weight_eq_zero_of_isZero p.2
  have hright : W.weight R.X₃ = 1 := by
    calc
      W.weight R.X₃ = W.weight (T.obj p.1) :=
        W.iso_invariant ⟨T.rightTermIso (T.obj p.1)⟩
      _ = weight p.1 := T.additiveObjectWeightOfLabelWeight_obj weight p.1
      _ = 1 := hpWeight
  have hdefect :
      rightMeshLabelWeightDefect T weight p.1 =
        if p.1 = D.source then 1 else 0 :=
    multiplicity_rightMeshDefect D p.1
  constructor
  · intro hmiddle
    have hmiddleWeight : W.weight R.X₂ = 0 :=
      W.weight_eq_zero_of_isZero hmiddle
    rw [rightMeshLabelWeightDefect,
      hleft, hmiddleWeight, hright] at hdefect
    by_contra hne
    simp [hne] at hdefect
  · intro hp
    have hmiddleWeight : W.weight R.X₂ = 0 := by
      have heq : 0 - W.weight R.X₂ + 1 = 1 := by
        calc
          0 - W.weight R.X₂ + 1 =
              rightMeshLabelWeightDefect T weight p.1 := by
            rw [rightMeshLabelWeightDefect, hleft, hright]
          _ = if p.1 = D.source then 1 else 0 := hdefect
          _ = 1 := if_pos hp
      omega
    exact
      (additiveObjectWeight_eq_zero_iff_isZero T weight
          (fun x ↦ by
            change (0 : ℤ) < (D.multiplicity x.1 : ℤ)
            exact_mod_cast PrimitiveMultiplicityInput.multiplicity_pos
              (S := S) D x) R.X₂).mp hmiddleWeight

/-- Among the tau-injective boundary labels, the distinguished sink is
exactly the one with zero left-mesh middle term. -/
theorem leftMiddle_isZero_iff_eq_sink
    (B : S.PrimitiveDirectedBoundaryData D)
    (i : S.FactorInjectiveLabel K) :
    IsZero ((S.factorFiniteTauCategoryData K).thetaMinus i.1) ↔
      i.1 = D.sink := by
  let T := S.factorFiniteTauCategoryData K
  let weight : S.SurvivingLabel K → ℤ :=
    fun x ↦ D.multiplicity x.1
  let W := T.additiveObjectWeightOfLabelWeight weight
  let L := T.leftMesh (T.obj i.1)
  have hiWeight : weight i.1 = 1 := by
    change (D.multiplicity i.1.1 : ℤ) = 1
    exact_mod_cast B.injective_multiplicity_eq_one i
  have hleft : W.weight L.X₁ = 1 := by
    calc
      W.weight L.X₁ = W.weight (T.obj i.1) :=
        W.iso_invariant ⟨T.leftTermIso (T.obj i.1)⟩
      _ = weight i.1 := T.additiveObjectWeightOfLabelWeight_obj weight i.1
      _ = 1 := hiWeight
  have hright : W.weight L.X₃ = 0 :=
    W.weight_eq_zero_of_isZero i.2
  have hdefect :
      leftMeshLabelWeightDefect T weight i.1 =
        if i.1 = D.sink then 1 else 0 :=
    multiplicity_leftMeshDefect D i.1
  constructor
  · intro hmiddle
    have hmiddleWeight : W.weight L.X₂ = 0 :=
      W.weight_eq_zero_of_isZero hmiddle
    rw [leftMeshLabelWeightDefect,
      hleft, hmiddleWeight, hright] at hdefect
    by_contra hne
    simp [hne] at hdefect
  · intro hi
    have hmiddleWeight : W.weight L.X₂ = 0 := by
      have heq : 1 - W.weight L.X₂ + 0 = 1 := by
        calc
          1 - W.weight L.X₂ + 0 =
              leftMeshLabelWeightDefect T weight i.1 := by
            rw [leftMeshLabelWeightDefect, hleft, hright]
          _ = if i.1 = D.sink then 1 else 0 := hdefect
          _ = 1 := if_pos hi
      omega
    exact
      (additiveObjectWeight_eq_zero_iff_isZero T weight
          (fun x ↦ by
            change (0 : ℤ) < (D.multiplicity x.1 : ℤ)
            exact_mod_cast PrimitiveMultiplicityInput.multiplicity_pos
              (S := S) D x) L.X₂).mp hmiddleWeight

end PrimitiveDirectedBoundaryData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
