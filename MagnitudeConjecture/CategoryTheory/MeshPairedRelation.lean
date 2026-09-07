import MagnitudeConjecture.CategoryTheory.LinearPathIncoming
import MagnitudeConjecture.CategoryTheory.MeshIncomingDecomposition

/-!
# Paired arrows and the ordinary mesh relation

The polarization pairs every arrow ending at a nonprojective vertex with an
arrow out of its translate.  Summing the resulting length-two composites is
exactly the defining mesh relation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.MeshCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- Before quotienting, the sum of the paired translate-arrow/incoming-arrow
composites is exactly a left multiple of the defining mesh relation. -/
theorem free_paired_incomingSum_eq_comp_meshRelation
    (x : {x : Q // x ∉ T.projective}) {y : Q}
    (q : MagnitudeConjecture.LinearPathCategory.obj k Q y ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau x)) :
    MagnitudeConjecture.LinearPathCategory.incomingSum
        (fun a : MagnitudeConjecture.LinearPathCategory.IncomingArrow x.1 ↦
          q ≫ MagnitudeConjecture.LinearPathCategory.pathHom
            ((T.arrowEquiv x a.1) a.2).toPath) =
      q ≫ T.meshRelation (k := k) x := by
  rw [MagnitudeConjecture.LinearPathCategory.incomingSum, meshRelation,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Category.assoc]
  rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp]
  rfl

/-- One paired translate-arrow/incoming-arrow composite is the corresponding
term of the ordinary mesh relation. -/
theorem pairedArrow_comp_incomingArrowHom
    (x : {x : Q // x ∉ T.projective}) (a : T.MeshArrow x) :
    T.incomingArrowHom (k := k)
          (⟨T.tau x, T.arrowEquiv x a.1 a.2⟩ : IncomingArrow a.1) ≫
        T.incomingArrowHom (k := k)
          (⟨a.1, a.2⟩ : IncomingArrow x.1) =
      (quotientFunctor (k := k) T).map
        (MagnitudeConjecture.LinearPathCategory.pathHom (T.meshPath x a)) := by
  rw [incomingArrowHom, incomingArrowHom,
    ← (quotientFunctor (k := k) T).map_comp,
    MagnitudeConjecture.LinearPathCategory.pathHom_comp]
  rfl

/-- Precomposing all paired translate arrows with one morphism gives zero
after summing against the incoming arrows, because the sum is the defining
mesh relation. -/
theorem paired_incomingSum_eq_zero
    (x : {x : Q // x ∉ T.projective}) {y : Q}
    (q : obj (k := k) T y ⟶ obj (k := k) T (T.tau x)) :
    T.incomingSum (k := k)
        (fun a : IncomingArrow x.1 ↦
          q ≫ T.incomingArrowHom (k := k)
            (⟨T.tau x, T.arrowEquiv x a.1 a.2⟩ :
              IncomingArrow a.1)) = 0 := by
  rw [incomingSum]
  simp_rw [Category.assoc,
    T.pairedArrow_comp_incomingArrowHom (k := k) x]
  rw [← Preadditive.comp_sum]
  have hrel := quotient_map_meshRelation_eq_zero (k := k) T x
  rw [meshRelation, (quotientFunctor (k := k) T).map_sum] at hrel
  calc
    q ≫ ∑ a, (quotientFunctor (k := k) T).map
          (MagnitudeConjecture.LinearPathCategory.pathHom (T.meshPath x a)) =
        q ≫ 0 := congrArg
          (fun r : obj (k := k) T (T.tau x) ⟶ obj (k := k) T x.1 ↦
            q ≫ r) hrel
    _ = 0 := by simp

/-- The paired incoming sum also vanishes when its source is an arbitrary
raw mesh-category object rather than a displayed vertex object. -/
theorem raw_paired_incomingSum_eq_zero
    (x : {x : Q // x ∉ T.projective})
    (X : RawCategory (k := k) T)
    (q : X ⟶ obj (k := k) T (T.tau x)) :
    (∑ a : IncomingArrow x.1,
      (q ≫ T.incomingArrowHom (k := k)
        (⟨T.tau x, T.arrowEquiv x a.1 a.2⟩ : IncomingArrow a.1)) ≫
          T.incomingArrowHom (k := k) a) = 0 := by
  rcases X with ⟨X⟩
  let y := MagnitudeConjecture.LinearPathCategory.vertex X
  have hobj : ({ as := X } : RawCategory (k := k) T) =
      obj (k := k) T y := rfl
  let q' : obj (k := k) T y ⟶ obj (k := k) T (T.tau x) :=
    eqToHom hobj.symm ≫ q
  have h := T.paired_incomingSum_eq_zero (k := k) x q'
  rw [incomingSum] at h
  have hcomp := congrArg
    (fun r : obj (k := k) T y ⟶ obj (k := k) T x.1 ↦
      eqToHom hobj ≫ r) h
  rw [Preadditive.comp_sum] at hcomp
  simpa [q', Category.assoc] using hcomp

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing the defining mesh relation by an arbitrary raw
mesh-category morphism still gives zero. -/
theorem paired_incomingSum_comp_eq_zero
    (x : {x : Q // x ∉ T.projective})
    (X : RawCategory (k := k) T)
    (q : obj (k := k) T x.1 ⟶ X) :
    (∑ a : IncomingArrow x.1,
      T.incomingArrowHom (k := k)
          (⟨T.tau x, T.arrowEquiv x a.1 a.2⟩ : IncomingArrow a.1) ≫
        T.incomingArrowHom (k := k) a ≫ q) = 0 := by
  have hrel := quotient_map_meshRelation_eq_zero (k := k) T x
  rw [meshRelation, (quotientFunctor (k := k) T).map_sum] at hrel
  calc
    (∑ a : IncomingArrow x.1,
        T.incomingArrowHom (k := k)
            (⟨T.tau x, T.arrowEquiv x a.1 a.2⟩ : IncomingArrow a.1) ≫
          T.incomingArrowHom (k := k) a ≫ q) =
        (∑ a, (quotientFunctor (k := k) T).map
          (MagnitudeConjecture.LinearPathCategory.pathHom
            (T.meshPath x a))) ≫ q := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Category.assoc,
        T.pairedArrow_comp_incomingArrowHom (k := k) x]
    _ = 0 := by rw [hrel]; simp

end RightMeshData

end MagnitudeConjecture.MeshCategory
