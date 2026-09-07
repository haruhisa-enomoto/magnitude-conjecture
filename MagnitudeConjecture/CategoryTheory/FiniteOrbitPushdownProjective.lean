import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownExact
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownHomEquiv
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownMinimalPresentation
import MagnitudeConjecture.CategoryTheory.ShiftOrbitFactorization

/-!
# Projective objects under finite skeletal push-down

Finite skeletal Gabriel push-down preserves finite projective modules because
they are finite sums of representables.  Conversely, projectivity of a
pushed module reflects upstairs: a downstairs lift decomposes into deck
degrees, and its identity-degree component is an ordinary upstairs lift.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finite skeletal push-down preserves projective finite modules. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_projective
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Projective M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Projective
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Projective M := hM
  obtain ⟨Q⟩ := finiteRepresentableCoordinates_nonempty_of_projective
    hP hlocal M
  let MQ : Mat_ (Cᵒᵖ) :=
    { ι := Fin Q.n
      X := fun i ↦ Opposite.op (Q.X i) }
  have hsource : Projective
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj MQ)) :=
    D.finiteProjectiveRepresentableSumOrbitSkeletonPushdown_projective
      (k := k) hP MQ
  let e :
      (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj MQ ≅ M :=
    Q.isoSource
  exact Projective.of_iso
    ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).mapIso e)
      hsource

set_option backward.isDefEq.respectTransparency false in
/-- Projectivity of a finite module reflects from its finite skeletal
push-down.  The identity-degree component of a downstairs factorization is
the required upstairs factorization. -/
theorem projective_of_finiteDimensionalModuleOrbitSkeletonPushdown_projective
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      Projective
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M)) :
    Projective M := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  classical
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : Projective (P.obj M) := hM
  constructor
  intro E X f e hepi
  letI : Epi e := hepi
  letI : Epi (P.map e) := inferInstance
  obtain ⟨q, hq⟩ := Projective.factors (P.map f) (P.map e)
  let EM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M E
  let EX := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M X
  let r : ShiftOrbitHom (Additive G) M.obj E.obj := EM.symm q
  let E₀ := shiftHomZeroLinearEquiv
    (k := k) (A := Additive G) M.obj E.obj
  let c : M ⟶ E := ObjectProperty.homMk (E₀.symm (r 0))
  refine ⟨c, ?_⟩
  have horbit :
      shiftOrbitCompHom r
          (shiftOrbitOf E.obj X.obj 0
            (shiftHomZero (A := Additive G) e.hom)) =
        shiftOrbitOf M.obj X.obj 0
          (shiftHomZero (A := Additive G) f.hom) := by
    apply EX.injective
    rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
      (k := k) M E X]
    rw [D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero,
      EM.apply_symm_apply, hq,
      D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero]
  have hzero := congrArg
    (fun z : ShiftOrbitHom (Additive G) M.obj X.obj ↦ z 0) horbit
  rw [shiftOrbitComp_zero_right_component_zero (k := k)] at hzero
  have hright :
      (shiftOrbitOf M.obj X.obj 0
        (shiftHomZero (A := Additive G) f.hom)) 0 =
          shiftHomZero (A := Additive G) f.hom := by
    change DirectSum.component k (Additive G)
        (fun a ↦ ShiftHom M.obj X.obj a) 0
          (DirectSum.lof k (Additive G)
            (fun a ↦ ShiftHom M.obj X.obj a) 0
              (shiftHomZero (A := Additive G) f.hom)) = _
    rw [DirectSum.component.of]
    simp
  rw [hright] at hzero
  apply ObjectProperty.hom_ext
  change c.hom ≫ e.hom = f.hom
  change (shiftHomZeroLinearEquiv
      (k := k) (A := Additive G) M.obj X.obj)
        (E₀.symm (r 0) ≫ e.hom) =
      (shiftHomZeroLinearEquiv
        (k := k) (A := Additive G) M.obj X.obj) f.hom at hzero
  exact (shiftHomZeroLinearEquiv
    (k := k) (A := Additive G) M.obj X.obj).injective hzero

/-- Finite skeletal push-down identifies projective status exactly. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_projective_iff
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (Projective
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) ↔
      Projective M) := by
  constructor
  · exact D.projective_of_finiteDimensionalModuleOrbitSkeletonPushdown_projective
      (k := k) M
  · exact D.finiteDimensionalModuleOrbitSkeletonPushdown_projective
      (k := k) hP hlocal M

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
