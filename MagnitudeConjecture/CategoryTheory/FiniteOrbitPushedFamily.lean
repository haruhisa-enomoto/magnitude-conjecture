import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleTrivialStabilizer
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownShift

/-!
# A finite family of pushed indecomposables

When the strict deck-orbit quotient has finitely many objects, local
representation-finiteness produces finitely many upstairs indecomposables
whose push-downs represent the push-down of every upstairs indecomposable.
The proof translates a supported object to the chosen representative of its
deck orbit and then uses the finite fiber at that representative.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
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

/-- A finite list of upstairs indecomposables whose push-downs represent
the push-down of every upstairs indecomposable. -/
structure FinitePushedIndecomposableFamily where
  n : ℕ
  upstairsObj : Fin n →
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k
  upstairsIndecomposable : ∀ i, Indecomposable (upstairsObj i)
  downstairsIndecomposable :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ i, Indecomposable
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (upstairsObj i))
  covers :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
    ∀ (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
      Indecomposable M →
        ∃ i, Nonempty (P.obj (upstairsObj i) ≅ P.obj M)

namespace FinitePushedIndecomposableFamily

variable (S : FinitePushedIndecomposableFamily (k := k) D)

/-- The downstairs member represented by an index of the finite pushed
family. -/
abbrev obj :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    Fin S.n → FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  exact fun i ↦
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
      (S.upstairsObj i)

end FinitePushedIndecomposableFamily

/-- Local representation-finiteness, together with finiteness of the strict
object-orbit quotient, supplies a finite pushed indecomposable family. -/
noncomputable def finitePushedIndecomposableFamily
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    FinitePushedIndecomposableFamily (k := k) D := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  let Q := MulAction.orbitRel.Quotient G C
  letI : Fintype Q := Fintype.ofFinite Q
  let H (q : Q) := Classical.choice
    (hrep (deckOrbitRepresentative (C := C) (G := G) q))
  let I := Σ q : Q, Fin (H q).n
  letI : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let upstairsObj (t : Fin n) := (H (e t).1).obj (e t).2
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  refine
    { n := n
      upstairsObj := upstairsObj
      upstairsIndecomposable := fun t ↦ (H (e t).1).indecomposable (e t).2
      downstairsIndecomposable := fun t ↦
        finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
          D
          (k := k) (upstairsObj t)
            ((H (e t).1).indecomposable (e t).2)
            (D.finiteDimensionalModule_trivialStabilizer
              (k := k) (upstairsObj t)
              ((H (e t).1).indecomposable (e t).2).1)
      covers := ?_ }
  dsimp only
  intro M hM
  obtain ⟨X, hX⟩ :=
    finiteDimensionalModule_moduleSupport_nonempty (k := k) M hM.1
  let q : Q := Quotient.mk'' X
  let R : C := deckOrbitRepresentative (C := C) (G := G) q
  have hq : (Quotient.mk'' R : Q) = Quotient.mk'' X :=
    deckOrbitRepresentative_mk (C := C) (G := G) q
  have horbit : R ∈ MulAction.orbit G X :=
    MulAction.orbitRel_apply.mp (Quotient.exact hq)
  let g : G := horbit.choose
  have hg : g • X = R := horbit.choose_spec
  let a : Additive G := Additive.ofMul g⁻¹
  let N := M⟦a⟧
  have hN : Indecomposable N :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) a)
      M).2 hM
  have hR : g⁻¹ • R = X := by
    rw [← hg, inv_smul_smul]
  have hNR : Nontrivial (N.obj.obj.obj R) := by
    let eR := D.finiteDimensionalModuleShiftEvaluationIso
      (k := k) M g⁻¹ R
    have he := eR.toLinearEquiv.toEquiv.nontrivial_congr
    rw [hR] at he
    exact he.mpr hX
  obtain ⟨j, ⟨eN⟩⟩ := (H q).covers hN hNR
  let p : I := ⟨q, j⟩
  refine ⟨e.symm p, ?_⟩
  have hep : upstairsObj (e.symm p) = (H q).obj j := by
    dsimp only [upstairsObj]
    rw [e.apply_symm_apply p]
  rw [hep]
  exact ⟨P.mapIso eN ≪≫
    D.finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
      (k := k) M a⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
