import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleOrbit

/-!
# Local representation-finiteness from finitely many deck orbits

For a free deck action, a finite-support module has only finitely many
translates that are nonzero at a fixed base object.  Consequently, a finite
family that represents all indecomposable finite modules up to translation
supplies the finite pointwise fibres required by local
representation-finiteness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finitely many indecomposable representatives up to deck translation imply
pointwise local representation-finiteness. -/
theorem isLocallyRepresentationFinite_of_finite_shift_orbit_representatives
    (n : ℕ)
    (N : Fin n → FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hN : ∀ i, Indecomposable (N i)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    (∀ (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
      Indecomposable Y →
        ∃ i : Fin n, ∃ g : G, Nonempty (N i⟦Additive.ofMul g⟧ ≅ Y)) →
      IsLocallyRepresentationFinite (k := k) (C := C) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  intro hcover X
  let labels (i : Fin n) : Set G :=
    {g | g • X ∈ moduleSupport k (N i).obj.obj}
  have hlabels (i : Fin n) : (labels i).Finite := by
    apply (finite_moduleSupport k (N i)).preimage
    intro g _ h _ heq
    exact IsCancelSMul.right_cancel g h X heq
  let I := Σ i : Fin n, labels i
  letI (i : Fin n) : Fintype (labels i) := (hlabels i).fintype
  letI : Fintype I := Fintype.ofFinite I
  let m := Fintype.card I
  let e : Fin m ≃ I := (Fintype.equivFin I).symm
  refine ⟨
    { n := m
      obj := fun t ↦ N (e t).1⟦Additive.ofMul (e t).2.1⟧
      indecomposable := ?_
      covers := ?_ }⟩
  · intro t
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor
          (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
          (Additive.ofMul (e t).2.1)) (N (e t).1)).mpr (hN (e t).1)
  · intro Y hY hYX
    obtain ⟨i, g, ⟨eY⟩⟩ := hcover Y hY
    let J := (IsFiniteDimensionalModule (C := C) k).ι
    let Q := (IsLinearModule (C := C) k).ι
    let eEval := (Q.mapIso (J.mapIso eY)).app X
    have hshiftX : Nontrivial
        ((N i⟦Additive.ofMul g⟧).obj.obj.obj X) :=
      eEval.toLinearEquiv.toEquiv.nontrivial_congr.mpr hYX
    have hbaseX : Nontrivial ((N i).obj.obj.obj (g • X)) :=
      (D.finiteDimensionalModuleShiftEvaluationIso
        (k := k) (N i) g X).toLinearEquiv.toEquiv.nontrivial_congr.mp hshiftX
    let p : I := ⟨i, ⟨g, hbaseX⟩⟩
    refine ⟨e.symm p, ?_⟩
    rw [e.apply_symm_apply p]
    exact ⟨eY⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
