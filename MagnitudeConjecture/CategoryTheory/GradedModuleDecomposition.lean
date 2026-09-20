import MagnitudeConjecture.CategoryTheory.GradedModuleClassification
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Finite decompositions in the category of graded modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- The zero graded module. -/
def zeroObject : FiniteGradedModule.{u,u} R where
  module := ModuleCat.of A PUnit
  finite := inferInstance
  grading :=
    { component := fun _ ↦ ⊥
      internal := by
        classical
        change Function.Bijective (DirectSum.coeAddMonoidHom (fun _ : ℤ ↦ (⊥ : Submodule k PUnit)))
        exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun x ↦ ⟨0, Subsingleton.elim _ x⟩⟩
      smul_mem := by intros; exact Subsingleton.elim _ _ }

instance : HasZeroObject (ShiftedModule.{u,u} (R := R)) := by
  apply IsZero.hasZeroObject (X := ⟨zeroObject, 0⟩)
  apply (IsZero.iff_id_eq_zero _).2
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change (x : PUnit) = 0
  exact Subsingleton.elim (α := PUnit) _ _

instance : HasFiniteBiproducts (ShiftedModule.{u,u} (R := R)) := by
  let : HasFiniteProducts (ShiftedModule.{u,u} (R := R)) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Forget both the grading and the external shift label. -/
def shiftedUnderlying : ShiftedModule.{u,u} (R := R) ⥤ ModuleCat A :=
  homGrading.forget ⋙ underlying

instance : (shiftedUnderlying (R := R)).Faithful := by
  unfold shiftedUnderlying
  infer_instance
instance : (shiftedUnderlying (R := R)).Additive := by
  unfold shiftedUnderlying
  infer_instance

theorem isZero_of_underlying (X : ShiftedModule.{u,u} (R := R))
    (h : IsZero X.obj.module) : IsZero X := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (shiftedUnderlying (R := R)).map_injective
  change (𝟙 X.obj.module) = 0
  exact h.eq_of_src _ _

/-- Every finite-dimensional graded module has a finite graded indecomposable decomposition. -/
theorem finiteDecomposition (M : ShiftedModule.{u,u} (R := R)) :
    Nonempty (MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition M) := by
  classical
  let F := shiftedUnderlying (R := R)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  generalize hn : Module.finrank k M.obj.module = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : IsZero M
    · exact ⟨{
        n := 0
        summand := fun i ↦ Fin.elim0 i
        indecomposable := fun i ↦ Fin.elim0 i
        isoBiproduct := MagnitudeConjecture.CategoryTheory.zeroIsoEmptyBiproduct M hz }⟩
    by_cases hi : Indecomposable M
    · exact ⟨MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton M hi⟩
    have hs : ∃ X Y, ∃ e : M ≅ X ⊞ Y, ¬ IsZero X ∧ ¬ IsZero Y := by
      rw [Indecomposable] at hi
      push Not at hi
      exact hi hz
    obtain ⟨X, Y, e, hx, hy⟩ := hs
    let e' : M.obj.module ≅ X.obj.module ⊞ Y.obj.module := F.mapIso e ≪≫ F.mapBiprod X Y
    let l := ((e'.trans (ModuleCat.biprodIsoProd X.obj.module Y.obj.module)).toLinearEquiv).restrictScalars k
    have hd : Module.finrank k M.obj.module =
        Module.finrank k X.obj.module + Module.finrank k Y.obj.module :=
      l.finrank_eq.trans Module.finrank_prod
    have hx' : ¬ Subsingleton X.obj.module := by
      intro h
      exact hx (isZero_of_underlying X (ModuleCat.isZero_iff_subsingleton.mpr h))
    have hy' : ¬ Subsingleton Y.obj.module := by
      intro h
      exact hy (isZero_of_underlying Y (ModuleCat.isZero_iff_subsingleton.mpr h))
    letI : Nontrivial X.obj.module := not_subsingleton_iff_nontrivial.mp hx'
    letI : Nontrivial Y.obj.module := not_subsingleton_iff_nontrivial.mp hy'
    have hxpos : 0 < Module.finrank k X.obj.module := Module.finrank_pos
    have hypos : 0 < Module.finrank k Y.obj.module := Module.finrank_pos
    obtain ⟨dX⟩ := ih (Module.finrank k X.obj.module) (by omega) X rfl
    obtain ⟨dY⟩ := ih (Module.finrank k Y.obj.module) (by omega) Y rfl
    exact ⟨MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.ofIso e (dX.biprod dY)⟩

end MagnitudeConjecture.Graded.FiniteGradedModule
