import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAlmostSplit
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownWindow

/-!
# Shift orthogonality on additive control windows

Pairwise nonidentity shift-Hom vanishing for a finite family of
indecomposable modules extends to every finite biproduct in its additive
hull.  This is the bridge from residual separation of the manuscript's
finite vertex set to fullness of push-down on the categorical window that
contains relevant factorization cores.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- Nonidentity shift-Hom vanishing on the literal finite range of chosen
representatives extends across isomorphisms. -/
theorem finiteModuleWindowShiftHomOrthogonal_isoClosure
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) (Set.range S.obj) →
      D.FiniteModuleWindowShiftHomOrthogonal (k := k) S.isoClosure := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  intro horthogonal M N a ha
  obtain ⟨i, ⟨eM⟩⟩ := M.2
  obtain ⟨j, ⟨eN⟩⟩ := N.2
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let eM' := J.mapIso eM
  let eN' := J.mapIso eN
  let T := shiftFunctor
    (LinearModuleCategory.{u, v, v, v} (C := C) k) a
  let eNshift := T.mapIso eN'
  let Mi : CoveringSeparation.WindowCategory (Set.range S.obj) :=
    ⟨S.obj i, ⟨i, rfl⟩⟩
  let Nj : CoveringSeparation.WindowCategory (Set.range S.obj) :=
    ⟨S.obj j, ⟨j, rfl⟩⟩
  constructor
  intro q r
  have eq_zero (t : ShiftHom M.1.obj N.1.obj a) : t = 0 := by
    let c : ShiftHom (S.obj i).obj (S.obj j).obj a :=
      (eM'.hom ≫ t) ≫ eNshift.inv
    have hc : c = 0 := by
      haveI : Subsingleton (ShiftHom (S.obj i).obj (S.obj j).obj a) :=
        horthogonal Mi Nj a ha
      exact Subsingleton.elim _ _
    calc
      t = (eM'.inv ≫ c) ≫ eNshift.hom := by
        simp [c, Category.assoc]
      _ = 0 := by
        rw [hc, comp_zero, zero_comp]
  exact (eq_zero q).trans (eq_zero r).symm

/-- Nonidentity shift-Hom vanishing on the finite indecomposable generators
extends to their full additive hull. -/
theorem finiteModuleWindowShiftHomOrthogonal_additiveClosure
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) S.isoClosure →
      D.FiniteModuleWindowShiftHomOrthogonal (k := k) S.additiveClosure := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro horthogonal M N a ha
  constructor
  intro q r
  have eq_zero (t : ShiftHom M.1.obj N.1.obj a) : t = 0 := by
    obtain ⟨m, labelM, ⟨eM⟩⟩ := M.2
    obtain ⟨n, labelN, ⟨eN⟩⟩ := N.2
    let T := shiftFunctor
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) a
    let eNshift : N.1⟦a⟧ ≅
        ⨁ fun j : Fin n ↦ (S.obj (labelN j))⟦a⟧ :=
      T.mapIso eN.symm ≪≫ T.mapBiproduct
        (fun j : Fin n ↦ S.obj (labelN j))
    let t' : M.1 ⟶ N.1⟦a⟧ :=
      finiteDimensionalShiftHom (k := k) D M.1 N.1 a t
    let matrix :
        (⨁ fun i : Fin m ↦ S.obj (labelM i)) ⟶
          ⨁ fun j : Fin n ↦ (S.obj (labelN j))⟦a⟧ :=
      eM.hom ≫ t' ≫ eNshift.hom
    have hmatrix : matrix = 0 := by
      apply biproduct.hom_ext'
      intro i
      apply biproduct.hom_ext
      intro j
      let c : S.obj (labelM i) ⟶ (S.obj (labelN j))⟦a⟧ :=
        biproduct.ι (fun i : Fin m ↦ S.obj (labelM i)) i ≫ matrix ≫
          biproduct.π (fun j : Fin n ↦ (S.obj (labelN j))⟦a⟧) j
      let J := (IsFiniteDimensionalModule (C := C) k).ι
      let es := D.finiteDimensionalModuleShiftUnderlyingIso
        (k := k) (S.obj (labelN j)) a
      let Mi : CoveringSeparation.WindowCategory S.isoClosure :=
        ⟨S.obj (labelM i), S.obj_mem_isoClosure (labelM i)⟩
      let Nj : CoveringSeparation.WindowCategory S.isoClosure :=
        ⟨S.obj (labelN j), S.obj_mem_isoClosure (labelN j)⟩
      let cShift : ShiftHom
          (S.obj (labelM i)).obj (S.obj (labelN j)).obj a :=
        J.map c ≫ es.hom
      have hcShift : cShift = 0 := by
        haveI : Subsingleton
            (ShiftHom (S.obj (labelM i)).obj (S.obj (labelN j)).obj a) :=
          horthogonal Mi Nj a ha
        exact Subsingleton.elim _ _
      have hc : c = 0 := by
        apply J.map_injective
        apply (cancel_mono es.hom).1
        rw [J.map_zero, zero_comp]
        change cShift = 0
        exact hcShift
      simpa [c] using hc
    have ht' : t' = 0 := by
      apply (cancel_epi eM.hom).1
      apply (cancel_mono eNshift.hom).1
      simpa [matrix] using hmatrix
    have hroundtrip :=
      finiteDimensionalShiftHom_roundtrip (k := k) D M.1 N.1 a t
    have hroundtrip' :
        (IsFiniteDimensionalModule (C := C) k).ι.map t' ≫
          (D.finiteDimensionalModuleShiftUnderlyingIso
            (k := k) N.1 a).hom = t := by
      simpa [t'] using hroundtrip
    rw [ht'] at hroundtrip'
    simpa using hroundtrip'.symm
  exact (eq_zero q).trans (eq_zero r).symm

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
