import MagnitudeConjecture.CategoryTheory.CoherentDeckShiftRestriction
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownWindow
import MagnitudeConjecture.Combinatorics.SupportInteractionSeparation

/-!
# Residual separation of a finite module family

A nonzero shifted map between finite-support modules forces the source support
to meet a translate of the target support.  Only finitely many deck degrees
can do this for a finite family.  Residual finiteness therefore supplies a
finite-index normal subgroup on which every nonidentity shifted Hom between
the chosen modules vanishes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- A nonzero shifted map between finite modules is detected at an object in
the source support whose translate belongs to the target support. -/
theorem exists_support_overlap_of_shiftHom_ne_zero
    (M N : FiniteDimensionalModuleCategory (k := k) (C := C))
    (g : G)
    (t : letI := D.hasShift
         letI := D.additiveShift
         letI := D.linearShift (k := k)
         letI := isLinearModule_stableUnderShift (k := k) D.core
         letI := linearModuleCategoryHasShift (k := k) D.core
         ShiftHom M.obj N.obj (Additive.ofMul g))
    (ht : t ≠ 0) :
    ∃ X : C, X ∈ moduleSupport k M.obj.obj ∧
      g • X ∈ moduleSupport k N.obj.obj := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  have hex : ∃ X : C, t.hom.app X ≠ 0 := by
    by_contra h
    apply ht
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact not_ne_iff.mp (not_exists.mp h X)
  obtain ⟨X, hX⟩ := hex
  have hexValue : ∃ x : M.obj.obj.obj X,
      (t.hom.app X).hom x ≠ 0 := by
    by_contra h
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hexValue
  have hMX : X ∈ moduleSupport k M.obj.obj := by
    change Nontrivial (M.obj.obj.obj X)
    refine ⟨⟨x, 0, ?_⟩⟩
    intro hxzero
    apply hx
    simp [hxzero]
  have hshiftN : Nontrivial
      (((IsLinearModule (C := C) k).ι.obj
        (N.obj⟦Additive.ofMul g⟧)).obj X) :=
    ⟨⟨(t.hom.app X).hom x, 0, hx⟩⟩
  exact ⟨X, hMX,
    (D.linearModuleShiftEvaluationIso k N.obj g X).toLinearEquiv.toEquiv.nontrivial_congr.mp
      hshiftN⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]

/-- Deck degrees carrying some object of the source support into the target
support. -/
def moduleSupportTransportDegrees
    (M N : FiniteDimensionalModuleCategory (k := k) (C := C)) : Set G :=
  {g | ∃ X : C, X ∈ moduleSupport k M.obj.obj ∧
    g • X ∈ moduleSupport k N.obj.obj}

/-- Only finitely many deck degrees can carry one finite module support into
another when the action on objects is free. -/
theorem moduleSupportTransportDegrees_finite
    (M N : FiniteDimensionalModuleCategory (k := k) (C := C)) :
    (moduleSupportTransportDegrees (G := G) M N).Finite := by
  classical
  let sourceSupport : Finset C := (finite_moduleSupport k M).toFinset
  let targetSupport : Finset C := (finite_moduleSupport k N).toFinset
  let bound : Finset G :=
    sourceSupport.biUnion fun X ↦
      targetSupport.biUnion fun Y ↦
        (CoveringSeparation.smulTransporter_finite
          (G := G) X Y).toFinset
  apply bound.finite_toSet.subset
  intro g hg
  obtain ⟨X, hMX, hNgX⟩ := hg
  change g ∈ bound
  apply Finset.mem_biUnion.mpr
  refine ⟨X, (finite_moduleSupport k M).mem_toFinset.mpr hMX, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨g • X, (finite_moduleSupport k N).mem_toFinset.mpr hNgX, ?_⟩
  exact (CoveringSeparation.smulTransporter_finite
    (G := G) X (g • X)).mem_toFinset.mpr rfl

/-- The nonidentity ambient degrees that can overlap the supports of two
chosen modules. -/
def finiteModuleFamilySupportBadDegrees
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C)) : Set G :=
  {g | g ≠ 1 ∧ ∃ i j,
    g ∈ moduleSupportTransportDegrees (S.obj i) (S.obj j)}

theorem finiteModuleFamilySupportBadDegrees_finite
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    (finiteModuleFamilySupportBadDegrees (G := G) S).Finite := by
  classical
  let bound : Finset G := Finset.univ.biUnion fun i ↦
    Finset.univ.biUnion fun j ↦
      (moduleSupportTransportDegrees_finite
        (G := G) (S.obj i) (S.obj j)).toFinset
  apply bound.finite_toSet.subset
  intro g hg
  obtain ⟨_, i, j, hij⟩ := hg
  change g ∈ bound
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨j, Finset.mem_univ j,
    (moduleSupportTransportDegrees_finite
      (G := G) (S.obj i) (S.obj j)).mem_toFinset.mpr hij⟩

/-- Residual finiteness supplies one finite-index normal subgroup avoiding
every nonidentity support-overlap degree of the finite module family. -/
theorem exists_finiteIndexNormalSubgroup_avoiding_supportBadDegrees
    [Group.ResiduallyFinite G]
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    ∃ N : FiniteIndexNormalSubgroup G,
      ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) S, g ∉ N :=
  CoveringSeparation.exists_finiteIndexNormalSubgroup_avoiding
    (finiteModuleFamilySupportBadDegrees_finite (G := G) S)
    (fun _ hg ↦ hg.1)

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

omit [IsCancelSMul G C] in
/-- Avoiding every nonidentity support-overlap degree makes the restricted
deck shift orthogonal on the literal chosen family. -/
theorem restrict_finiteModuleWindowShiftHomOrthogonal_of_avoids
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (N : Subgroup G)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) S,
      g ∉ N) :
    (D.restrict N).FiniteModuleWindowShiftHomOrthogonal
      (k := k) (Set.range S.obj) := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) (D.restrict N).core
  letI := linearModuleCategoryHasShift (k := k) (D.restrict N).core
  intro M N' a ha
  obtain ⟨i, hi⟩ := M.2
  obtain ⟨j, hj⟩ := N'.2
  constructor
  intro q r
  have eq_zero (t : ShiftHom M.1.obj N'.1.obj a) : t = 0 := by
    by_contra ht
    change ShiftHom M.1.obj N'.1.obj (Additive.ofMul a.toMul) at t
    let g : G := a.toMul
    have hgne : g ≠ 1 := by
      intro hg
      apply ha
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hg
    obtain ⟨Z, hZM, hZN⟩ :=
      (D.restrict N).exists_support_overlap_of_shiftHom_ne_zero
        (k := k) M.1 N'.1 a.toMul t ht
    have hZi : Z ∈ moduleSupport k (S.obj i).obj.obj := by
      simpa only [hi] using hZM
    have hZj : g • Z ∈ moduleSupport k (S.obj j).obj.obj := by
      simpa only [g, hj, MulAction.subgroup_smul_def] using hZN
    exact havoid g ⟨hgne, i, j, Z, hZi, hZj⟩ a.toMul.property
  exact (eq_zero q).trans (eq_zero r).symm

/-- Residual finiteness produces a finite-index normal subgroup whose
restricted coherent deck shift is shift-Hom orthogonal on the chosen finite
module family. -/
theorem exists_finiteIndexNormalSubgroup_restrict_shiftHomOrthogonal
    [Group.ResiduallyFinite G]
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    ∃ N : FiniteIndexNormalSubgroup G,
      (D.restrict N).FiniteModuleWindowShiftHomOrthogonal
        (k := k) (Set.range S.obj) := by
  obtain ⟨N, hN⟩ :=
    exists_finiteIndexNormalSubgroup_avoiding_supportBadDegrees
      (G := G) S
  exact ⟨N,
    D.restrict_finiteModuleWindowShiftHomOrthogonal_of_avoids
      (k := k) S N hN⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
