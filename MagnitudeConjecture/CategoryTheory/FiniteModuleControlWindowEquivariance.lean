import MagnitudeConjecture.CategoryTheory.FiniteModuleResidualSeparation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleOrbit

/-!
# Equivariance of finite module control windows

The covering-average proof chooses one three-step window at a base object and
uses its deck translates at every orbit representative.  Although the finite
families implementing local representation-finiteness are chosen
noncomputably, their isomorphism closures are intrinsic: the seed consists
exactly of indecomposables nonzero at the base object, and each enlargement
consists exactly of indecomposables sharing a support object with the preceding
window.  Consequently deck translation carries the window at `g • x` into the
window at `x`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The filtered fibre seed represents exactly the indecomposable modules
which are nonzero at its base object. -/
theorem mem_finiteFiberControlSeed_isoClosure_iff
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (X : C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    M ∈ (finiteFiberControlSeed hlocal X).isoClosure ↔
      Indecomposable M ∧ Nontrivial (M.obj.obj.obj X) := by
  constructor
  · rintro ⟨i, ⟨e⟩⟩
    have hMind : Indecomposable M :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).1
        ((finiteFiberControlSeed hlocal X).indecomposable i)
    let J := (IsLinearModule.{u, v, v, v} (C := C) k).ι
    let eX := (J.mapIso
      ((IsFiniteDimensionalModule (C := C) k).ι.mapIso e)).app X
    exact ⟨hMind, eX.toLinearEquiv.toEquiv.nontrivial_congr.mp
      (finiteFiberControlSeed_obj_nontrivial hlocal X i)⟩
  · rintro ⟨hM, hMX⟩
    exact mem_finiteFiberControlSeed_isoClosure hlocal X hM hMX

namespace FiniteIndecomposableModuleFamily

variable (S : FiniteIndecomposableModuleFamily (k := k) (C := C))

/-- A common-support neighbor of any represented member belongs to the next
finite Hom window; the represented member need not be a literal chosen
label. -/
theorem mem_homNeighborhood_isoClosure_of_mem_commonSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {M Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : M ∈ S.isoClosure) (hY : Indecomposable Y)
    (hcommon : ∃ X : C,
      X ∈ moduleSupport k M.obj.obj ∧
        X ∈ moduleSupport k Y.obj.obj) :
    Y ∈ (S.homNeighborhood hlocal).isoClosure := by
  obtain ⟨i, ⟨e⟩⟩ := hM
  obtain ⟨X, hMX, hYX⟩ := hcommon
  have hSX : X ∈ moduleSupport k (S.obj i).obj.obj :=
    (mem_moduleSupport_iff_of_iso e X).2 hMX
  exact S.mem_homNeighborhood_isoClosure_of_commonSupport hlocal hY
    ⟨i, X, hSX, hYX⟩

/-- Membership in a chosen Hom-neighborhood supplies a represented member of
the preceding family sharing an actual support object with it. -/
theorem exists_mem_commonSupport_of_mem_homNeighborhood_isoClosure
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hY : Y ∈ (S.homNeighborhood hlocal).isoClosure) :
    Indecomposable Y ∧
      ∃ M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
        M ∈ S.isoClosure ∧ ∃ X : C,
          X ∈ moduleSupport k M.obj.obj ∧
            X ∈ moduleSupport k Y.obj.obj := by
  obtain ⟨j, ⟨e⟩⟩ := hY
  have hYind : Indecomposable Y :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).1
      ((S.homNeighborhood hlocal).indecomposable j)
  obtain ⟨i, X, hSX, hjX⟩ := S.homNeighborhood_obj_commonSupport hlocal j
  have hYX : X ∈ moduleSupport k Y.obj.obj :=
    (mem_moduleSupport_iff_of_iso e X).1 hjX
  exact ⟨hYind, S.obj i, ⟨i, Nonempty.intro (Iso.refl _)⟩,
    X, hSX, hYX⟩

end FiniteIndecomposableModuleFamily

namespace CoherentDeckShift

variable {G : Type v} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Shifting two finite modules by the same deck element transports an actual
common support object by the inverse deck action. -/
theorem exists_common_moduleSupport_shift
    (g : G)
    (M Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hcommon : ∃ X : C,
      X ∈ moduleSupport k M.obj.obj ∧
        X ∈ moduleSupport k Y.obj.obj) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∃ X : C,
      X ∈ moduleSupport k
        ((IsFiniteDimensionalModule (C := C) k).ι.obj
          (M⟦Additive.ofMul g⟧)).obj ∧
      X ∈ moduleSupport k
        ((IsFiniteDimensionalModule (C := C) k).ι.obj
          (Y⟦Additive.ofMul g⟧)).obj := by
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  obtain ⟨X, hMX, hYX⟩ := hcommon
  refine ⟨g⁻¹ • X, ?_, ?_⟩
  · rw [D.finiteDimensionalModuleSupport_shift_eq_preimage (k := k) M g]
    simpa using hMX
  · rw [D.finiteDimensionalModuleSupport_shift_eq_preimage (k := k) Y g]
    simpa using hYX

/-- Deck translation sends every represented member of the `n`-step window
at `g • x` into the corresponding window at `x`.  This statement is about
isomorphism closures and is therefore independent of the noncomputable local
representative choices. -/
theorem iterateHomNeighborhood_shift_mem
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C) (g : G) (n : ℕ)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : M ∈
      ((finiteFiberControlSeed hlocal (g • x)).iterateHomNeighborhood
        hlocal n).isoClosure) :
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    M⟦Additive.ofMul g⟧ ∈
      ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
        hlocal n).isoClosure := by
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  induction n generalizing M with
  | zero =>
      change M ∈ (finiteFiberControlSeed hlocal (g • x)).isoClosure at hM
      change M⟦Additive.ofMul g⟧ ∈
        (finiteFiberControlSeed hlocal x).isoClosure
      rw [mem_finiteFiberControlSeed_isoClosure_iff] at hM ⊢
      refine ⟨?_, ?_⟩
      · exact
          (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
            (shiftFunctor
              (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
              (Additive.ofMul g)) M).mpr hM.1
      · exact (D.finiteDimensionalModuleShiftEvaluationIso
          (k := k) M g x).toLinearEquiv.toEquiv.nontrivial_congr.mpr
            hM.2
  | succ n ih =>
      let Sg := (finiteFiberControlSeed hlocal (g • x)).iterateHomNeighborhood
        hlocal n
      let S := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood
        hlocal n
      have hdata :=
        Sg.exists_mem_commonSupport_of_mem_homNeighborhood_isoClosure
          hlocal hM
      obtain ⟨hMind, P, hP, hcommon⟩ := hdata
      have hPshift : P⟦Additive.ofMul g⟧ ∈ S.isoClosure := ih P hP
      have hMshift : Indecomposable (M⟦Additive.ofMul g⟧) :=
        (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          (shiftFunctor
            (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
            (Additive.ofMul g)) M).mpr hMind
      exact S.mem_homNeighborhood_isoClosure_of_mem_commonSupport hlocal
        hPshift hMshift (D.exists_common_moduleSupport_shift
          (k := k) g P M hcommon)

include D in
/-- A bad support-overlap degree for the independently chosen window at
`g • x` conjugates to a bad degree for the base window at `x`.  Normality is
therefore exactly what makes one residual subgroup work at every translate. -/
theorem inv_mul_mul_mem_threeStepControlFamilySupportBadDegrees
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C) (g a : G)
    (ha : a ∈ finiteModuleFamilySupportBadDegrees (G := G)
      (finiteThreeStepControlFamily hlocal (g • x))) :
    g⁻¹ * a * g ∈ finiteModuleFamilySupportBadDegrees (G := G)
      (finiteThreeStepControlFamily hlocal x) := by
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  let V := finiteThreeStepControlFamily hlocal (g • x)
  let U := finiteThreeStepControlFamily hlocal x
  obtain ⟨hane, i, j, X, hXi, hXj⟩ := ha
  have hiShift : V.obj i⟦Additive.ofMul g⟧ ∈ U.isoClosure :=
    D.iterateHomNeighborhood_shift_mem (k := k) hlocal x g 3 (V.obj i)
      ⟨i, Nonempty.intro (Iso.refl _)⟩
  have hjShift : V.obj j⟦Additive.ofMul g⟧ ∈ U.isoClosure :=
    D.iterateHomNeighborhood_shift_mem (k := k) hlocal x g 3 (V.obj j)
      ⟨j, Nonempty.intro (Iso.refl _)⟩
  obtain ⟨p, ⟨ep⟩⟩ := hiShift
  obtain ⟨q, ⟨eq⟩⟩ := hjShift
  let Z := g⁻¹ • X
  have hiShiftSupport : Z ∈ moduleSupport k
      ((IsFiniteDimensionalModule (C := C) k).ι.obj
        (V.obj i⟦Additive.ofMul g⟧)).obj := by
    rw [D.finiteDimensionalModuleSupport_shift_eq_preimage
      (k := k) (V.obj i) g]
    simpa [Z] using hXi
  have hiBase : Z ∈ moduleSupport k (U.obj p).obj.obj :=
    (mem_moduleSupport_iff_of_iso ep Z).2 hiShiftSupport
  have hjShiftSupport : g⁻¹ • (a • X) ∈ moduleSupport k
      ((IsFiniteDimensionalModule (C := C) k).ι.obj
        (V.obj j⟦Additive.ofMul g⟧)).obj := by
    rw [D.finiteDimensionalModuleSupport_shift_eq_preimage
      (k := k) (V.obj j) g]
    simpa using hXj
  have hjBaseRaw : g⁻¹ • (a • X) ∈
      moduleSupport k (U.obj q).obj.obj :=
    (mem_moduleSupport_iff_of_iso eq (g⁻¹ • (a • X))).2 hjShiftSupport
  have hjBase : (g⁻¹ * a * g) • Z ∈
      moduleSupport k (U.obj q).obj.obj := by
    simpa [Z, mul_smul] using hjBaseRaw
  have hconjNe : g⁻¹ * a * g ≠ 1 := by
    intro hzero
    apply hane
    have h := congrArg (fun b : G ↦ g * b * g⁻¹) hzero
    simpa [mul_assoc] using h
  exact ⟨hconjNe, p, q, Z, hiBase, hjBase⟩

include D in
/-- Residual finiteness chooses one normal finite-index subgroup avoiding the
bad support degrees of every three-step window in the entire orbit of `x`.
This removes the apparent circularity between choosing the subgroup and then
enumerating its quotient representatives. -/
theorem exists_finiteIndexNormalSubgroup_avoiding_orbit_threeStepControlFamilies
    [IsCancelSMul G C] [Group.ResiduallyFinite G]
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C) :
    ∃ N : FiniteIndexNormalSubgroup G,
      ∀ g : G, ∀ a ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hlocal (g • x)),
        a ∉ (N : Subgroup G) := by
  obtain ⟨N, hN⟩ :=
    exists_finiteIndexNormalSubgroup_avoiding_supportBadDegrees
      (G := G) (finiteThreeStepControlFamily hlocal x)
  refine ⟨N, ?_⟩
  intro g a ha hag
  have hconj := D.inv_mul_mul_mem_threeStepControlFamilySupportBadDegrees
    (k := k) hlocal x g a ha
  have hconjMem : g⁻¹ * a * g ∈ (N : Subgroup G) := by
    simpa using
      ((show (N : Subgroup G).Normal from inferInstance).conj_mem a hag g⁻¹)
  exact hN (g⁻¹ * a * g) hconj hconjMem

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
