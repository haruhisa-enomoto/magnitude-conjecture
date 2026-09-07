import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAlmostSplitMinimal
import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauLocalDensity

/-!
# Intrinsic local density in a locally representation-finite module category

The manuscript defines the local density at an indecomposable module from
the total number of occurrences in a sink map and from projectivity of the
endpoint.  Local representation-finiteness supplies a right almost-split
map without choosing a global finite skeleton; minimalization and finite
Krull--Schmidt decomposition then make this definition literal.  Uniqueness
of minimal right almost-split maps proves independence from all choices.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- A minimal right almost-split sink together with a displayed finite
indecomposable decomposition of its source. -/
structure FiniteModuleMinimalSinkData
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) where
  source : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k
  map : source ⟶ M
  rightAlmostSplit : IsRightAlmostSplit map
  rightMinimal : IsRightMinimal map
  decomposition :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition source

/-- Local representation-finiteness chooses a finite minimal sink at every
indecomposable finite module. -/
noncomputable def finiteModuleMinimalSinkData
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) :
    FiniteModuleMinimalSinkData M :=
  let h :=
    finiteDimensionalModule_exists_rightAlmostSplit_of_locallyRepresentationFinite
      hlocal hM
  let f := Classical.choose (Classical.choose_spec h)
  let hf := Classical.choose_spec (Classical.choose_spec h)
  let hmin := finiteDimensionalModule_exists_rightMinimal_rightAlmostSplit f hf
  let E' := Classical.choose hmin
  let f' := Classical.choose (Classical.choose_spec hmin)
  { source := E'
    map := f'
    rightAlmostSplit := (Classical.choose_spec
      (Classical.choose_spec hmin)).1
    rightMinimal := (Classical.choose_spec
      (Classical.choose_spec hmin)).2
    decomposition := Classical.choice
      (finiteDimensionalModule_finiteIndecomposableDecomposition E') }

/-- The manuscript's local density `ρ_C(M)`: twice the nonprojective
indicator minus the number of indecomposable occurrences in a minimal sink
source. -/
noncomputable def finiteModuleLocalDensity
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) : ℤ :=
  MagnitudeConjecture.ARCount.localDensityOfIncomingArity
    (finiteModuleMinimalSinkData hlocal M hM).decomposition.n
    (Projective M)

/-- The chosen minimal-sink arity agrees with every displayed decomposition
of every other minimal right almost-split source at the same endpoint. -/
theorem finiteModuleMinimalSinkData_arity_eq
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    {E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {f : E ⟶ M}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E)
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f) :
    (finiteModuleMinimalSinkData hlocal M hM).decomposition.n = d.n := by
  let S := finiteModuleMinimalSinkData hlocal M hM
  exact S.decomposition.n_eq_of_minimalRightAlmostSplit d
    (fun i ↦ finiteDimensionalModule_end_isLocalRing
      k (S.decomposition.summand i) (S.decomposition.indecomposable i))
    S.rightAlmostSplit S.rightMinimal hf hfmin

/-- Any displayed finite decomposition of a minimal sink computes the
intrinsic local density. -/
theorem finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    {E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {f : E ⟶ M}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E)
    (hf : IsRightAlmostSplit f) (hfmin : IsRightMinimal f) :
    finiteModuleLocalDensity hlocal M hM =
      MagnitudeConjecture.ARCount.localDensityOfIncomingArity d.n
        (Projective M) := by
  rw [finiteModuleLocalDensity,
    finiteModuleMinimalSinkData_arity_eq hlocal M hM d hf hfmin]

/-- Local density depends only on the isomorphism class of the represented
indecomposable module. -/
theorem finiteModuleLocalDensity_eq_of_iso
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : Indecomposable M) (hN : Indecomposable N) (e : M ≅ N) :
    finiteModuleLocalDensity hlocal M hM =
      finiteModuleLocalDensity hlocal N hN := by
  classical
  let S := finiteModuleMinimalSinkData hlocal M hM
  have hMcalc :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocal M hM S.decomposition S.rightAlmostSplit S.rightMinimal
  have hNcalc :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocal N hN S.decomposition
        (S.rightAlmostSplit.postcomp_iso e)
        (S.rightMinimal.postcomp_iso e)
  rw [hMcalc, hNcalc,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity]
  have hProjective : Projective M ↔ Projective N :=
    ⟨fun h ↦ Projective.of_iso e h,
      fun h ↦ Projective.of_iso e.symm h⟩
  by_cases h : Projective M
  · have h' : Projective N := hProjective.1 h
    simp [h, h']
  · have h' : ¬ Projective N := fun hNproj ↦ h (hProjective.2 hNproj)
    simp [h, h']

end MagnitudeConjecture.CoveringHom
