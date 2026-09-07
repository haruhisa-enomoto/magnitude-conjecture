import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleHomFinite
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteNeighborhoodAlmostSplit
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Local representation-finiteness for finite functor modules

The manuscript's local representation-finiteness condition is recorded
without choosing a global skeleton: at each object of the base category, a
finite family represents every indecomposable module nonzero there.  Finite
support turns these pointwise families into a finite target Hom neighborhood
for any fixed module.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [CategoryTheory.Linear k C]

/-- A finite family representing all indecomposable finite modules nonzero
at one base-category object. -/
structure FiniteIndecomposableFiber (X : C) where
  n : ℕ
  obj : Fin n →
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k
  indecomposable : ∀ j, Indecomposable (obj j)
  covers : ∀ {Y :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k},
    Indecomposable Y → Nontrivial (Y.obj.obj.obj X) →
      ∃ j, Nonempty (obj j ≅ Y)

/-- Only finitely many isomorphism classes of indecomposable finite modules
are nonzero at each object of the base category. -/
def IsLocallyRepresentationFinite : Prop :=
  ∀ X : C, Nonempty (FiniteIndecomposableFiber (k := k) X)

/-- A finite-support module has only finitely many indecomposable target
neighbors in a locally representation-finite module category. -/
def finiteIndecomposableTargetNeighborhood_of_locallyRepresentationFinite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableTargetNeighborhood M := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  let H (X : S) := Classical.choice (hlocal X.1)
  let I := Σ X : S, Fin (H X).n
  letI : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  refine
    { n := n
      obj := fun t ↦ (H (e t).1).obj (e t).2
      indecomposable := fun t ↦ (H (e t).1).indecomposable (e t).2
      covers := ?_ }
  intro Y hY f hf
  have hcomponent : ∃ X : C, f.hom.hom.app X ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact hall X
  obtain ⟨X, hX⟩ := hcomponent
  have hMX : Nontrivial (M.obj.obj.obj X) := by
    by_contra htrivial
    rw [not_nontrivial_iff_subsingleton] at htrivial
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [show x = 0 from Subsingleton.elim _ _]
    simp
  have hYX : Nontrivial (Y.obj.obj.obj X) := by
    by_contra htrivial
    rw [not_nontrivial_iff_subsingleton] at htrivial
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  let Xs : S := ⟨X, hMX⟩
  obtain ⟨j, hj⟩ := (H Xs).covers hY hYX
  let p : I := ⟨Xs, j⟩
  refine ⟨e.symm p, ?_⟩
  rw [e.apply_symm_apply p]
  exact hj

/-- A finite-support module has only finitely many indecomposable source
neighbors in a locally representation-finite module category. -/
def finiteIndecomposableSourceNeighborhood_of_locallyRepresentationFinite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableSourceNeighborhood M := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  let H (X : S) := Classical.choice (hlocal X.1)
  let I := Σ X : S, Fin (H X).n
  letI : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  refine
    { n := n
      obj := fun t ↦ (H (e t).1).obj (e t).2
      indecomposable := fun t ↦ (H (e t).1).indecomposable (e t).2
      covers := ?_ }
  intro Y hY f hf
  have hcomponent : ∃ X : C, f.hom.hom.app X ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact hall X
  obtain ⟨X, hX⟩ := hcomponent
  have hMX : Nontrivial (M.obj.obj.obj X) := by
    by_contra htrivial
    rw [not_nontrivial_iff_subsingleton] at htrivial
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  have hYX : Nontrivial (Y.obj.obj.obj X) := by
    by_contra htrivial
    rw [not_nontrivial_iff_subsingleton] at htrivial
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [show x = 0 from Subsingleton.elim _ _]
    simp
  let Xs : S := ⟨X, hMX⟩
  obtain ⟨j, hj⟩ := (H Xs).covers hY hYX
  let p : I := ⟨Xs, j⟩
  refine ⟨e.symm p, ?_⟩
  rw [e.apply_symm_apply p]
  exact hj

/-- Finite radical evaluation gives a left almost-split map from every
indecomposable finite module under local representation-finiteness. -/
theorem finiteDimensionalModule_exists_leftAlmostSplit_of_locallyRepresentationFinite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : Indecomposable M) :
    ∃ (E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
      (f : M ⟶ E),
      IsLeftAlmostSplit f := by
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hM
  exact
    MagnitudeConjecture.CategoryTheory.exists_leftAlmostSplit_of_finiteIndecomposableTargetNeighborhood
      k finiteDimensionalModule_finiteIndecomposableDecomposition hM
        (finiteIndecomposableTargetNeighborhood_of_locallyRepresentationFinite
          hlocal M)

/-- Finite radical coevaluation gives a right almost-split map to every
indecomposable finite module under local representation-finiteness. -/
theorem finiteDimensionalModule_exists_rightAlmostSplit_of_locallyRepresentationFinite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : Indecomposable M) :
    ∃ (E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
      (f : E ⟶ M),
      IsRightAlmostSplit f := by
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hM
  exact
    MagnitudeConjecture.CategoryTheory.exists_rightAlmostSplit_of_finiteIndecomposableSourceNeighborhood
      k finiteDimensionalModule_finiteIndecomposableDecomposition hM
        (finiteIndecomposableSourceNeighborhood_of_locallyRepresentationFinite
          hlocal M)

/-- At a noninjective indecomposable, the finite radical-evaluation map can
be chosen monic whenever the finite module category has enough injectives. -/
theorem finiteDimensionalModule_exists_mono_leftAlmostSplit_of_locallyRepresentationFinite
    [EnoughInjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : Indecomposable M) (hMnot : ¬ Injective M) :
    ∃ (E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
      (f : M ⟶ E),
      Mono f ∧ IsLeftAlmostSplit f := by
  obtain ⟨E, f, hf⟩ :=
    finiteDimensionalModule_exists_leftAlmostSplit_of_locallyRepresentationFinite
      hlocal hM
  let P := (EnoughInjectives.presentation M).some
  have hPnonsplit : ¬ IsSplitMono P.f := by
    intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitMono
    apply hMnot
    exact Retract.injective
      { i := P.f
        r := s.retraction
        retract := s.id }
  haveI : Mono f := hf.mono_of_nonsplit_mono P.f hPnonsplit
  exact ⟨E, f, inferInstance, hf⟩

end MagnitudeConjecture.CoveringHom
