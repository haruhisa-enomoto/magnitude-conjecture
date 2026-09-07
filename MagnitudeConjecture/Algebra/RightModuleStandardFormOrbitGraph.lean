import MagnitudeConjecture.Algebra.RightModuleStandardFormMesh
import MagnitudeConjecture.CategoryTheory.TranslationQuiverComponentGraph

/-!
# Translation orbit graph of the standard form

Auslander--Reiten translation is an equivalence from nonprojective to
noninjective standard-form labels.  In particular its underlying right
translation is injective, so the generic tau- and sigma-orbit graph applies.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormOrbitQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver
local instance standardFormOrbitArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

omit [IsAlgClosed k] in
/-- The standard-form AR translation is injective on nonprojective labels. -/
theorem standardFormTau_injective :
    Function.Injective S.standardFormTau := by
  intro x y hxy
  apply Subtype.ext
  let x' : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    ⟨x.1, by simpa [standardFormProjectiveSet] using x.2⟩
  let y' : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    ⟨y.1, by simpa [standardFormProjectiveSet] using y.2⟩
  have h : S.rightTranslationEquiv x' = S.rightTranslationEquiv y' := by
    apply Subtype.ext
    exact hxy
  exact congrArg Subtype.val (S.rightTranslationEquiv.injective h)

/-- The standard-form mesh data has injective right translation. -/
theorem standardFormRightMeshData_isTauInjective :
    S.standardFormRightMeshData.IsTauInjective :=
  S.standardFormTau_injective

/-- Tau-orbits of standard-form labels. -/
abbrev StandardFormTauOrbit :=
  MeshCategory.RightMeshData.IsTauInjective.TauOrbit
    S.standardFormRightMeshData

/-- Sigma-orbits of standard-form ordinary arrows. -/
abbrev StandardFormArrowOrbit :=
  MeshCategory.RightMeshData.IsTauInjective.ArrowOrbit
    S.standardFormRightMeshData
      S.standardFormRightMeshData_isTauInjective

/-- Periodic tau-orbits of standard-form labels. -/
abbrev StandardFormPeriodicTauOrbit :=
  MeshCategory.RightMeshData.IsTauInjective.PeriodicTauOrbit
    S.standardFormRightMeshData

/-- Nonperiodic tau-orbits of standard-form labels. -/
abbrev StandardFormNonperiodicTauOrbit :=
  MeshCategory.RightMeshData.IsTauInjective.NonperiodicTauOrbit
    S.standardFormRightMeshData

/-- Periodic stable components of the standard-form translation quiver. -/
abbrev StandardFormPeriodicComponent :=
  MeshCategory.RightMeshData.IsTauInjective.PeriodicComponent
    S.standardFormRightMeshData
      S.standardFormRightMeshData_isTauInjective

/-- Nonperiodic sigma-orbits of standard-form arrows. -/
abbrev StandardFormNonperiodicArrowOrbit :=
  MeshCategory.RightMeshData.IsTauInjective.NonperiodicArrowOrbit
    S.standardFormRightMeshData
      S.standardFormRightMeshData_isTauInjective

/-- Vertices of the standard-form Bongartz--Gabriel component graph. -/
abbrev StandardFormComponentGraphVertex :=
  MeshCategory.RightMeshData.IsTauInjective.ComponentGraphVertex
    S.standardFormRightMeshData
      S.standardFormRightMeshData_isTauInjective

/-- Unindexed edges of the standard-form Bongartz--Gabriel component graph. -/
abbrev StandardFormComponentGraphEdge :=
  MeshCategory.RightMeshData.IsTauInjective.ComponentGraphEdge
    S.standardFormRightMeshData
      S.standardFormRightMeshData_isTauInjective

noncomputable instance standardFormTauOrbitFintype :
    Fintype S.StandardFormTauOrbit := by
  letI := Classical.decEq S.StandardFormTauOrbit
  exact Fintype.ofSurjective
    (MeshCategory.RightMeshData.IsTauInjective.tauClass
      S.standardFormRightMeshData)
    Quotient.mk_surjective

noncomputable instance standardFormArrowOrbitFintype :
    Fintype S.StandardFormArrowOrbit := by
  letI := Classical.decEq S.StandardFormArrowOrbit
  exact Fintype.ofSurjective
    (fun a : MeshCategory.RightMeshData.IsTauInjective.Arrow
        S.standardFormRightMeshData ↦ Quotient.mk _ a)
    Quotient.mk_surjective

noncomputable instance standardFormPeriodicTauOrbitFintype :
    Fintype S.StandardFormPeriodicTauOrbit :=
  Fintype.ofFinite _

noncomputable instance standardFormNonperiodicTauOrbitFintype :
    Fintype S.StandardFormNonperiodicTauOrbit :=
  Fintype.ofFinite _

noncomputable instance standardFormPeriodicComponentFintype :
    Fintype S.StandardFormPeriodicComponent := by
  letI := Classical.decEq S.StandardFormPeriodicComponent
  exact Fintype.ofSurjective
    (MeshCategory.RightMeshData.IsTauInjective.periodicComponentClass
      S.standardFormRightMeshData
        S.standardFormRightMeshData_isTauInjective)
    Quotient.mk_surjective

noncomputable instance standardFormNonperiodicArrowOrbitFintype :
    Fintype S.StandardFormNonperiodicArrowOrbit :=
  Fintype.ofFinite _

noncomputable instance standardFormComponentGraphVertexFintype :
    Fintype S.StandardFormComponentGraphVertex :=
  Fintype.ofFinite _

noncomputable instance standardFormComponentGraphEdgeFintype :
    Fintype S.StandardFormComponentGraphEdge :=
  Fintype.ofFinite _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
