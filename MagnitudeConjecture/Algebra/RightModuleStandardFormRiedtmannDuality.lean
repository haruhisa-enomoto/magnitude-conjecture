import MagnitudeConjecture.Algebra.RightModuleStandardFormGlobalDimension
import MagnitudeConjecture.Algebra.RightModuleStandardFormRiedtmann
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleInjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope
import MagnitudeConjecture.CategoryTheory.MeshRiedtmannContravariantDuality
import MagnitudeConjecture.CategoryTheory.MeshTopTorsionfree

/-!
# Projective--injective coordinates in the standard mesh category

In the contravariant standard-mesh module category used by the
Bongartz--Gabriel recovery argument, Riedtmann condition (c) identifies the
injective `D Hom(p,-)` at a projective vertex with a contravariant
representable.  Hence this injective coordinate is projective.  Its canonical
simple socle is an essential submodule.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormRiedtmannDualityQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormRiedtmannDualityArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The raw standard-mesh Hom spaces between vertices are
finite-dimensional. -/
theorem standardFormVertexMeshHomFinite (x y : Fin S.n) :
    FiniteDimensional k
      (MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData y) :=
  S.standardFormMeshHomFinite
    (MeshCategory.obj (k := k) S.standardFormRightMeshData x)
    (MeshCategory.obj (k := k) S.standardFormRightMeshData y)

/-- All dual corepresentables in the contravariant standard-mesh module
category are finite-dimensional. -/
theorem standardFormFiniteContravariantDualCorepresentables :
    ∀ X : S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ,
      IsFiniteDimensionalModule
        (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k
        (dualLinearYonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (Module.Dual k (Y ⟶ X))
    letI : FiniteDimensional k (X.unop ⟶ Y.unop) := by
      letI : FiniteDimensional k
          (MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop ⟶
            MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop) :=
        S.standardFormVertexMeshHomFinite X.unop Y.unop
      exact FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    letI : FiniteDimensional k (Y ⟶ X) :=
      FiniteDimensional.of_injective
        (oppositeHomLinearEquiv Y X).toLinearMap
        (oppositeHomLinearEquiv Y X).injective
    infer_instance
  · exact Set.toFinite _

/-- A standard-form vertex regarded as an object of the opposite strict
vertex category. -/
abbrev standardFormOppositeVertex (x : Fin S.n) :
    S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ :=
  Opposite.op x

/-- The canonical simple socle of `D Hom(x,-)` in the contravariant
standard-mesh module category. -/
noncomputable abbrev standardFormContravariantDualSocle (x : Fin S.n) :=
  finiteDimensionalDualLinearYonedaSocle
    (k := k) (S.standardFormOppositeVertex (k := k) x)
    (S.standardFormFiniteContravariantDualCorepresentables
      (S.standardFormOppositeVertex (k := k) x))

/-- The canonical socle inclusion into `D Hom(x,-)`. -/
noncomputable abbrev standardFormContravariantDualSocleInclusion
    (x : Fin S.n) :
    S.standardFormContravariantDualSocle (k := k) x ⟶
      finiteDimensionalDualLinearYoneda
        (k := k) (S.standardFormOppositeVertex (k := k) x)
        (S.standardFormFiniteContravariantDualCorepresentables
          (S.standardFormOppositeVertex (k := k) x)) :=
  finiteDimensionalDualLinearYonedaSocleInclusion
    (k := k) (S.standardFormOppositeVertex (k := k) x)
    (S.standardFormFiniteContravariantDualCorepresentables
      (S.standardFormOppositeVertex (k := k) x))

/-- The canonical contravariant standard-mesh socle coordinate is
simple. -/
theorem standardFormContravariantDualSocle_simple (x : Fin S.n) :
    Simple (S.standardFormContravariantDualSocle (k := k) x) :=
  finiteDimensionalDualLinearYonedaSocle_simple
    S.standardFormFiniteContravariantDualCorepresentables
    S.standardFormOppositeVertexCategoryEndLocal
    (S.standardFormOppositeVertex (k := k) x)

/-- The canonical contravariant standard-mesh socle inclusion is
nonzero. -/
theorem standardFormContravariantDualSocleInclusion_ne_zero
    (x : Fin S.n) :
    S.standardFormContravariantDualSocleInclusion (k := k) x ≠ 0 :=
  finiteDimensionalDualLinearYonedaSocleInclusion_ne_zero
    S.standardFormFiniteContravariantDualCorepresentables
    S.standardFormOppositeVertexCategoryEndLocal
    (S.standardFormOppositeVertex (k := k) x)

/-- The canonical socle of `D Hom(x,-)` is the mesh simple supported at
`x`. -/
noncomputable def standardFormContravariantDualSocleIsoSimple
    (x : Fin S.n) :
    S.standardFormContravariantDualSocle (k := k) x ≅
      S.standardFormRightMeshData.simpleFiniteModule (k := k) x := by
  letI : Simple (S.standardFormContravariantDualSocle (k := k) x) :=
    S.standardFormContravariantDualSocle_simple x
  let hex :=
    S.exists_iso_standardFormSimpleFiniteModule_of_simple
      (S.standardFormContravariantDualSocle (k := k) x)
  let z := Classical.choose hex
  let e := Classical.choice (Classical.choose_spec hex)
  let s := e.inv ≫
    S.standardFormContravariantDualSocleInclusion (k := k) x
  have hs : s ≠ 0 := by
    intro hzero
    apply S.standardFormContravariantDualSocleInclusion_ne_zero x
    apply (cancel_epi e.inv).1
    simpa [s] using hzero
  have hzx : z = x :=
    S.standardFormRightMeshData.eq_of_nonzero_map_simple_to_dualCorepresentable
      (k := k)
      (S.standardFormFiniteContravariantDualCorepresentables
        (S.standardFormOppositeVertex (k := k) x))
      s hs
  exact e ≪≫ eqToIso (congrArg
    (S.standardFormRightMeshData.simpleFiniteModule (k := k)) hzx)

/-- The canonical simple socle is essential in its indecomposable injective
dual corepresentable. -/
theorem standardFormContravariantDualSocleInclusion_essential
    (x : Fin S.n) :
    IsEssentialMono
      (S.standardFormContravariantDualSocleInclusion (k := k) x) := by
  letI : Injective
      (finiteDimensionalDualLinearYoneda
        (k := k) (S.standardFormOppositeVertex (k := k) x)
        (S.standardFormFiniteContravariantDualCorepresentables
          (S.standardFormOppositeVertex (k := k) x))) :=
    finiteDimensionalDualLinearYoneda_injective
      (S.standardFormOppositeVertex (k := k) x)
      (S.standardFormFiniteContravariantDualCorepresentables
        (S.standardFormOppositeVertex (k := k) x))
  letI : IsLocalRing
      (End (finiteDimensionalDualLinearYoneda
        (k := k) (S.standardFormOppositeVertex (k := k) x)
        (S.standardFormFiniteContravariantDualCorepresentables
          (S.standardFormOppositeVertex (k := k) x)))) :=
    finiteDimensionalDualLinearYoneda_end_isLocalRing
      S.standardFormFiniteContravariantDualCorepresentables
      S.standardFormOppositeVertexCategoryEndLocal
      (S.standardFormOppositeVertex (k := k) x)
  exact isEssentialMono_of_mono_nonzero_of_injective_local_end
    (S.standardFormContravariantDualSocleInclusion (k := k) x)
    (S.standardFormContravariantDualSocleInclusion_ne_zero x)

/-- The canonical condition-(c) datum chosen at a projective standard-form
vertex. -/
noncomputable def standardFormProjectiveDualityData
    (p : S.StandardFormProjectiveVertex) :
    S.StandardFormRiedtmannProjectiveDualityData (k := k) p.1 :=
  Classical.choice
    (S.standardFormRiedtmannConditionC p.1
      ((S.mem_standardFormProjectiveSet_iff p.1).2 p.2))

/-- Condition (c), in the orientation used by the recovery proof, identifies
`D Hom(p,-)` with the contravariant representable at the paired vertex. -/
noncomputable def standardFormProjectiveContravariantDualityFiniteModuleIso
    (p : S.StandardFormProjectiveVertex) :
    finiteDimensionalDualLinearYoneda
        (k := k) (S.standardFormOppositeVertex (k := k) p.1)
        (S.standardFormFiniteContravariantDualCorepresentables
          (S.standardFormOppositeVertex (k := k) p.1)) ≅
      S.standardFormRightMeshData.contravariantRepresentableFiniteModule
        (k := k) S.standardFormFiniteContravariantRepresentables
        (S.standardFormProjectiveDualityData p).dualVertex :=
  S.standardFormRightMeshData.riedtmannProjectiveContravariantFiniteModuleIso
    (k := k) S.standardFormVertexMeshHomFinite
    S.standardFormFiniteContravariantRepresentables
    (S.standardFormProjectiveDualityData p)
    (S.standardFormFiniteContravariantDualCorepresentables
      (S.standardFormOppositeVertex (k := k) p.1))

set_option maxHeartbeats 800000 in
/-- The injective `D Hom(p,-)` based at a projective standard-form vertex
is projective. -/
theorem standardFormProjectiveContravariantDualLinearYoneda_projective
    (p : S.StandardFormProjectiveVertex) :
    Projective
      (finiteDimensionalDualLinearYoneda
        (k := k) (S.standardFormOppositeVertex (k := k) p.1)
        (S.standardFormFiniteContravariantDualCorepresentables
          (S.standardFormOppositeVertex (k := k) p.1))) :=
  Projective.of_iso
    (S.standardFormProjectiveContravariantDualityFiniteModuleIso p).symm
    (S.standardFormRightMeshData.contravariantRepresentableFiniteModule_projective
      (k := k) S.standardFormFiniteContravariantRepresentables
      (S.standardFormProjectiveDualityData p).dualVertex)

/-- A finite injective contravariant standard-mesh module is projective once
each indecomposable retract is identified with `D Hom(p,-)` for a projective
vertex `p`. -/
theorem standardFormFiniteContravariantInjective_projective_of_conditionC_coordinates
    (M : FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k)
    [Injective M]
    (hcoordinates : ∀ N : FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k,
      Indecomposable N → Injective N →
        ∀ (i : N ⟶ M) (r : M ⟶ N), i ≫ r = 𝟙 N →
          ∃ p : S.StandardFormProjectiveVertex, Nonempty
          (finiteDimensionalDualLinearYoneda
              (k := k) (S.standardFormOppositeVertex (k := k) p.1)
              (S.standardFormFiniteContravariantDualCorepresentables
                (S.standardFormOppositeVertex (k := k) p.1)) ≅ N)) :
    Projective M := by
  apply finiteDimensionalModule_projective_of_injective_of_indec_projective M
  intro N hN hNinjective i r hir
  obtain ⟨p, ⟨e⟩⟩ := hcoordinates N hN hNinjective i r hir
  exact Projective.of_iso e
    (S.standardFormProjectiveContravariantDualLinearYoneda_projective p)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
