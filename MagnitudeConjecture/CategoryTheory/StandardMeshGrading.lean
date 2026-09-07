import MagnitudeConjecture.CategoryTheory.DirectedMeshFaithfulness
import MagnitudeConjecture.Algebra.RightModuleFactorCategory

/-!
# Path-length gradings supplied by a standard mesh presentation

Ringel standardness identifies the category of selected indecomposable
modules with the mesh category of its Auslander--Reiten quiver.  This file
records the strict linear presentation obtained after choosing the skeleton
objects and transports the mesh path-length grading to the ambient Hom spaces.

The quotient by the deleted-object ideal is handled separately.  Keeping that
step separate makes the exact content of standardness visible: a compatible
family of linear Hom equivalences preserving identities and composition.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

section Presentation

variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [quiver : Quiver.{0} (Fin S.n)]
variable [arrowFintype : ∀ x y : Fin S.n, Fintype (x ⟶ y)]

/-- A strict linear realization of the selected indecomposable skeleton by a
mesh category.  It is the choice-dependent output of Ringel standardness used
by the grading argument. -/
structure StandardMeshPresentation
    (T : @MeshCategory.RightMeshData (Fin S.n) quiver) where
  homEquiv : ∀ x y : Fin S.n,
    (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y) ≃ₗ[k]
      (S.ambientAddPoint x ⟶ S.ambientAddPoint y)
  map_id : ∀ x,
    homEquiv x x (𝟙 (MeshCategory.obj (k := k) T x)) =
      𝟙 (S.ambientAddPoint x)
  map_comp : ∀ {x y z : Fin S.n}
      (f : MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y)
      (g : MeshCategory.obj (k := k) T y ⟶ MeshCategory.obj (k := k) T z),
    homEquiv x z (f ≫ g) = homEquiv x y f ≫ homEquiv y z g

end Presentation

namespace StandardMeshPresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable [quiver : Quiver.{0} (Fin S.n)]
variable [arrowFintype : ∀ x y : Fin S.n, Fintype (x ⟶ y)]
variable {T : @MeshCategory.RightMeshData (Fin S.n) quiver}

/-- A full linear realization which is injective on every displayed Hom
space is exactly a standard mesh presentation of the selected skeleton. -/
def ofRealizationInjective
    (R : MeshCategory.Realization (k := k) T S.ambientAddPoint)
    [R.functor.Full]
    (hinjective : ∀ x y : Fin S.n, Function.Injective
      (fun f : MeshCategory.obj (k := k) T x ⟶
          MeshCategory.obj (k := k) T y ↦ R.functor.map f)) :
    S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T where
  homEquiv := fun x y ↦ R.homLinearEquivOfInjective x y (hinjective x y)
  map_id := by
    intro x
    change R.functor.map (𝟙 (MeshCategory.obj (k := k) T x)) =
      𝟙 (S.ambientAddPoint x)
    exact R.functor.map_id _
  map_comp := by
    intro x y z f g
    change R.functor.map (f ≫ g) =
      R.functor.map f ≫ R.functor.map g
    exact R.functor.map_comp f g

/-- A full and faithful linear realization of a mesh quotient is exactly a
standard mesh presentation of the selected skeleton. -/
def ofRealization
    (R : MeshCategory.Realization (k := k) T S.ambientAddPoint)
    [R.functor.Full] [R.functor.Faithful] :
    S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T :=
  ofRealizationInjective R (fun _ _ ↦ R.functor.map_injective)

/-- Ringel's directed target induction turns a full realization satisfying
the local projective and almost-split exactness conditions into a standard
mesh presentation. -/
def ofDirectedExact
    (R : MeshCategory.Realization (k := k) T S.ambientAddPoint)
    [R.functor.Full]
    (D : R.DirectedExactData) :
    S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T :=
  ofRealizationInjective R D.map_injective

/-- The path-degree-`d` component transported to an ambient skeleton Hom
space. -/
def component
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (x y : Fin S.n) (d : ℕ) :
    Submodule k (S.ambientAddPoint x ⟶ S.ambientAddPoint y) :=
  (MeshCategory.lengthComponent (k := k) T x y d).map
    (H.homEquiv x y).toLinearMap

/-- Standardness transports the internal mesh path-length decomposition to
every ambient skeleton Hom space. -/
theorem component_isInternal
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (x y : Fin S.n) :
    DirectSum.IsInternal (H.component (T := T) x y) :=
  MagnitudeConjecture.Graded.image_isInternal_of_equiv
    (MeshCategory.lengthComponent (k := k) T x y)
    (MeshCategory.lengthComponent_isInternal (k := k) T x y)
    (H.homEquiv x y)

/-- Composition of transported homogeneous morphisms adds path degrees. -/
theorem comp_mem_component
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    {x y z : Fin S.n} {i j : ℕ}
    {f : S.ambientAddPoint x ⟶ S.ambientAddPoint y}
    {g : S.ambientAddPoint y ⟶ S.ambientAddPoint z}
    (hf : f ∈ H.component (T := T) x y i)
    (hg : g ∈ H.component (T := T) y z j) :
    f ≫ g ∈ H.component (T := T) x z (i + j) := by
  rcases hf with ⟨f, hf, rfl⟩
  rcases hg with ⟨g, hg, rfl⟩
  refine ⟨f ≫ g, MeshCategory.comp_mem_lengthComponent T hf hg, ?_⟩
  exact H.map_comp f g

/-- Ambient skeleton identities have path degree zero. -/
theorem id_mem_component_zero
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    (x : Fin S.n) :
    𝟙 (S.ambientAddPoint x) ∈ H.component (T := T) x x 0 := by
  refine ⟨𝟙 (MeshCategory.obj (k := k) T x),
    MeshCategory.id_mem_lengthComponent_zero (k := k) T x, ?_⟩
  exact H.map_id x

/-- Between distinct skeleton labels the transported degree-zero component
vanishes. -/
theorem component_zero_eq_bot_of_ne
    (H : S.StandardMeshPresentation (quiver := quiver)
      (arrowFintype := arrowFintype) T)
    {x y : Fin S.n} (hxy : x ≠ y) :
    H.component (T := T) x y 0 = ⊥ := by
  rw [component, MeshCategory.lengthComponent_zero_eq_bot_of_ne
    (k := k) T hxy.symm]
  exact Submodule.map_bot _

end StandardMeshPresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
