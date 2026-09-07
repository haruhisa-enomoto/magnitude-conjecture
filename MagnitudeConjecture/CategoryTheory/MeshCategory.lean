import MagnitudeConjecture.CategoryTheory.HomogeneousRelationQuotient

/-!
# Finite mesh categories and their path-length grading

This file packages the right-translation data needed for ordinary mesh
relations.  The quiver is written in the orientation used by the free linear
path category: an arrow `x ⟶ y` represents an irreducible morphism from `y`
to `x`.  Thus the translation pairing at a nonprojective `x` sends

`x ⟶ y` to `y ⟶ τx`.

When the arrow star at each vertex is finite, the mesh relation is the sum of
the corresponding length-two paths.  The vertex type itself may be infinite,
as it is for a universal Auslander--Reiten cover.  The general homogeneous-
relation quotient construction then gives an internally graded mesh category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.MeshCategory

open QuotientSubmoduleEquidistribution.CategoricalIdeal

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- The minimal right-translation-quiver data needed to form ordinary mesh
relations.  Full Auslander--Reiten data will provide this by restricting the
translation to nonprojective vertices and pairing the two sides of each
mesh. -/
structure RightMeshData (Q : Type v) [Quiver.{w} Q] where
  projective : Set Q
  tau : {x : Q // x ∉ projective} → Q
  arrowEquiv : ∀ (x : {x : Q // x ∉ projective}) (y : Q),
    (x.1 ⟶ y) ≃ (y ⟶ tau x)

namespace RightMeshData

variable (T : RightMeshData Q)

/-- A reversed incoming arrow at the endpoint of a mesh. -/
abbrev MeshArrow (x : {x : Q // x ∉ T.projective}) :=
  Σ y : Q, x.1 ⟶ y

/-- The length-two reversed-quiver path associated to one paired mesh
arrow. -/
def meshPath (x : {x : Q // x ∉ T.projective})
    (a : T.MeshArrow x) : Quiver.Path x.1 (T.tau x) :=
  a.2.toPath.comp ((T.arrowEquiv x a.1) a.2).toPath

@[simp]
theorem meshPath_length (x : {x : Q // x ∉ T.projective})
    (a : T.MeshArrow x) :
    (T.meshPath x a).length = 2 := by
  simp [meshPath]

variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

/-- The ordinary mesh relation at a nonprojective vertex. -/
def meshRelation (x : {x : Q // x ∉ T.projective}) :
    MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau x) ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q x.1 :=
  ∑ a : T.MeshArrow x,
    MagnitudeConjecture.LinearPathCategory.pathHom (k := k) (T.meshPath x a)

/-- Every ordinary mesh relation has path degree two. -/
theorem meshRelation_mem_lengthComponent_two
    (x : {x : Q // x ∉ T.projective}) :
    T.meshRelation (k := k) x ∈
      MagnitudeConjecture.LinearPathCategory.lengthComponent
        (MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau x))
        (MagnitudeConjecture.LinearPathCategory.obj k Q x.1) 2 := by
  rw [meshRelation]
  apply Submodule.sum_mem
  intro a ha
  rw [MagnitudeConjecture.LinearPathCategory.pathHom_mem_lengthComponent_iff]
  exact T.meshPath_length x a

/-- The family of all mesh-relation generators, indexed by their categorical
endpoints.  Equality transports only place a relation in the requested Hom
type; after substituting the endpoint equalities they are identities. -/
def meshGeneratorSet
    (X Y : MagnitudeConjecture.LinearPathCategory.Category k Q) :
    Set (X ⟶ Y) :=
  {f | ∃ (x : {x : Q // x ∉ T.projective})
      (hX : X = MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau x))
      (hY : Y = MagnitudeConjecture.LinearPathCategory.obj k Q x.1),
    f = eqToHom hX ≫ T.meshRelation (k := k) x ≫ eqToHom hY.symm}

/-- The defining mesh relation occurs in the generator family at its literal
endpoints. -/
theorem meshRelation_mem_meshGeneratorSet
    (x : {x : Q // x ∉ T.projective}) :
    T.meshRelation (k := k) x ∈
      T.meshGeneratorSet (k := k)
        (MagnitudeConjecture.LinearPathCategory.obj k Q (T.tau x))
        (MagnitudeConjecture.LinearPathCategory.obj k Q x.1) := by
  exact ⟨x, rfl, rfl, by simp⟩

/-- Every generator in the endpoint-indexed family has degree two. -/
theorem meshGeneratorSet_mem_lengthComponent_two
    (X Y : MagnitudeConjecture.LinearPathCategory.Category k Q) (f : X ⟶ Y)
    (hf : f ∈ T.meshGeneratorSet (k := k) X Y) :
    f ∈ MagnitudeConjecture.LinearPathCategory.lengthComponent X Y 2 := by
  rcases hf with ⟨x, rfl, rfl, rfl⟩
  simpa using T.meshRelation_mem_lengthComponent_two (k := k) x

/-- In particular, every mesh generator is homogeneous. -/
theorem meshGeneratorSet_isHomogeneous
    (X Y : MagnitudeConjecture.LinearPathCategory.Category k Q) (f : X ⟶ Y)
    (hf : f ∈ T.meshGeneratorSet (k := k) X Y) :
    ∃ n, f ∈ MagnitudeConjecture.LinearPathCategory.lengthComponent X Y n :=
  ⟨2, T.meshGeneratorSet_mem_lengthComponent_two (k := k) X Y f hf⟩

/-- Every path-basis two-sided composite of a mesh generator has strictly
positive path length. -/
theorem basisCompositeSet_mem_positive
    (X Y : MagnitudeConjecture.LinearPathCategory.Category k Q) (f : X ⟶ Y)
    (hf : f ∈ MagnitudeConjecture.LinearPathCategory.basisCompositeSet
      (T.meshGeneratorSet (k := k)) X Y) :
    ∃ n, n ≠ 0 ∧
      f ∈ MagnitudeConjecture.LinearPathCategory.lengthComponent X Y n := by
  rcases hf with ⟨A, B, r, hr, p, q, rfl⟩
  have hp : MagnitudeConjecture.LinearPathCategory.pathHom p ∈
      MagnitudeConjecture.LinearPathCategory.lengthComponent X A p.length :=
    (MagnitudeConjecture.LinearPathCategory.pathHom_mem_lengthComponent_iff
      p p.length).2 rfl
  have hr' : r ∈ MagnitudeConjecture.LinearPathCategory.lengthComponent A B 2 :=
    T.meshGeneratorSet_mem_lengthComponent_two (k := k) A B r hr
  have hq : MagnitudeConjecture.LinearPathCategory.pathHom q ∈
      MagnitudeConjecture.LinearPathCategory.lengthComponent B Y q.length :=
    (MagnitudeConjecture.LinearPathCategory.pathHom_mem_lengthComponent_iff
      q q.length).2 rfl
  refine ⟨p.length + 2 + q.length, by omega, ?_⟩
  exact MagnitudeConjecture.CategoricalGrading.comp_comp_mem
    (fun X Y ↦ MagnitudeConjecture.LinearPathCategory.lengthComponent X Y)
    (fun ha hb ↦ MagnitudeConjecture.LinearPathCategory.comp_mem_lengthComponent ha hb)
    hp hr' hq

end RightMeshData

variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

/-- The raw categorical quotient by the ordinary mesh relations. -/
abbrev RawCategory (T : RightMeshData Q) :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.RawCategory
    (T.meshGeneratorSet (k := k))

/-- The functor from the free linear path category to the raw mesh
category. -/
abbrev quotientFunctor (T : RightMeshData Q) :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.quotientFunctor
    (T.meshGeneratorSet (k := k))

/-- A quiver vertex as an object of the raw mesh category. -/
abbrev obj (T : RightMeshData Q) (x : Q) : RawCategory (k := k) T :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.obj
    (T.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)

/-- The degree-`n` part of a mesh-category Hom space. -/
def lengthComponent (T : RightMeshData Q) (x y : Q) (n : ℕ) :
    Submodule k (obj (k := k) T x ⟶ obj (k := k) T y) :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.lengthComponent
    (T.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q y) n

/-- The path-length pieces form an internal decomposition of every
mesh-category Hom space. -/
theorem lengthComponent_isInternal (T : RightMeshData Q) (x y : Q) :
    DirectSum.IsInternal (lengthComponent (k := k) T x y) :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.lengthComponent_isInternal
    (T.meshGeneratorSet (k := k)) T.meshGeneratorSet_isHomogeneous
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q y)

/-- Composition in the mesh category adds degrees. -/
theorem comp_mem_lengthComponent
    (T : RightMeshData Q) {x y z : Q} {i j : ℕ}
    {f : obj (k := k) T x ⟶ obj (k := k) T y}
    {g : obj (k := k) T y ⟶ obj (k := k) T z}
    (hf : f ∈ lengthComponent (k := k) T x y i)
    (hg : g ∈ lengthComponent (k := k) T y z j) :
    f ≫ g ∈ lengthComponent (k := k) T x z (i + j) :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.comp_mem_lengthComponent
    (T.meshGeneratorSet (k := k)) hf hg

/-- Every mesh-category vertex identity has path degree zero. -/
@[simp]
theorem id_mem_lengthComponent_zero (T : RightMeshData Q) (x : Q) :
    𝟙 (obj (k := k) T x) ∈ lengthComponent (k := k) T x x 0 :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.id_mem_lengthComponent_zero
    (T.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)

/-- Degree zero at a mesh-category vertex is the scalar span of its
identity. -/
theorem lengthComponent_zero_self (T : RightMeshData Q) (x : Q) :
    lengthComponent (k := k) T x x 0 = k ∙ (𝟙 (obj (k := k) T x)) :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.lengthComponent_zero_self
    (T.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)

/-- Degree zero between distinct mesh-category vertices vanishes. -/
theorem lengthComponent_zero_eq_bot_of_ne
    (T : RightMeshData Q) {x y : Q} (hxy : y ≠ x) :
    lengthComponent (k := k) T x y 0 = ⊥ :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.lengthComponent_zero_eq_bot_of_vertex_ne
    (T.meshGeneratorSet (k := k)) hxy

/-- Every defining mesh relation vanishes in the raw mesh category. -/
theorem quotient_map_meshRelation_eq_zero
    (T : RightMeshData Q) (x : {x : Q // x ∉ T.projective}) :
    (quotientFunctor (k := k) T).map (T.meshRelation (k := k) x) = 0 := by
  apply ((MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.relationIdeal
    (T.meshGeneratorSet (k := k))).map_eq_zero_iff _).2
  exact HomIdeal.relation_mem_linearSpan _
    (T.meshRelation_mem_meshGeneratorSet (k := k) x)

/-- Mesh relations cannot kill a vertex identity: every two-sided
path-basis composite of a mesh relation has positive length, while the
identity has nonzero trivial-path coefficient. -/
theorem id_ne_zero (T : RightMeshData Q) (x : Q) :
    𝟙 (obj (k := k) T x) ≠ 0 :=
  MagnitudeConjecture.LinearPathCategory.HomogeneousQuotient.id_ne_zero_of_basisCompositeSet_positive
    (T.meshGeneratorSet (k := k))
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (fun f hf ↦ T.basisCompositeSet_mem_positive (k := k) _ _ f hf)

end MagnitudeConjecture.MeshCategory
