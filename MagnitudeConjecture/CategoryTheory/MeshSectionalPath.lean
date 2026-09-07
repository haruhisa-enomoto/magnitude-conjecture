import MagnitudeConjecture.CategoryTheory.MeshIdealEndpoint
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Sectional paths in ordinary mesh categories

A path containing none of the length-two hooks occurring in a mesh relation
cannot be cancelled by the two-sided mesh ideal.  Its own path coefficient
annihilates every basis composite of a mesh relation and hence descends to a
nonzero witness in the mesh quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.MeshCategory

open QuotientSubmoduleEquidistribution.CategoricalIdeal

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- A path contains a mesh hook when it factors through one of the
length-two paths occurring in a mesh relation. -/
def PathContainsMeshHook {x y : Q} (r : Quiver.Path x y) : Prop :=
  ∃ (s : {z : Q // z ∉ T.projective}) (a : T.MeshArrow s)
      (left : Quiver.Path x s.1) (right : Quiver.Path (T.tau s) y),
    r = left.comp ((T.meshPath s a).comp right)

/-- A mesh-sectional path is a path containing no mesh hook. -/
def PathIsMeshSectional {x y : Q} (r : Quiver.Path x y) : Prop :=
  ¬ T.PathContainsMeshHook r

/-- Mesh-sectionality is unchanged by equality transport of path endpoints. -/
theorem pathIsMeshSectional_cast {x y x' y' : Q}
    (r : Quiver.Path x y) (hx : x = x') (hy : y = y') :
    T.PathIsMeshSectional (r.cast hx hy) ↔ T.PathIsMeshSectional r := by
  subst x'
  subst y'
  rfl

/-- If appending one arrow destroys mesh-sectionality, the newly appended
arrow is the terminal polarized partner in the unique new mesh hook. -/
theorem terminalMeshHook_of_not_sectional_cons
    {x y z : Q} (p : Quiver.Path x y) (hp : T.PathIsMeshSectional p)
    (a : y ⟶ z) (hpa : ¬ T.PathIsMeshSectional (p.cons a)) :
    ∃ (s : {s : Q // s ∉ T.projective}) (b : T.MeshArrow s)
        (left : Quiver.Path x s.1) (hy : y = b.1) (hz : z = T.tau s),
      p.cast rfl hy = left.comp b.2.toPath ∧
        a.cast hy hz = (T.arrowEquiv s b.1) b.2 := by
  have hhook : T.PathContainsMeshHook (p.cons a) := not_not.mp hpa
  rcases hhook with ⟨s, b, left, right, hfac⟩
  cases right with
  | nil =>
      simp only [Quiver.Path.comp_nil, RightMeshData.meshPath] at hfac
      let hy : y = b.1 := Quiver.Path.obj_eq_of_cons_eq_cons hfac
      refine ⟨s, b, left, hy, rfl, ?_, ?_⟩
      · exact Quiver.cast_eq_of_cons_eq_cons hfac
      · exact Quiver.hom_cast_eq_of_cons_eq_cons hfac
  | cons right c =>
      rename_i w
      simp only [RightMeshData.meshPath, Quiver.Path.comp_assoc,
        Quiver.Path.comp_cons] at hfac
      let hy : y = w := Quiver.Path.obj_eq_of_cons_eq_cons hfac
      have hpref := Quiver.cast_eq_of_cons_eq_cons hfac
      cases hy
      exfalso
      apply hp
      exact ⟨s, b, left, right, by
        simpa only [Quiver.Path.cast_rfl_rfl, RightMeshData.meshPath,
          Quiver.Path.comp_assoc] using hpref⟩

/-- If a sectional path already ends in `c`, then the only arrow whose
addition creates a mesh hook is the polarized partner of `c`. -/
theorem paired_eq_of_sectional_cons_not_sectional
    {x z w : Q} (s : {s : Q // s ∉ T.projective})
    (p : Quiver.Path x s.1) (c : s.1 ⟶ z)
    (hp : T.PathIsMeshSectional (p.cons c))
    (a : z ⟶ w) (hpa : ¬ T.PathIsMeshSectional ((p.cons c).cons a)) :
    ∃ hw : w = T.tau s,
      a.cast rfl hw = (T.arrowEquiv s z) c := by
  rcases T.terminalMeshHook_of_not_sectional_cons (p.cons c) hp a hpa with
    ⟨s', b, left, hy, hw, hpath, ha⟩
  rw [Quiver.Path.cast_cons] at hpath
  simp only [Quiver.Hom.toPath, Quiver.Path.comp_cons,
    Quiver.Path.comp_nil] at hpath
  let hsval : s.1 = s'.1 := Quiver.Path.obj_eq_of_cons_eq_cons hpath
  have hs : s = s' := Subtype.ext hsval
  cases hs
  cases hy
  have hc : c = b.2 := by
    simpa only [Quiver.Hom.cast_rfl_rfl] using
      Quiver.hom_cast_eq_of_cons_eq_cons hpath
  rw [← hc] at ha
  exact ⟨hw, by simpa only [Quiver.Hom.cast_rfl_rfl] using ha⟩

/-- Appending the polarized partner of the final arrow creates the displayed
terminal mesh hook. -/
theorem cons_paired_not_sectional
    {x z : Q} (s : {s : Q // s ∉ T.projective})
    (p : Quiver.Path x s.1) (c : s.1 ⟶ z) :
    ¬ T.PathIsMeshSectional
      ((p.cons c).cons ((T.arrowEquiv s z) c)) := by
  intro hsectional
  apply hsectional
  refine ⟨s, ⟨z, c⟩, p, Quiver.Path.nil, ?_⟩
  simp [RightMeshData.meshPath]

@[simp]
theorem meshPath_vertices
    (s : {z : Q // z ∉ T.projective}) (a : T.MeshArrow s) :
    (T.meshPath s a).vertices = [s.1, a.1, T.tau s] := by
  simp [meshPath]

/-- A vertex labelling which identifies the two ends of every mesh detects
sectional paths: a path whose label sequence has no repetition contains no
mesh hook. -/
theorem pathIsMeshSectional_of_map_vertices_nodup
    {C : Type z} (color : Q → C)
    (hcolor : ∀ s : {z : Q // z ∉ T.projective},
      color (T.tau s) = color s.1)
    {x y : Q} (r : Quiver.Path x y)
    (hr : (r.vertices.map color).Nodup) :
    T.PathIsMeshSectional r := by
  intro hhook
  rcases hhook with ⟨s, a, left, right, hfac⟩
  subst r
  simp only [Quiver.Path.vertices_comp, List.map_append] at hr
  have hparts := List.nodup_append.mp hr
  have htail := List.nodup_append.mp hparts.2.1
  have hsleft : color s.1 ∈
      (T.meshPath s a).vertices.dropLast.map color := by
    simp
  have hsright : color s.1 ∈ right.vertices.map color := by
    rw [← hcolor s]
    exact List.mem_map.mpr ⟨T.tau s, right.start_mem_vertices, rfl⟩
  exact (htail.2.2 (color s.1) hsleft (color s.1) hsright) rfl

/-- Coefficient of a chosen path in a morphism of the free linear path
category. -/
def pathCoefficient
    {X Y : MagnitudeConjecture.LinearPathCategory.Category k Q}
    (r : Quiver.Path
      (MagnitudeConjecture.LinearPathCategory.vertex Y)
      (MagnitudeConjecture.LinearPathCategory.vertex X)) :
    (X ⟶ Y) →ₗ[k] k :=
  (Finsupp.lapply r).comp
    (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
      X Y).toLinearMap

@[simp]
theorem pathCoefficient_pathHom_self
    {X Y : MagnitudeConjecture.LinearPathCategory.Category k Q}
    (r : Quiver.Path
      (MagnitudeConjecture.LinearPathCategory.vertex Y)
      (MagnitudeConjecture.LinearPathCategory.vertex X)) :
    pathCoefficient (k := k) r
      (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) r) = 1 := by
  rw [pathCoefficient, LinearMap.comp_apply, Finsupp.lapply_apply]
  calc
    _ = (Finsupp.single r 1 :
        Quiver.Path (MagnitudeConjecture.LinearPathCategory.vertex Y)
          (MagnitudeConjecture.LinearPathCategory.vertex X) →₀ k) r :=
      congrArg (fun f ↦ f r)
        (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv_pathHom
          (k := k) (x := X) (y := Y) r)
    _ = 1 := by simp

/-- Distinct paths have zero coefficient in one another's basis vector. -/
theorem pathCoefficient_pathHom_eq_zero_of_ne
    {X Y : MagnitudeConjecture.LinearPathCategory.Category k Q}
    (r q : Quiver.Path
      (MagnitudeConjecture.LinearPathCategory.vertex Y)
      (MagnitudeConjecture.LinearPathCategory.vertex X)) (h : r ≠ q) :
    pathCoefficient (k := k) r
      (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) q) = 0 := by
  classical
  rw [pathCoefficient, LinearMap.comp_apply, Finsupp.lapply_apply]
  calc
    _ = (Finsupp.single q 1 :
        Quiver.Path (MagnitudeConjecture.LinearPathCategory.vertex Y)
          (MagnitudeConjecture.LinearPathCategory.vertex X) →₀ k) r :=
      congrArg (fun f ↦ f r)
        (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv_pathHom
          (k := k) (x := X) (y := Y) q)
    _ = 0 := by simp [h]

variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

set_option backward.isDefEq.respectTransparency false in
private theorem pathCoefficient_basisComposite_eq_zero
    {x y : Q} (r : Quiver.Path x y) (hr : T.PathIsMeshSectional r)
    {f : MagnitudeConjecture.LinearPathCategory.obj k Q y ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q x}
    (hf : f ∈ MagnitudeConjecture.LinearPathCategory.basisCompositeSet
      (T.meshGeneratorSet (k := k))
      (MagnitudeConjecture.LinearPathCategory.obj k Q y)
      (MagnitudeConjecture.LinearPathCategory.obj k Q x)) :
    pathCoefficient (k := k) r f = 0 := by
  classical
  rcases hf with ⟨A, B, g, hg, p, q, rfl⟩
  rcases hg with ⟨s, hA, hB, rfl⟩
  subst A
  subst B
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [meshRelation]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [MagnitudeConjecture.LinearPathCategory.pathHom_comp_assoc,
    MagnitudeConjecture.LinearPathCategory.pathHom_comp]
  apply pathCoefficient_pathHom_eq_zero_of_ne
  intro h
  apply hr
  exact ⟨s, a, q, p, h⟩

/-- The mesh ideal is contained in the kernel of the coefficient functional
of any mesh-sectional path. -/
theorem meshIdealHom_le_ker_pathCoefficient
    {x y : Q} (r : Quiver.Path x y) (hr : T.PathIsMeshSectional r) :
    T.meshIdealHom (k := k) y x ≤
      LinearMap.ker (pathCoefficient (k := k) r) := by
  rw [meshIdealHom,
    MagnitudeConjecture.LinearPathCategory.generatedHomSubmodule_eq_span_basisCompositeSet]
  apply Submodule.span_le.2
  intro f hf
  change pathCoefficient (k := k) r f = 0
  exact T.pathCoefficient_basisComposite_eq_zero (k := k) r hr hf

/-- A mesh-sectional path survives as a nonzero morphism in the mesh
category. -/
theorem quotient_map_pathHom_ne_zero_of_isMeshSectional
    {x y : Q} (r : Quiver.Path x y) (hr : T.PathIsMeshSectional r) :
    (quotientFunctor (k := k) T).map
        (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) r) ≠ 0 := by
  intro hzero
  have hmem : MagnitudeConjecture.LinearPathCategory.pathHom (k := k) r ∈
      T.meshIdealHom (k := k) y x :=
    (T.quotient_map_eq_zero_iff_mem_meshIdealHom
      (k := k) y x _).1 hzero
  have hker := T.meshIdealHom_le_ker_pathCoefficient (k := k) r hr hmem
  change pathCoefficient (k := k) r
    (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) r) = 0 at hker
  have hone : pathCoefficient (k := k) r
      (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) r) = 1 := by
    exact pathCoefficient_pathHom_self r
  rw [hone] at hker
  exact one_ne_zero hker

end RightMeshData

end MagnitudeConjecture.MeshCategory
