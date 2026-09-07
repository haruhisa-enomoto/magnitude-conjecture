import MagnitudeConjecture.CategoryTheory.LinearCovering
import MagnitudeConjecture.CategoryTheory.LinearPathCovering
import MagnitudeConjecture.CategoryTheory.MeshRealization
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Coverings of polarized right translation quivers

This file connects Mathlib's star-and-costar notion of a quiver covering to
the polarized right-mesh data used by the magnitude formalization.  A mesh
cover preserves projective vertices, translation, and the polarization.  Its
star bijections transport local finiteness and identify every lifted mesh with
the corresponding mesh downstairs.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory

open CategoryTheory

universe u v₁ v₂ w₁ w₂

variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]

namespace RightMeshData

/-- A nonprojective vertex remains nonprojective under a map preserving and
reflecting projective vertices. -/
def mappedNonprojective
    (T₁ : RightMeshData Q₁) (T₂ : RightMeshData Q₂)
    (π : Q₁ ⥤q Q₂)
    (hprojective : ∀ x, x ∈ T₁.projective ↔ π.obj x ∈ T₂.projective)
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    {x : Q₂ // x ∉ T₂.projective} :=
  ⟨π.obj x.1, fun hx ↦ x.2 ((hprojective x.1).2 hx)⟩

/-- A covering of polarized right translation quivers.  Besides Mathlib's
local star-and-costar bijections, it preserves the projective boundary,
translation, and the chosen pairing of the two sides of every mesh. -/
structure Cover (T₁ : RightMeshData Q₁) (T₂ : RightMeshData Q₂) where
  toPrefunctor : Q₁ ⥤q Q₂
  isCovering : toPrefunctor.IsCovering
  map_projective_iff :
    ∀ x, x ∈ T₁.projective ↔ toPrefunctor.obj x ∈ T₂.projective
  map_tau : ∀ x : {x : Q₁ // x ∉ T₁.projective},
    toPrefunctor.obj (T₁.tau x) =
      T₂.tau (mappedNonprojective T₁ T₂ toPrefunctor
        map_projective_iff x)
  map_arrowEquiv :
    ∀ (x : {x : Q₁ // x ∉ T₁.projective}) (y : Q₁) (a : x.1 ⟶ y),
      (toPrefunctor.map ((T₁.arrowEquiv x y) a)).cast rfl (map_tau x) =
        (T₂.arrowEquiv
          (mappedNonprojective T₁ T₂ toPrefunctor
            map_projective_iff x)
          (toPrefunctor.obj y)) (toPrefunctor.map a)

namespace Cover

variable {T₁ : RightMeshData Q₁} {T₂ : RightMeshData Q₂}
variable {k : Type u} [Field k]

/-- The image of a nonprojective source vertex as a nonprojective target
vertex. -/
abbrev mapNonprojective (C : Cover T₁ T₂)
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    {x : Q₂ // x ∉ T₂.projective} :=
  mappedNonprojective T₁ T₂ C.toPrefunctor C.map_projective_iff x

/-- The map of incoming mesh-arrow stars induced by the underlying quiver
prefunctor. -/
def meshArrowMap (C : Cover T₁ T₂)
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    T₁.MeshArrow x → T₂.MeshArrow (C.mapNonprojective x) :=
  C.toPrefunctor.star x.1

/-- A quiver covering identifies each lifted incoming mesh-arrow star with
the corresponding star downstairs. -/
def meshArrowEquiv (C : Cover T₁ T₂)
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    T₁.MeshArrow x ≃ T₂.MeshArrow (C.mapNonprojective x) :=
  Equiv.ofBijective (C.meshArrowMap x)
    (C.isCovering.star_bijective x.1)

@[simp]
theorem meshArrowEquiv_apply (C : Cover T₁ T₂)
    (x : {x : Q₁ // x ∉ T₁.projective}) (a : T₁.MeshArrow x) :
    C.meshArrowEquiv x a = C.meshArrowMap x a :=
  rfl

/-- Local finiteness of arrow stars pulls back along a quiver covering. -/
@[reducible] def sourceStarFintype (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    ∀ x : Q₁, Fintype (Quiver.Star x) := fun x ↦
  Fintype.ofEquiv (Quiver.Star (C.toPrefunctor.obj x))
    (Equiv.ofBijective (C.toPrefunctor.star x)
      (C.isCovering.star_bijective x)).symm

/-- Mapping a lifted mesh path gives the corresponding mesh path downstairs,
after transporting its translated endpoint along translation compatibility. -/
theorem mapPath_meshPath (C : Cover T₁ T₂)
    (x : {x : Q₁ // x ∉ T₁.projective}) (a : T₁.MeshArrow x) :
    (C.toPrefunctor.mapPath (T₁.meshPath x a)).cast rfl (C.map_tau x) =
      T₂.meshPath (C.mapNonprojective x) (C.meshArrowMap x a) := by
  rw [RightMeshData.meshPath, RightMeshData.meshPath,
    Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath,
    Prefunctor.mapPath_toPath]
  change
    (((C.toPrefunctor.map a.2).toPath.comp
      (C.toPrefunctor.map ((T₁.arrowEquiv x a.1) a.2)).toPath).cast
        rfl (C.map_tau x)) =
      (C.toPrefunctor.map a.2).toPath.comp
        ((T₂.arrowEquiv (C.mapNonprojective x)
          (C.toPrefunctor.obj a.1)) (C.toPrefunctor.map a.2)).toPath
  rw [show
      (C.toPrefunctor.map a.2).toPath.comp
          (C.toPrefunctor.map ((T₁.arrowEquiv x a.1) a.2)).toPath =
        (C.toPrefunctor.map a.2).toPath.cons
          (C.toPrefunctor.map ((T₁.arrowEquiv x a.1) a.2)) from rfl,
    Quiver.Path.cast_cons, C.map_arrowEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The free path-category functor sends a lifted mesh relation exactly to
the corresponding target mesh relation, with the required transport along
translation compatibility. -/
theorem prefunctorFunctor_map_meshRelation (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    letI := C.sourceStarFintype
    (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
      (k := k) C.toPrefunctor).map (T₁.meshRelation (k := k) x) =
      eqToHom (congrArg
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂) (C.map_tau x)) ≫
        T₂.meshRelation (k := k) (C.mapNonprojective x) := by
  letI := C.sourceStarFintype
  rw [RightMeshData.meshRelation, Functor.map_sum]
  simp_rw [MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom]
  have hpath : ∀ a : T₁.MeshArrow x,
      MagnitudeConjecture.LinearPathCategory.pathHom
          (C.toPrefunctor.mapPath (T₁.meshPath x a)) =
        eqToHom (congrArg
          (MagnitudeConjecture.LinearPathCategory.obj k Q₂) (C.map_tau x)) ≫
          MagnitudeConjecture.LinearPathCategory.pathHom
            (T₂.meshPath (C.mapNonprojective x) (C.meshArrowMap x a)) := by
    intro a
    rw [MagnitudeConjecture.LinearPathCategory.pathHom_eq_eqToHom_comp_cast_end
      (k := k) (Q₂ := Q₂)
      (C.toPrefunctor.mapPath (T₁.meshPath x a)) (C.map_tau x)]
    rw [C.mapPath_meshPath]
  simp_rw [hpath]
  rw [← Preadditive.comp_sum]
  have hreindex := (C.meshArrowEquiv x).sum_comp
    (fun b : T₂.MeshArrow (C.mapNonprojective x) ↦
      MagnitudeConjecture.LinearPathCategory.pathHom (k := k)
        (T₂.meshPath (C.mapNonprojective x) b))
  simp only [C.meshArrowEquiv_apply] at hreindex
  rw [hreindex]
  rw [RightMeshData.meshRelation]

/-- The represented target-mesh morphism attached to one source-quiver
arrow. -/
def mappedArrowHom (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    {i j : Q₁} (a : i ⟶ j) :
    obj (k := k) T₂ (C.toPrefunctor.obj j) ⟶
      obj (k := k) T₂ (C.toPrefunctor.obj i) :=
  (quotientFunctor (k := k) T₂).map
    (MagnitudeConjecture.LinearPathCategory.pathHom
      (C.toPrefunctor.map a).toPath)

set_option backward.isDefEq.respectTransparency false in
/-- Reversed path evaluation for the mapped-arrow realization is the target
mesh quotient applied to the mapped quiver path. -/
theorem pathMap_mappedArrowHom (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    {i j : Q₁} (p : Quiver.Path i j) :
    MagnitudeConjecture.LinearPathCategory.pathMap
        (fun x ↦ obj (k := k) T₂ (C.toPrefunctor.obj x))
        (fun {_ _} a ↦ C.mappedArrowHom (k := k) a) p =
      (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom
          (C.toPrefunctor.mapPath p)) := by
  induction p with
  | nil =>
      rw [MagnitudeConjecture.LinearPathCategory.pathMap_nil,
        Prefunctor.mapPath_nil,
        MagnitudeConjecture.LinearPathCategory.pathHom_nil,
        (quotientFunctor (k := k) T₂).map_id]
      change 𝟙 (obj (k := k) T₂ (C.toPrefunctor.obj i)) =
        𝟙 (obj (k := k) T₂ (C.toPrefunctor.obj i))
      rfl
  | cons p a ih =>
      rw [MagnitudeConjecture.LinearPathCategory.pathMap_cons,
        ih, mappedArrowHom, Prefunctor.mapPath_cons]
      erw [← (quotientFunctor (k := k) T₂).map_comp,
        MagnitudeConjecture.LinearPathCategory.pathHom_comp]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Changing the target vertex of a quiver path becomes precomposition by
the corresponding equality morphism in the raw mesh category. -/
theorem map_pathHom_eq_eqToHom_comp_cast
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    {i j j' : Q₂} (p : Quiver.Path i j) (h : j = j') :
    (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom p) =
      eqToHom (congrArg (obj (k := k) T₂) h) ≫
        (quotientFunctor (k := k) T₂).map
          (MagnitudeConjecture.LinearPathCategory.pathHom
            (p.cast rfl h)) := by
  subst j'
  simp

set_option backward.isDefEq.respectTransparency false in
/-- One mapped lifted mesh path is the corresponding target mesh path,
including the categorical transport along translation compatibility. -/
theorem map_pathHom_meshPath (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : {x : Q₁ // x ∉ T₁.projective}) (a : T₁.MeshArrow x) :
    (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom
          (C.toPrefunctor.mapPath (T₁.meshPath x a))) =
      eqToHom (congrArg (obj (k := k) T₂) (C.map_tau x)) ≫
        (quotientFunctor (k := k) T₂).map
          (MagnitudeConjecture.LinearPathCategory.pathHom
            (T₂.meshPath (C.mapNonprojective x)
              (C.meshArrowMap x a))) := by
  calc
    _ = eqToHom (congrArg (obj (k := k) T₂) (C.map_tau x)) ≫
        (quotientFunctor (k := k) T₂).map
          (MagnitudeConjecture.LinearPathCategory.pathHom
            ((C.toPrefunctor.mapPath (T₁.meshPath x a)).cast
              rfl (C.map_tau x))) :=
      map_pathHom_eq_eqToHom_comp_cast
        (k := k) (T₂ := T₂) _ _
    _ = _ := by rw [C.mapPath_meshPath]

set_option backward.isDefEq.respectTransparency false in
/-- The mapped-arrow free realization sends every lifted mesh relation to
zero in the target mesh category. -/
theorem lift_map_meshRelation (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    letI := C.sourceStarFintype
    (MagnitudeConjecture.LinearPathCategory.lift
      (k := k)
      (fun y ↦ obj (k := k) T₂ (C.toPrefunctor.obj y))
      (fun {_ _} a ↦ C.mappedArrowHom (k := k) a)).map
        (T₁.meshRelation (k := k) x) = 0 := by
  letI := C.sourceStarFintype
  rw [RightMeshData.meshRelation, Functor.map_sum]
  simp_rw [MagnitudeConjecture.LinearPathCategory.lift_map_pathHom,
    C.pathMap_mappedArrowHom, C.map_pathHom_meshPath]
  rw [← Preadditive.comp_sum]
  have hreindex := (C.meshArrowEquiv x).sum_comp
    (fun b : T₂.MeshArrow (C.mapNonprojective x) ↦
      (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom
          (T₂.meshPath (C.mapNonprojective x) b)))
  simp only [C.meshArrowEquiv_apply] at hreindex
  rw [hreindex]
  rw [← Functor.map_sum]
  change eqToHom (congrArg (obj (k := k) T₂) (C.map_tau x)) ≫
      (quotientFunctor (k := k) T₂).map
        (T₂.meshRelation (k := k) (C.mapNonprojective x)) = 0
  rw [quotient_map_meshRelation_eq_zero (k := k) T₂]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The mapped-arrow free realization kills every source mesh relation when
the source arrow-star finiteness structure has already been fixed by the
ambient construction. -/
theorem lift_map_meshRelationUsingSourceFintype (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : {x : Q₁ // x ∉ T₁.projective}) :
    (MagnitudeConjecture.LinearPathCategory.lift
      (k := k)
      (fun y ↦ obj (k := k) T₂ (C.toPrefunctor.obj y))
      (fun {_ _} a ↦ C.mappedArrowHom (k := k) a)).map
        (T₁.meshRelation (k := k) x) = 0 := by
  rw [RightMeshData.meshRelation, Functor.map_sum]
  simp_rw [MagnitudeConjecture.LinearPathCategory.lift_map_pathHom,
    C.pathMap_mappedArrowHom, C.map_pathHom_meshPath]
  rw [← Preadditive.comp_sum]
  have hreindex := (C.meshArrowEquiv x).sum_comp
    (fun b : T₂.MeshArrow (C.mapNonprojective x) ↦
      (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom
          (T₂.meshPath (C.mapNonprojective x) b)))
  simp only [C.meshArrowEquiv_apply] at hreindex
  rw [hreindex]
  rw [← Functor.map_sum]
  change eqToHom (congrArg (obj (k := k) T₂) (C.map_tau x)) ≫
      (quotientFunctor (k := k) T₂).map
        (T₂.meshRelation (k := k) (C.mapNonprojective x)) = 0
  rw [quotient_map_meshRelation_eq_zero (k := k) T₂]
  simp

/-- The mesh realization induced by a polarized quiver covering, using an
ambiently chosen source arrow-star finiteness structure.  This is essential
for endocovers, where reconstructing the source instance would otherwise
change the Lean type of the source mesh category. -/
def realizationUsingSourceFintype (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    Realization (k := k) T₁
      (fun y ↦ obj (k := k) T₂ (C.toPrefunctor.obj y)) :=
  { arrowMap := fun {_ _} a ↦ C.mappedArrowHom (k := k) a
    map_meshRelation := C.lift_map_meshRelationUsingSourceFintype (k := k) }

/-- The linear mesh functor induced by a polarized quiver covering, with the
source finiteness structure supplied by the ambient category. -/
def functorUsingSourceFintype (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    RawCategory (k := k) T₁ ⥤ RawCategory (k := k) T₂ :=
  (C.realizationUsingSourceFintype (k := k)).functor

noncomputable instance functorUsingSourceFintype_additive (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    (C.functorUsingSourceFintype (k := k)).Additive := by
  dsimp only [functorUsingSourceFintype]
  infer_instance

noncomputable instance functorUsingSourceFintype_linear (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    (C.functorUsingSourceFintype (k := k)).Linear k := by
  dsimp only [functorUsingSourceFintype]
  infer_instance

@[simp]
theorem functorUsingSourceFintype_obj_obj (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)] (x : Q₁) :
    (C.functorUsingSourceFintype (k := k)).obj (obj (k := k) T₁ x) =
      obj (k := k) T₂ (C.toPrefunctor.obj x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ambient-source mesh functor sends a represented path to its
represented image path. -/
theorem functorUsingSourceFintype_map_quotient_pathHom
    (C : Cover T₁ T₂)
    [∀ y : Q₁, Fintype (Quiver.Star y)]
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    {i j : Q₁} (p : Quiver.Path i j) :
    (C.functorUsingSourceFintype (k := k)).map
        ((quotientFunctor (k := k) T₁).map
          (MagnitudeConjecture.LinearPathCategory.pathHom p)) =
      (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom
          (C.toPrefunctor.mapPath p)) := by
  change (C.realizationUsingSourceFintype (k := k)).functor.map
      ((quotientFunctor (k := k) T₁).map
        (MagnitudeConjecture.LinearPathCategory.pathHom p)) = _
  rw [Realization.functor_map_quotient_map,
    MagnitudeConjecture.LinearPathCategory.lift_map_pathHom]
  change MagnitudeConjecture.LinearPathCategory.pathMap
      (fun x ↦ obj (k := k) T₂ (C.toPrefunctor.obj x))
      (fun {_ _} a ↦ C.mappedArrowHom (k := k) a) p = _
  exact C.pathMap_mappedArrowHom (k := k) p

/-- The mesh realization of a lifted translation quiver in the target mesh
category induced by a polarized quiver covering. -/
def realization (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    letI := C.sourceStarFintype
    Realization (k := k) T₁
      (fun y ↦ obj (k := k) T₂ (C.toPrefunctor.obj y)) := by
  letI := C.sourceStarFintype
  exact
    { arrowMap := fun {_ _} a ↦ C.mappedArrowHom (k := k) a
      map_meshRelation := C.lift_map_meshRelation (k := k) }

/-- The linear functor between raw mesh categories induced by a polarized
translation-quiver covering. -/
def functor (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    letI := C.sourceStarFintype
    RawCategory (k := k) T₁ ⥤ RawCategory (k := k) T₂ := by
  letI := C.sourceStarFintype
  exact (C.realization (k := k)).functor

noncomputable instance functor_additive (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    letI := C.sourceStarFintype
    C.functor (k := k) |>.Additive := by
  letI := C.sourceStarFintype
  dsimp only [functor]
  infer_instance

noncomputable instance functor_linear (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] :
    letI := C.sourceStarFintype
    C.functor (k := k) |>.Linear k := by
  letI := C.sourceStarFintype
  dsimp only [functor]
  infer_instance

@[simp]
theorem functor_obj_obj (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] (x : Q₁) :
    letI := C.sourceStarFintype
    (C.functor (k := k)).obj (obj (k := k) T₁ x) =
      obj (k := k) T₂ (C.toPrefunctor.obj x) := by
  letI := C.sourceStarFintype
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The induced mesh functor sends every represented lifted path to its
represented image path downstairs. -/
theorem functor_map_quotient_pathHom (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    {i j : Q₁} (p : Quiver.Path i j) :
    letI := C.sourceStarFintype
    (C.functor (k := k)).map
        ((quotientFunctor (k := k) T₁).map
          (MagnitudeConjecture.LinearPathCategory.pathHom p)) =
      (quotientFunctor (k := k) T₂).map
        (MagnitudeConjecture.LinearPathCategory.pathHom
          (C.toPrefunctor.mapPath p)) := by
  letI := C.sourceStarFintype
  change (C.realization (k := k)).functor.map
      ((quotientFunctor (k := k) T₁).map
        (MagnitudeConjecture.LinearPathCategory.pathHom p)) = _
  rw [Realization.functor_map_quotient_map,
    MagnitudeConjecture.LinearPathCategory.lift_map_pathHom]
  change MagnitudeConjecture.LinearPathCategory.pathMap
      (fun x ↦ obj (k := k) T₂ (C.toPrefunctor.obj x))
      (fun {_ _} a ↦ C.mappedArrowHom (k := k) a) p = _
  exact C.pathMap_mappedArrowHom (k := k) p

set_option backward.isDefEq.respectTransparency false in
/-- The induced mesh functor is the quotient of the free path-category
functor induced by the underlying quiver prefunctor. -/
theorem functor_map_quotient_map (C : Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    {X Y : MagnitudeConjecture.LinearPathCategory.Category k Q₁}
    (f : X ⟶ Y) :
    letI := C.sourceStarFintype
    (C.functor (k := k)).map ((quotientFunctor (k := k) T₁).map f) =
      (quotientFunctor (k := k) T₂).map
        ((MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) C.toPrefunctor).map f) := by
  letI := C.sourceStarFintype
  let lhs :
      (X ⟶ Y) →ₗ[k]
        (obj (k := k) T₂ (C.toPrefunctor.obj
            (MagnitudeConjecture.LinearPathCategory.vertex X)) ⟶
          obj (k := k) T₂ (C.toPrefunctor.obj
            (MagnitudeConjecture.LinearPathCategory.vertex Y))) :=
    (C.functor (k := k)).mapLinearMap k ∘ₗ
      (quotientFunctor (k := k) T₁).mapLinearMap k
  let rhs :
      (X ⟶ Y) →ₗ[k]
        (obj (k := k) T₂ (C.toPrefunctor.obj
            (MagnitudeConjecture.LinearPathCategory.vertex X)) ⟶
          obj (k := k) T₂ (C.toPrefunctor.obj
            (MagnitudeConjecture.LinearPathCategory.vertex Y))) :=
    (quotientFunctor (k := k) T₂).mapLinearMap k ∘ₗ
      (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
        (k := k) C.toPrefunctor).mapLinearMap k
  change lhs f = rhs f
  have hmaps : lhs = rhs := by
    apply (MagnitudeConjecture.LinearPathCategory.homPathBasis
      X Y).ext
    intro p
    change (C.functor (k := k)).map
        ((quotientFunctor (k := k) T₁).map
          (MagnitudeConjecture.LinearPathCategory.pathHom p)) =
      (quotientFunctor (k := k) T₂).map
        ((MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) C.toPrefunctor).map
            (MagnitudeConjecture.LinearPathCategory.pathHom p))
    rw [C.functor_map_quotient_pathHom (k := k),
      MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom]
  rw [hmaps]

end Cover

end RightMeshData

end MagnitudeConjecture.MeshCategory
