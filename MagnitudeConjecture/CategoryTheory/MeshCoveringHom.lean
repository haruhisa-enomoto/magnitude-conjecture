import MagnitudeConjecture.CategoryTheory.MeshCovering
import MagnitudeConjecture.CategoryTheory.MeshIdealEndpoint

/-!
# Hom-space quotient squares for mesh coverings

This file compares the free path-category covering equivalences with the two
direct-sum Hom maps of the induced mesh-category functor.  The comparison is
set up using the literal fibres of the mesh functor, so that the eventual
covering theorem has exactly the Bongartz--Gabriel type.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory

universe u v₁ v₂ w₁ w₂

variable {Q₁ : Type v₁} [Quiver.{w₁} Q₁]
variable {Q₂ : Type v₂} [Quiver.{w₂} Q₂]

namespace RightMeshData.Cover

variable {T₁ : RightMeshData Q₁} {T₂ : RightMeshData Q₂}
variable {k : Type u} [Field k]

/-- A fibre object of the mesh functor is the same thing as a source vertex
lying over the chosen target vertex. -/
def meshFunctorFiberVertexEquiv (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] (y : Q₂) :
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y) ≃
      {z : Q₁ // C.toPrefunctor.obj z = y} := by
  letI := C.sourceStarFintype
  exact
    { toFun := fun Z ↦
        ⟨MagnitudeConjecture.LinearPathCategory.vertex Z.1.as, by
          have h := congrArg
            (fun W : RawCategory (k := k) T₂ ↦
              MagnitudeConjecture.LinearPathCategory.vertex W.as) Z.2
          change C.toPrefunctor.obj
              (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) = y at h
          exact h⟩
      invFun := fun z ↦
        ⟨obj (k := k) T₁ z.1,
          congrArg (obj (k := k) T₂) z.2⟩
      left_inv := by
        rintro ⟨Z, hZ⟩
        rfl
      right_inv := by
        rintro ⟨z, hz⟩
        rfl }

/-- Fixed-terminal path indices written using fibres of the mesh functor. -/
def targetMeshFunctorPathEquiv (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y),
      Quiver.Path (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) x) ≃
      Quiver.Path y (C.toPrefunctor.obj x) := by
  letI := C.sourceStarFintype
  exact
    (Equiv.sigmaCongr (C.meshFunctorFiberVertexEquiv (k := k) y)
      (fun _ ↦ Equiv.refl _)).trans
        (MagnitudeConjecture.LinearPathCategory.targetPathEquiv
          C.toPrefunctor C.isCovering x y)

/-- Fixed-initial path indices written using fibres of the mesh functor. -/
def sourceMeshFunctorPathEquiv (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x),
      Quiver.Path y (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as)) ≃
      Quiver.Path (C.toPrefunctor.obj y) x := by
  letI := C.sourceStarFintype
  exact
    (Equiv.sigmaCongr (C.meshFunctorFiberVertexEquiv (k := k) x)
      (fun _ ↦ Equiv.refl _)).trans
        (MagnitudeConjecture.LinearPathCategory.sourcePathEquiv
          C.toPrefunctor C.isCovering x y)

/-- The free path basis on the fixed-source direct sum indexed by fibres of
the mesh functor. -/
def targetFreeFiberHomBasis (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    Module.Basis
      (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y),
        Quiver.Path (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) x)
      k
      (DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as)) := by
  letI := C.sourceStarFintype
  exact DFinsupp.basis fun Z ↦
    MagnitudeConjecture.LinearPathCategory.homPathBasis
      (MagnitudeConjecture.LinearPathCategory.obj k Q₁ x) Z.1.as

/-- The free path basis on the fixed-target direct sum indexed by fibres of
the mesh functor. -/
def sourceFreeFiberHomBasis (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    Module.Basis
      (Σ Z : MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x),
        Quiver.Path y (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as))
      k
      (DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)) := by
  letI := C.sourceStarFintype
  exact DFinsupp.basis fun Z ↦
    MagnitudeConjecture.LinearPathCategory.homPathBasis Z.1.as
      (MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)

/-- Include one free fixed-source Hom space in the direct sum indexed by the
mesh-functor fibre. -/
def targetFreeFiberLof (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y)) :
    letI := C.sourceStarFintype
    (MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as) →ₗ[k]
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun W ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          W.1.as) := by
  letI := C.sourceStarFintype
  classical
  exact DirectSum.lof k
    (MagnitudeConjecture.LinearCovering.Fiber
      (C.functor (k := k)) (obj (k := k) T₂ y))
    (fun W ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ W.1.as) Z

/-- Include one free fixed-target Hom space in the direct sum indexed by the
mesh-functor fibre. -/
def sourceFreeFiberLof (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x)) :
    letI := C.sourceStarFintype
    (Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) →ₗ[k]
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun W ↦ W.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) := by
  letI := C.sourceStarFintype
  classical
  exact DirectSum.lof k
    (MagnitudeConjecture.LinearCovering.Fiber
      (C.functor (k := k)) (obj (k := k) T₂ x))
    (fun W ↦ W.1.as ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) Z

theorem targetFreeFiberHomBasis_apply
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y))
    (p : Quiver.Path
      (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) x) :
    letI := C.sourceStarFintype
    C.targetFreeFiberHomBasis (k := k) x y ⟨Z, p⟩ =
      C.targetFreeFiberLof (k := k) x y Z
        (MagnitudeConjecture.LinearPathCategory.pathHom p) := by
  letI := C.sourceStarFintype
  classical
  unfold targetFreeFiberHomBasis
  rw [← MagnitudeConjecture.LinearPathCategory.homPathBasis_apply
    (k := k) (Q := Q₁)
    (MagnitudeConjecture.LinearPathCategory.obj k Q₁ x) Z.1.as p]
  unfold targetFreeFiberLof
  exact MagnitudeConjecture.LinearPathCategory.dfinsuppBasis_apply (k := k)
    (ι := MagnitudeConjecture.LinearCovering.Fiber
      (C.functor (k := k)) (obj (k := k) T₂ y))
    (M := fun W ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
      W.1.as)
    (η := fun W ↦ Quiver.Path
      (MagnitudeConjecture.LinearPathCategory.vertex W.1.as) x)
    (fun W ↦ MagnitudeConjecture.LinearPathCategory.homPathBasis
      (MagnitudeConjecture.LinearPathCategory.obj k Q₁ x) W.1.as) Z p

theorem sourceFreeFiberHomBasis_apply
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x))
    (p : Quiver.Path y
      (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as)) :
    letI := C.sourceStarFintype
    C.sourceFreeFiberHomBasis (k := k) x y ⟨Z, p⟩ =
      C.sourceFreeFiberLof (k := k) x y Z
        (MagnitudeConjecture.LinearPathCategory.pathHom p) := by
  letI := C.sourceStarFintype
  classical
  unfold sourceFreeFiberHomBasis
  rw [← MagnitudeConjecture.LinearPathCategory.homPathBasis_apply
    (k := k) (Q := Q₁) Z.1.as
    (MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) p]
  unfold sourceFreeFiberLof
  exact MagnitudeConjecture.LinearPathCategory.dfinsuppBasis_apply (k := k)
    (ι := MagnitudeConjecture.LinearCovering.Fiber
      (C.functor (k := k)) (obj (k := k) T₂ x))
    (M := fun W ↦ W.1.as ⟶
      MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)
    (η := fun W ↦ Quiver.Path y
      (MagnitudeConjecture.LinearPathCategory.vertex W.1.as))
    (fun W ↦ MagnitudeConjecture.LinearPathCategory.homPathBasis W.1.as
      (MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)) Z p

set_option backward.isDefEq.respectTransparency false in
/-- The free fixed-source direct-sum map, indexed by fibres of the mesh
functor but evaluated before imposing mesh relations. -/
def targetFreeFiberHomMap (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as) →ₗ[k]
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂
          (C.toPrefunctor.obj x) ⟶
        MagnitudeConjecture.LinearPathCategory.obj k Q₂ y) := by
  letI := C.sourceStarFintype
  classical
  exact DirectSum.toModule k _ _ fun Z ↦
    { toFun := fun f ↦
        (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) C.toPrefunctor).map f ≫
          eqToHom (congrArg
            (MagnitudeConjecture.LinearPathCategory.obj k Q₂)
            (C.meshFunctorFiberVertexEquiv (k := k) y Z).2)
      map_add' := by
        intro f g
        rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := by
        intro r f
        rw [Functor.map_smul, CategoryTheory.Linear.smul_comp]
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- The free fixed-target direct-sum map, indexed by fibres of the mesh
functor but evaluated before imposing mesh relations. -/
def sourceFreeFiberHomMap (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) →ₗ[k]
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂ x ⟶
        MagnitudeConjecture.LinearPathCategory.obj k Q₂
          (C.toPrefunctor.obj y)) := by
  letI := C.sourceStarFintype
  classical
  exact DirectSum.toModule k _ _ fun Z ↦
    { toFun := fun f ↦
        eqToHom (congrArg
          (MagnitudeConjecture.LinearPathCategory.obj k Q₂)
          (C.meshFunctorFiberVertexEquiv (k := k) x Z).2).symm ≫
          (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
            (k := k) C.toPrefunctor).map f
      map_add' := by
        intro f g
        rw [Functor.map_add, Preadditive.comp_add]
      map_smul' := by
        intro r f
        rw [Functor.map_smul, CategoryTheory.Linear.comp_smul]
        simp }

@[simp]
theorem targetFreeFiberHomMap_lof
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y))
    (f : MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as) :
    letI := C.sourceStarFintype
    C.targetFreeFiberHomMap (k := k) x y
        (C.targetFreeFiberLof (k := k) x y Z f) =
      (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
        (k := k) C.toPrefunctor).map f ≫
        eqToHom (congrArg
          (MagnitudeConjecture.LinearPathCategory.obj k Q₂)
          (C.meshFunctorFiberVertexEquiv (k := k) y Z).2) := by
  letI := C.sourceStarFintype
  classical
  simp [targetFreeFiberHomMap, targetFreeFiberLof]
  rfl

@[simp]
theorem sourceFreeFiberHomMap_lof
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x))
    (f : Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) :
    letI := C.sourceStarFintype
    C.sourceFreeFiberHomMap (k := k) x y
        (C.sourceFreeFiberLof (k := k) x y Z f) =
      eqToHom (congrArg
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂)
        (C.meshFunctorFiberVertexEquiv (k := k) x Z).2).symm ≫
        (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
          (k := k) C.toPrefunctor).map f := by
  letI := C.sourceStarFintype
  classical
  simp [sourceFreeFiberHomMap, sourceFreeFiberLof]
  rfl

/-- The free fixed-source Hom equivalence, indexed by the literal mesh-functor
fibre. -/
def targetFreeFiberHomEquiv (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as) ≃ₗ[k]
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂
          (C.toPrefunctor.obj x) ⟶
        MagnitudeConjecture.LinearPathCategory.obj k Q₂ y) := by
  letI := C.sourceStarFintype
  exact (C.targetFreeFiberHomBasis (k := k) x y).equiv
    (MagnitudeConjecture.LinearPathCategory.homPathBasis
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj x))
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂ y))
    (C.targetMeshFunctorPathEquiv (k := k) x y)

/-- The free fixed-target Hom equivalence, indexed by the literal mesh-functor
fibre. -/
def sourceFreeFiberHomEquiv (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) ≃ₗ[k]
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂ x ⟶
        MagnitudeConjecture.LinearPathCategory.obj k Q₂
          (C.toPrefunctor.obj y)) := by
  letI := C.sourceStarFintype
  exact (C.sourceFreeFiberHomBasis (k := k) x y).equiv
    (MagnitudeConjecture.LinearPathCategory.homPathBasis
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂ x)
      (MagnitudeConjecture.LinearPathCategory.obj k Q₂
        (C.toPrefunctor.obj y)))
    (C.sourceMeshFunctorPathEquiv (k := k) x y)

set_option backward.isDefEq.respectTransparency false in
theorem targetFreeFiberHomEquiv_eq_map
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    (C.targetFreeFiberHomEquiv (k := k) x y).toLinearMap =
      C.targetFreeFiberHomMap (k := k) x y := by
  letI := C.sourceStarFintype
  apply (C.targetFreeFiberHomBasis (k := k) x y).ext
  rintro ⟨Z, p⟩
  change ((C.targetFreeFiberHomBasis (k := k) x y).equiv
      (MagnitudeConjecture.LinearPathCategory.homPathBasis
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂
          (C.toPrefunctor.obj x))
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂ y))
      (C.targetMeshFunctorPathEquiv (k := k) x y))
        (C.targetFreeFiberHomBasis (k := k) x y ⟨Z, p⟩) = _
  rw [Module.Basis.equiv_apply,
    C.targetFreeFiberHomBasis_apply (k := k),
    C.targetFreeFiberHomMap_lof (k := k),
    MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom,
    MagnitudeConjecture.LinearPathCategory.pathHom_comp_eqToHom_eq_cast_start
      (k := k) (Q₂ := Q₂)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sourceFreeFiberHomEquiv_eq_map
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    (C.sourceFreeFiberHomEquiv (k := k) x y).toLinearMap =
      C.sourceFreeFiberHomMap (k := k) x y := by
  letI := C.sourceStarFintype
  apply (C.sourceFreeFiberHomBasis (k := k) x y).ext
  rintro ⟨Z, p⟩
  change ((C.sourceFreeFiberHomBasis (k := k) x y).equiv
      (MagnitudeConjecture.LinearPathCategory.homPathBasis
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂ x)
        (MagnitudeConjecture.LinearPathCategory.obj k Q₂
          (C.toPrefunctor.obj y)))
      (C.sourceMeshFunctorPathEquiv (k := k) x y))
        (C.sourceFreeFiberHomBasis (k := k) x y ⟨Z, p⟩) = _
  rw [Module.Basis.equiv_apply,
    C.sourceFreeFiberHomBasis_apply (k := k),
    C.sourceFreeFiberHomMap_lof (k := k),
    MagnitudeConjecture.LinearPathCategory.prefunctorFunctor_map_pathHom,
    MagnitudeConjecture.LinearPathCategory.eqToHom_comp_pathHom_eq_cast_end
      (k := k) (Q₂ := Q₂)]
  rfl

/-- Every quotient-category object is canonically the quotient functor
applied to its stored source object. -/
theorem quotientObjectEq
    {Q : Type v₁} [Quiver.{w₁} Q] (T : RightMeshData Q)
    [∀ z : Q, Fintype (Quiver.Star z)] (Z : RawCategory (k := k) T) :
    (quotientFunctor (k := k) T).obj Z.as = Z := by
  rcases Z with ⟨Z⟩
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Quotient one free fixed-source Hom component, with the canonical object
transport to the literal fibre object. -/
def targetComponentQuotientMap (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y)) :
    letI := C.sourceStarFintype
    (MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as) →ₗ[k]
      (obj (k := k) T₁ x ⟶ Z.1) := by
  letI := C.sourceStarFintype
  exact
    { toFun := fun f ↦ (quotientFunctor (k := k) T₁).map f ≫
        eqToHom (quotientObjectEq (k := k) T₁ Z.1)
      map_add' := by
        intro f g
        rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := by
        intro r f
        rw [Functor.map_smul, CategoryTheory.Linear.smul_comp]
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- Quotient one free fixed-target Hom component, with the canonical object
transport from the literal fibre object. -/
def sourceComponentQuotientMap (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x)) :
    letI := C.sourceStarFintype
    (Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) →ₗ[k]
      (Z.1 ⟶ obj (k := k) T₁ y) := by
  letI := C.sourceStarFintype
  exact
    { toFun := fun f ↦
        eqToHom (quotientObjectEq (k := k) T₁ Z.1).symm ≫
          (quotientFunctor (k := k) T₁).map f
      map_add' := by
        intro f g
        rw [Functor.map_add, Preadditive.comp_add]
      map_smul' := by
        intro r f
        rw [Functor.map_smul, CategoryTheory.Linear.comp_smul]
        simp }

@[simp]
theorem targetComponentQuotientMap_apply
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y))
    (f : MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as) :
    letI := C.sourceStarFintype
    C.targetComponentQuotientMap (k := k) x y Z f =
      (quotientFunctor (k := k) T₁).map f ≫
        eqToHom (quotientObjectEq (k := k) T₁ Z.1) := by
  letI := C.sourceStarFintype
  rfl

@[simp]
theorem sourceComponentQuotientMap_apply
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x))
    (f : Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) :
    letI := C.sourceStarFintype
    C.sourceComponentQuotientMap (k := k) x y Z f =
      eqToHom (quotientObjectEq (k := k) T₁ Z.1).symm ≫
        (quotientFunctor (k := k) T₁).map f := by
  letI := C.sourceStarFintype
  rfl

theorem targetComponentQuotientMap_surjective
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y)) :
    letI := C.sourceStarFintype
    Function.Surjective (C.targetComponentQuotientMap (k := k) x y Z) := by
  letI := C.sourceStarFintype
  intro g
  obtain ⟨f, hf⟩ := (quotientFunctor (k := k) T₁).map_surjective
    (g ≫ eqToHom (quotientObjectEq (k := k) T₁ Z.1).symm)
  refine ⟨f, ?_⟩
  change (quotientFunctor (k := k) T₁).map f ≫
      eqToHom (quotientObjectEq (k := k) T₁ Z.1) = g
  rw [hf, Category.assoc]
  simp

theorem sourceComponentQuotientMap_surjective
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x)) :
    letI := C.sourceStarFintype
    Function.Surjective (C.sourceComponentQuotientMap (k := k) x y Z) := by
  letI := C.sourceStarFintype
  intro g
  obtain ⟨f, hf⟩ := (quotientFunctor (k := k) T₁).map_surjective
    (eqToHom (quotientObjectEq (k := k) T₁ Z.1) ≫ g)
  refine ⟨f, ?_⟩
  change eqToHom (quotientObjectEq (k := k) T₁ Z.1).symm ≫
      (quotientFunctor (k := k) T₁).map f = g
  rw [hf, ← Category.assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A source mesh-ideal element is killed by the fixed-target component
quotient map. -/
theorem sourceComponentQuotientMap_eq_zero_of_mem_meshIdealHom
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x))
    (f : Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) :
    letI := C.sourceStarFintype
    f ∈ T₁.meshIdealHom (k := k)
        (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) y →
      C.sourceComponentQuotientMap (k := k) x y Z f = 0 := by
  letI := C.sourceStarFintype
  intro hf
  rw [C.sourceComponentQuotientMap_apply (k := k)]
  rw [(T₁.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k)
    (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) y f).2 hf]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A source mesh-ideal element is killed by the fixed-source component
quotient map. -/
theorem targetComponentQuotientMap_eq_zero_of_mem_meshIdealHom
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y))
    (f : MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as) :
    letI := C.sourceStarFintype
    f ∈ T₁.meshIdealHom (k := k) x
        (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) →
      C.targetComponentQuotientMap (k := k) x y Z f = 0 := by
  letI := C.sourceStarFintype
  intro hf
  rw [C.targetComponentQuotientMap_apply (k := k)]
  rw [(T₁.quotient_map_eq_zero_iff_mem_meshIdealHom (k := k)
    x (MagnitudeConjecture.LinearPathCategory.vertex Z.1.as) f).2 hf]
  simp

/-- Quotient every component in the fixed-source free direct sum by the
source mesh ideal. -/
def targetFiberQuotientMap (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as) →ₗ[k]
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ obj (k := k) T₁ x ⟶ Z.1) := by
  letI := C.sourceStarFintype
  exact DirectSum.lmap fun Z ↦
    C.targetComponentQuotientMap (k := k) x y Z

/-- Quotient every component in the fixed-target free direct sum by the
source mesh ideal. -/
def sourceFiberQuotientMap (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) →ₗ[k]
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1 ⟶ obj (k := k) T₁ y) := by
  letI := C.sourceStarFintype
  exact DirectSum.lmap fun Z ↦
    C.sourceComponentQuotientMap (k := k) x y Z

@[simp]
theorem targetFiberQuotientMap_lof
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ y))
    (f : MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶ Z.1.as) :
    letI := C.sourceStarFintype
    C.targetFiberQuotientMap (k := k) x y
        (C.targetFreeFiberLof (k := k) x y Z f) =
      MagnitudeConjecture.LinearCovering.targetFiberLof
        (k := k) (C.functor (k := k))
        (obj (k := k) T₁ x) (obj (k := k) T₂ y) Z
        (C.targetComponentQuotientMap (k := k) x y Z f) := by
  letI := C.sourceStarFintype
  classical
  simp [targetFiberQuotientMap, targetFreeFiberLof,
    MagnitudeConjecture.LinearCovering.targetFiberLof]

@[simp]
theorem sourceFiberQuotientMap_lof
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁)
    (Z : letI := C.sourceStarFintype
      MagnitudeConjecture.LinearCovering.Fiber
        (C.functor (k := k)) (obj (k := k) T₂ x))
    (f : Z.1.as ⟶ MagnitudeConjecture.LinearPathCategory.obj k Q₁ y) :
    letI := C.sourceStarFintype
    C.sourceFiberQuotientMap (k := k) x y
        (C.sourceFreeFiberLof (k := k) x y Z f) =
      MagnitudeConjecture.LinearCovering.sourceFiberLof
        (k := k) (C.functor (k := k))
        (obj (k := k) T₂ x) (obj (k := k) T₁ y) Z
        (C.sourceComponentQuotientMap (k := k) x y Z f) := by
  letI := C.sourceStarFintype
  classical
  simp [sourceFiberQuotientMap, sourceFreeFiberLof,
    MagnitudeConjecture.LinearCovering.sourceFiberLof]

theorem targetFiberQuotientMap_surjective
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    Function.Surjective (C.targetFiberQuotientMap (k := k) x y) := by
  letI := C.sourceStarFintype
  change Function.Surjective (DFinsupp.mapRange
    (fun Z f ↦ C.targetComponentQuotientMap (k := k) x y Z f)
      (fun Z ↦ (C.targetComponentQuotientMap (k := k) x y Z).map_zero))
  rw [DFinsupp.mapRange_surjective]
  intro Z
  exact C.targetComponentQuotientMap_surjective (k := k) x y Z

theorem sourceFiberQuotientMap_surjective
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    Function.Surjective (C.sourceFiberQuotientMap (k := k) x y) := by
  letI := C.sourceStarFintype
  change Function.Surjective (DFinsupp.mapRange
    (fun Z f ↦ C.sourceComponentQuotientMap (k := k) x y Z f)
      (fun Z ↦ (C.sourceComponentQuotientMap (k := k) x y Z).map_zero))
  rw [DFinsupp.mapRange_surjective]
  intro Z
  exact C.sourceComponentQuotientMap_surjective (k := k) x y Z

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-source free covering equivalence and the mesh-functor Hom map
form a commutative square with the componentwise quotient maps. -/
theorem targetFiber_quotient_square
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₁) (y : Q₂) (a : letI := C.sourceStarFintype
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as)) :
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₁ x) (obj (k := k) T₂ y)
        (C.targetFiberQuotientMap (k := k) x y a) =
      (quotientFunctor (k := k) T₂).map
        (C.targetFreeFiberHomMap (k := k) x y a) := by
  letI := C.sourceStarFintype
  classical
  let lhs :=
    (MagnitudeConjecture.LinearCovering.targetFiberHomMap
      (k := k) (C.functor (k := k))
      (obj (k := k) T₁ x) (obj (k := k) T₂ y)).comp
        (C.targetFiberQuotientMap (k := k) x y)
  let rhs :=
    (quotientFunctor (k := k) T₂).mapLinearMap k |>.comp
      (C.targetFreeFiberHomMap (k := k) x y)
  change lhs a = rhs a
  have hmaps : lhs = rhs := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨Z⟩, hZ⟩
    ext f
    change lhs (C.targetFreeFiberLof (k := k) x y ⟨⟨Z⟩, hZ⟩ f) =
      rhs (C.targetFreeFiberLof (k := k) x y ⟨⟨Z⟩, hZ⟩ f)
    simp only [lhs, rhs, LinearMap.comp_apply]
    rw [C.targetFiberQuotientMap_lof (k := k),
      MagnitudeConjecture.LinearCovering.targetFiberHomMap_lof,
      C.targetFreeFiberHomMap_lof (k := k),
      C.targetComponentQuotientMap_apply (k := k)]
    change (C.functor (k := k)).map
          ((quotientFunctor (k := k) T₁).map f ≫
            eqToHom (quotientObjectEq (k := k) T₁ ⟨Z⟩)) ≫
          eqToHom hZ =
        (quotientFunctor (k := k) T₂).map
          ((MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
            (k := k) C.toPrefunctor).map f ≫
            eqToHom (congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k Q₂)
              (C.meshFunctorFiberVertexEquiv (k := k) y ⟨⟨Z⟩, hZ⟩).2))
    rw [Functor.map_comp,
      C.functor_map_quotient_map (k := k)]
    rw [Functor.map_comp]
    rw [eqToHom_map]
    rw [eqToHom_map]
    simp only [Category.assoc, eqToHom_trans]
  rw [hmaps]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-target free covering equivalence and the mesh-functor Hom map
form a commutative square with the componentwise quotient maps. -/
theorem sourceFiber_quotient_square
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (x : Q₂) (y : Q₁) (a : letI := C.sourceStarFintype
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)) :
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.sourceFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₂ x) (obj (k := k) T₁ y)
        (C.sourceFiberQuotientMap (k := k) x y a) =
      (quotientFunctor (k := k) T₂).map
        (C.sourceFreeFiberHomMap (k := k) x y a) := by
  letI := C.sourceStarFintype
  classical
  let lhs :=
    (MagnitudeConjecture.LinearCovering.sourceFiberHomMap
      (k := k) (C.functor (k := k))
      (obj (k := k) T₂ x) (obj (k := k) T₁ y)).comp
        (C.sourceFiberQuotientMap (k := k) x y)
  let rhs :=
    (quotientFunctor (k := k) T₂).mapLinearMap k |>.comp
      (C.sourceFreeFiberHomMap (k := k) x y)
  change lhs a = rhs a
  have hmaps : lhs = rhs := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨Z⟩, hZ⟩
    ext f
    change lhs (C.sourceFreeFiberLof (k := k) x y ⟨⟨Z⟩, hZ⟩ f) =
      rhs (C.sourceFreeFiberLof (k := k) x y ⟨⟨Z⟩, hZ⟩ f)
    simp only [lhs, rhs, LinearMap.comp_apply]
    rw [C.sourceFiberQuotientMap_lof (k := k),
      MagnitudeConjecture.LinearCovering.sourceFiberHomMap_lof,
      C.sourceFreeFiberHomMap_lof (k := k),
      C.sourceComponentQuotientMap_apply (k := k)]
    change eqToHom hZ.symm ≫ (C.functor (k := k)).map
          (eqToHom (quotientObjectEq (k := k) T₁ ⟨Z⟩).symm ≫
            (quotientFunctor (k := k) T₁).map f) =
        (quotientFunctor (k := k) T₂).map
          (eqToHom (congrArg
              (MagnitudeConjecture.LinearPathCategory.obj k Q₂)
              (C.meshFunctorFiberVertexEquiv (k := k) x ⟨⟨Z⟩, hZ⟩).2).symm ≫
            (MagnitudeConjecture.LinearPathCategory.prefunctorFunctor
              (k := k) C.toPrefunctor).map f)
    rw [Functor.map_comp,
      C.functor_map_quotient_map (k := k)]
    rw [Functor.map_comp]
    rw [eqToHom_map]
    rw [eqToHom_map]
    rfl
  rw [hmaps]
  rfl

/-- The exact remaining relation-lifting condition for a polarized mesh
covering.  It says that a free direct-sum element which lands in the target
mesh ideal is already componentwise zero after quotienting by the source mesh
ideal, in both Hom variables. -/
structure HasMeshIdealLifting (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)] : Prop where
  target : ∀ (x : Q₁) (y : Q₂) (a : letI := C.sourceStarFintype
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ y))
        (fun Z ↦ MagnitudeConjecture.LinearPathCategory.obj k Q₁ x ⟶
          Z.1.as)),
    letI := C.sourceStarFintype
    (quotientFunctor (k := k) T₂).map
        (C.targetFreeFiberHomMap (k := k) x y a) = 0 →
      C.targetFiberQuotientMap (k := k) x y a = 0
  source : ∀ (x : Q₂) (y : Q₁) (a : letI := C.sourceStarFintype
      DirectSum
        (MagnitudeConjecture.LinearCovering.Fiber
          (C.functor (k := k)) (obj (k := k) T₂ x))
        (fun Z ↦ Z.1.as ⟶
          MagnitudeConjecture.LinearPathCategory.obj k Q₁ y)),
    letI := C.sourceStarFintype
    (quotientFunctor (k := k) T₂).map
        (C.sourceFreeFiberHomMap (k := k) x y a) = 0 →
      C.sourceFiberQuotientMap (k := k) x y a = 0

/-- Mesh-ideal lifting gives the fixed-source covering bijection at literal
vertex objects. -/
theorem targetFiberHomMap_bijective_of_hasMeshIdealLifting
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (hC : C.HasMeshIdealLifting (k := k)) (x : Q₁) (y : Q₂) :
    letI := C.sourceStarFintype
    Function.Bijective
      (MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₁ x) (obj (k := k) T₂ y)) := by
  letI := C.sourceStarFintype
  apply MagnitudeConjecture.LinearCovering.bijective_of_surjective_quotient_square
      (C.targetFreeFiberHomEquiv (k := k) x y)
      (C.targetFiberQuotientMap (k := k) x y)
      ((quotientFunctor (k := k) T₂).mapLinearMap k)
      (MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₁ x) (obj (k := k) T₂ y))
      (C.targetFiberQuotientMap_surjective (k := k) x y)
      (quotientFunctor (k := k) T₂).map_surjective
  · intro a
    calc
      _ = (quotientFunctor (k := k) T₂).map
          (C.targetFreeFiberHomMap (k := k) x y a) :=
        C.targetFiber_quotient_square (k := k) x y a
      _ = _ := by
        rw [← C.targetFreeFiberHomEquiv_eq_map (k := k)]
        rfl
  · intro a ha
    apply hC.target x y a
    rw [← C.targetFreeFiberHomEquiv_eq_map (k := k)]
    exact ha

/-- Mesh-ideal lifting gives the fixed-target covering bijection at literal
vertex objects. -/
theorem sourceFiberHomMap_bijective_of_hasMeshIdealLifting
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (hC : C.HasMeshIdealLifting (k := k)) (x : Q₂) (y : Q₁) :
    letI := C.sourceStarFintype
    Function.Bijective
      (MagnitudeConjecture.LinearCovering.sourceFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₂ x) (obj (k := k) T₁ y)) := by
  letI := C.sourceStarFintype
  apply MagnitudeConjecture.LinearCovering.bijective_of_surjective_quotient_square
      (C.sourceFreeFiberHomEquiv (k := k) x y)
      (C.sourceFiberQuotientMap (k := k) x y)
      ((quotientFunctor (k := k) T₂).mapLinearMap k)
      (MagnitudeConjecture.LinearCovering.sourceFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₂ x) (obj (k := k) T₁ y))
      (C.sourceFiberQuotientMap_surjective (k := k) x y)
      (quotientFunctor (k := k) T₂).map_surjective
  · intro a
    calc
      _ = (quotientFunctor (k := k) T₂).map
          (C.sourceFreeFiberHomMap (k := k) x y a) :=
        C.sourceFiber_quotient_square (k := k) x y a
      _ = _ := by
        rw [← C.sourceFreeFiberHomEquiv_eq_map (k := k)]
        rfl
  · intro a ha
    apply hC.source x y a
    rw [← C.sourceFreeFiberHomEquiv_eq_map (k := k)]
    exact ha

/-- Once mesh-ideal lifting is known, the induced mesh-category functor is a
linear covering functor. -/
theorem functor_isCovering_of_hasMeshIdealLifting
    (C : RightMeshData.Cover T₁ T₂)
    [∀ y : Q₂, Fintype (Quiver.Star y)]
    (hC : C.HasMeshIdealLifting (k := k)) :
    letI := C.sourceStarFintype
    MagnitudeConjecture.LinearCovering.IsCovering
      (k := k) (C.functor (k := k)) := by
  letI := C.sourceStarFintype
  constructor
  · rintro ⟨X⟩ ⟨Y⟩
    change Function.Bijective
      (MagnitudeConjecture.LinearCovering.targetFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₁ (MagnitudeConjecture.LinearPathCategory.vertex X))
        (obj (k := k) T₂ (MagnitudeConjecture.LinearPathCategory.vertex Y)))
    exact C.targetFiberHomMap_bijective_of_hasMeshIdealLifting
      (k := k) hC _ _
  · rintro ⟨X⟩ ⟨Y⟩
    change Function.Bijective
      (MagnitudeConjecture.LinearCovering.sourceFiberHomMap
        (k := k) (C.functor (k := k))
        (obj (k := k) T₂ (MagnitudeConjecture.LinearPathCategory.vertex X))
        (obj (k := k) T₁ (MagnitudeConjecture.LinearPathCategory.vertex Y)))
    exact C.sourceFiberHomMap_bijective_of_hasMeshIdealLifting
      (k := k) hC _ _

end RightMeshData.Cover

end MagnitudeConjecture.MeshCategory
