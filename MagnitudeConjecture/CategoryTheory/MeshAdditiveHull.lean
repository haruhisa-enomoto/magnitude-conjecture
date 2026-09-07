import MagnitudeConjecture.CategoryTheory.MeshSimplePresentation
import QuotientSubmoduleEquidistribution.CategoryTheory.MatWeakExactness

/-!
# Weak mesh exactness in the finite additive hull

The finite matrix category is the additive hull of the strict raw mesh
category.  The objectwise exactness of the contravariant mesh
representables therefore upgrades to a genuine weak-kernel statement for
each nonprojective mesh.  This is the additive categorical form used in the
Bongartz--Gabriel Auslander-category argument.

Only the middle exactness of the mesh is asserted.  In particular, the map
from the translate need not be monic.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.MeshCategory

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

namespace RightMeshData

variable (T : RightMeshData Q)

/-- The finite additive hull of the strict vertex model of the raw mesh
category. -/
abbrev AdditiveHull := Mat_ (T.VertexCategory (k := k))

/-- A mesh vertex as a singleton object of the finite additive hull. -/
abbrev additiveVertexObj (x : Q) : T.AdditiveHull (k := k) :=
  (Mat_.embedding (T.VertexCategory (k := k))).obj x

/-- The additive-hull object indexed by the arrows entering `z`. -/
def additiveIncomingObj (z : Q) : T.AdditiveHull (k := k) where
  ι := IncomingArrow z
  X := fun a ↦ a.1

/-- The matrix of paired arrows from the translate into the incoming middle
term of a nonprojective mesh. -/
def additiveTranslationMap
    (z : {z : Q // z ∉ T.projective}) :
    T.additiveVertexObj (k := k) (T.tau z) ⟶
      T.additiveIncomingObj (k := k) z.1 := by
  dsimp only [additiveVertexObj, additiveIncomingObj, Mat_.embedding]
  exact fun _ a ↦ InducedCategory.homMk
      (T.incomingArrowHom (k := k)
        (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1))

/-- The matrix of incoming arrows from the middle term to its endpoint. -/
def additiveIncomingMap (z : Q) :
    T.additiveIncomingObj (k := k) z ⟶
      T.additiveVertexObj (k := k) z := by
  dsimp only [additiveIncomingObj, additiveVertexObj, Mat_.embedding]
  exact fun a _ ↦ InducedCategory.homMk
      (T.incomingArrowHom (k := k) a)

/-- The complete incoming-arrow matrix never has a section: every entry of a
hypothetical section--matrix composite has positive path length, whereas the
identity of the endpoint vertex has degree zero. -/
theorem additiveIncomingMap_not_splitEpi (z : Q) :
    ¬ IsSplitEpi (T.additiveIncomingMap (k := k) z) := by
  intro hsplit
  let g := T.additiveIncomingMap (k := k) z
  letI : IsSplitEpi g := hsplit
  let s := section_ g
  have hid : s ≫ g = 𝟙 (T.additiveVertexObj (k := k) z) :=
    IsSplitEpi.id g
  have hentry := congrFun (congrFun hid PUnit.unit) PUnit.unit
  rw [Mat_.comp_apply] at hentry
  dsimp only [g, additiveIncomingMap, additiveVertexObj,
    additiveIncomingObj, Mat_.embedding] at hentry
  simp only [id, Mat_.id_apply_self] at hentry
  let q (a : IncomingArrow z) :
      obj (k := k) T z ⟶ obj (k := k) T a.1 := by
    exact (s PUnit.unit a).hom
  have htail :
      (∑ a : IncomingArrow z,
        q a ≫ T.incomingArrowHom (k := k) a) ∈
        lengthTail (k := k) T z z 1 := by
    apply Submodule.sum_mem
    intro a _
    have hs : q a ∈
        lengthTail (k := k) T z a.1 0 := by
      rw [lengthTail_zero_eq_top]
      exact Submodule.mem_top
    have ha : T.incomingArrowHom (k := k) a ∈
        lengthTail (k := k) T a.1 z 1 :=
      mem_lengthTail_of_mem_lengthComponent (k := k) T (by omega)
        (T.incomingArrowHom_mem_lengthComponent_one (k := k) a)
    simpa using comp_mem_lengthTail (k := k) T hs ha
  have hraw :
      (∑ a : IncomingArrow z,
        q a ≫ T.incomingArrowHom (k := k) a) =
        𝟙 (obj (k := k) T z) := by
    have hlin := congrArg
      (InducedCategory.homLinearEquiv (R := k)) hentry
    simp only [map_sum, InducedCategory.homLinearEquiv_apply,
      InducedCategory.comp_hom, InducedCategory.homMk_hom,
      InducedCategory.id_hom] at hlin
    exact hlin
  rw [hraw] at htail
  exact id_not_mem_lengthTail_one (k := k) T z htail

set_option backward.isDefEq.respectTransparency false in
/-- The right mesh ending at a nonprojective vertex, inside the finite
additive hull. -/
def additiveRightMesh
    (z : {z : Q // z ∉ T.projective}) :
    ShortComplex (T.AdditiveHull (k := k)) :=
  ShortComplex.mk
    (T.additiveTranslationMap (k := k) z)
    (T.additiveIncomingMap (k := k) z.1) (by
      apply Mat_.hom_ext
      rintro ⟨⟩ ⟨⟩
      change (∑ a : IncomingArrow z.1,
        InducedCategory.homMk
            (T.incomingArrowHom (k := k)
              (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ :
                IncomingArrow a.1)) ≫
          InducedCategory.homMk
            (T.incomingArrowHom (k := k) a)) = 0
      apply (InducedCategory.homLinearEquiv (R := k)).injective
      rw [map_sum, map_zero]
      change (∑ a : IncomingArrow z.1,
        T.incomingArrowHom (k := k)
              (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ :
                IncomingArrow a.1) ≫
            T.incomingArrowHom (k := k) a) = 0
      simpa only [incomingSum, Category.id_comp] using
        T.paired_incomingSum_eq_zero (k := k) z
          (𝟙 (obj (k := k) T (T.tau z))))

/-- Evaluation of a one-row matrix, reindexed by the actual incoming
arrows and stripped of the induced-category wrapper. -/
def additiveIncomingHomLinearEquiv (x z : Q) :
    (T.additiveVertexObj (k := k) x ⟶
        T.additiveIncomingObj (k := k) z) ≃ₗ[k]
      IncomingCoefficient (k := k) T x z where
  toFun f a :=
    (f PUnit.unit a).hom
  invFun c _ a := InducedCategory.homMk (c a)
  left_inv f := by
    apply Mat_.hom_ext
    intro i j
    cases i
    apply InducedCategory.hom_ext
    rfl
  right_inv _ := rfl
  map_add' f g := by
    funext a
    rfl
  map_smul' r f := by
    funext a
    rfl

/-- Evaluation identifies a one-by-one matrix with the underlying raw mesh
Hom space. -/
def additiveVertexHomLinearEquiv (x y : Q) :
    (T.additiveVertexObj (k := k) x ⟶
        T.additiveVertexObj (k := k) y) ≃ₗ[k]
      (obj (k := k) T x ⟶ obj (k := k) T y) where
  toFun f := (f PUnit.unit PUnit.unit).hom
  invFun q _ _ := InducedCategory.homMk q
  left_inv f := by
    apply Mat_.hom_ext
    intro i j
    cases i
    cases j
    apply InducedCategory.hom_ext
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluating postcomposition by the matrix of paired arrows gives the
paired-coefficient map of the representable mesh presentation. -/
theorem additiveIncomingHomLinearEquiv_comp_translationMap
    (x : Q) (z : {z : Q // z ∉ T.projective})
    (f : T.additiveVertexObj (k := k) x ⟶
      T.additiveVertexObj (k := k) (T.tau z)) :
    T.additiveIncomingHomLinearEquiv (k := k) x z.1
        (f ≫ T.additiveTranslationMap (k := k) z) =
      T.pairedCoefficient (k := k) z
        (T.additiveVertexHomLinearEquiv (k := k) x (T.tau z) f) := by
  funext a
  change (∑ i, f PUnit.unit i ≫
      T.additiveTranslationMap (k := k) z i
        a).hom =
    (f PUnit.unit PUnit.unit).hom ≫
      T.incomingArrowHom (k := k)
        (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1)
  change (∑ i : PUnit, f PUnit.unit i ≫
      T.additiveTranslationMap (k := k) z i a).hom =
    (f PUnit.unit PUnit.unit).hom ≫
      T.incomingArrowHom (k := k)
        (⟨T.tau z, T.arrowEquiv z a.1 a.2⟩ : IncomingArrow a.1)
  rw [Fintype.sum_unique]
  rfl

/-- Evaluating postcomposition by the incoming-arrow matrix gives literal
incoming summation. -/
theorem additiveVertexHomLinearEquiv_comp_incomingMap
    (x z : Q)
    (f : T.additiveVertexObj (k := k) x ⟶
      T.additiveIncomingObj (k := k) z) :
    T.additiveVertexHomLinearEquiv (k := k) x z
        (f ≫ T.additiveIncomingMap (k := k) z) =
      T.incomingSum (k := k)
        (T.additiveIncomingHomLinearEquiv (k := k) x z f) := by
  change (InducedCategory.homLinearEquiv (R := k))
      ((f ≫ T.additiveIncomingMap (k := k) z)
        PUnit.unit PUnit.unit) =
    T.incomingSum (k := k)
      (T.additiveIncomingHomLinearEquiv (k := k) x z f)
  rw [Mat_.comp_apply, map_sum]
  simp only [additiveIncomingMap, additiveIncomingHomLinearEquiv,
    incomingSum]
  dsimp only [id]
  rfl

/-- The additive-hull mesh is exact against every singleton source. -/
theorem additiveRightMesh_exact_from_vertex
    (x : Q) (z : {z : Q // z ∉ T.projective}) :
    Function.Exact
      (fun l : T.additiveVertexObj (k := k) x ⟶
          (T.additiveRightMesh (k := k) z).X₁ ↦
        l ≫ (T.additiveRightMesh (k := k) z).f)
      (fun q : T.additiveVertexObj (k := k) x ⟶
          (T.additiveRightMesh (k := k) z).X₂ ↦
        q ≫ (T.additiveRightMesh (k := k) z).g) := by
  intro q
  constructor
  · intro hq
    change q ≫ T.additiveIncomingMap (k := k) z.1 = 0 at hq
    have hsum : T.incomingSum (k := k)
        (T.additiveIncomingHomLinearEquiv (k := k) x z.1 q) = 0 := by
      have h := congrArg
        (T.additiveVertexHomLinearEquiv (k := k) x z.1) hq
      calc
        T.incomingSum (k := k)
            (T.additiveIncomingHomLinearEquiv (k := k) x z.1 q) =
            T.additiveVertexHomLinearEquiv (k := k) x z.1
              (q ≫ T.additiveIncomingMap (k := k) z.1) :=
          (T.additiveVertexHomLinearEquiv_comp_incomingMap
            (k := k) x z.1 q).symm
        _ = T.additiveVertexHomLinearEquiv (k := k) x z.1 0 := h
        _ = 0 := map_zero _
    have hker : T.additiveIncomingHomLinearEquiv (k := k) x z.1 q ∈
        LinearMap.ker (T.incomingSumLinearMap (k := k) x z.1) := by
      rw [LinearMap.mem_ker]
      exact hsum
    rw [← T.range_pairedCoefficientLinearMap_eq_ker_incomingSumLinearMap
      (k := k) z x] at hker
    obtain ⟨a, ha⟩ := hker
    let l := (T.additiveVertexHomLinearEquiv
      (k := k) x (T.tau z)).symm a
    refine ⟨l, ?_⟩
    change l ≫ T.additiveTranslationMap (k := k) z = q
    apply (T.additiveIncomingHomLinearEquiv (k := k) x z.1).injective
    rw [T.additiveIncomingHomLinearEquiv_comp_translationMap
      (k := k) x z l]
    change T.pairedCoefficient (k := k) z
        (T.additiveVertexHomLinearEquiv (k := k) x (T.tau z) l) =
      T.additiveIncomingHomLinearEquiv (k := k) x z.1 q
    rw [LinearEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨l, rfl⟩
    change (l ≫ (T.additiveRightMesh (k := k) z).f) ≫
      (T.additiveRightMesh (k := k) z).g = 0
    rw [Category.assoc, (T.additiveRightMesh (k := k) z).zero,
      comp_zero]

/-- The right mesh ending at a nonprojective vertex is a weak-kernel pair in
the finite additive hull.  No monicity of its first map is used or claimed. -/
theorem additiveRightMesh_isWeakKernel
    (z : {z : Q // z ∉ T.projective}) :
    QuotientSubmoduleEquidistribution.Iyama.ShortComplex.IsWeakKernel
      (T.additiveRightMesh (k := k) z) := by
  apply QuotientSubmoduleEquidistribution.Iyama.mat_isWeakKernel_of_exact_embedding
  intro X
  exact T.additiveRightMesh_exact_from_vertex (k := k) X z

set_option backward.isDefEq.respectTransparency false in
/-- At a projective vertex, the incoming-arrow matrix is monic in the finite
additive hull.  This is the projective boundary case complementary to the
nonprojective weak mesh above. -/
theorem additiveIncomingMap_mono_of_projective
    (z : Q) (hz : z ∈ T.projective) :
    Mono (T.additiveIncomingMap (k := k) z) := by
  apply Preadditive.mono_of_cancel_zero
  intro W f hf
  apply Mat_.hom_ext
  intro i a
  let x : Q := W.X i
  let row : T.additiveVertexObj (k := k) x ⟶
      T.additiveIncomingObj (k := k) z :=
    fun _ b ↦ f i b
  have hrow : row ≫ T.additiveIncomingMap (k := k) z = 0 := by
    apply Mat_.hom_ext
    rintro ⟨⟩ ⟨⟩
    have hentry := congrFun (congrFun hf i) PUnit.unit
    change (row ≫ T.additiveIncomingMap (k := k) z)
      PUnit.unit PUnit.unit = 0
    change (f ≫ T.additiveIncomingMap (k := k) z)
      i PUnit.unit = 0 at hentry
    exact hentry
  let c := T.additiveIncomingHomLinearEquiv (k := k) x z row
  have hsum : T.incomingSum (k := k) c = 0 := by
    calc
      T.incomingSum (k := k) c =
          T.additiveVertexHomLinearEquiv (k := k) x z
            (row ≫ T.additiveIncomingMap (k := k) z) :=
        (T.additiveVertexHomLinearEquiv_comp_incomingMap
          (k := k) x z row).symm
      _ = T.additiveVertexHomLinearEquiv (k := k) x z 0 :=
        congrArg (T.additiveVertexHomLinearEquiv (k := k) x z) hrow
      _ = 0 := map_zero _
  have hc : c = 0 := by
    apply T.incomingSumLinearMap_injective_of_projective (k := k) z hz x
    rw [T.incomingSumLinearMap_apply (k := k) c, hsum, map_zero]
  have hca := congrFun hc a
  apply InducedCategory.hom_ext
  change c a = 0
  exact hca

end RightMeshData

end MagnitudeConjecture.MeshCategory
