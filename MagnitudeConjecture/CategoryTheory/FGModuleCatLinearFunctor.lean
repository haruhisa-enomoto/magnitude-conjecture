import MagnitudeConjecture.CategoryTheory.FGModuleCatAdditiveFinrank
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Linear endofunctors of finite-dimensional vector spaces

A linear endofunctor of finite-dimensional vector spaces has a canonical
evaluation map

`F(k) ⊗ V → F(V)`.

It sends `x ⊗ v` to the image of `x` under `F` applied to the linear map
`k → V`, `a ↦ a • v`.  This is the natural comparison needed to upgrade the
finite-string detector calculation at the ground field to a natural
functorial statement.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace MagnitudeConjecture.FiniteVectorSpace

universe u

variable {k : Type u} [Field k]

/-- A vector, regarded as the linear map from the ground field which sends
`1` to that vector. -/
def pointMap (V : FGModuleCat.{u} k) (v : V) :
    FGModuleCat.of k k ⟶ V :=
  FGModuleCat.ofHom (LinearMap.toSpanSingleton k V v)

@[simp]
theorem pointMap_apply (V : FGModuleCat.{u} k) (v : V) (a : k) :
    (pointMap V v).hom.hom a = a • v :=
  rfl

@[simp]
theorem pointMap_add (V : FGModuleCat.{u} k) (v w : V) :
    pointMap V (v + w) = pointMap V v + pointMap V w := by
  change FGModuleCat.ofHom (LinearMap.toSpanSingleton k V (v + w)) = _
  rw [LinearMap.toSpanSingleton_add]
  rfl

@[simp]
theorem pointMap_smul (V : FGModuleCat.{u} k) (r : k) (v : V) :
    pointMap V (r • v) = r • pointMap V v := by
  change FGModuleCat.ofHom (LinearMap.toSpanSingleton k V (r • v)) = _
  rw [LinearMap.toSpanSingleton_smul]
  rfl

/-- The bilinear evaluation pairing associated to a linear endofunctor. -/
def functorEvaluationBilinear
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k]
    (V : FGModuleCat.{u} k) :
    (F.obj (FGModuleCat.of k k) : Type u) →ₗ[k]
      V →ₗ[k] (F.obj V : Type u) where
  toFun x :=
    { toFun := fun v ↦ (F.map (pointMap V v)).hom.hom x
      map_add' := by
        intro v w
        have hpoint := pointMap_add V v w
        rw [hpoint, F.map_add]
        rfl
      map_smul' := by
        intro r v
        have hpoint := pointMap_smul V r v
        rw [hpoint, F.map_smul]
        rfl }
  map_add' x y := by
    apply LinearMap.ext
    intro v
    exact (F.map (pointMap V v)).hom.hom.map_add x y
  map_smul' r x := by
    apply LinearMap.ext
    intro v
    exact (F.map (pointMap V v)).hom.hom.map_smul r x

/-- The canonical evaluation map `F(k) ⊗ V → F(V)` of a linear
endofunctor. -/
def functorEvaluation
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k]
    (V : FGModuleCat.{u} k) :
    (F.obj (FGModuleCat.of k k) ⊗ V) ⟶ F.obj V :=
  FGModuleCat.ofHom (TensorProduct.lift (functorEvaluationBilinear F V))

@[simp]
theorem functorEvaluation_tmul
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k]
    (V : FGModuleCat.{u} k)
    (x : F.obj (FGModuleCat.of k k)) (v : V) :
    (functorEvaluation F V).hom.hom (x ⊗ₜ[k] v) =
      (F.map (pointMap V v)).hom.hom x := by
  rfl

/-- Evaluation is natural in the finite-dimensional coefficient space. -/
def functorEvaluationNatTrans
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k] :
    MonoidalCategory.tensorLeft (F.obj (FGModuleCat.of k k)) ⟶ F where
  app V := functorEvaluation F V
  naturality {V W} f := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x v
    change (F.map (pointMap W (f.hom.hom v))).hom.hom x =
      (F.map f).hom.hom ((F.map (pointMap V v)).hom.hom x)
    have hpoint : pointMap V v ≫ f =
        pointMap W (f.hom.hom v) := by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext
      change f.hom.hom ((pointMap V v).hom.hom 1) =
        (pointMap W (f.hom.hom v)).hom.hom 1
      rw [pointMap_apply, pointMap_apply]
      rw [one_smul k v]
      exact (one_smul k (f.hom.hom v)).symm
    rw [← hpoint]
    exact congrArg (fun q ↦ q.hom.hom x)
      (F.map_comp (pointMap V v) f)

@[simp]
theorem hom_hom_sum {ι : Type*} [Fintype ι]
    {V W : FGModuleCat.{u} k} (f : ι → (V ⟶ W)) :
    (∑ i, f i).hom.hom = ∑ i, (f i).hom.hom := by
  have hmodule : (∑ i, f i).hom = ∑ i, (f i).hom :=
    map_sum (InducedCategory.homLinearEquiv (R := k)).toLinearMap
      f Finset.univ
  rw [hmodule, ModuleCat.hom_sum]

/-- A basis coordinate, bundled as a morphism to the ground field. -/
def coordinateMap {ι : Type*} [Fintype ι]
    (V : FGModuleCat.{u} k) (b : Module.Basis ι k V) (i : ι) :
    V ⟶ FGModuleCat.of k k :=
  FGModuleCat.ofHom (b.coord i)

@[simp]
theorem coordinateMap_apply {ι : Type*} [Fintype ι]
    (V : FGModuleCat.{u} k) (b : Module.Basis ι k V) (i : ι) (v : V) :
    (coordinateMap V b i).hom.hom v = b.repr v i :=
  rfl

/-- The rank-one maps supplied by a finite basis sum to the identity. -/
theorem sum_coordinateMap_comp_pointMap_eq_id {ι : Type*} [Fintype ι]
    (V : FGModuleCat.{u} k) (b : Module.Basis ι k V) :
    ∑ i, coordinateMap V b i ≫ pointMap V (b i) = 𝟙 V := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext v
  rw [hom_hom_sum, LinearMap.sum_apply]
  simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply]
  exact b.sum_repr v

/-- A basis-dependent right inverse to the basis-free evaluation map.  Its
only role is to prove that evaluation is an isomorphism. -/
def functorEvaluationSection
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k] (V : FGModuleCat.{u} k) :
    F.obj V ⟶ F.obj (FGModuleCat.of k k) ⊗ V :=
  let b := Module.finBasis k V
  FGModuleCat.ofHom
    (∑ i, ((TensorProduct.mk k
      (F.obj (FGModuleCat.of k k) : Type u) V).flip (b i)).comp
        (F.map (coordinateMap V b i)).hom.hom)

@[simp]
theorem functorEvaluationSection_apply
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k] (V : FGModuleCat.{u} k) (y : F.obj V) :
    (functorEvaluationSection F V).hom.hom y =
      ∑ i, (F.map (coordinateMap V (Module.finBasis k V) i)).hom.hom y
        ⊗ₜ[k] (Module.finBasis k V) i := by
  unfold functorEvaluationSection
  dsimp only
  change (∑ i, ((TensorProduct.mk k
      (F.obj (FGModuleCat.of k k) : Type u) V).flip
        ((Module.finBasis k V) i)).comp
      (F.map (coordinateMap V (Module.finBasis k V) i)).hom.hom) y = _
  rw [LinearMap.sum_apply]
  rfl

/-- The basis section is a right inverse of the canonical evaluation map. -/
theorem functorEvaluationSection_comp_evaluation
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k] (V : FGModuleCat.{u} k) :
    functorEvaluationSection F V ≫ functorEvaluation F V = 𝟙 (F.obj V) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext y
  let b := Module.finBasis k V
  change (functorEvaluation F V).hom.hom
      ((functorEvaluationSection F V).hom.hom y) = y
  rw [functorEvaluationSection_apply]
  change (functorEvaluation F V).hom.hom
      (∑ i, (F.map (coordinateMap V b i)).hom.hom y ⊗ₜ[k] b i) = y
  rw [map_sum]
  simp only [functorEvaluation_tmul]
  have hterm : ∀ i,
      (F.map (pointMap V (b i))).hom.hom
          ((F.map (coordinateMap V b i)).hom.hom y) =
        (F.map (coordinateMap V b i ≫ pointMap V (b i))).hom.hom y := by
    intro i
    exact congrArg (fun q ↦ q.hom.hom y)
      (F.map_comp (coordinateMap V b i) (pointMap V (b i))).symm
  simp_rw [hterm]
  rw [← LinearMap.sum_apply, ← hom_hom_sum]
  rw [← F.map_sum, sum_coordinateMap_comp_pointMap_eq_id, F.map_id]
  rfl

/-- The canonical evaluation map of an additive linear endofunctor is
bijective on every finite-dimensional vector space. -/
theorem functorEvaluation_bijective
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k] (V : FGModuleCat.{u} k) :
    Function.Bijective (functorEvaluation F V).hom.hom := by
  have hsurjective : Function.Surjective
      (functorEvaluation F V).hom.hom := by
    intro y
    refine ⟨(functorEvaluationSection F V).hom.hom y, ?_⟩
    exact congrArg (fun q ↦ q.hom.hom y)
      (functorEvaluationSection_comp_evaluation F V)
  have hfinrank :
      Module.finrank k
          ((F.obj (FGModuleCat.of k k) ⊗ V : FGModuleCat.{u} k) : Type u) =
        Module.finrank k (F.obj V) := by
    change Module.finrank k
        (TensorProduct k (F.obj (FGModuleCat.of k k) : Type u) V) = _
    rw [Module.finrank_tensorProduct]
    conv_rhs => rw [finrank_map_eq_mul F V]
    exact Nat.mul_comm _ _
  exact ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).2
      hsurjective,
    hsurjective⟩

/-- Finite-dimensional Eilenberg--Watts over a field: an additive linear
endofunctor is naturally isomorphic to tensoring with its value on the ground
field. -/
def functorEvaluationNatIso
    (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] [F.Linear k] :
    MonoidalCategory.tensorLeft (F.obj (FGModuleCat.of k k)) ≅ F :=
  NatIso.ofComponents
    (fun V ↦ (LinearEquiv.ofBijective
      (functorEvaluation F V).hom.hom
      (functorEvaluation_bijective F V)).toFGModuleCatIso)
    (fun f ↦ (functorEvaluationNatTrans F).naturality f)

end MagnitudeConjecture.FiniteVectorSpace
