import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Regular right modules and complete idempotent decompositions

A complete orthogonal family of idempotents decomposes the regular right
module as the finite biproduct of its principal right ideals.  The explicit
maps here are shared by support quotients and primitive deletion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ModuleCat.Algebra

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace MagnitudeConjecture.RightModule

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

omit [IsNoetherianRing Bᵐᵒᵖ] in
private theorem fg_hom_sum_apply {J : Type*} [Fintype J]
    {X Y : FGModuleCat.{u} Bᵐᵒᵖ} (f : J → (X ⟶ Y)) (x : X) :
    ((∑ j, f j).hom.hom) x = ∑ j, (f j).hom.hom x := by
  have h : (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h, ModuleCat.hom_sum]
  exact LinearMap.sum_apply _ _ x

/-- The regular right module as a literal finitely generated object. -/
abbrev rightRegularFGObj : FinitelyGeneratedCategory B := by
  letI : Module.Finite Bᵐᵒᵖ B :=
    Module.Finite.equiv rightRegularLinearEquiv
  exact FGModuleCat.of Bᵐᵒᵖ B

/-- The literal inclusion `eB → B`. -/
def rightIdealInclusion (e : B) :
    rightIdealFGObj e ⟶ rightRegularFGObj (B := B) := by
  letI : Module.Finite Bᵐᵒᵖ B :=
    Module.Finite.equiv rightRegularLinearEquiv
  letI : IsNoetherian Bᵐᵒᵖ B := inferInstance
  letI : Module.Finite Bᵐᵒᵖ (rightIdeal e) := inferInstance
  exact FGModuleCat.ofHom (rightIdeal e).subtype

/-- Left multiplication by `e`, as the projection `B → eB`. -/
def rightIdealProjection (e : B) :
    rightRegularFGObj (B := B) ⟶ rightIdealFGObj e := by
  letI : Module.Finite Bᵐᵒᵖ B :=
    Module.Finite.equiv rightRegularLinearEquiv
  letI : IsNoetherian Bᵐᵒᵖ B := inferInstance
  letI : Module.Finite Bᵐᵒᵖ (rightIdeal e) := inferInstance
  exact FGModuleCat.ofHom <|
    (rightRegularLeftMul e).codRestrict
      (rightIdeal e) fun y ↦ ⟨y, rfl⟩

@[simp]
theorem rightIdealInclusion_apply_val (e : B) (y : rightIdealFGObj e) :
    (rightIdealInclusion e).hom.hom y = y.1 :=
  rfl

@[simp]
theorem rightIdealProjection_apply_val
    (e : B) (y : rightRegularFGObj (B := B)) :
    ((rightIdealProjection e).hom.hom y).1 = e * y :=
  rfl

omit [IsNoetherianRing Bᵐᵒᵖ] in
/-- Every finitely generated right module is a quotient of a finite free
right module, with the source kept explicit for additive-closure arguments. -/
theorem exists_fin_free_epimorphism
    (X : FinitelyGeneratedCategory B) :
    ∃ n : ℕ, ∃ q :
      FGModuleCat.of Bᵐᵒᵖ (Fin n → Bᵐᵒᵖ) ⟶ X,
      Epi q := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Bᵐᵒᵖ X
  let q : FGModuleCat.of Bᵐᵒᵖ (Fin n → Bᵐᵒᵖ) ⟶ X :=
    FGModuleCat.ofHom p
  exact ⟨n, q,
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      q).2 hp⟩

variable {I : Type} [Fintype I]

/-- Project the regular module to all right ideals in an idempotent family. -/
def regularDecompositionMap (idempotent : I → B) :
    rightRegularFGObj (B := B) ⟶
      ⨁ fun i : I ↦ rightIdealFGObj (idempotent i) :=
  biproduct.lift fun i ↦ rightIdealProjection (idempotent i)

/-- Assemble the right ideals in an idempotent family into the regular
module. -/
def regularAssemblyMap (idempotent : I → B) :
    (⨁ fun i : I ↦ rightIdealFGObj (idempotent i)) ⟶
      rightRegularFGObj (B := B) :=
  biproduct.desc fun i ↦ rightIdealInclusion (idempotent i)

/-- Completeness makes regular decomposition followed by assembly the
identity. -/
theorem regularDecompositionMap_comp_assemblyMap
    (idempotent : I → B)
    (h : CompleteOrthogonalIdempotents idempotent) :
    regularDecompositionMap idempotent ≫ regularAssemblyMap idempotent =
      𝟙 _ := by
  classical
  rw [regularDecompositionMap, regularAssemblyMap, biproduct.lift_desc]
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [fg_hom_sum_apply]
  change (∑ i : I, idempotent i * y) = y
  rw [← Finset.sum_mul, h.complete, one_mul]

/-- Orthogonality makes assembly followed by regular decomposition the
identity on the biproduct of principal right ideals. -/
theorem regularAssemblyMap_comp_decompositionMap
    (idempotent : I → B)
    (h : CompleteOrthogonalIdempotents idempotent) :
    regularAssemblyMap idempotent ≫ regularDecompositionMap idempotent =
      𝟙 _ := by
  classical
  apply biproduct.hom_ext
  intro j
  apply biproduct.hom_ext'
  intro i
  simp only [Category.assoc]
  rw [regularAssemblyMap, regularDecompositionMap,
    biproduct.ι_desc_assoc, biproduct.lift_π]
  simp only [Category.id_comp]
  by_cases hij : i = j
  · subst j
    rw [biproduct.ι_π_self]
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact rightIdeal_fixed (h.idem i) y
  · rw [biproduct.ι_π_ne _ hij]
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    obtain ⟨a, ha⟩ := y.2
    change idempotent j * y.1 = 0
    change idempotent i * a = y.1 at ha
    rw [← ha, ← mul_assoc, h.ortho (Ne.symm hij), zero_mul]

/-- The regular right module is the biproduct of the principal right ideals
from any complete orthogonal idempotent family. -/
def regularDecompositionIso
    (idempotent : I → B)
    (h : CompleteOrthogonalIdempotents idempotent) :
    rightRegularFGObj (B := B) ≅
      ⨁ fun i : I ↦ rightIdealFGObj (idempotent i) where
  hom := regularDecompositionMap idempotent
  inv := regularAssemblyMap idempotent
  hom_inv_id := regularDecompositionMap_comp_assemblyMap idempotent h
  inv_hom_id := regularAssemblyMap_comp_decompositionMap idempotent h

end MagnitudeConjecture.RightModule
