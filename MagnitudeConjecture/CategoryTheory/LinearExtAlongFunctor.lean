import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Linear Ext along a functor

For an `R`-linear abelian category `C` and a functor `T : D ⥤ C`, this file
packages

`(X, d) ↦ Extⁿ(X, T(d))`

as a functor `Cᵒᵖ ⥤ D ⥤ ModuleCat R`.  The derived-category Ext API already
provides the groups and their two composition maps; the construction here
only records their linear functoriality in a reusable, elaboration-light form.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace MagnitudeConjecture.CategoryTheory

universe u v w uD vD uR

variable {R : Type uR} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]
variable {D : Type uD} [Category.{vD} D]

/-- For fixed first argument, degree, and `T : D ⥤ C`, Ext is a linear-module
valued functor on `D`. -/
def linearExtObjAlong (T : D ⥤ C) (X : C) (n : ℕ) :
    D ⥤ ModuleCat.{w} R where
  obj d := ModuleCat.of R (Ext.{w} X (T.obj d) n)
  map f := ModuleCat.ofHom <|
    Ext.postcompOfLinear (Ext.mk₀ (T.map f)) R X (add_zero n)
  map_id d := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro xi
    change xi.comp (Ext.mk₀ (T.map (𝟙 d))) (add_zero n) = xi
    rw [T.map_id]
    exact Ext.comp_mk₀_id xi
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro xi
    change xi.comp (Ext.mk₀ (T.map (f ≫ g))) (add_zero n) =
      (xi.comp (Ext.mk₀ (T.map f)) (add_zero n)).comp
        (Ext.mk₀ (T.map g)) (add_zero n)
    rw [T.map_comp, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_third_deg_zero]

/-- Precomposition in the first Ext variable, natural in the variable along
`T`. -/
def linearExtPrecompAlong (T : D ⥤ C) (n : ℕ)
    {X Y : C} (a : Y ⟶ X) :
    linearExtObjAlong (R := R) T X n ⟶
      linearExtObjAlong (R := R) T Y n where
  app d := ModuleCat.ofHom <|
    Ext.precompOfLinear (Ext.mk₀ a) R (T.obj d) (zero_add n)
  naturality := by
    intro d e f
    dsimp only [linearExtObjAlong]
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]
    apply LinearMap.ext
    intro xi
    have h := Ext.comp_assoc (a₁₂ := n) (a₂₃ := n) (a := n)
      (Ext.mk₀ a) xi (Ext.mk₀ (T.map f))
      (zero_add n) (add_zero n) (by omega)
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Ext.precompOfLinear, Ext.postcompOfLinear,
      Ext.bilinearCompOfLinear_apply_apply,
      LinearMap.flip_apply]
    exact h.symm

@[simp]
theorem linearExtPrecompAlong_id (T : D ⥤ C) (X : C) (n : ℕ) :
    linearExtPrecompAlong (R := R) T n (𝟙 X) = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  dsimp only [linearExtPrecompAlong, NatTrans.comp_app]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro xi
  dsimp only [linearExtPrecompAlong, ModuleCat.id_apply,
    ModuleCat.ofHom_apply]
  change (Ext.mk₀ (𝟙 X)).comp xi (zero_add n) = xi
  exact Ext.mk₀_id_comp xi

@[simp]
theorem linearExtPrecompAlong_comp (T : D ⥤ C) (n : ℕ)
    {X Y Z : C} (a : Y ⟶ X) (b : Z ⟶ Y) :
    linearExtPrecompAlong (R := R) T n (b ≫ a) =
      linearExtPrecompAlong (R := R) T n a ≫
        linearExtPrecompAlong (R := R) T n b := by
  apply NatTrans.ext
  funext d
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro xi
  have h := Ext.comp_assoc (a₁₂ := 0) (a₂₃ := n) (a := n)
    (Ext.mk₀ b) (Ext.mk₀ a) xi
    (zero_add 0) (zero_add n) (by omega)
  change (Ext.mk₀ (b ≫ a)).comp xi (zero_add n) =
    (Ext.mk₀ b).comp
      ((Ext.mk₀ a).comp xi (zero_add n)) (zero_add n)
  simpa only [Ext.mk₀_comp_mk₀] using h

/-- The linear Ext bifunctor after restricting its second variable along
`T`. -/
def linearExtAlong (T : D ⥤ C) (n : ℕ) :
    Cᵒᵖ ⥤ (D ⥤ ModuleCat.{w} R) where
  obj X := linearExtObjAlong (R := R) T X.unop n
  map a := linearExtPrecompAlong (R := R) T n a.unop
  map_id X := linearExtPrecompAlong_id (R := R) T X.unop n
  map_comp a b := by
    rw [unop_comp]
    exact linearExtPrecompAlong_comp (R := R) T n a.unop b.unop

end MagnitudeConjecture.CategoryTheory
