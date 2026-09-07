import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Reflecting a finite relation through linear Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u w

variable {k : Type w} [Ring k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C]

/-- A relation among maps of representables reflects to the represented
morphisms. The finite sum is evaluated at the identity of its source. -/
theorem linearYoneda_reflect_sum_relation {ι : Type*} [Fintype ι]
    {Z X : C} (V : ι → C) (p : ∀ i, Z ⟶ V i) (q : ∀ i, V i ⟶ X)
    (M : Cᵒᵖ ⥤ ModuleCat k)
    (inc : ∀ i, (linearYoneda k C).obj (V i) ⟶ M)
    (h : M ⟶ (linearYoneda k C).obj X)
    (t : (linearYoneda k C).obj Z ⟶ M)
    (ht : t = ∑ i, (linearYoneda k C).map (p i) ≫ inc i)
    (hq : ∀ i, (linearYoneda k C).map (q i) = inc i ≫ h)
    (hh : t ≫ h = 0) : ∑ i, p i ≫ q i = 0 := by
  classical
  let Y := linearYoneda k C
  have hs : (∑ i, Y.map (p i ≫ q i)) = 0 := by
    simp only [Y, Functor.map_comp, hq, ← Category.assoc]
    rw [← Preadditive.sum_comp, ← ht]
    exact hh
  have hv := congrArg (fun f ↦ (f.app (Opposite.op Z)).hom (𝟙 Z)) hs
  rw [NatTrans.app_sum] at hv
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply] at hv
  change (∑ i, 𝟙 Z ≫ (p i ≫ q i)) = 0 at hv
  simpa only [Category.id_comp] using hv

end CategoryTheory
