import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-! # Transport of represented modules along a fully faithful linear functor -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CategoryTheory
universe u v w z t
variable {k : Type t} [Field k]
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
variable {P : C} {Q : D} (e : F.obj P ≅ Q)

/-- The algebra comparison induced by realization and a chosen generator isomorphism. -/
def representedEndEquiv : End P ≃ₐ[k] End Q :=
  (Functor.endAlgEquivOfFullyFaithful F P).trans (Iso.endAlgEquiv e)

/-- Hom from the generator is unchanged by fully faithful realization. -/
def representedHomEquiv (X : C) : (P ⟶ X) ≃ₗ[k] (Q ⟶ F.obj X) where
  toFun f := e.inv ≫ F.map f
  invFun g := F.preimage (e.hom ≫ g)
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp only [F.map_add, Preadditive.comp_add]
  map_smul' c f := by simp only [F.map_smul, Linear.comp_smul, RingHom.id_apply]

/-- This comparison preserves the right endomorphism-algebra action. -/
theorem representedHomEquiv_precomp (X : C) (a : End P) (f : P ⟶ X) :
    representedHomEquiv (k := k) F e X (a.asHom ≫ f) =
      (representedEndEquiv (k := k) F e a).asHom ≫ representedHomEquiv (k := k) F e X f := by
  change e.inv ≫ F.map (a.asHom ≫ f) =
    (e.inv ≫ F.map a.asHom ≫ e.hom) ≫ e.inv ≫ F.map f
  simp

/-- The comparison is natural in the target. -/
theorem representedHomEquiv_postcomp {X Y : C} (f : P ⟶ X) (g : X ⟶ Y) :
    representedHomEquiv (k := k) F e Y (f ≫ g) = representedHomEquiv (k := k) F e X f ≫ F.map g := by
  change e.inv ≫ F.map (f ≫ g) = (e.inv ≫ F.map f) ≫ F.map g
  simp

/-- After restriction along the opposite algebra comparison, the Hom comparison
is an isomorphism of actual right modules. -/
def representedModuleEquiv (X : C) :
    letI : Module (End P)ᵐᵒᵖ (Q ⟶ F.obj X) := Module.compHom _
      (AlgEquiv.op (representedEndEquiv (k := k) F e)).toRingHom
    (P ⟶ X) ≃ₗ[(End P)ᵐᵒᵖ] (Q ⟶ F.obj X) := by
  letI : Module (End P)ᵐᵒᵖ (Q ⟶ F.obj X) := Module.compHom _
    (AlgEquiv.op (representedEndEquiv (k := k) F e)).toRingHom
  exact
    { (representedHomEquiv (k := k) F e X).toAddEquiv with
      map_smul' := fun a f ↦ representedHomEquiv_precomp (k := k) F e X a.unop f }

/-- The same comparison over the realized generator algebra, restricting the
source action along the inverse algebra equivalence. -/
def representedModuleEquivOverTarget (X : C) :
    letI : Module (End Q)ᵐᵒᵖ (P ⟶ X) := Module.compHom _
      (AlgEquiv.op (representedEndEquiv (k := k) F e).symm).toRingHom
    (P ⟶ X) ≃ₗ[(End Q)ᵐᵒᵖ] (Q ⟶ F.obj X) := by
  letI : Module (End Q)ᵐᵒᵖ (P ⟶ X) := Module.compHom _
    (AlgEquiv.op (representedEndEquiv (k := k) F e).symm).toRingHom
  refine { (representedHomEquiv (k := k) F e X).toAddEquiv with map_smul' := ?_ }
  intro a f
  change representedHomEquiv (k := k) F e X
      (((representedEndEquiv (k := k) F e).symm a.unop).asHom ≫ f) =
    a.unop.asHom ≫ representedHomEquiv (k := k) F e X f
  have h := representedHomEquiv_precomp (k := k) F e X
    ((representedEndEquiv (k := k) F e).symm a.unop) f
  simpa only [AlgEquiv.apply_symm_apply] using h

end MagnitudeConjecture.CategoryTheory
