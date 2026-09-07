import MagnitudeConjecture.Algebra.RightModuleAuslanderTranspose

/-!
# Projective-stable Hom spaces for right modules

This file forms the scalar quotient of a right-module Hom space by maps
factoring through finitely generated projectives.  Only the one-sided
projective-stable vector spaces and their postcomposition maps are retained;
no unrelated stable-category infrastructure is imported.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

/-- A morphism of finitely generated right modules factors through a
finitely generated categorical projective. -/
structure FactorsThroughProjective
    {X Y : FGModuleCat.{u} Bᵐᵒᵖ} (f : X ⟶ Y) where
  middle : FGModuleCat.{u} Bᵐᵒᵖ
  projective : Projective middle
  left : X ⟶ middle
  right : middle ⟶ Y
  fac : left ≫ right = f

namespace FactorsThroughProjective

/-- The zero map factors through the zero module. -/
def zero {X Y : FGModuleCat.{u} Bᵐᵒᵖ} :
    FactorsThroughProjective (0 : X ⟶ Y) :=
  { middle := rightRegularFGObj (B := B)
    projective := by
      apply fgProjective_of_moduleProjective
      exact rightRegular_projective
    left := 0
    right := 0
    fac := by simp }

/-- Projective factorizations are closed under addition. -/
def add {X Y : FGModuleCat.{u} Bᵐᵒᵖ} {f g : X ⟶ Y}
    (hf : FactorsThroughProjective f)
    (hg : FactorsThroughProjective g) :
    FactorsThroughProjective (f + g) := by
  letI : Projective hf.middle := hf.projective
  letI : Projective hg.middle := hg.projective
  exact
    { middle := hf.middle ⊞ hg.middle
      projective := inferInstance
      left := biprod.lift hf.left hg.left
      right := biprod.desc hf.right hg.right
      fac := by rw [biprod.lift_desc, hf.fac, hg.fac] }

/-- Projective factorizations are closed under scalar multiplication. -/
def smul {X Y : FGModuleCat.{u} Bᵐᵒᵖ} {f : X ⟶ Y}
    (a : k) (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (a • f) :=
  { middle := hf.middle
    projective := hf.projective
    left := a • hf.left
    right := hf.right
    fac := by rw [Linear.smul_comp, hf.fac] }

/-- Postcomposition preserves projective factorization. -/
def postcomp {X Y Z : FGModuleCat.{u} Bᵐᵒᵖ}
    {f : X ⟶ Y} (hf : FactorsThroughProjective f) (g : Y ⟶ Z) :
    FactorsThroughProjective (f ≫ g) :=
  { middle := hf.middle
    projective := hf.projective
    left := hf.left
    right := hf.right ≫ g
    fac := by rw [← Category.assoc, hf.fac] }

/-- Precomposition preserves projective factorization. -/
def precomp {W X Y : FGModuleCat.{u} Bᵐᵒᵖ}
    (g : W ⟶ X) {f : X ⟶ Y} (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (g ≫ f) :=
  { middle := hf.middle
    projective := hf.projective
    left := g ≫ hf.left
    right := hf.right
    fac := by rw [Category.assoc, hf.fac] }

end FactorsThroughProjective

/-- The subspace of morphisms factoring through projectives. -/
def projectiveFactorSubmodule
    (X Y : FGModuleCat.{u} Bᵐᵒᵖ) : Submodule k (X ⟶ Y) where
  carrier := {f | Nonempty (FactorsThroughProjective f)}
  zero_mem' := ⟨FactorsThroughProjective.zero⟩
  add_mem' := by
    rintro f g ⟨hf⟩ ⟨hg⟩
    exact ⟨hf.add hg⟩
  smul_mem' := by
    rintro a f ⟨hf⟩
    exact ⟨hf.smul a⟩

/-- The projective-stable Hom vector space. -/
abbrev projectiveStableHom
    (X Y : FGModuleCat.{u} Bᵐᵒᵖ) :=
  (X ⟶ Y) ⧸ projectiveFactorSubmodule (k := k) X Y

/-- The class of an ordinary morphism in projective-stable Hom. -/
abbrev projectiveStableClass
    {X Y : FGModuleCat.{u} Bᵐᵒᵖ} :
    (X ⟶ Y) →ₗ[k] projectiveStableHom (k := k) X Y :=
  (projectiveFactorSubmodule (k := k) X Y).mkQ

/-- Postcomposition on projective-stable Hom. -/
def projectiveStablePostcomp
    (X : FGModuleCat.{u} Bᵐᵒᵖ)
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z) :
    projectiveStableHom (k := k) X Y →ₗ[k]
      projectiveStableHom (k := k) X Z :=
  (projectiveFactorSubmodule (k := k) X Y).mapQ
    (projectiveFactorSubmodule (k := k) X Z)
    (CategoryTheory.Linear.rightComp k X g) (by
      intro f hf
      obtain ⟨hfactor⟩ := hf
      exact ⟨hfactor.postcomp g⟩)

@[simp]
theorem projectiveStablePostcomp_mk
    (X : FGModuleCat.{u} Bᵐᵒᵖ)
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z) (f : X ⟶ Y) :
    projectiveStablePostcomp (k := k) X g
        (projectiveStableClass (k := k) f) =
      projectiveStableClass (k := k) (f ≫ g) := by
  rfl

/-- If the identity factors through a projective, the module is
projective. -/
theorem projective_of_id_factorsThroughProjective
    (X : FGModuleCat.{u} Bᵐᵒᵖ)
    (h : FactorsThroughProjective (𝟙 X)) : Projective X := by
  letI : Projective h.middle := h.projective
  let r : Retract X h.middle :=
    { i := h.left
      r := h.right
      retract := h.fac }
  exact r.projective

/-- A nonprojective module has a nonzero stable identity class. -/
theorem projectiveStableClass_id_ne_zero
    (X : FGModuleCat.{u} Bᵐᵒᵖ) (hX : ¬ Projective X) :
    projectiveStableClass (k := k) (𝟙 X) ≠ 0 := by
  intro hzero
  apply hX
  apply projective_of_id_factorsThroughProjective X
  exact Classical.choice
    ((Submodule.Quotient.mk_eq_zero _).mp hzero)

end MagnitudeConjecture.RightModule
