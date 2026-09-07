import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Projective-stable Hom spaces in a linear category

This file forms the scalar quotient of a Hom space by the maps which factor
through categorical projectives.  It records only the one-sided stable Hom
spaces and their postcomposition maps needed by the finite-functor-category
Auslander--Reiten argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MagnitudeConjecture.ProjectiveStable

universe uk v u

variable {k : Type uk} [Field k]
variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [CategoryTheory.Linear k D] [HasZeroObject D]
variable [HasBinaryBiproducts D]

/-- A morphism factors through a categorical projective object. -/
structure FactorsThroughProjective {X Y : D} (f : X ⟶ Y) where
  middle : D
  projective : Projective middle
  left : X ⟶ middle
  right : middle ⟶ Y
  fac : left ≫ right = f

namespace FactorsThroughProjective

/-- The zero map factors through the zero object. -/
def zero {X Y : D} : FactorsThroughProjective (0 : X ⟶ Y) where
  middle := 0
  projective := inferInstance
  left := 0
  right := 0
  fac := by simp

/-- Projective factorizations are closed under addition. -/
def add {X Y : D} {f g : X ⟶ Y}
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
def smul {X Y : D} {f : X ⟶ Y}
    (a : k) (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (a • f) where
  middle := hf.middle
  projective := hf.projective
  left := a • hf.left
  right := hf.right
  fac := by rw [CategoryTheory.Linear.smul_comp, hf.fac]

/-- Postcomposition preserves projective factorization. -/
def postcomp {X Y Z : D} {f : X ⟶ Y}
    (hf : FactorsThroughProjective f) (g : Y ⟶ Z) :
    FactorsThroughProjective (f ≫ g) where
  middle := hf.middle
  projective := hf.projective
  left := hf.left
  right := hf.right ≫ g
  fac := by rw [← Category.assoc, hf.fac]

/-- Precomposition preserves projective factorization. -/
def precomp {W X Y : D} (g : W ⟶ X) {f : X ⟶ Y}
    (hf : FactorsThroughProjective f) :
    FactorsThroughProjective (g ≫ f) where
  middle := hf.middle
  projective := hf.projective
  left := g ≫ hf.left
  right := hf.right
  fac := by rw [Category.assoc, hf.fac]

end FactorsThroughProjective

/-- The linear subspace of morphisms which factor through projectives. -/
def factorSubmodule (X Y : D) : Submodule k (X ⟶ Y) where
  carrier := {f | Nonempty (FactorsThroughProjective f)}
  zero_mem' := ⟨FactorsThroughProjective.zero⟩
  add_mem' := by
    rintro f g ⟨hf⟩ ⟨hg⟩
    exact ⟨hf.add hg⟩
  smul_mem' := by
    rintro a f ⟨hf⟩
    exact ⟨hf.smul a⟩

/-- The projective-stable Hom space. -/
abbrev Hom (X Y : D) := (X ⟶ Y) ⧸ factorSubmodule (k := k) X Y

/-- The class of an ordinary morphism in projective-stable Hom. -/
abbrev mk {X Y : D} : (X ⟶ Y) →ₗ[k] Hom (k := k) X Y :=
  (factorSubmodule (k := k) X Y).mkQ

/-- Postcomposition on projective-stable Hom. -/
def postcomp (X : D) {Y Z : D} (g : Y ⟶ Z) :
    Hom (k := k) X Y →ₗ[k] Hom (k := k) X Z :=
  (factorSubmodule (k := k) X Y).mapQ
    (factorSubmodule (k := k) X Z)
    (CategoryTheory.Linear.rightComp k X g) (by
      intro f hf
      obtain ⟨hfactor⟩ := hf
      exact ⟨hfactor.postcomp g⟩)

@[simp]
theorem postcomp_mk (X : D) {Y Z : D} (g : Y ⟶ Z) (f : X ⟶ Y) :
    postcomp (k := k) X g (mk (k := k) f) = mk (k := k) (f ≫ g) :=
  rfl

omit [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
/-- If the identity factors through a projective, then the object itself is
projective. -/
theorem projective_of_id_factorsThroughProjective
    (X : D) (h : FactorsThroughProjective (𝟙 X)) : Projective X := by
  letI : Projective h.middle := h.projective
  let r : Retract X h.middle :=
    { i := h.left
      r := h.right
      retract := h.fac }
  exact r.projective

/-- A nonprojective object has a nonzero stable identity class. -/
theorem mk_id_ne_zero (X : D) (hX : ¬ Projective X) :
    mk (k := k) (𝟙 X) ≠ 0 := by
  intro hzero
  apply hX
  apply projective_of_id_factorsThroughProjective X
  exact Classical.choice ((Submodule.Quotient.mk_eq_zero _).mp hzero)

end MagnitudeConjecture.ProjectiveStable
