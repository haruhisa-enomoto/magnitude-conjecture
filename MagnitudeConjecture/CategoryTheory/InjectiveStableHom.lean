import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Factorization through injective objects

This file records the small categorical fragment of injective-stable Hom
needed by the finite-functor Auslander--Reiten argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MagnitudeConjecture.InjectiveStable

universe u v

variable {D : Type u} [Category.{v} D]

/-- A morphism factors through an injective object. -/
structure FactorsThroughInjective {U V : D} (f : U ⟶ V) where
  middle : D
  injective : Injective middle
  left : U ⟶ middle
  right : middle ⟶ V
  fac : left ≫ right = f

section Idempotent

variable [HasZeroMorphisms D] [IsIdempotentComplete D]

/-- An idempotent which factors through an injective vanishes if its source
has no nonzero injective retract. -/
theorem idempotent_eq_zero_of_factorsThroughInjective
    {T : D} (a : T ⟶ T)
    (haa : a ≫ a = a)
    (hfac : Nonempty (FactorsThroughInjective a))
    (hzero : ∀ {I : D} [Injective I], Retract I T → IsZero I) :
    a = 0 := by
  obtain ⟨I, i, e, hie, hei⟩ :=
    IsIdempotentComplete.idempotents_split T a haa
  let rIT : Retract I T :=
    { i := i
      r := e
      retract := hie }
  obtain ⟨F⟩ := hfac
  letI : Injective F.middle := F.injective
  let rIJ : Retract I F.middle :=
    { i := i ≫ F.left
      r := F.right ≫ e
      retract := by
        calc
          (i ≫ F.left) ≫ (F.right ≫ e) =
              i ≫ (F.left ≫ F.right) ≫ e := by simp [Category.assoc]
          _ = i ≫ a ≫ e := by rw [F.fac]
          _ = i ≫ (e ≫ i) ≫ e := by rw [hei]
          _ = 𝟙 I := by simp [Category.assoc, hie] }
  letI : Injective I := rIJ.injective
  have hI : IsZero I := hzero rIT
  have hi : i = 0 := hI.eq_of_src i 0
  calc
    a = e ≫ i := hei.symm
    _ = 0 := by rw [hi, comp_zero]

end Idempotent

namespace FactorsThroughInjective

universe uk

variable {k : Type uk} [Field k]
variable [Preadditive D] [CategoryTheory.Linear k D]
variable [HasZeroObject D] [HasBinaryBiproducts D]

/-- The zero map factors through the zero injective. -/
def zero {X Y : D} : FactorsThroughInjective (0 : X ⟶ Y) where
  middle := 0
  injective := inferInstance
  left := 0
  right := 0
  fac := by simp

/-- Injective factorizations are closed under addition. -/
def add {X Y : D} {f g : X ⟶ Y}
    (hf : FactorsThroughInjective f)
    (hg : FactorsThroughInjective g) :
    FactorsThroughInjective (f + g) := by
  letI : Injective hf.middle := hf.injective
  letI : Injective hg.middle := hg.injective
  exact
    { middle := hf.middle ⊞ hg.middle
      injective := inferInstance
      left := biprod.lift hf.left hg.left
      right := biprod.desc hf.right hg.right
      fac := by simp [hf.fac, hg.fac] }

/-- Injective factorizations are closed under scalar multiplication. -/
def smul {X Y : D} {f : X ⟶ Y}
    (a : k) (hf : FactorsThroughInjective f) :
    FactorsThroughInjective (a • f) where
  middle := hf.middle
  injective := hf.injective
  left := a • hf.left
  right := hf.right
  fac := by rw [CategoryTheory.Linear.smul_comp, hf.fac]

/-- Postcomposition preserves injective factorization. -/
def postcomp {X Y Z : D} {f : X ⟶ Y}
    (hf : FactorsThroughInjective f) (g : Y ⟶ Z) :
    FactorsThroughInjective (f ≫ g) where
  middle := hf.middle
  injective := hf.injective
  left := hf.left
  right := hf.right ≫ g
  fac := by rw [← Category.assoc, hf.fac]

/-- Precomposition preserves injective factorization. -/
def precomp {W X Y : D} (g : W ⟶ X) {f : X ⟶ Y}
    (hf : FactorsThroughInjective f) :
    FactorsThroughInjective (g ≫ f) where
  middle := hf.middle
  injective := hf.injective
  left := g ≫ hf.left
  right := hf.right
  fac := by rw [Category.assoc, hf.fac]

end FactorsThroughInjective

universe uk

variable {k : Type uk} [Field k]
variable [Preadditive D] [CategoryTheory.Linear k D]
variable [HasZeroObject D] [HasBinaryBiproducts D]

/-- The linear subspace of morphisms which factor through injectives. -/
def factorSubmodule (X Y : D) : Submodule k (X ⟶ Y) where
  carrier := {f | Nonempty (FactorsThroughInjective f)}
  zero_mem' := ⟨FactorsThroughInjective.zero⟩
  add_mem' := by
    rintro f g ⟨hf⟩ ⟨hg⟩
    exact ⟨hf.add hg⟩
  smul_mem' := by
    rintro a f ⟨hf⟩
    exact ⟨hf.smul a⟩

/-- The injective-stable Hom space. -/
abbrev Hom (X Y : D) := (X ⟶ Y) ⧸ factorSubmodule (k := k) X Y

/-- The class of an ordinary morphism in injective-stable Hom. -/
abbrev mk {X Y : D} : (X ⟶ Y) →ₗ[k] Hom (k := k) X Y :=
  (factorSubmodule (k := k) X Y).mkQ

/-- Postcomposition on injective-stable Hom. -/
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

/-- Precomposition on injective-stable Hom. -/
def precomp {W X : D} (g : W ⟶ X) (Y : D) :
    Hom (k := k) X Y →ₗ[k] Hom (k := k) W Y :=
  (factorSubmodule (k := k) X Y).mapQ
    (factorSubmodule (k := k) W Y)
    (CategoryTheory.Linear.leftComp k Y g) (by
      intro f hf
      obtain ⟨hfactor⟩ := hf
      exact ⟨hfactor.precomp g⟩)

@[simp]
theorem precomp_mk {W X : D} (g : W ⟶ X) (Y : D) (f : X ⟶ Y) :
    precomp (k := k) g Y (mk (k := k) f) = mk (k := k) (g ≫ f) :=
  rfl

omit [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] in
/-- If the identity factors through an injective, then the object itself is
injective. -/
theorem injective_of_id_factorsThroughInjective
    (X : D) (h : FactorsThroughInjective (𝟙 X)) : Injective X := by
  letI : Injective h.middle := h.injective
  let r : Retract X h.middle :=
    { i := h.left
      r := h.right
      retract := h.fac }
  exact r.injective

/-- A noninjective object has a nonzero injective-stable identity class. -/
theorem mk_id_ne_zero (X : D) (hX : ¬ Injective X) :
    mk (k := k) (𝟙 X) ≠ 0 := by
  intro hzero
  apply hX
  apply injective_of_id_factorsThroughInjective X
  exact Classical.choice ((Submodule.Quotient.mk_eq_zero _).mp hzero)

end MagnitudeConjecture.InjectiveStable
