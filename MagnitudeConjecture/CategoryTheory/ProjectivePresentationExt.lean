import MagnitudeConjecture.CategoryTheory.ProjectiveCover
import MagnitudeConjecture.CategoryTheory.ProjectiveStableHom
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Degree-one Ext from a short projective presentation

For a short exact sequence `0 ⟶ K ⟶ P ⟶ X ⟶ 0` with projective
middle term, this file identifies `Ext¹(X,Y)` with the quotient of
`Hom(K,Y)` by maps which extend across `P`.  The equivalence is also proved
natural under postcomposition in `Y`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.ProjectivePresentationExt

universe uk w v u

variable {k : Type uk} [CommRing k]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C]

/-- The connecting map of a short exact sequence, as a linear map. -/
def connectingLinear {S : ShortComplex C} (hS : S.ShortExact) (Y : C) :
    (S.X₁ ⟶ Y) →ₗ[k] Ext.{w} S.X₃ Y 1 :=
  (Ext.precompOfLinear hS.extClass k Y (rfl : 1 + 0 = 1)).comp
    (Ext.linearEquiv₀ (R := k)).symm.toLinearMap

/-- Precomposition with the first map of a short complex. -/
def presentationPrecompLinear (S : ShortComplex C) (Y : C) :
    (S.X₂ ⟶ Y) →ₗ[k] (S.X₁ ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y S.f

/-- The presentation coboundaries. -/
abbrev presentationRange (S : ShortComplex C) (Y : C) :
    Submodule k (S.X₁ ⟶ Y) :=
  (presentationPrecompLinear (k := k) S Y).range

omit [HasExt C] in
@[simp]
theorem mem_presentationRange_iff (S : ShortComplex C) (Y : C)
    (f : S.X₁ ⟶ Y) :
    f ∈ presentationRange (k := k) S Y ↔
      ∃ u : S.X₂ ⟶ Y, S.f ≫ u = f := by
  rfl

/-- Exactness identifies presentation coboundaries with the kernel of the
connecting map. -/
theorem presentationRange_eq_connectingLinear_ker
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) :
    presentationRange (k := k) S Y =
      (connectingLinear (k := k) hS Y).ker := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    change hS.extClass.comp (Ext.mk₀ (S.f ≫ u)) (add_zero 1) = 0
    rw [← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, hS.extClass_comp]
    simp
  · intro hf
    change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
    obtain ⟨x₂, hx₂⟩ :=
      Ext.contravariant_sequence_exact₁
        (Y := Y) hS (Ext.mk₀ f) (rfl : 1 + 0 = 1) hf
    refine ⟨Ext.linearEquiv₀ (R := k) x₂, ?_⟩
    apply (Ext.mk₀_bijective S.X₁ Y).1
    change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := k) x₂) = Ext.mk₀ f
    simpa only [← Ext.mk₀_comp_mk₀, Ext.mk₀_linearEquiv₀_apply] using hx₂

/-- Vanishing of degree-one extensions out of the middle term makes the
connecting map surjective. -/
theorem connectingLinear_surjective_of_ext_subsingleton_middle
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Ext.{w} S.X₂ Y 1)] :
    Function.Surjective (connectingLinear (k := k) hS Y) := by
  intro xi
  have hzero : (Ext.mk₀ S.g).comp xi (zero_add 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₁, hx₁⟩ :=
    Ext.contravariant_sequence_exact₃
      (Y := Y) hS xi hzero (rfl : 1 + 0 = 1)
  refine ⟨Ext.linearEquiv₀ (R := k) x₁, ?_⟩
  simpa [connectingLinear] using hx₁

/-- Projectivity of the middle term makes the connecting map surjective. -/
theorem connectingLinear_surjective
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) : Function.Surjective (connectingLinear (k := k) hS Y) := by
  intro xi
  have hzero : (Ext.mk₀ S.g).comp xi (zero_add 1) = 0 :=
    Ext.eq_zero_of_projective _
  obtain ⟨x₁, hx₁⟩ :=
    Ext.contravariant_sequence_exact₃
      (Y := Y) hS xi hzero (rfl : 1 + 0 = 1)
  refine ⟨Ext.linearEquiv₀ (R := k) x₁, ?_⟩
  simpa [connectingLinear] using hx₁

/-- A short projective presentation computes degree-one Ext. -/
def quotientLinearEquivExtOne
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) :
    ((S.X₁ ⟶ Y) ⧸ presentationRange (k := k) S Y) ≃ₗ[k]
      Ext.{w} S.X₃ Y 1 :=
  (Submodule.quotEquivOfEq
      (presentationRange (k := k) S Y)
      (connectingLinear (k := k) hS Y).ker
      (presentationRange_eq_connectingLinear_ker (k := k) hS Y)).trans
    ((connectingLinear (k := k) hS Y).quotKerEquivOfSurjective
      (connectingLinear_surjective (k := k) hS Y))

@[simp]
theorem quotientLinearEquivExtOne_mk
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (f : S.X₁ ⟶ Y) :
    quotientLinearEquivExtOne (k := k) hS Y (Submodule.Quotient.mk f) =
      hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
  simp [quotientLinearEquivExtOne, connectingLinear]

/-- Postcomposition descends to the presentation quotient. -/
def postcompQuotient (S : ShortComplex C)
    {Y Y' : C} (a : Y ⟶ Y') :
    ((S.X₁ ⟶ Y) ⧸ presentationRange (k := k) S Y) →ₗ[k]
      ((S.X₁ ⟶ Y') ⧸ presentationRange (k := k) S Y') :=
  (presentationRange (k := k) S Y).mapQ
    (presentationRange (k := k) S Y')
    (CategoryTheory.Linear.rightComp k S.X₁ a) (by
      intro f hf
      obtain ⟨u, rfl⟩ := hf
      refine ⟨u ≫ a, ?_⟩
      simp [presentationPrecompLinear, Category.assoc])

omit [HasExt C] in
@[simp]
theorem postcompQuotient_mk
    (S : ShortComplex C) {Y Y' : C}
    (a : Y ⟶ Y') (f : S.X₁ ⟶ Y) :
    postcompQuotient (k := k) S a (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (f ≫ a) := by
  rfl

/-- Pushforward on degree-one Ext. -/
def pushforwardLinear (S : ShortComplex C)
    {Y Y' : C} (a : Y ⟶ Y') :
    Ext.{w} S.X₃ Y 1 →ₗ[k] Ext.{w} S.X₃ Y' 1 :=
  Ext.postcompOfLinear (Ext.mk₀ a) k S.X₃ (add_zero 1)

/-- The connecting map commutes with postcomposition. -/
theorem connectingLinear_postcomp
    {S : ShortComplex C} (hS : S.ShortExact)
    {Y Y' : C} (a : Y ⟶ Y') (f : S.X₁ ⟶ Y) :
    connectingLinear (k := k) hS Y' (f ≫ a) =
      pushforwardLinear (k := k) S a
        (connectingLinear (k := k) hS Y f) := by
  change
    hS.extClass.comp (Ext.mk₀ (f ≫ a)) (add_zero 1) =
      (hS.extClass.comp (Ext.mk₀ f) (add_zero 1)).comp
        (Ext.mk₀ a) (add_zero 1)
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The quotient description is natural under pushforward. -/
theorem quotientLinearEquivExtOne_postcompQuotient
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    {Y Y' : C} (a : Y ⟶ Y')
    (q : (S.X₁ ⟶ Y) ⧸ presentationRange (k := k) S Y) :
    quotientLinearEquivExtOne (k := k) hS Y'
        (postcompQuotient (k := k) S a q) =
      pushforwardLinear (k := k) S a
        (quotientLinearEquivExtOne (k := k) hS Y q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp [pushforwardLinear, connectingLinear_postcomp]

end MagnitudeConjecture.ProjectivePresentationExt

namespace MagnitudeConjecture.ProjectivePresentationExt

universe uk w v u

variable {k : Type uk} [Field k]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C]

/-- The presentation quotient maps canonically onto projective-stable Hom:
every presentation coboundary factors through the projective middle term. -/
def presentationToProjectiveStable
    [HasBinaryBiproducts C]
    {S : ShortComplex C} [Projective S.X₂] (Y : C) :
    ((S.X₁ ⟶ Y) ⧸ presentationRange (k := k) S Y) →ₗ[k]
      ProjectiveStable.Hom (k := k) S.X₁ Y :=
  (presentationRange (k := k) S Y).mapQ
    (ProjectiveStable.factorSubmodule (k := k) S.X₁ Y)
    (LinearMap.id (R := k) (M := S.X₁ ⟶ Y)) (by
      intro f hf
      obtain ⟨u, rfl⟩ := hf
      exact ⟨{
        middle := S.X₂
        projective := inferInstance
        left := S.f
        right := u
        fac := rfl }⟩)

@[simp]
theorem presentationToProjectiveStable_mk
    [HasBinaryBiproducts C]
    {S : ShortComplex C} [Projective S.X₂] (Y : C) (f : S.X₁ ⟶ Y) :
    presentationToProjectiveStable (k := k) (S := S) Y
        (Submodule.Quotient.mk f) =
      ProjectiveStable.mk (k := k) f := by
  rfl

/-- The canonical map from the presentation quotient onto stable Hom is
surjective. -/
theorem presentationToProjectiveStable_surjective
    [HasBinaryBiproducts C]
    {S : ShortComplex C} [Projective S.X₂] (Y : C) :
    Function.Surjective
      (presentationToProjectiveStable (k := k) (S := S) Y) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk f, rfl⟩

/-- The presentation-to-stable quotient is natural under postcomposition. -/
theorem presentationToProjectiveStable_postcompQuotient
    [HasBinaryBiproducts C]
    {S : ShortComplex C} [Projective S.X₂]
    {Y Y' : C} (a : Y ⟶ Y')
    (q : (S.X₁ ⟶ Y) ⧸ presentationRange (k := k) S Y) :
    presentationToProjectiveStable (k := k) (S := S) Y'
        (postcompQuotient (k := k) S a q) =
      ProjectiveStable.postcomp (k := k) S.X₁ a
        (presentationToProjectiveStable (k := k) (S := S) Y q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- The canonical quotient from `Ext¹(S.X₃,Y)` onto
projective-stable `Hom(S.X₁,Y)`. -/
def extOneToProjectiveStable
    [HasBinaryBiproducts C]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) :
    Ext.{w} S.X₃ Y 1 →ₗ[k] ProjectiveStable.Hom (k := k) S.X₁ Y :=
  (presentationToProjectiveStable (k := k) (S := S) Y).comp
    (quotientLinearEquivExtOne (k := k) hS Y).symm.toLinearMap

/-- The canonical map from degree-one Ext onto stable Hom is surjective. -/
theorem extOneToProjectiveStable_surjective
    [HasBinaryBiproducts C]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) :
    Function.Surjective (extOneToProjectiveStable (k := k) hS Y) :=
  (presentationToProjectiveStable_surjective
      (k := k) (S := S) Y).comp
    (quotientLinearEquivExtOne (k := k) hS Y).symm.surjective

/-- The quotient from degree-one Ext to stable Hom is natural under
postcomposition. -/
theorem extOneToProjectiveStable_postcomp
    [HasBinaryBiproducts C]
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    {Y Y' : C} (a : Y ⟶ Y') (xi : Ext.{w} S.X₃ Y 1) :
    extOneToProjectiveStable (k := k) hS Y'
        (pushforwardLinear (k := k) S a xi) =
      ProjectiveStable.postcomp (k := k) S.X₁ a
        (extOneToProjectiveStable (k := k) hS Y xi) := by
  obtain ⟨q, rfl⟩ :=
    (quotientLinearEquivExtOne (k := k) hS Y).surjective xi
  rw [← quotientLinearEquivExtOne_postcompQuotient
    (k := k) hS a q]
  simp [extOneToProjectiveStable,
    presentationToProjectiveStable_postcompQuotient]

end MagnitudeConjecture.ProjectivePresentationExt
