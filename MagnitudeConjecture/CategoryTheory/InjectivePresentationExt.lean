import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Degree-one Ext from a short injective presentation

For a short exact sequence `0 ⟶ T ⟶ I ⟶ C ⟶ 0` with injective
middle term, this file identifies `Ext¹(Y,T)` with the quotient of
`Hom(Y,C)` by maps which lift through `I`.  The equivalence is also proved
natural under pullback in `Y`.

This generic routine is adapted from the clean equidistribution
formalization.  It has no OP-specific dependency.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.InjectivePresentationExt

universe uk w v u

variable {k : Type uk} [CommRing k]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C]

/-- The connecting map of a short exact sequence, as a linear map. -/
def connectingLinear {S : ShortComplex C} (hS : S.ShortExact) (Y : C) :
    (Y ⟶ S.X₃) →ₗ[k] Ext.{w} Y S.X₁ 1 :=
  (hS.extClass.postcompOfLinear k Y (rfl : 0 + 1 = 1)).comp
    (Ext.linearEquiv₀ (R := k)).symm.toLinearMap

/-- Postcomposition with the second map of a short complex. -/
def presentationPostcompLinear (S : ShortComplex C) (Y : C) :
    (Y ⟶ S.X₂) →ₗ[k] (Y ⟶ S.X₃) :=
  CategoryTheory.Linear.rightComp k Y S.g

/-- The presentation coboundaries. -/
abbrev presentationRange (S : ShortComplex C) (Y : C) :
    Submodule k (Y ⟶ S.X₃) :=
  (presentationPostcompLinear (k := k) S Y).range

omit [HasExt C] in
@[simp]
theorem mem_presentationRange_iff (S : ShortComplex C) (Y : C)
    (f : Y ⟶ S.X₃) :
    f ∈ presentationRange (k := k) S Y ↔
      ∃ u : Y ⟶ S.X₂, u ≫ S.g = f := by
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
    change (Ext.mk₀ (u ≫ S.g)).comp hS.extClass (zero_add 1) = 0
    rw [← Ext.mk₀_comp_mk₀_assoc]
    simp
  · intro hf
    change (Ext.mk₀ f).comp hS.extClass (zero_add 1) = 0 at hf
    obtain ⟨x₂, hx₂⟩ :=
      Ext.covariant_sequence_exact₃
        (X := Y) hS (Ext.mk₀ f) (rfl : 0 + 1 = 1) hf
    refine ⟨Ext.linearEquiv₀ (R := k) x₂, ?_⟩
    apply (Ext.mk₀_bijective Y S.X₃).1
    change Ext.mk₀ (Ext.linearEquiv₀ (R := k) x₂ ≫ S.g) = Ext.mk₀ f
    rw [← Ext.mk₀_comp_mk₀]
    simpa using hx₂

/-- If `X ⟶ I` is essential, a simple map to its cokernel must vanish as
soon as the corresponding degree-one Ext group is trivial.  Exactness first
lifts the map to `I`; essentiality then forces every such simple map to die
under the cokernel projection. -/
theorem simple_to_cokernel_eq_zero_of_extOne_subsingleton
    {X I S : C} [Simple S] (f : X ⟶ I)
    (hessential : IsEssentialMono f)
    [Subsingleton (Ext.{w} S X 1)] (t : S ⟶ cokernel f) :
    t = 0 := by
  letI : Mono f := hessential.1
  let C₀ : ShortComplex C :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hC₀ : C₀.ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  have hboundary :
      (Ext.mk₀ t).comp hC₀.extClass (rfl : 0 + 1 = 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₃
    (X := S) hC₀ (Ext.mk₀ t) (rfl : 0 + 1 = 1) hboundary
  let qHom : S ⟶ I := Ext.addEquiv₀ q
  have hqt : qHom ≫ cokernel.π f = t := by
    apply (Ext.mk₀_bijective S (cokernel f)).1
    rw [← Ext.mk₀_comp_mk₀]
    simpa [C₀, qHom] using hq
  rw [← hqt]
  exact simple_comp_cokernel_π_eq_zero_of_isEssentialMono f hessential qHom

/-- If there are no nonzero maps from `Y` to the middle term, the connecting
map is injective.  This is the exact left-hand fragment of the long exact
`Hom`--`Ext` sequence, packaged for later use without choosing an injective
presentation. -/
theorem connectingLinear_injective_of_subsingleton_hom_middle
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Y ⟶ S.X₂)] :
    Function.Injective (connectingLinear (k := k) hS Y) := by
  rw [← LinearMap.ker_eq_bot,
    ← presentationRange_eq_connectingLinear_ker (k := k) hS Y]
  ext f
  simp only [mem_presentationRange_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨u, rfl⟩
    rw [Subsingleton.elim u 0, zero_comp]
  · rintro rfl
    exact ⟨0, by simp⟩

/-- Vanishing of degree-one extensions into the middle term makes the
connecting map surjective. -/
theorem connectingLinear_surjective_of_ext_subsingleton_middle
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Ext.{w} Y S.X₂ 1)] :
    Function.Surjective (connectingLinear (k := k) hS Y) := by
  intro xi
  have hzero : xi.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₃, hx₃⟩ :=
    Ext.covariant_sequence_exact₁
      (X := Y) hS xi hzero (rfl : 0 + 1 = 1)
  refine ⟨Ext.linearEquiv₀ (R := k) x₃, ?_⟩
  simpa [connectingLinear] using hx₃

/-- Injectivity of the middle term makes the connecting map surjective. -/
theorem connectingLinear_surjective
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) : Function.Surjective (connectingLinear (k := k) hS Y) := by
  intro xi
  have hzero : xi.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ :=
    Ext.covariant_sequence_exact₁
      (X := Y) hS xi hzero (rfl : 0 + 1 = 1)
  refine ⟨Ext.linearEquiv₀ (R := k) x₃, ?_⟩
  simpa [connectingLinear] using hx₃

/-- A short injective presentation computes degree-one Ext. -/
def quotientLinearEquivExtOne
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) :
    ((Y ⟶ S.X₃) ⧸ presentationRange (k := k) S Y) ≃ₗ[k]
      Ext.{w} Y S.X₁ 1 :=
  (Submodule.quotEquivOfEq
      (presentationRange (k := k) S Y)
      (connectingLinear (k := k) hS Y).ker
      (presentationRange_eq_connectingLinear_ker (k := k) hS Y)).trans
    ((connectingLinear (k := k) hS Y).quotKerEquivOfSurjective
      (connectingLinear_surjective (k := k) hS Y))

@[simp]
theorem quotientLinearEquivExtOne_mk
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) (f : Y ⟶ S.X₃) :
    quotientLinearEquivExtOne (k := k) hS Y (Submodule.Quotient.mk f) =
      (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
  simp [quotientLinearEquivExtOne, connectingLinear]

/-- Precomposition descends to the presentation quotient. -/
def precompQuotient (S : ShortComplex C)
    {Y' Y : C} (a : Y' ⟶ Y) :
    ((Y ⟶ S.X₃) ⧸ presentationRange (k := k) S Y) →ₗ[k]
      ((Y' ⟶ S.X₃) ⧸ presentationRange (k := k) S Y') :=
  (presentationRange (k := k) S Y).mapQ
    (presentationRange (k := k) S Y')
    (CategoryTheory.Linear.leftComp k S.X₃ a) (by
      intro f hf
      obtain ⟨u, rfl⟩ := hf
      refine ⟨a ≫ u, ?_⟩
      simp [presentationPostcompLinear, Category.assoc])

omit [HasExt C] in
@[simp]
theorem precompQuotient_mk
    (S : ShortComplex C) {Y' Y : C}
    (a : Y' ⟶ Y) (f : Y ⟶ S.X₃) :
    precompQuotient (k := k) S a (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (a ≫ f) := by
  rfl

/-- Pullback on degree-one Ext. -/
def pullbackLinear (S : ShortComplex C)
    {Y' Y : C} (a : Y' ⟶ Y) :
    Ext.{w} Y S.X₁ 1 →ₗ[k] Ext.{w} Y' S.X₁ 1 :=
  Ext.precompOfLinear (Ext.mk₀ a) k S.X₁ (zero_add 1)

/-- The connecting map commutes with precomposition. -/
theorem connectingLinear_precomp
    {S : ShortComplex C} (hS : S.ShortExact)
    {Y' Y : C} (a : Y' ⟶ Y) (f : Y ⟶ S.X₃) :
    connectingLinear (k := k) hS Y' (a ≫ f) =
      pullbackLinear (k := k) S a
        (connectingLinear (k := k) hS Y f) := by
  change
    (Ext.mk₀ (a ≫ f)).comp hS.extClass (zero_add 1) =
      (Ext.mk₀ a).comp
        ((Ext.mk₀ f).comp hS.extClass (zero_add 1)) (zero_add 1)
  symm
  exact Ext.mk₀_comp_mk₀_assoc a f hS.extClass

/-- The quotient description is natural under pullback. -/
theorem quotientLinearEquivExtOne_precompQuotient
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    {Y' Y : C} (a : Y' ⟶ Y)
    (q : (Y ⟶ S.X₃) ⧸ presentationRange (k := k) S Y) :
    quotientLinearEquivExtOne (k := k) hS Y'
        (precompQuotient (k := k) S a q) =
      pullbackLinear (k := k) S a
        (quotientLinearEquivExtOne (k := k) hS Y q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp [pullbackLinear]

end MagnitudeConjecture.InjectivePresentationExt
