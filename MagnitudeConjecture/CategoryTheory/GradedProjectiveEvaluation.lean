import MagnitudeConjecture.Graded.IdempotentProjective
import MagnitudeConjecture.Graded.ModuleBundling
import MagnitudeConjecture.CategoryTheory.GradedModuleSupport

/-! # Projective evaluation in the actual category of shifted graded modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))

/-- The graded regular module with the canonical bundled field action. -/
def regularObject : FiniteGradedModule R := (R.regularModuleGrading hmul).toBundled

/-- The actual graded module Ae attached to a homogeneous idempotent. -/
def principalObject (e : A) (he0 : e ∈ R.component 0) : FiniteGradedModule R :=
  (principalProjectiveGrading R hmul e he0).toBundled

/-- Evaluation at one identifies maps from a shifted regular module with the target degree. -/
def regularShiftHomEquiv (h1 : (1 : A) ∈ R.component 0)
    (r : ℤ) (X : ShiftedModule.{u,u} (R := R)) :
    ((⟨regularObject R hmul, r⟩ : ShiftedModule) ⟶ X) ≃ₗ[k]
      X.obj.grading.component (r - X.degree) :=
  R.regularHomEquiv hmul X.obj.grading h1 (r - X.degree)

/-- Evaluation at e gives the idempotent coordinate of the physical target degree. -/
def principalShiftHomEquiv (e : A) (he : e * e = e) (he0 : e ∈ R.component 0)
    (r : ℤ) (X : ShiftedModule.{u,u} (R := R)) :
    ((⟨principalObject R hmul e he0, r⟩ : ShiftedModule) ⟶ X) ≃ₗ[k]
      idempotentComponent R X.obj.grading e (r - X.degree) :=
  principalHomEquiv R hmul X.obj.grading e he he0 (r - X.degree)

/-- Projective evaluation on a module supported in [0,m] vanishes outside that interval. -/
theorem regularHom_eq_zero_outside (h1 : (1 : A) ∈ R.component 0)
    {m : ℕ} (X : ShiftedModule.{u,u} (R := R)) (hX : SupportedIn m X)
    (r : ℤ) (hr : r < 0 ∨ (m : ℤ) < r)
    (f : (⟨regularObject R hmul, r⟩ : ShiftedModule) ⟶ X) : f = 0 := by
  apply (regularShiftHomEquiv R hmul h1 r X).injective
  rw [map_zero]
  apply Subtype.ext
  have hd : X.obj.grading.component (r - X.degree) = ⊥ := by
    by_contra hn
    have hm : r ∈ shiftedSupport X := Finset.mem_image.mpr
      ⟨r - X.degree, (X.obj.grading.toVectorGrading.mem_support_iff _).mpr hn, by omega⟩
    have hb := hX r hm
    omega
  have hf := (regularShiftHomEquiv R hmul h1 r X f).property
  exact hd.le hf

/-- A projective evaluation is zero at every degree outside the actual support. -/
theorem principalHom_eq_zero_of_not_mem (e : A) (he : e * e = e) (he0 : e ∈ R.component 0)
    (X : ShiftedModule.{u,u} (R := R)) (r : ℤ) (hr : r ∉ shiftedSupport X)
    (f : (⟨principalObject R hmul e he0, r⟩ : ShiftedModule) ⟶ X) : f = 0 := by
  apply (principalShiftHomEquiv R hmul e he he0 r X).injective
  rw [map_zero]
  apply Subtype.ext
  have hx := (principalShiftHomEquiv R hmul e he he0 r X f).property.1
  by_contra hn
  apply hr
  apply Finset.mem_image.mpr
  refine ⟨r - X.degree, (X.obj.grading.toVectorGrading.mem_support_iff _).mpr ?_, by omega⟩
  intro hz
  have hx0 := (show X.obj.grading.component (r - X.degree) ≤ ⊥ from hz.le) hx
  exact hn hx0

/-- The same vanishing holds for every degree-zero idempotent coordinate. -/
theorem principalHom_eq_zero_outside (e : A) (he : e * e = e) (he0 : e ∈ R.component 0)
    {m : ℕ} (X : ShiftedModule.{u,u} (R := R)) (hX : SupportedIn m X)
    (r : ℤ) (hr : r < 0 ∨ (m : ℤ) < r)
    (f : (⟨principalObject R hmul e he0, r⟩ : ShiftedModule) ⟶ X) : f = 0 := by
  apply principalHom_eq_zero_of_not_mem R hmul e he he0 X r _ f
  intro hm
  have hb := hX r hm
  omega

end MagnitudeConjecture.Graded.FiniteGradedModule
