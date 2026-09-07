import MagnitudeConjecture.CategoryTheory.ShiftOrbitWindow

/-!
# Coherent shifts from a left deck action

Mathlib's `HasShift` is a coherent right action by endofunctors.  The
manuscript writes its deck group as a left action.  This file records the
exact conversion convention: additive degree `g` is the deck transformation
`g⁻¹`.  It packages the coherent functor data as a `ShiftMkCore`, constructs
the actual `HasShift` instance, and supplies the object-action comparison
used by control-window separation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable (C : Type u) [Category.{v} C]
variable (G : Type w) [Group G] [MulAction G C]

/-- Coherent inverse deck-translation functors in Mathlib's right-action
orientation.  The functor at additive degree `g` acts on objects as the
inverse of the manuscript's left deck transformation `g`. -/
structure CoherentDeckShift where
  core : ShiftMkCore C (Additive G)
  objIso : ∀ (g : G) (X : C),
    (core.F (Additive.ofMul g)).obj X ≅ g⁻¹ • X

namespace CoherentDeckShift

variable {C G}

/-- The actual Mathlib shift instance constructed from coherent deck
translation functors. -/
@[implicit_reducible]
def hasShift (D : CoherentDeckShift C G) : HasShift C (Additive G) :=
  hasShiftMk C (Additive G) D.core

/-- The constructed shift functors agree objectwise with inverse left deck
translations. -/
def shiftObjectActionCompatibility (D : CoherentDeckShift C G) :
    letI := D.hasShift
    ShiftObjectActionCompatibility (C := C) (A := Additive G) := by
  letI := D.hasShift
  exact
    { objIso := fun a X ↦ by
        change (D.core.F a).obj X ≅ _
        exact D.objIso a.toMul X }

/-- Pairwise separation of distinct left deck translates gives shifted-Hom
orthogonality for the coherent deck shift on the selected window. -/
theorem windowShiftHomOrthogonal_of_pairwise_windowSeparated
    (D : CoherentDeckShift C G) {W : Set C}
    (separated :
      ∀ {g₁ g₂ : G}, g₁ ≠ g₂ →
        ∀ {X Y : C}, X ∈ W → Y ∈ W →
          ¬ CoveringSeparation.homInteraction (g₁ • X) (g₂ • Y)) :
    letI := D.hasShift
    WindowShiftHomOrthogonal (A := Additive G) W := by
  letI := D.hasShift
  exact CoveringHom.windowShiftHomOrthogonal_of_pairwise_windowSeparated
    D.shiftObjectActionCompatibility separated

section Linear

universe uK

variable {k : Type uK} [CommSemiring k]
variable [Preadditive C] [CategoryTheory.Linear k C]

theorem additiveShift (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive] :
    letI := D.hasShift
    ∀ a : Additive G, (shiftFunctor C a).Additive := by
  letI := D.hasShift
  intro a
  change (D.core.F a).Additive
  infer_instance

theorem linearShift (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Linear k] :
    letI := D.hasShift
    ∀ a : Additive G, (shiftFunctor C a).Linear k := by
  letI := D.hasShift
  intro a
  change (D.core.F a).Linear k
  infer_instance

/-- A separated window for coherent deck shifts has a full canonical functor
to the concrete shift-orbit category. -/
theorem windowIdentityComponentFunctor_full_of_pairwise_windowSeparated
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    {W : Set C}
    (separated :
      ∀ {g₁ g₂ : G}, g₁ ≠ g₂ →
        ∀ {X Y : C}, X ∈ W → Y ∈ W →
          ¬ CoveringSeparation.homInteraction (g₁ • X) (g₂ • Y)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (windowIdentityComponentFunctor (A := Additive G) W).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact windowIdentityComponentFunctor_fullOfShiftHomOrthogonal k
    (D.windowShiftHomOrthogonal_of_pairwise_windowSeparated separated)

end Linear

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
