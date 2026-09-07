import MagnitudeConjecture.CategoryTheory.HomInteractionSeparation
import MagnitudeConjecture.CategoryTheory.ShiftOrbitDecomposition

/-!
# Shift-orbit functors on finite control windows

The manuscript uses the orbit functor only on a finite full window, which is
not itself invariant under deck transformations.  This file restricts the
source of the ambient shift-orbit functor to such a window while retaining
ambient shifted Hom summands.  It also connects pairwise separation for a
strict object action to the exact shifted-Hom orthogonality predicate.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK

variable {k : Type uK} [CommSemiring k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- The inclusion of a full set-valued window into the ambient category. -/
abbrev windowInclusion (W : Set C) : CoveringSeparation.WindowCategory W ⥤ C :=
  (show ObjectProperty C from fun X ↦ X ∈ W).ι

/-- The ambient degree-zero orbit functor restricted to a full control
window.  The target remains the ambient orbit category because the window
need not be shift-invariant. -/
noncomputable def windowIdentityComponentFunctor (W : Set C) :
    CoveringSeparation.WindowCategory W ⥤ ShiftOrbitCategory C A :=
  windowInclusion W ⋙ ShiftOrbitCategory.identityComponentFunctor

/-- Ambient shifted Homs between two objects of a full window, indexed by the
multiplicative wrapper of the additive shift group. -/
abbrev windowMultiplicativeShiftHom (W : Set C)
    (X Y : CoveringSeparation.WindowCategory W) (a : Multiplicative A) :=
  multiplicativeShiftHom X.1 Y.1 a

/-- The restricted concrete orbit functor has the same tautological Gabriel
Hom decomposition as the ambient functor. -/
noncomputable def windowIdentityComponentFunctorOrbitHomDecomposition
    (W : Set C) :
    FunctorOrbitHomDecomposition (k := k)
      (windowIdentityComponentFunctor (A := A) W)
      (windowMultiplicativeShiftHom (A := A) W) where
  sourceEquiv X Y :=
    (InducedCategory.homLinearEquiv (R := k)).trans
      (shiftHomZeroLinearEquiv (A := A) X.1 Y.1)
  homDecomposition X Y :=
    identityComponentOrbitHomDecomposition (A := A) X.1 Y.1
  map_compat X Y f := by
    rfl

/-- Every nonzero ambient shift Hom between objects of the chosen window
vanishes. -/
def WindowShiftHomOrthogonal (W : Set C) : Prop :=
  ∀ (X Y : CoveringSeparation.WindowCategory W) (a : A),
    a ≠ 0 → Subsingleton (ShiftHom X.1 Y.1 a)

omit [Preadditive C] [∀ a : A, (shiftFunctor C a).Additive] in
theorem windowMultiplicativeShiftHom_translateHomOrthogonal
    {W : Set C} (h : WindowShiftHomOrthogonal (A := A) W) :
    TranslateHomOrthogonal (windowMultiplicativeShiftHom (A := A) W) := by
  intro X Y a ha
  apply h X Y a.toAdd
  intro hzero
  apply ha
  exact Multiplicative.toAdd.injective (by simpa using hzero)

/-- Shift-Hom orthogonality on a window makes the restricted concrete orbit
functor full. -/
theorem windowIdentityComponentFunctor_fullOfShiftHomOrthogonal
    (k : Type uK) [CommSemiring k] [CategoryTheory.Linear k C]
    [∀ a : A, (shiftFunctor C a).Linear k]
    {W : Set C} (h : WindowShiftHomOrthogonal (A := A) W) :
    (windowIdentityComponentFunctor (A := A) W).Full :=
  (windowIdentityComponentFunctorOrbitHomDecomposition
    (k := k) (A := A) W).fullOfOrthogonal
    (windowMultiplicativeShiftHom_translateHomOrthogonal h)

/-- The restricted concrete window orbit functor is faithful without any
orthogonality hypothesis. -/
theorem windowIdentityComponentFunctor_faithful
    (W : Set C) :
    (windowIdentityComponentFunctor (A := A) W).Faithful := by
  constructor
  intro X Y f g hfg
  apply InducedCategory.homEquiv.injective
  apply ShiftOrbitCategory.identityComponentFunctor_map_injective
    (C := C) (A := A) X.1 Y.1
  exact hfg

/-- Compatibility between a coherent additive right shift and a strict left
multiplicative action on objects.  The inverse converts the two action
conventions.  Only the objectwise comparison is needed to transfer
Hom-orthogonality; the eventual universal-cover construction must supply it
from its deck functors. -/
structure ShiftObjectActionCompatibility
    [MulAction (Multiplicative A) C] where
  objIso : ∀ (a : A) (X : C),
    (shiftFunctor C a).obj X ≅ (Multiplicative.ofAdd a)⁻¹ • X

variable [MulAction (Multiplicative A) C]

omit [Preadditive C] [∀ a : A, (shiftFunctor C a).Additive] in
/-- Pairwise Hom-interaction separation of distinct translates of a window
implies the exact shifted-Hom orthogonality needed by its orbit functor. -/
theorem windowShiftHomOrthogonal_of_pairwise_windowSeparated
    (D : ShiftObjectActionCompatibility (C := C) (A := A))
    {W : Set C}
    (separated :
      ∀ {g₁ g₂ : Multiplicative A}, g₁ ≠ g₂ →
        ∀ {X Y : C}, X ∈ W → Y ∈ W →
          ¬ CoveringSeparation.homInteraction (g₁ • X) (g₂ • Y)) :
    WindowShiftHomOrthogonal (A := A) W := by
  intro X Y a ha
  have hmul : (1 : Multiplicative A) ≠ (Multiplicative.ofAdd a)⁻¹ := by
    intro h
    apply ha
    exact Multiplicative.ofAdd.injective
      (by simpa using (inv_eq_one.mp h.symm))
  have hsep :
      ¬ CoveringSeparation.homInteraction X.1
        ((Multiplicative.ofAdd a)⁻¹ • Y.1) := by
    simpa only [one_smul] using
      separated hmul X.property Y.property
  letI : Subsingleton (X.1 ⟶ (Multiplicative.ofAdd a)⁻¹ • Y.1) :=
    CoveringSeparation.hom_subsingleton_of_not_homInteraction hsep
  constructor
  intro f g
  apply (cancel_mono (D.objIso a Y.1).hom).1
  exact Subsingleton.elim _ _

end MagnitudeConjecture.CoveringHom
