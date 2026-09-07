import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalChangeSum

/-!
# Finite module families pushed from full control windows

A finite indecomposable module family contained in a full object-property
window may be pushed through any functor which preserves its chosen
indecomposables.  If that window functor is full and faithful, the original
and pushed families represent the same finite quotient of indices by
isomorphism classes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u₁ u₂ v

variable {k : Type v} [Field k]
variable {C : Type u₁} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D] [Linear k D]

namespace FiniteIndecomposableModuleFamily

variable (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
variable (P : ObjectProperty
  (FiniteDimensionalModuleCategory.{u₁, v, v, v} (C := C) k))
variable (hWP : ∀ i, P (W.obj i))
variable (F : CategoryTheory.Functor
  (ObjectProperty.FullSubcategory P)
  (FiniteDimensionalModuleCategory.{u₂, v, v, v} (C := D) k))
variable (hF : ∀ i, Indecomposable (F.obj ⟨W.obj i, hWP i⟩))

/-- Apply a functor on a full control window to every member of a finite
indecomposable module family contained in that window. -/
def mapWindowFunctor :
    FiniteIndecomposableModuleFamily (k := k) (C := D) where
  n := W.n
  obj i := F.obj ⟨W.obj i, hWP i⟩
  indecomposable := hF

/-- The map on represented isomorphism classes induced by a window functor. -/
noncomputable def isoClassWindowMap :
    W.IsoClass → (W.mapWindowFunctor P hWP F hF).IsoClass :=
  Quotient.lift
    (fun i ↦ Quotient.mk (W.mapWindowFunctor P hWP F hF).isoSetoid i)
    (by
      intro i j hij
      apply Quotient.sound
      exact hij.map fun e ↦ F.mapIso (ObjectProperty.isoMk P e))

theorem isoClassWindowMap_injective :
    F.Full → F.Faithful →
    Function.Injective (W.isoClassWindowMap P hWP F hF) := by
  intro hFull hFaithful
  letI : F.Full := hFull
  letI : F.Faithful := hFaithful
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ i =>
      induction r using Quotient.inductionOn with
      | _ j =>
          apply Quotient.sound
          have hmap : Nonempty
              (F.obj ⟨W.obj i, hWP i⟩ ≅ F.obj ⟨W.obj j, hWP j⟩) :=
            Quotient.exact hqr
          obtain ⟨e⟩ := hmap
          exact ⟨(ObjectProperty.ι P).mapIso
            (show (⟨W.obj i, hWP i⟩ : ObjectProperty.FullSubcategory P) ≅
                ⟨W.obj j, hWP j⟩ from F.preimageIso e)⟩

theorem isoClassWindowMap_surjective :
    Function.Surjective (W.isoClassWindowMap P hWP F hF) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ i =>
      exact ⟨Quotient.mk W.isoSetoid i, rfl⟩

/-- A full and faithful control-window functor preserves the finite set of
isomorphism classes represented by the family. -/
noncomputable def isoClassWindowEquiv :
    F.Full → F.Faithful →
    W.IsoClass ≃ (W.mapWindowFunctor P hWP F hF).IsoClass :=
  fun hFull hFaithful ↦
    Equiv.ofBijective (W.isoClassWindowMap P hWP F hF)
      ⟨W.isoClassWindowMap_injective P hWP F hF hFull hFaithful,
        W.isoClassWindowMap_surjective P hWP F hF⟩

/-- Reindex a sum over a pushed family by the original represented
isomorphism classes. -/
theorem sum_isoClass_mapWindowFunctor
    (hFull : F.Full) (hFaithful : F.Faithful)
    (f : (W.mapWindowFunctor P hWP F hF).IsoClass → ℤ) :
    (∑ q, f q) = ∑ q, f (W.isoClassWindowMap P hWP F hF q) := by
  exact (Equiv.sum_comp
    (W.isoClassWindowEquiv P hWP F hF hFull hFaithful) f).symm

end FiniteIndecomposableModuleFamily

end MagnitudeConjecture.CoveringHom
