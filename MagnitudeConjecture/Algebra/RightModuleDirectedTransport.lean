import MagnitudeConjecture.Algebra.RightModuleDirected

/-! # Directedness under fully faithful additive transport -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A B : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [FiniteDimensional k A] [FiniteDimensional k B]
variable [IsNoetherianRing Aᵐᵒᵖ] [IsNoetherianRing Bᵐᵒᵖ]

/-- A fully faithful additive functor into a directed module category
preserves cycle-freeness on any selected family identified with ambient
indecomposables. -/
theorem hasAcyclicNonzeroNonisomorphisms_of_fullyFaithful
    (S : FiniteIndecomposableSkeleton k A) (T : FiniteIndecomposableSkeleton k B)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (F : RightModule.FinitelyGeneratedCategory B ⥤ RightModule.FinitelyGeneratedCategory A)
    [F.Full] [F.Faithful] [F.Additive]
    (j : Fin T.n → Fin S.n) (e : ∀ i, F.obj (T.fgObj i) ≅ S.fgObj (j i)) :
    T.HasAcyclicNonzeroNonisomorphisms := by
  have hedge {x y : Fin T.n} (h : T.NonzeroNonisomorphism x y) :
      S.NonzeroNonisomorphism (j x) (j y) := by
    obtain ⟨f, hf, hn⟩ := h
    let g := (e x).inv ≫ F.map f ≫ (e y).hom
    refine ⟨g, ?_, ?_⟩
    · intro hg
      have hz : F.map f = 0 := by
        have hc := congrArg (fun q ↦ (e x).hom ≫ q ≫ (e y).inv) hg
        simpa [g] using hc
      exact hf (F.map_eq_zero_iff.mp hz)
    · intro hg
      letI : IsIso g := hg
      haveI : IsIso ((e x).inv ≫ F.map f ≫ (e y).hom) := hg
      haveI : IsIso (F.map f ≫ (e y).hom) :=
        IsIso.of_isIso_comp_left (e x).inv _
      haveI : IsIso (F.map f) := IsIso.of_isIso_comp_right _ (e y).hom
      exact hn (isIso_of_fully_faithful F f)
  intro i hc
  exact H (j i) (hc.lift j (fun _ _ h ↦ hedge h))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
