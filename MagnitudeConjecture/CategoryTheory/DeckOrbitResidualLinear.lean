import MagnitudeConjecture.CategoryTheory.DeckOrbitResidualCoherentShift
import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslateLinear
import MagnitudeConjecture.CategoryTheory.LinearModuleDeckShift

/-!
# Residual shifts on the strict linear module category

The strict residual shift functors are linear.  Their coherent core therefore
induces inverse-precomposition shifts on linear modules over the deck-orbit
skeleton.  Degree `a` on modules evaluates by the strict orbit translation in
degree `-a`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable {k : Type uK} [CommRing k] [CategoryTheory.Linear k C]
variable [∀ a : Additive G, (D.core.F a).Linear k]

instance deckOrbitResidualCore_linear
    (N : Subgroup G) [N.Normal] (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    ((D.deckOrbitResidualCore N).F a).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  change (D.deckOrbitNormalTranslateFunctor N
    (normalQuotientRepresentative N a.toMul)).Linear k
  infer_instance

/-- The linear structure on the residual core is visible through its
packaged coherent deck shift. -/
instance deckOrbitResidualCoherentDeckShift_core_linear
    (N : Subgroup G) [N.Normal] (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    ((D.deckOrbitResidualCoherentDeckShift N).core.F a).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  change ((D.deckOrbitResidualCore N).F a).Linear k
  infer_instance

/-- Every strict residual shift functor is linear. -/
theorem deckOrbitResidualLinearShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.deckOrbitResidualHasShift N
    ∀ a : Additive (G ⧸ N),
      (shiftFunctor (DeckOrbitSkeleton C N) a).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.deckOrbitResidualHasShift N
  intro a
  change (D.deckOrbitNormalTranslateFunctor N
    (normalQuotientRepresentative N a.toMul)).Linear k
  infer_instance

/-- The residual quotient group acts coherently on linear modules over the
strict deck-orbit skeleton by inverse precomposition. -/
@[implicit_reducible]
noncomputable def deckOrbitResidualLinearModuleHasShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    HasShift
      (LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C N) k)
      (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  exact linearModuleCategoryHasShift (k := k)
    (D.deckOrbitResidualCore N)

/-- Forgetting the linear-module subtype identifies residual degree `a` with
inverse precomposition by strict residual degree `-a`. -/
noncomputable def deckOrbitResidualLinearModuleShiftUnderlyingIso
    (N : Subgroup G) [N.Normal]
    (M : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C N) k)
    (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : HasShift
        (LinearModuleCategory.{u, max v w, uK, uM}
          (C := DeckOrbitSkeleton C N) k)
        (Additive (G ⧸ N)) :=
      D.deckOrbitResidualLinearModuleHasShift N
    (IsLinearModule (C := DeckOrbitSkeleton C N) k).ι.obj (M⟦a⟧) ≅
      (D.deckOrbitResidualCore N).F (-a) ⋙ M.obj := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : HasShift
      (LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C N) k)
      (Additive (G ⧸ N)) :=
    D.deckOrbitResidualLinearModuleHasShift N
  exact linearModuleShiftUnderlyingIso (k := k)
    (D.deckOrbitResidualCore N) M a

/-- Evaluation of the residual module shift is inverse precomposition by the
strict deck-orbit translation in degree `-a`. -/
noncomputable def deckOrbitResidualLinearModuleShiftEvaluationIso
    (N : Subgroup G) [N.Normal]
    (M : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C N) k)
    (a : Additive (G ⧸ N))
    (q : MulAction.orbitRel.Quotient N C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : HasShift
        (LinearModuleCategory.{u, max v w, uK, uM}
          (C := DeckOrbitSkeleton C N) k)
        (Additive (G ⧸ N)) :=
      D.deckOrbitResidualLinearModuleHasShift N
    (((IsLinearModule (C := DeckOrbitSkeleton C N) k).ι.obj
      (M⟦a⟧)).obj q) ≅
      M.obj.obj ((D.deckOrbitNormalTranslateFunctor N
        (normalQuotientRepresentative N (-a).toMul)).obj q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : HasShift
      (LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C N) k)
      (Additive (G ⧸ N)) :=
    D.deckOrbitResidualLinearModuleHasShift N
  exact (D.deckOrbitResidualLinearModuleShiftUnderlyingIso N M a).app q

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
