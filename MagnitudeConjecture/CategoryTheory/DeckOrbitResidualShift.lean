import MagnitudeConjecture.CategoryTheory.DeckOrbitNormalTranslate
import MagnitudeConjecture.CategoryTheory.ShiftOrbitResidualShift

/-!
# The residual shift on the strict deck-orbit skeleton

For `N ◁ G`, the residual `G / N`-shift on the nonskeletal `N`-shift-orbit
category transports to the chosen deck-orbit skeleton.  Its degree-`q`
functor is literally the fixed strict translation by the chosen representative
`Quotient.out q`; the coherence is transported through the fully faithful
representative functor.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

private noncomputable def shiftMkCoreOfHasShift
    {B : Type u} [Category.{v} B]
    {A : Type w} [AddMonoid A] [HasShift B A] :
    ShiftMkCore B A where
  F := shiftFunctor B
  zero := shiftFunctorZero B A
  add := shiftFunctorAdd B
  assoc_hom_app := by
    intro a b c X
    simpa [shiftFunctorAdd'] using
      shiftFunctorAdd_assoc_hom_app a b c X
  zero_add_hom_app := shiftFunctorAdd_zero_add_hom_app
  add_zero_hom_app := shiftFunctorAdd_add_zero_hom_app

private theorem hasShiftMk_shiftMkCoreOfHasShift_eq
    {B : Type u} [Category.{v} B]
    {A : Type w} [AddMonoid A] (K : ShiftMkCore B A) :
    letI := hasShiftMk B A K
    hasShiftMk B A shiftMkCoreOfHasShift = hasShiftMk B A K := by
  letI := hasShiftMk B A K
  rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

set_option backward.isDefEq.respectTransparency false in
/-- Strict normal translation intertwines the representative inclusion with
normal translation on the nonskeletal orbit category. -/
noncomputable def deckOrbitNormalTranslateRepresentativeNatIso
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.deckOrbitNormalTranslateFunctor N g ⋙
        deckOrbitRepresentativeFunctor (C := C) (G := N) ≅
      deckOrbitRepresentativeFunctor (C := C) (G := N) ⋙
        D.shiftOrbitNormalTranslateFunctor N g := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  refine NatIso.ofComponents
    (fun q : DeckOrbitSkeleton C N ↦
      (D.shiftOrbitNormalTranslateRepresentativeIso N g q).symm) ?_
  intro q r f
  dsimp only [Functor.comp_obj, Functor.comp_map,
    deckOrbitRepresentativeFunctor, inducedFunctor_obj,
    inducedFunctor_map]
  change (D.deckOrbitNormalTranslateMap N g f).hom ≫
      (D.shiftOrbitNormalTranslateRepresentativeIso N g r).inv =
    (D.shiftOrbitNormalTranslateRepresentativeIso N g q).inv ≫
      (D.shiftOrbitNormalTranslateFunctor N g).map f.hom
  simp [deckOrbitNormalTranslateMap]

set_option backward.isDefEq.respectTransparency false in
/-- The strict normal translation by the chosen representative of a quotient
degree intertwines the representative inclusion with the residual shift. -/
noncomputable def deckOrbitResidualIntertwiningIso
    (N : Subgroup G) [N.Normal] (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := D.shiftOrbitResidualHasShift N
    D.deckOrbitNormalTranslateFunctor N
          (normalQuotientRepresentative N a.toMul) ⋙
        deckOrbitRepresentativeFunctor (C := C) (G := N) ≅
      deckOrbitRepresentativeFunctor (C := C) (G := N) ⋙
        shiftFunctor (ShiftOrbitCategory C (Additive N)) a := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.shiftOrbitResidualHasShift N
  exact D.deckOrbitNormalTranslateRepresentativeNatIso N
    (normalQuotientRepresentative N a.toMul)

@[implicit_reducible]
private noncomputable def deckOrbitResidualTransportHasShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    HasShift (DeckOrbitSkeleton C N) (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.shiftOrbitResidualHasShift N
  let F := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  let s := fun a : Additive (G ⧸ N) ↦
    D.deckOrbitNormalTranslateFunctor N
      (normalQuotientRepresentative N a.toMul)
  let i := fun a ↦ D.deckOrbitResidualIntertwiningIso N a
  exact hF.hasShift s i

/-- The coherent residual `G / N`-translation core on the strict deck-orbit
skeleton. -/
noncomputable def deckOrbitResidualCore
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ShiftMkCore (DeckOrbitSkeleton C N) (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.deckOrbitResidualTransportHasShift N
  exact shiftMkCoreOfHasShift

/-- The residual `G / N`-shift on the strict deck-orbit skeleton. -/
@[implicit_reducible]
noncomputable def deckOrbitResidualHasShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    HasShift (DeckOrbitSkeleton C N) (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact D.deckOrbitResidualTransportHasShift N

/-- Rebuilding the transported residual shift from its exported coherent core
does not change the `HasShift` instance.  This is the controlled comparison
used when a construction needs both the transport and coherent-deck APIs. -/
theorem hasShiftMk_deckOrbitResidualCore_eq
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    hasShiftMk (DeckOrbitSkeleton C N) (Additive (G ⧸ N))
        (D.deckOrbitResidualCore N) =
      D.deckOrbitResidualHasShift N := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  unfold deckOrbitResidualCore deckOrbitResidualHasShift
  unfold deckOrbitResidualTransportHasShift
  exact hasShiftMk_shiftMkCoreOfHasShift_eq _

/-- The representative inclusion intertwines the strict residual shift with
the nonskeletal residual shift, including zero and addition coherence. -/
@[implicit_reducible]
noncomputable def deckOrbitRepresentativeResidualCommShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := D.shiftOrbitResidualHasShift N
    letI := D.deckOrbitResidualHasShift N
    (deckOrbitRepresentativeFunctor (C := C) (G := N)).CommShift
      (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.shiftOrbitResidualHasShift N
  let F := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  let s := fun a : Additive (G ⧸ N) ↦
    D.deckOrbitNormalTranslateFunctor N
      (normalQuotientRepresentative N a.toMul)
  let i := fun a ↦ D.deckOrbitResidualIntertwiningIso N a
  letI : HasShift (DeckOrbitSkeleton C N) (Additive (G ⧸ N)) :=
    D.deckOrbitResidualHasShift N
  exact Functor.CommShift.ofHasShiftOfFullyFaithful hF s i

instance deckOrbitResidualCore_additive
    (N : Subgroup G) [N.Normal] (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    ((D.deckOrbitResidualCore N).F a).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  change (D.deckOrbitNormalTranslateFunctor N
    (normalQuotientRepresentative N a.toMul)).Additive
  infer_instance

/-- Every strict residual shift functor is additive. -/
theorem deckOrbitResidualAdditiveShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := D.deckOrbitResidualHasShift N
    ∀ a : Additive (G ⧸ N),
      (shiftFunctor (DeckOrbitSkeleton C N) a).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := D.deckOrbitResidualHasShift N
  intro a
  change (D.deckOrbitNormalTranslateFunctor N
    (normalQuotientRepresentative N a.toMul)).Additive
  infer_instance

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
