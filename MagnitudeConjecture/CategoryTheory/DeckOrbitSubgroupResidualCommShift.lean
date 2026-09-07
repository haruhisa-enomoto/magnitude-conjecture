import MagnitudeConjecture.CategoryTheory.DeckOrbitResidualLinear
import MagnitudeConjecture.CategoryTheory.DeckOrbitSubgroupFunctor
import MagnitudeConjecture.CategoryTheory.ShiftOrbitSubgroupResidualCommShift

/-!
# Residual descent on strict deck-orbit skeletons

For a normal subgroup `N ◁ G`, the functor from the strict `N`-orbit
skeleton to the strict `G`-orbit skeleton commutes coherently with the
residual `G / N` shift when the target is trivially shifted.  It therefore
descends through the residual shift-orbit category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe w

namespace CoherentDeckShift

universe u v uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The strict and nonskeletal subgroup functors commute with their
representative inclusions. -/
noncomputable def deckOrbitSubgroupRepresentativeNatIso
    (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    deckOrbitRepresentativeFunctor (C := C) (G := N) ⋙
        D.shiftOrbitSubgroupFunctor N ≅
      D.deckOrbitSubgroupFunctor N ⋙
        deckOrbitRepresentativeFunctor (C := C) (G := G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  refine NatIso.ofComponents (fun q ↦
    D.objectIsoDeckOrbitRepresentative
      (deckOrbitRepresentative (C := C) (G := N) q)) ?_
  intro q r f
  let X := deckOrbitRepresentative (C := C) (G := N) q
  let Y := deckOrbitRepresentative (C := C) (G := N) r
  change D.shiftOrbitSubgroupMap N X Y f.hom ≫
      (D.objectIsoDeckOrbitRepresentative Y).hom =
    (D.objectIsoDeckOrbitRepresentative X).hom ≫
      (D.objectIsoDeckOrbitRepresentative X).inv ≫
        D.shiftOrbitSubgroupMap N X Y f.hom ≫
          (D.objectIsoDeckOrbitRepresentative Y).hom
  simp

/-- Passing from the strict subgroup orbit skeleton to the strict ambient
orbit skeleton is linear. -/
instance deckOrbitSubgroupFunctor_linear (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.deckOrbitSubgroupFunctor N).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  constructor
  intro q r f a
  let X := deckOrbitRepresentative (C := C) (G := N) q
  let Y := deckOrbitRepresentative (C := C) (G := N) r
  apply InducedCategory.hom_ext
  change (D.objectIsoDeckOrbitRepresentative X).inv ≫
        D.shiftOrbitSubgroupMap N X Y (a • f.hom) ≫
          (D.objectIsoDeckOrbitRepresentative Y).hom =
      a • ((D.objectIsoDeckOrbitRepresentative X).inv ≫
        D.shiftOrbitSubgroupMap N X Y f.hom ≫
          (D.objectIsoDeckOrbitRepresentative Y).hom)
  rw [D.shiftOrbitSubgroupMap_smul]
  calc
    (D.objectIsoDeckOrbitRepresentative X).inv ≫
          (a • D.shiftOrbitSubgroupMap N X Y f.hom) ≫
            (D.objectIsoDeckOrbitRepresentative Y).hom =
        (D.objectIsoDeckOrbitRepresentative X).inv ≫
          (a • (D.shiftOrbitSubgroupMap N X Y f.hom ≫
            (D.objectIsoDeckOrbitRepresentative Y).hom)) := by
      rw [CategoryTheory.Linear.smul_comp]
    _ = a • ((D.objectIsoDeckOrbitRepresentative X).inv ≫
          (D.shiftOrbitSubgroupMap N X Y f.hom ≫
            (D.objectIsoDeckOrbitRepresentative Y).hom)) := by
      rw [CategoryTheory.Linear.comp_smul]
    _ = _ := rfl

/-- The strict subgroup orbit functor commutes coherently with residual
quotient shifts when the strict ambient orbit skeleton is trivially shifted. -/
@[implicit_reducible]
noncomputable def deckOrbitSubgroupResidualCommShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.deckOrbitResidualHasShift N
    letI := trivialHasShift
      (DeckOrbitSkeleton C G) (Additive (G ⧸ N))
    (D.deckOrbitSubgroupFunctor N).CommShift (Additive (G ⧸ N)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.deckOrbitResidualHasShift N
  letI := trivialHasShift
    (DeckOrbitSkeleton C G) (Additive (G ⧸ N))
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  let iN := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let iG := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let FN := D.deckOrbitSubgroupFunctor N
  let F := D.shiftOrbitSubgroupFunctor N
  letI : iN.CommShift (Additive (G ⧸ N)) :=
    D.deckOrbitRepresentativeResidualCommShift N
  letI : F.CommShift (Additive (G ⧸ N)) :=
    D.shiftOrbitSubgroupResidualCommShift N
  letI : iG.CommShift (Additive (G ⧸ N)) :=
    trivialFunctorCommShift iG
  let e : FN ⋙ iG ≅ iN ⋙ F :=
    (D.deckOrbitSubgroupRepresentativeNatIso N).symm
  exact Functor.CommShift.ofComp e (Additive (G ⧸ N))

/-- Residual descent of the strict subgroup orbit functor. -/
noncomputable def deckOrbitResidualFlattenFunctor
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    ShiftOrbitCategory (DeckOrbitSkeleton C N) (Additive (G ⧸ N)) ⥤
      DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (DeckOrbitSkeleton C G) (Additive (G ⧸ N))
  letI := D.deckOrbitSubgroupResidualCommShift N
  exact shiftOrbitDescendedFunctor (k := k)
    (A := Additive (G ⧸ N)) (D.deckOrbitSubgroupFunctor N)

instance deckOrbitResidualFlattenFunctor_additive
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitResidualFlattenFunctor (k := k) N).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (DeckOrbitSkeleton C G) (Additive (G ⧸ N))
  letI := D.deckOrbitSubgroupResidualCommShift N
  change (shiftOrbitDescendedFunctor (k := k)
    (A := Additive (G ⧸ N)) (D.deckOrbitSubgroupFunctor N)).Additive
  infer_instance

instance deckOrbitResidualFlattenFunctor_linear
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitResidualFlattenFunctor (k := k) N).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (DeckOrbitSkeleton C G) (Additive (G ⧸ N))
  letI := D.deckOrbitSubgroupResidualCommShift N
  change (shiftOrbitDescendedFunctor (k := k)
    (A := Additive (G ⧸ N)) (D.deckOrbitSubgroupFunctor N)).Linear k
  infer_instance

end CoherentDeckShift
end MagnitudeConjecture.CoveringHom
