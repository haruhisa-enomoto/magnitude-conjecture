import MagnitudeConjecture.CategoryTheory.DeckOrbitResidualCoherentShift
import MagnitudeConjecture.CategoryTheory.DeckOrbitSubgroupResidualCommShift

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

noncomputable def deckOrbitTowerFlattenFunctor
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N) ⥤
      DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  exact deckOrbitRepresentativeFunctor ⋙
    D.deckOrbitResidualFlattenFunctor (k := k) N

instance deckOrbitTowerFlattenFunctor_additive
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitTowerFlattenFunctor (k := k) N).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  change (deckOrbitRepresentativeFunctor ⋙
    D.deckOrbitResidualFlattenFunctor (k := k) N).Additive
  infer_instance

instance deckOrbitTowerFlattenFunctor_linear
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitTowerFlattenFunctor (k := k) N).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  change (deckOrbitRepresentativeFunctor ⋙
    D.deckOrbitResidualFlattenFunctor (k := k) N).Linear k
  infer_instance

theorem deckOrbitTowerFlattenFunctor_obj
    (N : Subgroup G) [N.Normal]
    (q : MulAction.orbitRel.Quotient (G ⧸ N)
      (MulAction.orbitRel.Quotient N C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitTowerFlattenFunctor (k := k) N).obj
        (show DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N) from q) =
      (show DeckOrbitSkeleton C G from
        MagnitudeConjecture.CoveringAction.orbitTowerEquiv N q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  change (D.deckOrbitSubgroupFunctor N).obj
      (deckOrbitRepresentative
        (C := MulAction.orbitRel.Quotient N C) (G := G ⧸ N) q) =
    MagnitudeConjecture.CoveringAction.orbitTowerEquiv N q
  rw [← D.orbitTowerEquiv_mk_eq_deckOrbitSubgroupFunctor_obj N
    (deckOrbitRepresentative
      (C := MulAction.orbitRel.Quotient N C) (G := G ⧸ N) q)]
  congr 1
  exact deckOrbitRepresentative_mk
    (C := MulAction.orbitRel.Quotient N C) (G := G ⧸ N) q

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
