import MagnitudeConjecture.CategoryTheory.DeckOrbitResidualShift

/-!
# The coherent residual deck shift

For a normal subgroup `N ◁ G`, the strict residual shift on the chosen
`N`-orbit skeleton is compatible with the canonical `G / N` action on
`N`-orbits.  This packages that shift core and object identification as a
`CoherentDeckShift` for the quotient group.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

set_option backward.isDefEq.respectTransparency false in
/-- On objects, strict residual degree `q` is inverse translation by the
quotient action. -/
theorem deckOrbitResidualCore_obj_eq_inv_smul
    (N : Subgroup G) [N.Normal] (q : G ⧸ N)
    (X : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      DeckOrbitSkeleton C N) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    ((D.deckOrbitResidualCore N).F (Additive.ofMul q)).obj X =
      q⁻¹ • X := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  have hq :
      (((normalQuotientRepresentative N q)⁻¹ : G) : G ⧸ N) = q⁻¹ := by
    convert congrArg (fun z : G ⧸ N ↦ z⁻¹)
      (normalQuotientRepresentative_mk N q) using 1
    simp
  change Quotient.mk''
      ((normalQuotientRepresentative N q)⁻¹ •
        deckOrbitRepresentative (C := C) (G := N)
          (show MulAction.orbitRel.Quotient N C from X)) = q⁻¹ • X
  conv_rhs =>
    rw [← deckOrbitRepresentative_mk (C := C) (G := N)
      (show MulAction.orbitRel.Quotient N C from X)]
  rw [← hq]
  rw [MagnitudeConjecture.CoveringAction.quotient_smul_orbit_mk]

/-- The strict residual core, together with the quotient action on orbit
objects, is a coherent deck shift by `G / N`. -/
noncomputable def deckOrbitResidualCoherentDeckShift
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    CoherentDeckShift (DeckOrbitSkeleton C N) (G ⧸ N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  exact
    { core := D.deckOrbitResidualCore N
      objIso := fun q X ↦
        eqToIso (D.deckOrbitResidualCore_obj_eq_inv_smul N q X) }

/-- The shift exported by the coherent residual deck package is the already
constructed transported residual shift. -/
theorem deckOrbitResidualCoherentDeckShift_hasShift_eq
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    (D.deckOrbitResidualCoherentDeckShift N).hasShift =
      D.deckOrbitResidualHasShift N := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  change hasShiftMk (DeckOrbitSkeleton C N) (Additive (G ⧸ N))
      (D.deckOrbitResidualCore N) = D.deckOrbitResidualHasShift N
  exact D.hasShiftMk_deckOrbitResidualCore_eq N

/-- Freeness of the ambient action descends to the canonical residual action
on the strict subgroup-orbit skeleton. -/
instance deckOrbitResidualIsCancelSMul
    [IsCancelSMul G C] (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    IsCancelSMul (G ⧸ N) (DeckOrbitSkeleton C N) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  change IsCancelSMul (G ⧸ N) (MulAction.orbitRel.Quotient N C)
  infer_instance

/-- The additive structure on the residual core is visible through its
packaged coherent deck shift. -/
instance deckOrbitResidualCoherentDeckShift_core_additive
    (N : Subgroup G) [N.Normal] (a : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    ((D.deckOrbitResidualCoherentDeckShift N).core.F a).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  change ((D.deckOrbitResidualCore N).F a).Additive
  infer_instance

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
