import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckShift
import MagnitudeConjecture.Combinatorics.FiniteOrbitCarrier

/-!
# Finite orbit sets for invariant deletion stages

The orbit set of an invariant object-deletion category embeds into the orbit
set of its ambient category by forgetting the surviving-object proof and the
Hom quotient.  Hence finite ambient orbit sets give finite orbit sets at every
deletion stage.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

universe u v w z

variable {k : Type z} [CommRing k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type w} [Group G] [MulAction G C]

/-- Forgetting from an invariant deletion stage to ambient objects induces a
map of strict orbit sets. -/
def deletionOrbitQuotientToAmbient
    (S : Set C) (hS : ActionInvariant (G := G) S) :
    letI := deletionMulAction (k := k) S hS
    MulAction.orbitRel.Quotient G (DeletionCategory (k := k) C S) →
      MulAction.orbitRel.Quotient G C := by
  letI := deletionMulAction (k := k) S hS
  intro q
  refine Quotient.liftOn' q
    (fun X ↦ (Quotient.mk'' X.obj.as : MulAction.orbitRel.Quotient G C)) ?_
  intro X Y hXY
  apply Quotient.sound
  change X.obj.as ∈ MulAction.orbit G Y.obj.as
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hXY
  apply MulAction.mem_orbit_iff.mpr
  exact ⟨g, by
    simpa only [deletion_smul_obj_as] using
      (congrArg
        (fun Z : DeletionCategory (k := k) C S ↦ Z.obj.as) hg)⟩

/-- The forgetful map on deletion-stage orbit sets is injective. -/
theorem deletionOrbitQuotientToAmbient_injective
    (S : Set C) (hS : ActionInvariant (G := G) S) :
    letI := deletionMulAction (k := k) S hS
    Function.Injective (deletionOrbitQuotientToAmbient (k := k) C S hS) := by
  letI := deletionMulAction (k := k) S hS
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ X =>
      induction r using Quotient.inductionOn' with
      | _ Y =>
          apply Quotient.sound
          apply MulAction.mem_orbit_iff.mpr
          change (Quotient.mk'' X.obj.as :
              MulAction.orbitRel.Quotient G C) =
            Quotient.mk'' Y.obj.as at hqr
          have hamb := Quotient.exact hqr
          obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hamb
          refine ⟨g, ?_⟩
          apply ObjectProperty.FullSubcategory.ext
          apply CategoryTheory.Quotient.ext
          simpa only [deletion_smul_obj_as] using hg

/-- An invariant deletion stage has finitely many strict orbits whenever
the ambient category does. -/
theorem finite_deletionOrbitQuotient
    (S : Set C) (hS : ActionInvariant (G := G) S)
    [Finite (MulAction.orbitRel.Quotient G C)] :
    letI := deletionMulAction (k := k) S hS
    Finite
      (MulAction.orbitRel.Quotient G
        (DeletionCategory (k := k) C S)) := by
  letI := deletionMulAction (k := k) S hS
  exact Finite.of_injective
    (deletionOrbitQuotientToAmbient (k := k) C S hS)
    (deletionOrbitQuotientToAmbient_injective (k := k) C S hS)

end MagnitudeConjecture.ObjectDeletion
