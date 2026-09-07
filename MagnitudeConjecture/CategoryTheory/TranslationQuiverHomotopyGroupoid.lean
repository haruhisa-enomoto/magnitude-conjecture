import MagnitudeConjecture.Combinatorics.FreeGroupResidualFinite
import MagnitudeConjecture.CategoryTheory.QuiverFreeGroupoid
import MagnitudeConjecture.CategoryTheory.TranslationQuiverDeckAction

/-!
# The mesh-homotopy groupoid of a translation quiver

The augmented-walk homotopy relation defines a groupoid whose morphisms are
homotopy classes of walks between arbitrary vertices.  Reversal identifies
the concrete based fundamental group with the endomorphism group at the base
vertex (with the multiplication-order correction built into the equivalence).

This formulation isolates the Bongartz--Gabriel graph-comparison input: once
the homotopy groupoid is proved free, connectedness makes its vertex group
free by the graph theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe u w

variable {Q : Type u} [Quiver.{w} Q]

/-- A type synonym carrying the groupoid of augmented walks modulo mesh
homotopy. -/
def HomotopyGroupoid (_T : RightMeshData.{u, w} Q) := Q

namespace HomotopyGroupoid

instance (T : RightMeshData Q) :
    Quiver (HomotopyGroupoid T) where
  Hom X Y := Quotient (homotopySetoid T
    (show Q from X) (show Q from Y))

/-- Concatenation of augmented walks, descended through mesh homotopy. -/
def homComp (T : RightMeshData Q) {X Y Z : HomotopyGroupoid T} :
    (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z) :=
  Quotient.map₂ (compWalk T) fun _p p' hp q _q' hq ↦
    Homotopic.trans (Homotopic.comp hp q)
      (Homotopic.left_comp T p' hq)

instance (T : RightMeshData Q) : Category (HomotopyGroupoid T) where
  id X := Quotient.mk _ Quiver.Path.nil
  comp := homComp T
  assoc f g h := by
    induction f, g, h using Quotient.inductionOn₃ with
    | _ p q r =>
        exact congrArg (Quotient.mk _)
          (Quiver.Path.comp_assoc p q r)
  id_comp f := by
    induction f using Quotient.inductionOn with
    | _ p =>
        exact congrArg (Quotient.mk _)
          (Quiver.Path.nil_comp p)
  comp_id f := by
    induction f using Quotient.inductionOn with
    | _ p =>
        exact congrArg (Quotient.mk _)
          (Quiver.Path.comp_nil p)

/-- Reversal of augmented walks, descended through mesh homotopy. -/
def homInv (T : RightMeshData Q) {X Y : HomotopyGroupoid T} :
    (X ⟶ Y) → (Y ⟶ X) :=
  Quotient.map (reverseWalk T) fun _ _ h ↦ Homotopic.reverse T h

instance (T : RightMeshData Q) : Groupoid (HomotopyGroupoid T) where
  inv := homInv T
  inv_comp f := by
    induction f using Quotient.inductionOn with
    | _ p =>
        apply Quotient.sound
        change Homotopic T _
          ((reverseWalk T p).comp p) Quiver.Path.nil
        simpa only [Quiver.Path.nil_comp] using
          Homotopic.reverse_comp T Quiver.Path.nil p
  comp_inv f := by
    induction f using Quotient.inductionOn with
    | _ p =>
        apply Quotient.sound
        change Homotopic T _
          (p.comp (reverseWalk T p)) Quiver.Path.nil
        simpa only [Quiver.Path.nil_comp] using
          Homotopic.comp_reverse T Quiver.Path.nil p

/-- Reversal corrects the order convention between concatenated based walks
and multiplication in a categorical endomorphism group. -/
def fundamentalGroupEquivEnd (T : RightMeshData Q) (x₀ : Q) :
    FundamentalGroup T x₀ ≃*
      End (show HomotopyGroupoid T from x₀) where
  toFun := Quotient.map (reverseWalk T) fun _ _ h ↦
    Homotopic.reverse T h
  invFun := Quotient.map (reverseWalk T) fun _ _ h ↦
    Homotopic.reverse T h
  left_inv g := by
    induction g using Quotient.inductionOn with
    | _ p =>
        exact congrArg (Quotient.mk _)
          (reverseWalk_reverseWalk T p)
  right_inv g := by
    induction g using Quotient.inductionOn with
    | _ p =>
        exact congrArg (Quotient.mk _)
          (reverseWalk_reverseWalk T p)
  map_mul' g h := by
    induction g, h using Quotient.inductionOn₂ with
    | _ p q =>
        exact congrArg (Quotient.mk _)
          (reverseWalk_comp T p q)

/-- Based walk-connectedness makes the mesh-homotopy groupoid connected. -/
theorem isConnected_of_isWalkConnectedAt
    (T : RightMeshData Q) (x₀ : Q)
    (hconnected : IsWalkConnectedAt T x₀) :
    IsConnected (HomotopyGroupoid T) := by
  letI : Nonempty (HomotopyGroupoid T) := ⟨x₀⟩
  exact CategoryTheory.zigzag_isConnected fun X Y ↦ by
    obtain ⟨p⟩ := hconnected (show Q from X)
    obtain ⟨q⟩ := hconnected (show Q from Y)
    exact CategoryTheory.Zigzag.of_hom
      (Quotient.mk _ ((reverseWalk T p).comp q))

section FreeConsequences

variable {Q₀ : Type u} [Quiver.{u} Q₀]

/-- A free based fundamental group and based walk-connectedness make the
entire mesh-homotopy groupoid free.  A basis of loops at the root is enlarged
by one chosen spoke from the root to every other object. -/
@[reducible] noncomputable def isFreeGroupoidOfFundamentalGroupIsFree
    (T : RightMeshData Q₀) (x₀ : Q₀)
    [IsFreeGroup (FundamentalGroup T x₀)]
    (hconnected : IsWalkConnectedAt T x₀) :
    IsFreeGroupoid (HomotopyGroupoid T) := by
  letI : IsFreeGroup
      (End (show HomotopyGroupoid T from x₀)) :=
    IsFreeGroup.ofMulEquiv (fundamentalGroupEquivEnd T x₀)
  exact MagnitudeConjecture.ConnectedGroupoid.isFreeGroupoidOfEndIsFree
    (show HomotopyGroupoid T from x₀)
    (fun y ↦ by
      obtain ⟨p⟩ := hconnected (show Q₀ from y)
      exact ⟨Quotient.mk _ p⟩)

/-- If the mesh-homotopy groupoid is free, then the based fundamental group
of a connected translation quiver is free. -/
theorem fundamentalGroup_isFree_of_isFreeGroupoid
    (T : RightMeshData Q₀) (x₀ : Q₀)
    [IsFreeGroupoid (HomotopyGroupoid T)]
    (hconnected : IsWalkConnectedAt T x₀) :
    IsFreeGroup (FundamentalGroup T x₀) := by
  letI : IsConnected (HomotopyGroupoid T) :=
    isConnected_of_isWalkConnectedAt T x₀ hconnected
  letI : IsFreeGroup
      (End (show HomotopyGroupoid T from x₀)) := inferInstance
  exact IsFreeGroup.ofMulEquiv (fundamentalGroupEquivEnd T x₀).symm

/-- A categorical graph model for the mesh-homotopy groupoid implies
freeness of the concrete fundamental group.  This is the exact categorical
target of the Bongartz--Gabriel tree-finite deformation argument. -/
theorem fundamentalGroup_isFree_of_freeGroupoidEquivalence
    {V : Type u} [Quiver.{u} V]
    (T : RightMeshData Q₀) (x₀ : Q₀)
    (E : HomotopyGroupoid T ≌ Quiver.FreeGroupoid V)
    (hconnected : IsWalkConnectedAt T x₀) :
    IsFreeGroup (FundamentalGroup T x₀) := by
  letI : IsConnected (HomotopyGroupoid T) :=
    isConnected_of_isWalkConnectedAt T x₀ hconnected
  letI : IsConnected (Quiver.FreeGroupoid V) :=
    CategoryTheory.isConnected_of_equivalent E
  letI : IsFreeGroup
      (End (E.functor.obj (show HomotopyGroupoid T from x₀))) :=
    inferInstance
  letI : IsFreeGroup
      (End (show HomotopyGroupoid T from x₀)) :=
    IsFreeGroup.ofMulEquiv
      (MagnitudeConjecture.CategoryTheory.Functor.endMulEquivOfFullyFaithful
        E.functor E.fullyFaithfulFunctor
          (show HomotopyGroupoid T from x₀)).symm
  exact IsFreeGroup.ofMulEquiv (fundamentalGroupEquivEnd T x₀).symm

/-- A categorical graph model supplies the torsion-freeness required by the
finite-cover averaging layer. -/
theorem fundamentalGroup_isMulTorsionFree_of_freeGroupoidEquivalence
    {V : Type u} [Quiver.{u} V]
    (T : RightMeshData Q₀) (x₀ : Q₀)
    (E : HomotopyGroupoid T ≌ Quiver.FreeGroupoid V)
    (hconnected : IsWalkConnectedAt T x₀) :
    IsMulTorsionFree (FundamentalGroup T x₀) := by
  letI : IsFreeGroup (FundamentalGroup T x₀) :=
    fundamentalGroup_isFree_of_freeGroupoidEquivalence
      T x₀ E hconnected
  exact MagnitudeConjecture.isMulTorsionFreeOfIsFreeGroup _

/-- A categorical graph model supplies the residual finiteness required by
the finite-cover averaging layer. -/
theorem fundamentalGroup_residuallyFinite_of_freeGroupoidEquivalence
    {V : Type u} [Quiver.{u} V]
    (T : RightMeshData Q₀) (x₀ : Q₀)
    (E : HomotopyGroupoid T ≌ Quiver.FreeGroupoid V)
    (hconnected : IsWalkConnectedAt T x₀) :
    Group.ResiduallyFinite (FundamentalGroup T x₀) := by
  letI : IsFreeGroup (FundamentalGroup T x₀) :=
    fundamentalGroup_isFree_of_freeGroupoidEquivalence
      T x₀ E hconnected
  exact MagnitudeConjecture.residuallyFiniteOfIsFreeGroup _

/-- The torsion-freeness consequence of a free mesh-homotopy groupoid. -/
theorem fundamentalGroup_isMulTorsionFree_of_isFreeGroupoid
    (T : RightMeshData Q₀) (x₀ : Q₀)
    [IsFreeGroupoid (HomotopyGroupoid T)]
    (hconnected : IsWalkConnectedAt T x₀) :
    IsMulTorsionFree (FundamentalGroup T x₀) := by
  letI : IsFreeGroup (FundamentalGroup T x₀) :=
    fundamentalGroup_isFree_of_isFreeGroupoid T x₀ hconnected
  exact MagnitudeConjecture.isMulTorsionFreeOfIsFreeGroup _

/-- The residual-finiteness consequence of a free mesh-homotopy groupoid. -/
theorem fundamentalGroup_residuallyFinite_of_isFreeGroupoid
    (T : RightMeshData Q₀) (x₀ : Q₀)
    [IsFreeGroupoid (HomotopyGroupoid T)]
    (hconnected : IsWalkConnectedAt T x₀) :
    Group.ResiduallyFinite (FundamentalGroup T x₀) := by
  letI : IsFreeGroup (FundamentalGroup T x₀) :=
    fundamentalGroup_isFree_of_isFreeGroupoid T x₀ hconnected
  exact MagnitudeConjecture.residuallyFiniteOfIsFreeGroup _

end FreeConsequences

end HomotopyGroupoid

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
