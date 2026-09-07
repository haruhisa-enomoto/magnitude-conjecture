import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.MeshRealization
import QuotientSubmoduleEquidistribution.RepresentationTheory.LeftAROccurrenceBasis
import QuotientSubmoduleEquidistribution.RepresentationTheory.RightAROccurrenceBasis
import Mathlib.Data.Fintype.EquivFin

/-!
# The Auslander--Reiten mesh of a directed right-module skeleton

This file constructs the concrete translation quiver used by Ringel
standardness.  An arrow `z ⟶ y` is an occurrence of the summand `y` in a
fixed minimal right almost-split middle term ending at `z`; this is the
reversed orientation used by the free path category.  At a projective
endpoint the middle term is the module radical and the map is its canonical
inclusion.

For a nonprojective endpoint, the same displayed middle decomposition is
also the middle decomposition of the left almost-split kernel map.  The
right- and left-occurrence bases of `rad/rad²` therefore give the cardinal
equality needed to pair the two sides of each mesh.  No multiplicity-one or
classification result is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The projective radical inclusion written in the selected skeleton's
object vocabulary. -/
def meshProjectiveBoundaryMap (z : Fin S.n) :
    S.projectiveBoundaryRadical z ⟶ S.almostSplitSkeleton.obj z :=
  S.projectiveBoundaryRadicalInclusion z

/-- A minimal right almost-split decomposition at every vertex, using the
radical inclusion at a projective vertex and the chosen AR decomposition at
a nonprojective vertex. -/
def meshRightAlmostSplitAt (z : Fin S.n) :
    S.almostSplitSkeleton.MinimalRightAlmostSplitDecomposition z := by
  classical
  by_cases hz : Projective (S.fgObj z)
  · exact
      IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap
        S.almostSplitSkeleton
        (S.meshProjectiveBoundaryMap z)
        (fgModule_isFiniteLength (k := k) (A := A)
          (S.projectiveBoundaryRadical z))
        (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit z hz)
        (S.projectiveBoundaryRadicalInclusion_isRightMinimal z)
  · exact S.minimalRightAlmostSplitAt z

@[simp]
theorem meshRightAlmostSplitAt_eq_of_not_projective
    (z : Fin S.n) (hz : ¬ Projective (S.fgObj z)) :
    S.meshRightAlmostSplitAt z = S.minimalRightAlmostSplitAt z := by
  simp [meshRightAlmostSplitAt, hz]

theorem meshRightAlmostSplitAt_eq_of_projective
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    S.meshRightAlmostSplitAt z =
      IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap
        S.almostSplitSkeleton
        (S.meshProjectiveBoundaryMap z)
        (fgModule_isFiniteLength (k := k) (A := A)
          (S.projectiveBoundaryRadical z))
        (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit z hz)
        (S.projectiveBoundaryRadicalInclusion_isRightMinimal z) := by
  simp [meshRightAlmostSplitAt, hz]

theorem meshRightAlmostSplitAt_middle_eq_of_projective
    (z : Fin S.n) (hz : Projective (S.fgObj z)) :
    (S.meshRightAlmostSplitAt z).middle =
      S.projectiveBoundaryRadical z := by
  rw [S.meshRightAlmostSplitAt_eq_of_projective z hz]
  simp [
    IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap]

/-- The middle term of the unified label mesh is the displayed middle term
of the corresponding minimal right almost-split decomposition. -/
theorem labelRightMesh_X₂ (z : Fin S.n) :
    (S.labelRightMesh z).X₂ =
      (S.meshRightAlmostSplitAt z).middle := by
  classical
  by_cases hz : Projective (S.fgObj z)
  · rw [S.meshRightAlmostSplitAt_eq_of_projective z hz]
    simp [labelRightMesh, hz, projectiveRightMesh,
      IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.ofMap]
  · rw [S.meshRightAlmostSplitAt_eq_of_not_projective z hz]
    simp [labelRightMesh, hz, nonprojectiveRightMesh]

/-- Projective vertices of the translation quiver. -/
def meshProjectiveSet : Set (Fin S.n) :=
  {z | Projective (S.fgObj z)}

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem mem_meshProjectiveSet_iff (z : Fin S.n) :
    z ∈ S.meshProjectiveSet ↔ Projective (S.fgObj z) :=
  Iff.rfl

/-- Reversed AR-quiver arrows.  Thus an element of `z ⟶ y` represents an
irreducible module morphism `S(y) ⟶ S(z)`. -/
abbrev MeshArrow (z y : Fin S.n) :=
  S.almostSplitSkeleton.RightAROccurrence
    (S.meshRightAlmostSplitAt z) y

/-- The reversed Auslander--Reiten quiver on the selected labels. -/
@[reducible] def meshQuiver : Quiver (Fin S.n) where
  Hom := S.MeshArrow

/-- Every displayed arrow type is finite. -/
@[reducible] noncomputable def meshArrowFintype (z y : Fin S.n) :
    Fintype (S.MeshArrow z y) :=
  Fintype.ofFinite (S.MeshArrow z y)

/-- The module morphism represented by a reversed AR-quiver arrow. -/
def meshArrowMap {z y : Fin S.n} (a : S.MeshArrow z y) :
    S.almostSplitSkeleton.obj y ⟶ S.almostSplitSkeleton.obj z :=
  S.almostSplitSkeleton.rightAROccurrenceArrow
    (S.meshRightAlmostSplitAt z) y a

/-- The displayed middle summands at `z` are canonically the disjoint union
of all arrows into `z`, with parallel occurrences kept distinct. -/
def meshMiddleIndexEquiv (z : Fin S.n) :
    (S.meshRightAlmostSplitAt z).index ≃ Σ y : Fin S.n, S.MeshArrow z y where
  toFun t := ⟨(S.meshRightAlmostSplitAt z).label t, ⟨t, rfl⟩⟩
  invFun a := a.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨y, t, ht⟩
    subst y
    rfl

/-- Assemble a map to the displayed right almost-split middle term from one
component for every incoming mesh arrow. -/
def meshMiddleLift {X : FGModuleCat.{u} Aᵐᵒᵖ}
    (z : Fin S.n)
    (c : ∀ a : Σ y : Fin S.n, S.MeshArrow z y,
      X ⟶ S.almostSplitSkeleton.obj a.1) :
    X ⟶ (S.meshRightAlmostSplitAt z).middle :=
  biproduct.lift (fun t ↦ c ⟨(S.meshRightAlmostSplitAt z).label t,
      ⟨t, rfl⟩⟩) ≫
    (S.meshRightAlmostSplitAt z).decomposition.inv

@[reassoc (attr := simp)]
theorem meshMiddleLift_decomposition_π
    {X : FGModuleCat.{u} Aᵐᵒᵖ} (z : Fin S.n)
    (c : ∀ a : Σ y : Fin S.n, S.MeshArrow z y,
      X ⟶ S.almostSplitSkeleton.obj a.1)
    (t : (S.meshRightAlmostSplitAt z).index) :
    S.meshMiddleLift z c ≫
        (S.meshRightAlmostSplitAt z).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.almostSplitSkeleton.obj
            ((S.meshRightAlmostSplitAt z).label j)) t =
      c (S.meshMiddleIndexEquiv z t) := by
  change
    (biproduct.lift (fun t ↦ c ⟨(S.meshRightAlmostSplitAt z).label t,
        ⟨t, rfl⟩⟩) ≫
        (S.meshRightAlmostSplitAt z).decomposition.inv) ≫
        (S.meshRightAlmostSplitAt z).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.almostSplitSkeleton.obj
            ((S.meshRightAlmostSplitAt z).label j)) t = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π]
  rfl

/-- Every displayed quiver arrow represents an irreducible module
morphism. -/
theorem meshArrowMap_isIrreducible {z y : Fin S.n}
    (a : S.MeshArrow z y) :
    IsIrreducibleMorphism (S.meshArrowMap a) := by
  rcases a with ⟨a, rfl⟩
  simpa [meshArrowMap,
    IndecomposableSkeleton.rightAROccurrenceArrow,
    IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.component]
    using (S.meshRightAlmostSplitAt z).component_irreducible
      S.almostSplitSkeleton a

/-- Reversed mesh arrows strictly lower the directed order. -/
theorem meshArrow_lt [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {z y : Fin S.n} (a : S.MeshArrow z y) :
    (S.directedLinearOrder H).lt y z :=
  S.directedLinearOrder_lt_of_irreducible H
    ⟨S.meshArrowMap a, S.meshArrowMap_isIrreducible a⟩

section Pairing

variable [IsAlgClosed k]

private theorem meshArrow_natCard_eq
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) (y : Fin S.n) :
    Nat.card (S.MeshArrow z.1 y) =
      Nat.card (S.MeshArrow y (S.rightTranslationLabel z)) := by
  let sigma := S.almostSplitSkeleton
  let Bz := S.minimalRightAlmostSplitAt z.1
  let By := S.meshRightAlmostSplitAt y
  let L := S.rightSequenceLeftDecomposition z
  have hleft :=
    sigma.finrank_irreducibleHomSpace_eq_card_leftAROccurrence
      (K := k) L y
      (HasAcyclicNonzeroNonisomorphisms.endomorphism_eq_smul_id S H y)
  have hright :=
    sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence
      (K := k) By (S.rightTranslationLabel z)
      (HasAcyclicNonzeroNonisomorphisms.endomorphism_eq_smul_id
        S H (S.rightTranslationLabel z))
  change Nat.card
      (sigma.RightAROccurrence (S.meshRightAlmostSplitAt z.1) y) = _
  rw [S.meshRightAlmostSplitAt_eq_of_not_projective z.1 z.2]
  change Nat.card (sigma.LeftAROccurrence L y) = _
  exact hleft.symm.trans hright

/-- A choice of pairing between the incoming arrows at a nonprojective
vertex and the outgoing arrows from its AR translate.  Its existence is the
right/left occurrence-basis theorem for `rad/rad²`. -/
def meshArrowEquiv
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) (y : Fin S.n) :
    S.MeshArrow z.1 y ≃
      S.MeshArrow y (S.rightTranslationLabel z) := by
  letI : Fintype (S.MeshArrow z.1 y) := S.meshArrowFintype z.1 y
  letI : Fintype (S.MeshArrow y (S.rightTranslationLabel z)) :=
    S.meshArrowFintype y (S.rightTranslationLabel z)
  apply Fintype.equivOfCardEq
  simpa only [Nat.card_eq_fintype_card] using S.meshArrow_natCard_eq H z y

/-- The concrete right-translation-quiver data of the selected module
skeleton. -/
def rightMeshData (H : S.HasAcyclicNonzeroNonisomorphisms) :
    @MeshCategory.RightMeshData (Fin S.n) S.meshQuiver := by
  letI : Quiver (Fin S.n) := S.meshQuiver
  exact
    { projective := S.meshProjectiveSet
      tau := fun z ↦ S.rightTranslationLabel
        ⟨z.1, by simpa [meshProjectiveSet] using z.2⟩
      arrowEquiv := fun z y ↦ by
        change S.MeshArrow z.1 y ≃
          S.MeshArrow y (S.rightTranslationLabel
            ⟨z.1, by simpa [meshProjectiveSet] using z.2⟩)
        exact S.meshArrowEquiv H
          ⟨z.1, by simpa [meshProjectiveSet] using z.2⟩ y }

end Pairing

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
