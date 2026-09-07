import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDirected
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStructure

/-!
# Admissible locally bounded categories

This is the manuscript's covering-theoretic admissibility package: local
representation-finiteness, directedness of the finite-support module
category, and containment of every finite object set in a finite convex full
subcategory.  Object deletion preserves all three clauses.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The locally bounded structure used throughout the covering argument.
Besides skeletality and local endomorphism rings, it records finite support
and finite-dimensionality of both covariant representables and coefficient-
dual corepresentables. -/
structure IsLocallyBounded : Prop where
  skeletal : Skeletal C
  finiteCovariantRepresentables :
    ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)
  finiteDualCorepresentables :
    ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)
  localEndomorphismRings : ∀ X : C, IsLocalRing (End X)

/-- A nonzero nonisomorphism in the base linear category. -/
def BaseNonzeroNonisomorphism (X Y : C) : Prop :=
  ∃ f : X ⟶ Y, f ≠ 0 ∧ ¬ IsIso f

/-- A set of objects is convex when every vertex on a path of nonzero
nonisomorphisms between two of its vertices also belongs to it. -/
def IsConvexObjectSet (U : Set C) : Prop :=
  ∀ {X Y Z : C}, X ∈ U → Z ∈ U →
    Relation.ReflTransGen
      (BaseNonzeroNonisomorphism (C := C)) X Y →
    Relation.ReflTransGen
      (BaseNonzeroNonisomorphism (C := C)) Y Z →
    Y ∈ U

/-- Every finite object set is contained in a finite convex full
subcategory, recorded by its object set. -/
def HasFiniteConvexObjectNeighborhoods : Prop :=
  ∀ T : Set C, T.Finite →
    ∃ U : Set C, U.Finite ∧ T ⊆ U ∧ IsConvexObjectSet U

/-- The exact admissibility package used in the local-deletion and
finite-covering arguments. -/
structure IsAdmissible : Prop where
  locallyBounded : IsLocallyBounded (k := k) (C := C)
  locallyRepresentationFinite :
    IsLocallyRepresentationFinite (k := k) (C := C)
  directed :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C)
  finiteConvexNeighborhoods :
    HasFiniteConvexObjectNeighborhoods (C := C)

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Locally bounded structure descends to every literal object-deletion
quotient. -/
theorem isLocallyBounded_deletion
    (S : Set C) (H : IsLocallyBounded (k := k) (C := C)) :
    IsLocallyBounded
      (k := k) (C := DeletionCategory (k := k) C S) where
  skeletal := deletion_skeletal (k := k) C H.skeletal
    H.localEndomorphismRings S
  finiteCovariantRepresentables :=
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C
      H.finiteCovariantRepresentables S
  finiteDualCorepresentables :=
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C
      H.finiteDualCorepresentables S
  localEndomorphismRings :=
    deletion_end_isLocalRing (k := k) C H.skeletal
      H.localEndomorphismRings S

private theorem baseNonzeroNonisomorphism_of_deletion
    (S : Set C) {X Y : DeletionCategory (k := k) C S}
    (h : BaseNonzeroNonisomorphism
      (C := DeletionCategory (k := k) C S) X Y) :
    BaseNonzeroNonisomorphism (C := C) X.obj.as Y.obj.as := by
  rcases h with ⟨f, hf, hnotIso⟩
  let g : X.obj.as ⟶ Y.obj.as := Quot.out f.hom
  have hg : (Quot.mk _ g : X.obj ⟶ Y.obj) = f.hom :=
    Quot.out_eq f.hom
  refine ⟨g, ?_, ?_⟩
  · intro hzero
    apply hf
    apply ObjectProperty.hom_ext
    rw [← hg, hzero]
    rfl
  · intro hgIso
    apply hnotIso
    letI : IsIso g := hgIso
    constructor
    refine ⟨ObjectProperty.homMk (Quot.mk _ (inv g)), ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      change f.hom ≫ Quot.mk _ (inv g) = 𝟙 X.obj
      rw [← hg]
      change Quot.mk _ (g ≫ inv g) = Quot.mk _ (𝟙 X.obj.as)
      rw [IsIso.hom_inv_id]
    · apply ObjectProperty.hom_ext
      change Quot.mk _ (inv g) ≫ f.hom = 𝟙 Y.obj
      rw [← hg]
      change Quot.mk _ (inv g ≫ g) = Quot.mk _ (𝟙 Y.obj.as)
      rw [IsIso.inv_hom_id]

private theorem reflTransGen_baseNonzeroNonisomorphism_of_deletion
    (S : Set C) {X Y : DeletionCategory (k := k) C S}
    (h : Relation.ReflTransGen
      (BaseNonzeroNonisomorphism
        (C := DeletionCategory (k := k) C S)) X Y) :
    Relation.ReflTransGen (BaseNonzeroNonisomorphism (C := C))
      X.obj.as Y.obj.as := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hXY hYZ ih =>
      exact ih.tail
        (baseNonzeroNonisomorphism_of_deletion
          (k := k) (C := C) S hYZ)

/-- Finite convex object neighborhoods descend to an object-deletion
category. -/
theorem hasFiniteConvexObjectNeighborhoods_deletion
    (S : Set C)
    (H : HasFiniteConvexObjectNeighborhoods (C := C)) :
    HasFiniteConvexObjectNeighborhoods
      (C := DeletionCategory (k := k) C S) := by
  intro T hT
  let underlying : DeletionCategory (k := k) C S → C :=
    fun X ↦ X.obj.as
  have underlying_injective : Function.Injective underlying := by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact hXY
  obtain ⟨U, hUfinite, hTU, hUconvex⟩ :=
    H (underlying '' T) (hT.image underlying)
  let V : Set (DeletionCategory (k := k) C S) := underlying ⁻¹' U
  refine ⟨V, ?_, ?_, ?_⟩
  · exact hUfinite.preimage underlying_injective.injOn
  · intro X hXT
    exact hTU ⟨X, hXT, rfl⟩
  · intro X Y Z hXV hZV hXY hYZ
    exact hUconvex hXV hZV
      (reflTransGen_baseNonzeroNonisomorphism_of_deletion
        (k := k) (C := C) S hXY)
      (reflTransGen_baseNonzeroNonisomorphism_of_deletion
        (k := k) (C := C) S hYZ)

/-- Every literal object-deletion quotient of an admissible category is
again admissible. -/
theorem isAdmissible_deletion
    (S : Set C) (H : IsAdmissible (k := k) (C := C)) :
    IsAdmissible (k := k) (C := DeletionCategory (k := k) C S) where
  locallyBounded := isLocallyBounded_deletion (k := k) (C := C) S
    H.locallyBounded
  locallyRepresentationFinite :=
    isLocallyRepresentationFinite_deletion
      (k := k) C S H.locallyRepresentationFinite
  directed :=
    hasAcyclicFiniteModuleNonzeroNonisomorphisms_deletion
      (k := k) (C := C) S H.directed
  finiteConvexNeighborhoods :=
    hasFiniteConvexObjectNeighborhoods_deletion
      (k := k) (C := C) S H.finiteConvexNeighborhoods

end MagnitudeConjecture.ObjectDeletion
