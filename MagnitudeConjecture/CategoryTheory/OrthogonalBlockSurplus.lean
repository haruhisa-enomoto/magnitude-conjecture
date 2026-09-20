import MagnitudeConjecture.CategoryTheory.OrthogonalModuleSupport
import MagnitudeConjecture.CategoryTheory.FiniteDeletionSurplus
import MagnitudeConjecture.CategoryTheory.FiniteDeletionSkeletonLocalChange
import MagnitudeConjecture.CategoryTheory.FiniteDecompositionVanishes
import MagnitudeConjecture.CategoryTheory.ObjectDeletionConvexComparison

/-! # Additivity of finite module surplus across orthogonal blocks -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.ObjectDeletion
universe u v w
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {J : Type w} (block : C → J)
variable (hcross : ∀ X Y : C, block X ≠ block Y → ∀ f : X ⟶ Y, f = 0)
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))
variable (hrep : IsLocallyRepresentationFinite (k := k) (C := C))

/-- Delete all objects outside a specified block. -/
def blockComplement (j : J) : Set C := {X | block X ≠ j}

include hcross hP in
/-- Restriction to the unique support block preserves an indecomposable's local density. -/
theorem blockExtendedDensity_eq (j : J)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) (hM : Indecomposable M)
    (hvan : ModuleVanishesOnDeleted (k := k) C (blockComplement block j) M.obj.obj) :
    finiteDeletionExtendedLocalDensity (k := k) C hrep (blockComplement block j) M hM =
      finiteModuleLocalDensity hrep M hM := by
  classical
  let A := finiteModuleMinimalSinkData hrep M hM
  have hsource : ModuleVanishesOnDeleted (k := k) C (blockComplement block j) A.source.obj.obj := by
    apply moduleVanishesOnDeleted_of_decomposition_summands
      (k := k) C (blockComplement block j) A.source A.decomposition
    intro i
    exact incoming_source_supported_on_block block hcross M j hvan
      (A.decomposition.summand i) (A.decomposition.indecomposable i)
      (A.decomposition.inclusion i ≫ A.map)
      (A.decomposition.inclusion_comp_ne_zero_of_isRightMinimal i A.map A.rightMinimal)
  rw [finiteDeletionExtendedLocalDensity, dif_pos hvan]
  exact finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
    (k := k) C hP hrep (blockComplement block j) M hM hvan
    A.map A.rightAlmostSplit A.rightMinimal A.decomposition hsource

include hcross hP in
/-- Summing the densities retained by all blocks counts an indecomposable exactly once. -/
theorem sum_blockExtendedDensity [Fintype J]
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) (hM : Indecomposable M) :
    (∑ j : J, finiteDeletionExtendedLocalDensity (k := k) C hrep (blockComplement block j) M hM) =
      finiteModuleLocalDensity hrep M hM := by
  classical
  obtain ⟨j, hj, huniq⟩ := existsUnique_support_block block hcross M hM
  rw [Finset.sum_eq_single j]
  · exact blockExtendedDensity_eq block hcross hP hrep j M hM hj
  · intro l _ hlj
    apply finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
    intro hl
    exact hlj (huniq l hl)
  · simp

include hcross hP in
/-- The intrinsic surplus is the sum of the surpluses of the separate blocks. -/
theorem finiteCategorySurplus_eq_sum_blockDeletionSurplus [Fintype C] [Fintype J] :
    finiteCategorySurplus hP hrep =
      ∑ j : J, finiteDeletionSurplus hP hrep (blockComplement block j) := by
  classical
  let := enoughProjectives_of_finiteRepresentables hP
  let S := finiteCategoryModuleIndecomposableSkeleton hrep
  rw [finiteCategorySurplus_eq_skeleton hP hrep S, ← S.sum_finiteModuleLocalDensity_eq_surplus hrep]
  calc
    (∑ i : Fin S.n, finiteModuleLocalDensity hrep (S.obj i) (S.indecomposable i)) =
        ∑ i : Fin S.n, ∑ j : J, finiteDeletionExtendedLocalDensity (k := k) C hrep
          (blockComplement block j) (S.obj i) (S.indecomposable i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (sum_blockExtendedDensity block hcross hP hrep (S.obj i) (S.indecomposable i)).symm
    _ = ∑ j : J, ∑ i : Fin S.n, finiteDeletionExtendedLocalDensity (k := k) C hrep
          (blockComplement block j) (S.obj i) (S.indecomposable i) := Finset.sum_comm
    _ = ∑ j : J, finiteDeletionSurplus hP hrep (blockComplement block j) := by
      apply Finset.sum_congr rfl
      intro j _
      let D := blockComplement block j
      let hPD := deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP D
      let hrepD := isLocallyRepresentationFinite_deletion (k := k) C D hrep
      let := enoughProjectives_of_finiteRepresentables hPD
      let T := finiteCategoryModuleIndecomposableSkeleton hrepD
      rw [FiniteDeletionSkeleton.sum_finiteDeletionExtendedLocalDensity_eq D S T hrep,
        T.sum_finiteModuleLocalDensity_eq_surplus hrepD]
      exact (finiteCategorySurplus_eq_skeleton hPD hrepD T).symm

include hcross in
/-- No nonzero composite between objects of a block can pass through its complement. -/
theorem blockComplement_noDeletedFactorization (j : J) :
    NoDeletedFactorization C (blockComplement block j) := by
  intro X Y Z hX _ hZ a b
  have hx : block X = j := not_ne_iff.mp hX
  have hxz : block X ≠ block Z := fun h ↦ hZ (h.symm.trans hx)
  rw [hcross X Z hxz a]
  exact zero_comp

include hcross hP in
/-- When all blocks are equivalent to the same finite category, surplus is
its surplus multiplied by the number of blocks. -/
theorem finiteCategorySurplus_eq_card_mul_of_blockEquivalences
    [Fintype C] [Fintype J]
    {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D] [Fintype D]
    (hQ : ∀ X : D, IsFiniteDimensionalModule (C := D) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrepD : IsLocallyRepresentationFinite (k := k) (C := D))
    (E : ∀ j : J, DeletionCategory (k := k) C (blockComplement block j) ≌ D)
    [∀ j, (E j).functor.Additive] [∀ j, (E j).functor.Linear k] :
    finiteCategorySurplus hP hrep = (Fintype.card J : ℤ) * finiteCategorySurplus hQ hrepD := by
  rw [finiteCategorySurplus_eq_sum_blockDeletionSurplus block hcross hP hrep]
  calc
    (∑ j : J, finiteDeletionSurplus hP hrep (blockComplement block j)) =
        ∑ _j : J, finiteCategorySurplus hQ hrepD := by
      apply Finset.sum_congr rfl
      intro j _
      exact finiteCategorySurplus_eq_of_equivalence _ hQ _ hrepD (E j)
    _ = _ := by simp

end MagnitudeConjecture.CoveringHom
