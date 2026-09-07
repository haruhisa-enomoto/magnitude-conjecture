import MagnitudeConjecture.CategoryTheory.FiniteDeletionSkeletonLocalChange
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalChangeSum

/-!
# Restricting finite deletion change to a support family

A finite indecomposable family may contain duplicates, so its quotient by
isomorphism classes is identified with the subset of a complete
duplicate-free skeleton which it represents.  If pointwise deletion change
vanishes outside that subset, summing over the family gives the full
finite-skeleton surplus difference.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

namespace FiniteIndecomposableModuleFamily

variable (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

/-- The complete-skeleton label representing one index of a finite family. -/
noncomputable def skeletonLabel (i : Fin W.n) : Fin S.n :=
  Classical.choose (S.complete (W.obj i) (W.indecomposable i))

/-- The chosen isomorphism from a family representative to its complete-
skeleton representative. -/
noncomputable def skeletonLabelIso (i : Fin W.n) :
    W.obj i ≅ S.obj (W.skeletonLabel S i) :=
  Classical.choice
    (Classical.choose_spec (S.complete (W.obj i) (W.indecomposable i)))

/-- The skeleton label depends only on the represented isomorphism class. -/
noncomputable def isoClassSkeletonLabel : W.IsoClass → Fin S.n :=
  Quotient.lift (W.skeletonLabel S) (by
    intro i j hij
    apply S.skeletal
    exact ⟨(W.skeletonLabelIso S i).symm |>.trans
      ((Classical.choice hij).trans (W.skeletonLabelIso S j))⟩)

/-- Every class maps to a skeleton label represented by the family. -/
theorem isoClassSkeletonLabel_mem_isoClosure (q : W.IsoClass) :
    S.obj (W.isoClassSkeletonLabel S q) ∈ W.isoClosure := by
  induction q using Quotient.inductionOn with
  | _ i =>
      exact ⟨i, ⟨W.skeletonLabelIso S i⟩⟩

/-- The quotient of the family by isomorphism classes maps into the subset
of complete-skeleton labels represented by the family. -/
noncomputable def isoClassSkeletonSubtype (q : W.IsoClass) :
    {i : Fin S.n // S.obj i ∈ W.isoClosure} :=
  ⟨W.isoClassSkeletonLabel S q,
    W.isoClassSkeletonLabel_mem_isoClosure S q⟩

theorem isoClassSkeletonSubtype_injective :
    Function.Injective (W.isoClassSkeletonSubtype S) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ i =>
      induction r using Quotient.inductionOn with
      | _ j =>
          apply Quotient.sound
          exact ⟨(W.skeletonLabelIso S i).trans
            ((eqToIso (congrArg S.obj (congrArg Subtype.val hqr))).trans
              (W.skeletonLabelIso S j).symm)⟩

theorem isoClassSkeletonSubtype_surjective :
    Function.Surjective (W.isoClassSkeletonSubtype S) := by
  intro i
  obtain ⟨j, ⟨e⟩⟩ := i.2
  refine ⟨Quotient.mk W.isoSetoid j, Subtype.ext ?_⟩
  apply S.skeletal
  exact ⟨(W.skeletonLabelIso S j).symm |>.trans e⟩

/-- Isomorphism classes represented by the family are equivalent to the
subset of labels they represent in any complete duplicate-free skeleton. -/
noncomputable def isoClassSkeletonEquiv :
    W.IsoClass ≃ {i : Fin S.n // S.obj i ∈ W.isoClosure} :=
  Equiv.ofBijective (W.isoClassSkeletonSubtype S)
    ⟨W.isoClassSkeletonSubtype_injective S,
      W.isoClassSkeletonSubtype_surjective S⟩

end FiniteIndecomposableModuleFamily

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- If a finite family contains the support of pointwise deletion change,
its isomorphism-class sum equals the sum over any complete ambient
indecomposable skeleton. -/
theorem finiteDeletionLocalChangeSum_eq_skeletonSum
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (D : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (S : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C))
    (hsupport : ∀ i : Fin S.n, S.obj i ∉ W.isoClosure →
      finiteDeletionLocalChangeAt (k := k) C hlocal D
        (S.obj i) (S.indecomposable i) = 0) :
    finiteDeletionLocalChangeSum (k := k) C hlocal D W =
      ∑ i : Fin S.n,
        finiteDeletionLocalChangeAt (k := k) C hlocal D
          (S.obj i) (S.indecomposable i) := by
  classical
  let p : Fin S.n → Prop := fun i ↦ S.obj i ∈ W.isoClosure
  let f : Fin S.n → ℤ := fun i ↦
    finiteDeletionLocalChangeAt (k := k) C hlocal D
      (S.obj i) (S.indecomposable i)
  have houtside : ∑ i : {i : Fin S.n // ¬ p i}, f i.1 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hsupport i.1 i.2
  have hpartition := Fintype.sum_subtype_add_sum_subtype p f
  have hrepresented :
      finiteDeletionLocalChangeSum (k := k) C hlocal D W =
        ∑ i : {i : Fin S.n // p i}, f i.1 := by
    unfold finiteDeletionLocalChangeSum
    exact Fintype.sum_bijective
      (W.isoClassSkeletonEquiv S)
      (W.isoClassSkeletonEquiv S).bijective
      (finiteDeletionLocalChangeOnIsoClass (k := k) C hlocal D W)
      (fun i : {i : Fin S.n // p i} ↦ f i.1)
      (fun q ↦ by
        induction q using Quotient.inductionOn with
        | _ j =>
            exact finiteDeletionLocalChangeAt_eq_of_iso
              (k := k) C hlocal D (W.indecomposable j)
                (S.indecomposable (W.skeletonLabel S j))
                (W.skeletonLabelIso S j))
  calc
    finiteDeletionLocalChangeSum (k := k) C hlocal D W =
        ∑ i : {i : Fin S.n // p i}, f i.1 := hrepresented
    _ = (∑ i : {i : Fin S.n // p i}, f i.1) +
        ∑ i : {i : Fin S.n // ¬ p i}, f i.1 := by rw [houtside, add_zero]
    _ = ∑ i : Fin S.n, f i := hpartition

/-- A support family turns its intrinsic isomorphism-class local-change sum
into the exact difference of complete-skeleton Auslander--Reiten surpluses. -/
theorem finiteDeletionLocalChangeSum_eq_surplus_sub
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (D : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (S : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C))
    (T : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := DeletionCategory (k := k) C D))
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C D) k)]
    (hsupport : ∀ i : Fin S.n, S.obj i ∉ W.isoClosure →
      finiteDeletionLocalChangeAt (k := k) C hlocal D
        (S.obj i) (S.indecomposable i) = 0) :
    finiteDeletionLocalChangeSum (k := k) C hlocal D W =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            S.toFiniteRightTauCategoryData)
          S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) -
        @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  rw [finiteDeletionLocalChangeSum_eq_skeletonSum
      (k := k) C hlocal D W S hsupport,
    FiniteDeletionSkeleton.sum_finiteDeletionLocalChangeAt_eq_surplus_sub
      (k := k) D S T hlocal]

end MagnitudeConjecture.ObjectDeletion
