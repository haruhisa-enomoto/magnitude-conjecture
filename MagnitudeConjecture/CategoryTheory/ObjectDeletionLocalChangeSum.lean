import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalDensity
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType

/-!
# Finite local-change sums for object deletion

The two-step control family is a finite list which may contain repeated
representatives.  The manuscript's local change is a sum over
indecomposable isomorphism classes, so this file quotients a finite module
family by isomorphism before summing the intrinsic pointwise change.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

namespace FiniteIndecomposableModuleFamily

variable (W : FiniteIndecomposableModuleFamily (k := k) (C := C))

/-- Isomorphism of represented indecomposables as an equivalence relation
on the indices of a finite module family. -/
def isoSetoid : Setoid (Fin W.n) where
  r i j := Nonempty (W.obj i ≅ W.obj j)
  iseqv := {
    refl := fun i ↦ ⟨Iso.refl (W.obj i)⟩
    symm := fun h ↦ h.map Iso.symm
    trans := fun hij hjl ↦ Nonempty.map2 Iso.trans hij hjl }

/-- The finite type of isomorphism classes represented by a finite module
family. -/
abbrev IsoClass := Quotient W.isoSetoid

noncomputable instance isoClassFintype : Fintype W.IsoClass := by
  classical
  letI : DecidableRel W.isoSetoid.r :=
    Classical.decRel _
  exact Quotient.fintype W.isoSetoid

end FiniteIndecomposableModuleFamily

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- Intrinsic local density descended to an isomorphism class represented by
a finite indecomposable family. -/
noncomputable def finiteModuleLocalDensityOnIsoClass
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    W.IsoClass → ℤ :=
  Quotient.lift
    (fun i ↦ finiteModuleLocalDensity hlocal
      (W.obj i) (W.indecomposable i))
    (by
      intro i j hij
      exact finiteModuleLocalDensity_eq_of_iso hlocal
        (W.indecomposable i) (W.indecomposable j) (Classical.choice hij))

/-- Sum of intrinsic local density over the represented isomorphism classes
of a finite indecomposable family. -/
noncomputable def finiteModuleLocalDensitySum
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) : ℤ :=
  ∑ q : W.IsoClass,
    finiteModuleLocalDensityOnIsoClass (k := k) C hlocal W q

/- A finite indecomposable family which covers a complete finite skeleton has
the same intrinsic density sum as that skeleton.  This is the finite
isomorphism-class reindexing used when passing from source representatives to
the canonical deleted-category skeleton. -/
theorem finiteModuleLocalDensitySum_eq_skeleton_sum_of_complete
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (S : MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C))
    (hWcover : ∀ (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C := C) k),
      Indecomposable M → ∃ i, Nonempty (M ≅ W.obj i)) :
    finiteModuleLocalDensitySum (k := k) C hlocal W =
      ∑ i : Fin S.n,
        finiteModuleLocalDensity hlocal (S.obj i) (S.indecomposable i) := by
  classical
  let φ : W.IsoClass → Fin S.n := Quotient.lift
    (fun i ↦ Classical.choose (S.complete (W.obj i) (W.indecomposable i)))
    (by
      intro i j hij
      apply S.skeletal
      obtain ⟨e⟩ := hij
      exact ⟨(Classical.choice (Classical.choose_spec
        (S.complete (W.obj i) (W.indecomposable i)))).symm ≪≫
        e ≪≫ Classical.choice (Classical.choose_spec
          (S.complete (W.obj j) (W.indecomposable j)))⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · intro q r hqr
      induction q using Quotient.inductionOn with
      | _ i =>
        induction r using Quotient.inductionOn with
        | _ j =>
          apply Quotient.sound
          have hij : φ (Quotient.mk W.isoSetoid i) =
              φ (Quotient.mk W.isoSetoid j) := hqr
          change Classical.choose (S.complete (W.obj i) (W.indecomposable i)) =
            Classical.choose (S.complete (W.obj j) (W.indecomposable j)) at hij
          have ewi := Classical.choice (Classical.choose_spec
            (S.complete (W.obj i) (W.indecomposable i)))
          have ewj := Classical.choice (Classical.choose_spec
            (S.complete (W.obj j) (W.indecomposable j)))
          exact ⟨ewi.trans ((eqToIso (congrArg S.obj hij)).trans ewj.symm)⟩
    · intro i
      obtain ⟨j, hj⟩ := hWcover (S.obj i) (S.indecomposable i)
      refine ⟨Quotient.mk W.isoSetoid j, ?_⟩
      apply S.skeletal
      exact ⟨((Classical.choice hj).trans (Classical.choice (Classical.choose_spec
        (S.complete (W.obj j) (W.indecomposable j))))).symm⟩
  unfold finiteModuleLocalDensitySum
  apply Fintype.sum_bijective φ hφ
    (finiteModuleLocalDensityOnIsoClass (k := k) C hlocal W)
    (fun i ↦ finiteModuleLocalDensity hlocal (S.obj i) (S.indecomposable i))
    (by
      intro q
      induction q using Quotient.inductionOn with
      | _ j =>
        dsimp [finiteModuleLocalDensityOnIsoClass, φ]
        let q := Classical.choose (S.complete (W.obj j) (W.indecomposable j))
        have e : W.obj j ≅ S.obj q :=
          Classical.choice (Classical.choose_spec
            (S.complete (W.obj j) (W.indecomposable j)))
        exact finiteModuleLocalDensity_eq_of_iso hlocal
          (W.indecomposable j) (S.indecomposable q) e
    )

/-- Deletion-extended intrinsic density descended to an isomorphism class
represented by a finite indecomposable family. -/
noncomputable def finiteDeletionExtendedLocalDensityOnIsoClass
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    W.IsoClass → ℤ :=
  Quotient.lift
    (fun i ↦ finiteDeletionExtendedLocalDensity
      (k := k) C hlocal S (W.obj i) (W.indecomposable i))
    (by
      intro i j hij
      exact finiteDeletionExtendedLocalDensity_eq_of_iso
        (k := k) C hlocal S (W.indecomposable i) (W.indecomposable j)
          (Classical.choice hij))

/-- Sum of deletion-extended density over the represented isomorphism
classes of a finite indecomposable family. -/
noncomputable def finiteDeletionExtendedLocalDensitySum
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) : ℤ :=
  ∑ q : W.IsoClass,
    finiteDeletionExtendedLocalDensityOnIsoClass
      (k := k) C hlocal S W q

/-- Pointwise deletion change descended to an isomorphism class represented
by a finite indecomposable family. -/
noncomputable def finiteDeletionLocalChangeOnIsoClass
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    W.IsoClass → ℤ :=
  Quotient.lift
    (fun i ↦ finiteDeletionLocalChangeAt
      (k := k) C hlocal S (W.obj i) (W.indecomposable i))
    (by
      intro i j hij
      exact finiteDeletionLocalChangeAt_eq_of_iso
        (k := k) C hlocal S (W.indecomposable i) (W.indecomposable j)
          (Classical.choice hij))

/-- The finite sum of pointwise deletion changes over the represented
indecomposable isomorphism classes. -/
noncomputable def finiteDeletionLocalChangeSum
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) : ℤ :=
  ∑ q : W.IsoClass,
    finiteDeletionLocalChangeOnIsoClass (k := k) C hlocal S W q

/-- Enlarging a finite representative family does not change its local-change
sum when every newly represented isomorphism class has zero pointwise change.
The statement only assumes inclusion of isomorphism closures, so it is
independent of labels and duplicate representatives. -/
theorem finiteDeletionLocalChangeSum_eq_of_isoClosure_subset
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (W U : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsubset : W.isoClosure ⊆ U.isoClosure)
    (houtside : ∀ i : Fin U.n, U.obj i ∉ W.isoClosure →
      finiteDeletionLocalChangeAt
        (k := k) C hlocal S (U.obj i) (U.indecomposable i) = 0) :
    finiteDeletionLocalChangeSum (k := k) C hlocal S W =
      finiteDeletionLocalChangeSum (k := k) C hlocal S U := by
  classical
  let label (i : Fin W.n) : Fin U.n :=
    Classical.choose (hsubset (W.obj_mem_isoClosure i))
  let labelIso (i : Fin W.n) : U.obj (label i) ≅ W.obj i :=
    Classical.choice
      (Classical.choose_spec (hsubset (W.obj_mem_isoClosure i)))
  let φ : W.IsoClass → U.IsoClass :=
    Quotient.lift
      (fun i ↦ Quotient.mk U.isoSetoid (label i))
      (by
        intro i j hij
        apply Quotient.sound
        exact ⟨(labelIso i).trans
          ((Classical.choice hij).trans (labelIso j).symm)⟩)
  have hφ : Function.Injective φ := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | _ i =>
        induction r using Quotient.inductionOn with
        | _ j =>
            apply Quotient.sound
            obtain ⟨e⟩ := Quotient.exact hqr
            exact ⟨(labelIso i).symm |>.trans
              (e.trans (labelIso j))⟩
  let p : U.IsoClass → Prop := fun q ↦ q ∈ Set.range φ
  letI : Fintype {q : U.IsoClass // p q} := Subtype.fintype p
  letI : Fintype {q : U.IsoClass // ¬ p q} := Subtype.fintype fun q ↦ ¬ p q
  let φsub : W.IsoClass → {q : U.IsoClass // p q} :=
    fun q ↦ ⟨φ q, q, rfl⟩
  have hφsub : Function.Bijective φsub := by
    constructor
    · intro q r hqr
      exact hφ (congrArg Subtype.val hqr)
    · intro q
      obtain ⟨r, hr⟩ := q.property
      exact ⟨r, Subtype.ext hr⟩
  let fW := finiteDeletionLocalChangeOnIsoClass (k := k) C hlocal S W
  let fU := finiteDeletionLocalChangeOnIsoClass (k := k) C hlocal S U
  have hcompat (q : W.IsoClass) : fU (φ q) = fW q := by
    induction q using Quotient.inductionOn with
    | _ i =>
        exact finiteDeletionLocalChangeAt_eq_of_iso
          (k := k) C hlocal S (U.indecomposable (label i))
            (W.indecomposable i) (labelIso i)
  have hrepresented : ∑ q, fW q = ∑ q : {q : U.IsoClass // p q}, fU q.1 := by
    exact Fintype.sum_bijective φsub hφsub fW
      (fun q : {q : U.IsoClass // p q} ↦ fU q.1)
      (fun q ↦ (hcompat q).symm)
  have hclassOutside (q : U.IsoClass) (hq : ¬ p q) : fU q = 0 := by
    induction q using Quotient.inductionOn with
    | _ j =>
        apply houtside j
        intro hUW
        apply hq
        obtain ⟨i, ⟨eWU⟩⟩ := hUW
        refine ⟨Quotient.mk W.isoSetoid i, ?_⟩
        apply Quotient.sound
        exact ⟨(labelIso i).trans eWU⟩
  have hzeroOutside : ∑ q : {q : U.IsoClass // ¬ p q}, fU q.1 = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact hclassOutside q.1 q.2
  have hpartition := Fintype.sum_subtype_add_sum_subtype p fU
  change (∑ q, fW q) = ∑ q, fU q
  calc
    ∑ q, fW q = ∑ q : {q : U.IsoClass // p q}, fU q.1 := hrepresented
    _ = (∑ q : {q : U.IsoClass // p q}, fU q.1) +
        ∑ q : {q : U.IsoClass // ¬ p q}, fU q.1 := by
      rw [hzeroOutside, add_zero]
    _ = ∑ q, fU q := hpartition

/-- The finite local-change sum is the represented pre-deletion density sum
minus the represented deletion-extended density sum. -/
theorem finiteDeletionLocalChangeSum_eq_densitySum_sub
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    finiteDeletionLocalChangeSum (k := k) C hlocal S W =
      finiteModuleLocalDensitySum (k := k) C hlocal W -
        finiteDeletionExtendedLocalDensitySum (k := k) C hlocal S W := by
  classical
  unfold finiteDeletionLocalChangeSum finiteDeletionLocalChangeOnIsoClass
    finiteModuleLocalDensitySum finiteModuleLocalDensityOnIsoClass
    finiteDeletionExtendedLocalDensitySum
    finiteDeletionExtendedLocalDensityOnIsoClass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | _ i => rfl

/-- The manuscript's local change at one object, written as the finite sum
over the two-step control core which contains its entire pointwise support. -/
noncomputable def finiteDeletionLocalChange
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) : ℤ :=
  finiteDeletionLocalChangeSum (k := k) C hlocal ({y} : Set C)
    ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood hlocal 2)

end MagnitudeConjecture.ObjectDeletion
