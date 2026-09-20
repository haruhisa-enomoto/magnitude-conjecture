import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalTuple
import MagnitudeConjecture.Combinatorics.SeparatedIntervalCoordinates
import MagnitudeConjecture.CategoryTheory.ObjectDeletionMatrixAlgebra

/-! # The literal retained interval category and its block coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0)

/-- The actual surviving category inside the packed ambient interval. -/
abbrev PrincipalRetainedCategory (r h q : ℕ) :=
  ObjectDeletion.SurvivingCategory
    (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ
    (principalIntervalSeparatedDeleted R hmul e he0 h (GradedInterval.packingEnd r h q) r q)

/-- A block coordinate as an actual surviving interval object. -/
def principalRetainedBlockObject (r h q : ℕ) (p : Fin q × (ι × Fin (r + 1))) :
    PrincipalRetainedCategory R hmul e he0 r h q :=
  ⟨op (p.2.1, GradedInterval.blockPoint r h q p.1 p.2.2), by
    change ¬ ¬ GradedInterval.Retained r h q _
    exact not_not.mpr ⟨p.1.val, p.1.isLt, GradedInterval.blockPoint_inBlock r h q p.1 p.2.2⟩⟩

/-- Block coordinates enumerate the literal surviving objects without repetition. -/
theorem principalRetainedBlockObject_bijective (r h q : ℕ) :
    Function.Bijective (principalRetainedBlockObject R hmul e he0 r h q) := by
  constructor
  · intro p t hpt
    have hi := congrArg (fun X : PrincipalRetainedCategory R hmul e he0 r h q ↦ X.obj.unop.1) hpt
    have hd := congrArg (fun X : PrincipalRetainedCategory R hmul e he0 r h q ↦ X.obj.unop.2) hpt
    have hb : (p.1, p.2.2) = (t.1, t.2.2) :=
      GradedInterval.blockPoint_injective r h q hd
    exact Prod.ext (congrArg (fun z : Fin q × Fin (r + 1) ↦ z.1) hb)
      (Prod.ext hi (congrArg (fun z : Fin q × Fin (r + 1) ↦ z.2) hb))
  · intro X
    have hx := X.property
    change ¬ ¬ GradedInterval.Retained r h q (X.obj.unop.2.val : ℤ) at hx
    obtain ⟨p, hp⟩ := GradedInterval.exists_blockPoint_of_retained r h q X.obj.unop.2 (not_not.mp hx)
    refine ⟨(p.1, X.obj.unop.1, p.2), ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    apply Opposite.unop_injective
    exact Prod.ext rfl hp

/-- Finite block coordinates for the retained category. -/
def principalRetainedBlockEquiv (r h q : ℕ) :
    Fin q × (ι × Fin (r + 1)) ≃ PrincipalRetainedCategory R hmul e he0 r h q :=
  Equiv.ofBijective _ (principalRetainedBlockObject_bijective R hmul e he0 r h q)

/-- The retained category is finite, including the empty packing. -/
instance principalRetainedFintype (r h q : ℕ) :
    Fintype (PrincipalRetainedCategory R hmul e he0 r h q) :=
  Fintype.ofEquiv _ (principalRetainedBlockEquiv R hmul e he0 r h q)

/-- Realize opposite retained objects by their actual principal projectives. -/
def principalRetainedRealization (r h q : ℕ) :
    (PrincipalRetainedCategory R hmul e he0 r h q)ᵒᵖ ⥤
      PrincipalDegreeCategory R hmul e he0 where
  obj X := intervalProjectiveLabel R hmul e he0 (GradedInterval.packingEnd r h q) X.unop.obj.unop
  map f := f.unop.hom.unop.hom

instance principalRetainedRealization_additive (r h q : ℕ) :
    (principalRetainedRealization R hmul e he0 r h q).Additive where
  map_add {_X _Y} _f _g := rfl

instance principalRetainedRealization_linear (r h q : ℕ) :
    (principalRetainedRealization R hmul e he0 r h q).Linear k where
  map_smul _ _ := rfl

instance principalRetainedRealization_faithful (r h q : ℕ) :
    (principalRetainedRealization R hmul e he0 r h q).Faithful where
  map_injective hfg := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Quiver.Hom.unop_inj
    exact InducedCategory.hom_ext hfg

instance principalRetainedRealization_full (r h q : ℕ) :
    (principalRetainedRealization R hmul e he0 r h q).Full where
  map_surjective {X Y} f := by
    let g : X.unop.obj.unop ⟶ Y.unop.obj.unop := InducedCategory.homMk f
    let t : Y.unop ⟶ X.unop := ObjectProperty.homMk g.op
    exact ⟨t.op, rfl⟩

/-- The matrix algebra of the literal retained interval category. -/
abbrev principalRetainedAlgebra (r h q : ℕ) :=
  End (CoveringHom.categoryAlgebraTuple (C := PrincipalRetainedCategory R hmul e he0 r h q))

/-- The retained category algebra is the separated-block tuple algebra. -/
def principalRetainedAlgebraTupleEquiv (r h q : ℕ) :
    principalRetainedAlgebra R hmul e he0 r h q ≃ₐ[k]
      End (principalSeparatedBlockTuple R hmul e he0 r h q) := by
  let F := principalRetainedRealization R hmul e he0 r h q
  let X := fun p : PrincipalRetainedCategory R hmul e he0 r h q ↦ F.obj (op p)
  let E := principalRetainedBlockEquiv R hmul e he0 r h q
  have heq : (⟨Fin q × (ι × Fin (r + 1)), X ∘ E⟩ : Mat_ (PrincipalDegreeCategory R hmul e he0)) =
      principalSeparatedBlockTuple R hmul e he0 r h q := by
    congr 1
    funext p
    change (p.2.1, ((GradedInterval.blockPoint r h q p.1 p.2.2).val : ℤ)) =
      (p.2.1, (p.2.2.val : ℤ) + (p.1.val : ℤ) * ((r : ℤ) + h + 1))
    apply Prod.ext
    · rfl
    change ((p.1.val * (r + h + 1) + p.2.2.val : ℕ) : ℤ) =
      (p.2.2.val : ℤ) + (p.1.val : ℤ) * ((r : ℤ) + h + 1)
    push_cast
    omega
  exact (MagnitudeConjecture.CategoryTheory.matrixFunctorEndAlgEquiv F
    (CoveringHom.categoryAlgebraTuple (C := PrincipalRetainedCategory R hmul e he0 r h q))).trans
      ((MagnitudeConjecture.CategoryTheory.matrixTupleReindexEndAlgEquiv E X).symm.trans
        (MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv (eqToIso heq)))

/-- The actual retained category algebra is the product of q smaller interval algebras. -/
def principalRetainedAlgebraProductEquiv (he : ∀ i, e i * e i = e i)
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ) :
    principalRetainedAlgebra R hmul e he0 r h q ≃ₐ[k]
      (Fin q → principalIntervalAlgebra R hmul e he0 he r) :=
  (principalRetainedAlgebraTupleEquiv R hmul e he0 r h q).trans
    (principalSeparatedBlockAlgebraEquiv R hmul e he0 he hneg h hupper r q)

/-- The matrix algebra of the literal finite category after deleting the gaps. -/
abbrev principalPackedDeletionAlgebra (r h q : ℕ) := by
  letI := principalRetainedFintype R hmul e he0 r h q
  exact End (CoveringHom.categoryAlgebraTuple (C := ObjectDeletion.DeletionCategory (k := k)
    (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ
    (principalIntervalSeparatedDeleted R hmul e he0 h (GradedInterval.packingEnd r h q) r q)))

/-- Gap deletion gives the product of the actual smaller interval algebras. -/
def principalPackedDeletionAlgebraProductEquiv (he : ∀ i, e i * e i = e i)
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ) :
    principalPackedDeletionAlgebra R hmul e he0 r h q ≃ₐ[k]
      (Fin q → principalIntervalAlgebra R hmul e he0 he r) := by
  letI := principalRetainedFintype R hmul e he0 r h q
  exact (ObjectDeletion.survivingDeletionMatrixAlgEquiv
    (PrincipalIntervalCategory R hmul e he0 (GradedInterval.packingEnd r h q))ᵒᵖ
    (principalIntervalSeparatedDeleted R hmul e he0 h (GradedInterval.packingEnd r h q) r q)
    (principalIntervalSeparated_noDeletedFactorization R hmul e he0 he hneg h hupper
      (GradedInterval.packingEnd r h q) r q)).symm.trans
        (principalRetainedAlgebraProductEquiv R hmul e he0 he hneg h hupper r q)

end MagnitudeConjecture.Graded.FiniteGradedModule
