import MagnitudeConjecture.CategoryTheory.GradedPrincipalRetainedOrthogonality
import MagnitudeConjecture.CategoryTheory.OrthogonalBlockSurplus
import MagnitudeConjecture.CategoryTheory.FullyFaithfulObjectLift

/-! # Each literal retained block is a translated small interval -/
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

/-- The full subcategory of retained objects in one specified block. -/
abbrev PrincipalRetainedBlockCategory (r h q : ℕ) (j : Fin q) :=
  ObjectDeletion.SurvivingCategory (PrincipalRetainedCategory R hmul e he0 r h q)
    (CoveringHom.blockComplement (principalRetainedBlock R hmul e he0 r h q) j)

/-- A block coordinate belongs to its specified block. -/
theorem principalRetainedBlock_blockObject (r h q : ℕ) (j : Fin q) (p : ι × Fin (r + 1)) :
    principalRetainedBlock R hmul e he0 r h q (principalRetainedBlockObject R hmul e he0 r h q (j, p)) = j :=
  congrArg Prod.fst ((principalRetainedBlockEquiv R hmul e he0 r h q).symm_apply_apply (j, p))

/-- Small interval labels as positive objects of the corresponding retained block. -/
def principalIntervalRetainedBlockObj (r h q : ℕ) (j : Fin q)
    (p : PrincipalIntervalCategory R hmul e he0 r) :
    (PrincipalRetainedBlockCategory R hmul e he0 r h q j)ᵒᵖ :=
  op ⟨principalRetainedBlockObject R hmul e he0 r h q (j, p), by
    change ¬ principalRetainedBlock R hmul e he0 r h q _ ≠ j
    exact not_not.mpr (principalRetainedBlock_blockObject R hmul e he0 r h q j p)⟩

/-- Realize a single retained block inside the whole principal degree category. -/
def principalRetainedBlockRealization (r h q : ℕ) (j : Fin q) :
    (PrincipalRetainedBlockCategory R hmul e he0 r h q j)ᵒᵖ ⥤ PrincipalDegreeCategory R hmul e he0 :=
  (ObjectDeletion.IsSurviving (PrincipalRetainedCategory R hmul e he0 r h q)
    (CoveringHom.blockComplement (principalRetainedBlock R hmul e he0 r h q) j)).ι.op ⋙
      principalRetainedRealization R hmul e he0 r h q

instance principalRetainedBlockRealization_full (r h q : ℕ) (j : Fin q) :
    (principalRetainedBlockRealization R hmul e he0 r h q j).Full := by
  dsimp [principalRetainedBlockRealization]; infer_instance
instance principalRetainedBlockRealization_faithful (r h q : ℕ) (j : Fin q) :
    (principalRetainedBlockRealization R hmul e he0 r h q j).Faithful := by
  dsimp [principalRetainedBlockRealization]; infer_instance
instance principalRetainedBlockRealization_additive (r h q : ℕ) (j : Fin q) :
    (principalRetainedBlockRealization R hmul e he0 r h q j).Additive := by
  dsimp [principalRetainedBlockRealization]; infer_instance
instance principalRetainedBlockRealization_linear (r h q : ℕ) (j : Fin q) :
    (principalRetainedBlockRealization R hmul e he0 r h q j).Linear k := by
  dsimp [principalRetainedBlockRealization]; infer_instance

variable (he : ∀ i, e i * e i = e i)

/-- The two realizations of a block point agree after common degree translation. -/
def principalIntervalRetainedBlockObjIso (r h q : ℕ) (j : Fin q)
    (p : PrincipalIntervalCategory R hmul e he0 r) :
    (principalRetainedBlockRealization R hmul e he0 r h q j).obj
        (principalIntervalRetainedBlockObj R hmul e he0 r h q j p) ≅
      (principalDegreeShift R hmul e he0 he ((j.val : ℤ) * ((r : ℤ) + h + 1))).obj
        (intervalProjectiveLabel R hmul e he0 r p) := eqToIso (by
  change (p.1, ((j.val * (r + h + 1) + p.2.val : ℕ) : ℤ)) =
    (p.1, (p.2.val : ℤ) + (j.val : ℤ) * ((r : ℤ) + h + 1))
  apply Prod.ext
  · rfl
  push_cast
  omega)

/-- Common degree translation lifted into the literal retained block category. -/
def principalIntervalToRetainedBlock (r h q : ℕ) (j : Fin q) :
    PrincipalIntervalCategory R hmul e he0 r ⥤
      (PrincipalRetainedBlockCategory R hmul e he0 r h q j)ᵒᵖ :=
  MagnitudeConjecture.CategoryTheory.fullyFaithfulObjectLift
    (principalRetainedBlockRealization R hmul e he0 r h q j)
    (inducedFunctor (intervalProjectiveLabel R hmul e he0 r) ⋙
      principalDegreeShift R hmul e he0 he ((j.val : ℤ) * ((r : ℤ) + h + 1)))
    (principalIntervalRetainedBlockObj R hmul e he0 r h q j)
    (principalIntervalRetainedBlockObjIso R hmul e he0 he r h q j)

instance principalIntervalToRetainedBlock_full (r h q : ℕ) (j : Fin q) :
    (principalIntervalToRetainedBlock R hmul e he0 he r h q j).Full := by
  dsimp [principalIntervalToRetainedBlock]; infer_instance
instance principalIntervalToRetainedBlock_faithful (r h q : ℕ) (j : Fin q) :
    (principalIntervalToRetainedBlock R hmul e he0 he r h q j).Faithful := by
  dsimp [principalIntervalToRetainedBlock]; infer_instance
instance principalIntervalToRetainedBlock_additive (r h q : ℕ) (j : Fin q) :
    (principalIntervalToRetainedBlock R hmul e he0 he r h q j).Additive := by
  dsimp [principalIntervalToRetainedBlock]; infer_instance
instance principalIntervalToRetainedBlock_linear (r h q : ℕ) (j : Fin q) :
    (principalIntervalToRetainedBlock R hmul e he0 he r h q j).Linear k := by
  dsimp [principalIntervalToRetainedBlock]; infer_instance

/-- Every object of the literal retained block has small-interval coordinates. -/
theorem principalIntervalRetainedBlockObj_surjective (r h q : ℕ) (j : Fin q) :
    Function.Surjective (principalIntervalRetainedBlockObj R hmul e he0 r h q j) := by
  intro Y
  let E := principalRetainedBlockEquiv R hmul e he0 r h q
  let p := E.symm Y.unop.obj
  have hp : p.1 = j := not_ne_iff.mp Y.unop.property
  have hp' : (j, p.2) = p := by
    apply Prod.ext
    · exact hp.symm
    · rfl
  refine ⟨p.2, ?_⟩
  apply Opposite.unop_injective
  apply ObjectProperty.FullSubcategory.ext
  exact (congrArg E hp').trans (E.apply_symm_apply Y.unop.obj)

instance principalIntervalToRetainedBlock_essSurj (r h q : ℕ) (j : Fin q) :
    (principalIntervalToRetainedBlock R hmul e he0 he r h q j).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, hX⟩ := principalIntervalRetainedBlockObj_surjective R hmul e he0 r h q j Y
    exact ⟨X, ⟨eqToIso hX⟩⟩

instance principalIntervalToRetainedBlock_leftOp_linear (r h q : ℕ) (j : Fin q) :
    (principalIntervalToRetainedBlock R hmul e he0 he r h q j).leftOp.Linear k where
  map_smul f c := by
    apply Quiver.Hom.op_inj
    change (principalIntervalToRetainedBlock R hmul e he0 he r h q j).map (c • f.unop) =
      c • (principalIntervalToRetainedBlock R hmul e he0 he r h q j).map f.unop
    exact (principalIntervalToRetainedBlock R hmul e he0 he r h q j).map_smul c f.unop

/-- In the module variance, the small interval is equivalent to the retained block. -/
def principalIntervalOpRetainedBlockEquivalence (r h q : ℕ) (j : Fin q) :
    (PrincipalIntervalCategory R hmul e he0 r)ᵒᵖ ≌
      PrincipalRetainedBlockCategory R hmul e he0 r h q j := by
  let F := principalIntervalToRetainedBlock R hmul e he0 he r h q j
  letI : F.IsEquivalence := {}
  exact F.leftOp.asEquivalence

instance principalIntervalOpRetainedBlockEquivalence_additive (r h q : ℕ) (j : Fin q) :
    (principalIntervalOpRetainedBlockEquivalence R hmul e he0 he r h q j).functor.Additive :=
  inferInstanceAs ((principalIntervalToRetainedBlock R hmul e he0 he r h q j).leftOp.Additive)
instance principalIntervalOpRetainedBlockEquivalence_linear (r h q : ℕ) (j : Fin q) :
    (principalIntervalOpRetainedBlockEquivalence R hmul e he0 he r h q j).functor.Linear k :=
  inferInstanceAs ((principalIntervalToRetainedBlock R hmul e he0 he r h q j).leftOp.Linear k)

/-- Deleting all other retained blocks gives precisely the small interval category. -/
def principalRetainedBlockDeletionEquivalence
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ) (j : Fin q) :
    ObjectDeletion.DeletionCategory (k := k) (PrincipalRetainedCategory R hmul e he0 r h q)
      (CoveringHom.blockComplement (principalRetainedBlock R hmul e he0 r h q) j) ≌
        (PrincipalIntervalCategory R hmul e he0 r)ᵒᵖ :=
  (ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
    (CoveringHom.blockComplement_noDeletedFactorization
      (principalRetainedBlock R hmul e he0 r h q)
      (principalRetained_hom_eq_zero_of_block_ne R hmul e he0 he hneg h hupper r q) j)).symm.trans
    (principalIntervalOpRetainedBlockEquivalence R hmul e he0 he r h q j).symm

instance principalRetainedBlockDeletionEquivalence_additive
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ) (j : Fin q) :
    (principalRetainedBlockDeletionEquivalence R hmul e he0 he hneg h hupper r q j).functor.Additive := by
  let E₁ := ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
    (CoveringHom.blockComplement_noDeletedFactorization
      (principalRetainedBlock R hmul e he0 r h q)
      (principalRetained_hom_eq_zero_of_block_ne R hmul e he0 he hneg h hupper r q) j)
  let E₂ := principalIntervalOpRetainedBlockEquivalence R hmul e he0 he r h q j
  let : E₁.inverse.Additive := Equivalence.inverse_additive E₁
  let : E₂.inverse.Additive := Equivalence.inverse_additive E₂
  change (E₁.inverse ⋙ E₂.inverse).Additive
  infer_instance
instance principalRetainedBlockDeletionEquivalence_linear
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ) (j : Fin q) :
    (principalRetainedBlockDeletionEquivalence R hmul e he0 he hneg h hupper r q j).functor.Linear k := by
  let E₁ := ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
    (CoveringHom.blockComplement_noDeletedFactorization
      (principalRetainedBlock R hmul e he0 r h q)
      (principalRetained_hom_eq_zero_of_block_ne R hmul e he0 he hneg h hupper r q) j)
  let E₂ := principalIntervalOpRetainedBlockEquivalence R hmul e he0 he r h q j
  let : E₁.inverse.Linear k := Equivalence.inverseLinear k E₁
  let : E₂.inverse.Linear k := Equivalence.inverseLinear k E₂
  change (E₁.inverse ⋙ E₂.inverse).Linear k
  infer_instance

end MagnitudeConjecture.Graded.FiniteGradedModule
