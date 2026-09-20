import MagnitudeConjecture.CategoryTheory.GradedSupportedProjectiveEquivalence
import MagnitudeConjecture.CategoryTheory.ObjectDeletionConvexComparison

/-! # The principal-projective interval as object deletion -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)

include he hneg in
/-- A nonzero map between the shifted principal projectives cannot increase degree. -/
theorem principalDegree_nonincreasing {p q : PrincipalDegreeCategory R hmul e he0}
    (f : p ⟶ q) (hf : f ≠ 0) : q.2 ≤ p.2 := by
  by_contra hn
  apply hf
  apply (principalDegreeHomEquiv R hmul e he0 he p q).injective
  apply Subtype.ext
  rw [map_zero]
  have h := (principalDegreeHomEquiv R hmul e he0 he p q f).property.1
  rw [hneg (p.2 - q.2) (by omega)] at h
  exact h

include he hneg in
/-- A factorization through an omitted degree vanishes between interval objects. -/
theorem principalInterval_noDeletedFactorization (m : ℕ) :
    ObjectDeletion.NoDeletedFactorization
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) := by
  intro X Y Z hX hY hZ a b
  by_contra hab
  have ha : a.unop ≠ 0 := by
    intro ha
    have hz : a = 0 := Quiver.Hom.unop_inj ha
    exact hab (by simp [hz])
  have hb : b.unop ≠ 0 := by
    intro hb
    have hz : b = 0 := Quiver.Hom.unop_inj hb
    exact hab (by simp [hz])
  have hda := principalDegree_nonincreasing R hmul e he0 he hneg a.unop ha
  have hdb := principalDegree_nonincreasing R hmul e he0 he hneg b.unop hb
  change ¬ (X.unop.2 < 0 ∨ (m : ℤ) < X.unop.2) at hX
  change ¬ (Y.unop.2 < 0 ∨ (m : ℤ) < Y.unop.2) at hY
  change Z.unop.2 < 0 ∨ (m : ℤ) < Z.unop.2 at hZ
  omega

/-- Finite interval coordinates viewed as surviving opposite degree objects. -/
def principalIntervalOpToSurviving (m : ℕ) :
    (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ ⥤ ObjectDeletion.SurvivingCategory
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) where
  obj p := ⟨op (intervalProjectiveLabel R hmul e he0 m p.unop), by
    change ¬ ((p.unop.2.val : ℤ) < 0 ∨ (m : ℤ) < p.unop.2.val)
    have hp := p.unop.2.isLt
    omega⟩
  map f := ObjectProperty.homMk f.unop.hom.op

instance principalIntervalOpToSurviving_full (m : ℕ) :
    (principalIntervalOpToSurviving R hmul e he0 m).Full where
  map_surjective {X Y} f := ⟨(show Y.unop ⟶ X.unop from
    InducedCategory.homMk f.hom.unop).op, by apply ObjectProperty.hom_ext; rfl⟩

instance principalIntervalOpToSurviving_faithful (m : ℕ) :
    (principalIntervalOpToSurviving R hmul e he0 m).Faithful where
  map_injective h := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    exact congrArg (fun f ↦ f.hom.unop) h

instance principalIntervalOpToSurviving_additive (m : ℕ) :
    (principalIntervalOpToSurviving R hmul e he0 m).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; rfl

instance principalIntervalOpToSurviving_linear (m : ℕ) :
    (principalIntervalOpToSurviving R hmul e he0 m).Linear k where
  map_smul := by intros; apply ObjectProperty.hom_ext; rfl

instance principalIntervalOpToSurviving_essSurj (m : ℕ) :
    (principalIntervalOpToSurviving R hmul e he0 m).EssSurj where
  mem_essImage Y := by
    have hy := Y.property
    change ¬ (Y.obj.unop.2 < 0 ∨ (m : ℤ) < Y.obj.unop.2) at hy
    let X : PrincipalIntervalCategory R hmul e he0 m :=
      (Y.obj.unop.1, ⟨Y.obj.unop.2.toNat, by omega⟩)
    have heq : (principalIntervalOpToSurviving R hmul e he0 m).obj (op X) = Y := by
      apply ObjectProperty.FullSubcategory.ext
      apply Opposite.unop_injective
      apply Prod.ext
      · rfl
      · change (Y.obj.unop.2.toNat : ℤ) = Y.obj.unop.2
        omega
    exact ⟨op X, ⟨eqToIso heq⟩⟩

/-- The interval and surviving full categories are equivalent. -/
def principalIntervalOpSurvivingEquivalence (m : ℕ) :
    (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ ≌ ObjectDeletion.SurvivingCategory
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) := by
  letI : (principalIntervalOpToSurviving R hmul e he0 m).IsEquivalence := {}
  exact (principalIntervalOpToSurviving R hmul e he0 m).asEquivalence

instance principalIntervalOpSurvivingEquivalence_additive (m : ℕ) :
    (principalIntervalOpSurvivingEquivalence R hmul e he0 m).functor.Additive :=
  inferInstanceAs ((principalIntervalOpToSurviving R hmul e he0 m).Additive)
instance principalIntervalOpSurvivingEquivalence_linear (m : ℕ) :
    (principalIntervalOpSurvivingEquivalence R hmul e he0 m).functor.Linear k :=
  inferInstanceAs ((principalIntervalOpToSurviving R hmul e he0 m).Linear k)

/-- Interval restriction agrees with deletion because no nonzero factorization leaves the interval. -/
def principalIntervalOpDeletionEquivalence (m : ℕ) :
    (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ ≌ ObjectDeletion.DeletionCategory (k := k)
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) :=
  (principalIntervalOpSurvivingEquivalence R hmul e he0 m).trans
    (ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
      (principalInterval_noDeletedFactorization R hmul e he0 he hneg m))

instance principalIntervalOpDeletionEquivalence_additive (m : ℕ) :
    (principalIntervalOpDeletionEquivalence R hmul e he0 he hneg m).functor.Additive := by
  change ((principalIntervalOpSurvivingEquivalence R hmul e he0 m).functor ⋙
    (ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
      (principalInterval_noDeletedFactorization R hmul e he0 he hneg m)).functor).Additive
  infer_instance
instance principalIntervalOpDeletionEquivalence_linear (m : ℕ) :
    (principalIntervalOpDeletionEquivalence R hmul e he0 he hneg m).functor.Linear k := by
  change ((principalIntervalOpSurvivingEquivalence R hmul e he0 m).functor ⋙
    (ObjectDeletion.survivingDeletionEquivalence (k := k) _ _
      (principalInterval_noDeletedFactorization R hmul e he0 he hneg m)).functor).Linear k
  infer_instance

end MagnitudeConjecture.Graded.FiniteGradedModule
