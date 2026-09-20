import MagnitudeConjecture.CategoryTheory.GradedIntervalDeletion
import MagnitudeConjecture.CategoryTheory.OppositeLinear

/-!
# Right-module variance for interval deletion

Right modules are contravariant on projectives. We therefore identify the
opposite interval category with deletion from the opposite degree category,
so the existing covariant module machinery applies with the correct variance.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

def outsideIntervalOp (m : ℕ) : Set (DegreeObject G)ᵒᵖ :=
  {X | X.unop ∈ G.outsideInterval m}

theorem noDeletedFactorization_outsideIntervalOp (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) :
    ObjectDeletion.NoDeletedFactorization (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m) := by
  intro X Y Z hX hY hZ a b
  apply Quiver.Hom.unop_inj
  change b.unop ≫ a.unop = 0
  exact G.noDeletedFactorization_outsideInterval h hbound m hY hX hZ b.unop a.unop

def intervalOpToSurviving (m : ℕ) :
    (G.Interval m)ᵒᵖ ⥤ ObjectDeletion.SurvivingCategory
      (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m) where
  obj X := ⟨op (G.intervalObject m X.unop), by
    change ¬ ((X.unop.2.val : ℤ) < 0 ∨ (m : ℤ) < X.unop.2.val)
    have hx := X.unop.2.isLt
    omega⟩
  map f := ObjectProperty.homMk f.unop.hom.op

instance (m : ℕ) : (G.intervalOpToSurviving m).Full where
  map_surjective {X Y} f := ⟨(show Y.unop ⟶ X.unop from
    InducedCategory.homMk f.hom.unop).op, by
    apply ObjectProperty.hom_ext
    rfl⟩

instance (m : ℕ) : (G.intervalOpToSurviving m).Faithful where
  map_injective h := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    exact congrArg (fun f ↦ f.hom.unop) h

instance (m : ℕ) : (G.intervalOpToSurviving m).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; rfl

instance (m : ℕ) : (G.intervalOpToSurviving m).Linear k where
  map_smul := by intros; apply ObjectProperty.hom_ext; rfl

instance (m : ℕ) : (G.intervalOpToSurviving m).EssSurj where
  mem_essImage Y := by
    have hy := Y.property
    change ¬ (Y.obj.unop.degree < 0 ∨ (m : ℤ) < Y.obj.unop.degree) at hy
    let X : G.Interval m := (Y.obj.unop.obj, ⟨Y.obj.unop.degree.toNat, by omega⟩)
    have heq : (G.intervalOpToSurviving m).obj (op X) = Y := by
      apply ObjectProperty.FullSubcategory.ext
      apply Opposite.unop_injective
      change (⟨Y.obj.unop.obj, (Y.obj.unop.degree.toNat : ℤ)⟩ : DegreeObject G) = Y.obj.unop
      have hd : (Y.obj.unop.degree.toNat : ℤ) = Y.obj.unop.degree := by omega
      rw [hd]
    exact ⟨op X, ⟨eqToIso heq⟩⟩

def intervalOpSurvivingEquivalence (m : ℕ) :
    (G.Interval m)ᵒᵖ ≌ ObjectDeletion.SurvivingCategory
      (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m) := by
  letI : (G.intervalOpToSurviving m).IsEquivalence := {}
  exact (G.intervalOpToSurviving m).asEquivalence

instance (m : ℕ) : (G.intervalOpSurvivingEquivalence m).functor.Additive :=
  inferInstanceAs ((G.intervalOpToSurviving m).Additive)

instance (m : ℕ) : (G.intervalOpSurvivingEquivalence m).functor.Linear k :=
  inferInstanceAs ((G.intervalOpToSurviving m).Linear k)

def intervalOpDeletionEquivalence (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) :
    (G.Interval m)ᵒᵖ ≌ ObjectDeletion.DeletionCategory (k := k)
      (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m) :=
  (G.intervalOpSurvivingEquivalence m).trans
    (ObjectDeletion.survivingDeletionEquivalence (k := k) (DegreeObject G)ᵒᵖ
      (G.outsideIntervalOp m) (G.noDeletedFactorization_outsideIntervalOp h hbound m))

instance (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) : (G.intervalOpDeletionEquivalence h hbound m).functor.Additive := by
  change ((G.intervalOpSurvivingEquivalence m).functor ⋙
    (ObjectDeletion.survivingDeletionEquivalence (k := k) (DegreeObject G)ᵒᵖ
      (G.outsideIntervalOp m) (G.noDeletedFactorization_outsideIntervalOp h hbound m)).functor).Additive
  infer_instance

instance (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) : (G.intervalOpDeletionEquivalence h hbound m).functor.Linear k := by
  change ((G.intervalOpSurvivingEquivalence m).functor ⋙
    (ObjectDeletion.survivingDeletionEquivalence (k := k) (DegreeObject G)ᵒᵖ
      (G.outsideIntervalOp m) (G.noDeletedFactorization_outsideIntervalOp h hbound m)).functor).Linear k
  infer_instance

end MagnitudeConjecture.GradedCategory.HomGrading
