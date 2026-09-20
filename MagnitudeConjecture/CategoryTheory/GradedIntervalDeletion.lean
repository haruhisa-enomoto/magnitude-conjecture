import MagnitudeConjecture.CategoryTheory.GradedIntervalCategory
import MagnitudeConjecture.CategoryTheory.ObjectDeletionConvexComparison

/-!
# Interval restriction as object deletion

Nonnegative degrees prevent a nonzero factorization between interval objects
from leaving the interval. Thus the finite interval category agrees with the
object-deletion quotient, allowing use of the proved extension-by-zero module
equivalence. This uses degree monotonicity, not a covering or averaging theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

/-- The objects outside the closed degree interval. -/
def outsideInterval (m : ℕ) : Set (DegreeObject G) :=
  {X | X.degree < 0 ∨ (m : ℤ) < X.degree}

/-- Between retained objects, factoring through a deleted degree gives zero. -/
theorem noDeletedFactorization_outsideInterval (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) :
    ObjectDeletion.NoDeletedFactorization (DegreeObject G) (G.outsideInterval m) := by
  intro X Y Z hX hY hZ a b
  by_contra hab
  have ha : a ≠ 0 := by intro hz; apply hab; simp [hz]
  have hb : b ≠ 0 := by intro hz; apply hab; simp [hz]
  have had := G.degree_bounds_of_ne_zero h hbound a ha
  have hbd := G.degree_bounds_of_ne_zero h hbound b hb
  change ¬ (X.degree < 0 ∨ (m : ℤ) < X.degree) at hX
  change ¬ (Y.degree < 0 ∨ (m : ℤ) < Y.degree) at hY
  change Z.degree < 0 ∨ (m : ℤ) < Z.degree at hZ
  omega

/-- The finite degree coordinates identify with the surviving objects. -/
def intervalToSurviving (m : ℕ) :
    G.Interval m ⥤ ObjectDeletion.SurvivingCategory (DegreeObject G) (G.outsideInterval m) where
  obj X := ⟨G.intervalObject m X, by
    change ¬ ((X.2.val : ℤ) < 0 ∨ (m : ℤ) < X.2.val)
    have hx := X.2.isLt
    omega⟩
  map f := ObjectProperty.homMk f.hom

instance (m : ℕ) : (G.intervalToSurviving m).Full where
  map_surjective f := ⟨InducedCategory.homMk f.hom, by
    apply ObjectProperty.hom_ext
    rfl⟩

instance (m : ℕ) : (G.intervalToSurviving m).Faithful where
  map_injective h := InducedCategory.hom_ext (congrArg (fun f ↦ f.hom) h)

instance (m : ℕ) : (G.intervalToSurviving m).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; rfl

instance (m : ℕ) : (G.intervalToSurviving m).Linear k where
  map_smul := by intros; apply ObjectProperty.hom_ext; rfl

instance (m : ℕ) : (G.intervalToSurviving m).EssSurj where
  mem_essImage Y := by
    have hy := Y.property
    change ¬ (Y.obj.degree < 0 ∨ (m : ℤ) < Y.obj.degree) at hy
    let X : G.Interval m := (Y.obj.obj, ⟨Y.obj.degree.toNat, by omega⟩)
    have heq : (G.intervalToSurviving m).obj X = Y := by
      apply ObjectProperty.FullSubcategory.ext
      change (⟨Y.obj.obj, (Y.obj.degree.toNat : ℤ)⟩ : DegreeObject G) = Y.obj
      have hd : (Y.obj.degree.toNat : ℤ) = Y.obj.degree := by omega
      rw [hd]
    exact ⟨X, ⟨eqToIso heq⟩⟩

/-- The interval category is equivalent to the full subcategory on surviving
degree-labelled objects. -/
def intervalSurvivingEquivalence (m : ℕ) :
    G.Interval m ≌ ObjectDeletion.SurvivingCategory (DegreeObject G) (G.outsideInterval m) := by
  letI : (G.intervalToSurviving m).IsEquivalence := {}
  exact (G.intervalToSurviving m).asEquivalence

instance (m : ℕ) : (G.intervalSurvivingEquivalence m).functor.Additive :=
  inferInstanceAs ((G.intervalToSurviving m).Additive)

instance (m : ℕ) : (G.intervalSurvivingEquivalence m).functor.Linear k :=
  inferInstanceAs ((G.intervalToSurviving m).Linear k)

/-- Nonnegative bounded Hom degrees identify the interval with deletion of
all degrees outside it. -/
def intervalDeletionEquivalence (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) :
    G.Interval m ≌ ObjectDeletion.DeletionCategory (k := k)
      (DegreeObject G) (G.outsideInterval m) :=
  (G.intervalSurvivingEquivalence m).trans
    (ObjectDeletion.survivingDeletionEquivalence (k := k) (DegreeObject G)
      (G.outsideInterval m) (G.noDeletedFactorization_outsideInterval h hbound m))

instance (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) : (G.intervalDeletionEquivalence h hbound m).functor.Additive := by
  change ((G.intervalSurvivingEquivalence m).functor ⋙
    (ObjectDeletion.survivingDeletionEquivalence (k := k) (DegreeObject G)
      (G.outsideInterval m) (G.noDeletedFactorization_outsideInterval h hbound m)).functor).Additive
  infer_instance

instance (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (m : ℕ) : (G.intervalDeletionEquivalence h hbound m).functor.Linear k := by
  change ((G.intervalSurvivingEquivalence m).functor ⋙
    (ObjectDeletion.survivingDeletionEquivalence (k := k) (DegreeObject G)
      (G.outsideInterval m) (G.noDeletedFactorization_outsideInterval h hbound m)).functor).Linear k
  infer_instance

end MagnitudeConjecture.GradedCategory.HomGrading
