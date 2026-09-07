import MagnitudeConjecture.Algebra.IdempotentCorner
import MagnitudeConjecture.Algebra.RightModulePrimitiveProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.HomSubbimodule

/-!
# The concrete corner category of a primitive-projective presentation

A complete primitive-projective presentation realizes the selected
projective category by the literal corners `e_q A e_p`.  This auxiliary
category keeps ambient algebra coordinates as the morphism type, which is
the convenient form for the finite-ideal pencil argument.  Its canonical
linear functor to the existing selected-projective category is fully
faithful and bijective on objects.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

/-- The literal primitive-corner category attached to the presentation.
The type wrapper retains `P` as an inferable parameter. -/
def PrimitiveCornerCategory
    (_P : S.PrimitiveProjectivePresentation) :=
  S.ProjectiveLabel

/-- Recover the selected-projective label represented by a corner object. -/
def cornerVertex (P : S.PrimitiveProjectivePresentation) :
    P.PrimitiveCornerCategory ≃ S.ProjectiveLabel :=
  Equiv.refl S.ProjectiveLabel

noncomputable instance primitiveCornerCategoryFintype
    (P : S.PrimitiveProjectivePresentation) :
    Fintype P.PrimitiveCornerCategory :=
  Fintype.ofEquiv S.ProjectiveLabel P.cornerVertex.symm

noncomputable instance primitiveCornerCategoryDecidableEq
    (P : S.PrimitiveProjectivePresentation) :
    DecidableEq P.PrimitiveCornerCategory :=
  Classical.decEq _

noncomputable instance primitiveCornerCategoryCategory
    (P : S.PrimitiveProjectivePresentation) :
    CategoryTheory.Category P.PrimitiveCornerCategory where
  Hom p q := idempotentCorner (k := k) P.idempotent
    (P.cornerVertex q) (P.cornerVertex p)
  id p := by
    refine ⟨P.idempotent (P.cornerVertex p), ?_⟩
    refine ⟨1, ?_⟩
    change P.idempotent (P.cornerVertex p) * 1 *
      P.idempotent (P.cornerVertex p) = P.idempotent (P.cornerVertex p)
    simpa using (P.primitive (P.cornerVertex p)).idempotent.eq
  comp {p q r} f g := by
    refine ⟨g.1 * f.1, ?_⟩
    obtain ⟨a, ha⟩ := f.2
    obtain ⟨b, hb⟩ := g.2
    change P.idempotent (P.cornerVertex q) * a *
      P.idempotent (P.cornerVertex p) = f.1 at ha
    change P.idempotent (P.cornerVertex r) * b *
      P.idempotent (P.cornerVertex q) = g.1 at hb
    refine ⟨b * P.idempotent (P.cornerVertex q) * a, ?_⟩
    change P.idempotent (P.cornerVertex r) *
        (b * P.idempotent (P.cornerVertex q) * a) *
          P.idempotent (P.cornerVertex p) = g.1 * f.1
    rw [← ha, ← hb]
    have hq := (P.primitive (P.cornerVertex q)).idempotent.eq
    simp only [← mul_assoc]
    rw [mul_assoc
      (P.idempotent (P.cornerVertex r) * b)
      (P.idempotent (P.cornerVertex q))
      (P.idempotent (P.cornerVertex q)), hq]
  comp_id {p q} f := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := f.2
    change P.idempotent (P.cornerVertex q) * a *
      P.idempotent (P.cornerVertex p) = f.1 at ha
    change P.idempotent (P.cornerVertex q) * f.1 = f.1
    rw [← ha, mul_assoc,
      ← mul_assoc (P.idempotent (P.cornerVertex q))
        (P.idempotent (P.cornerVertex q))
        (a * P.idempotent (P.cornerVertex p)),
      (P.primitive (P.cornerVertex q)).idempotent.eq]
  id_comp {p q} f := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := f.2
    change P.idempotent (P.cornerVertex q) * a *
      P.idempotent (P.cornerVertex p) = f.1 at ha
    change f.1 * P.idempotent (P.cornerVertex p) = f.1
    rw [← ha, mul_assoc,
      (P.primitive (P.cornerVertex p)).idempotent.eq]
  assoc f g h := by
    apply Subtype.ext
    exact (mul_assoc h.1 g.1 f.1).symm

@[simp]
theorem primitiveCornerCategory_id_val
    (P : S.PrimitiveProjectivePresentation)
    (p : P.PrimitiveCornerCategory) :
    (𝟙 p : p ⟶ p).1 = P.idempotent (P.cornerVertex p) :=
  rfl

@[simp]
theorem primitiveCornerCategory_comp_val
    (P : S.PrimitiveProjectivePresentation)
    {p q r : P.PrimitiveCornerCategory}
    (f : p ⟶ q) (g : q ⟶ r) :
    (f ≫ g : p ⟶ r).1 = g.1 * f.1 :=
  rfl

theorem primitiveCornerCategory_idempotent_mul_val
    (P : S.PrimitiveProjectivePresentation)
    {p q : P.PrimitiveCornerCategory} (f : p ⟶ q) :
    P.idempotent (P.cornerVertex q) * f.1 = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change P.idempotent (P.cornerVertex q) * a *
    P.idempotent (P.cornerVertex p) = f.1 at ha
  rw [← ha, mul_assoc,
    ← mul_assoc (P.idempotent (P.cornerVertex q))
      (P.idempotent (P.cornerVertex q))
      (a * P.idempotent (P.cornerVertex p)),
    (P.primitive (P.cornerVertex q)).idempotent.eq]

theorem primitiveCornerCategory_val_mul_idempotent
    (P : S.PrimitiveProjectivePresentation)
    {p q : P.PrimitiveCornerCategory} (f : p ⟶ q) :
    f.1 * P.idempotent (P.cornerVertex p) = f.1 := by
  obtain ⟨a, ha⟩ := f.2
  change P.idempotent (P.cornerVertex q) * a *
    P.idempotent (P.cornerVertex p) = f.1 at ha
  rw [← ha, mul_assoc,
    (P.primitive (P.cornerVertex p)).idempotent.eq]

noncomputable instance primitiveCornerCategoryPreadditive
    (P : S.PrimitiveProjectivePresentation) :
    Preadditive P.PrimitiveCornerCategory where
  homGroup p q := by
    change AddCommGroup (idempotentCorner (k := k) P.idempotent
      (P.cornerVertex q) (P.cornerVertex p))
    infer_instance
  add_comp _ _ _ f g h := by
    apply Subtype.ext
    exact mul_add h.1 f.1 g.1
  comp_add _ _ _ f g h := by
    apply Subtype.ext
    exact add_mul g.1 h.1 f.1

noncomputable instance primitiveCornerCategoryLinear
    (P : S.PrimitiveProjectivePresentation) :
    Linear k P.PrimitiveCornerCategory where
  homModule p q := by
    change Module k (idempotentCorner (k := k) P.idempotent
      (P.cornerVertex q) (P.cornerVertex p))
    infer_instance
  smul_comp _ _ _ c f g := by
    apply Subtype.ext
    exact Algebra.mul_smul_comm c g.1 f.1
  comp_smul _ _ _ f c g := by
    apply Subtype.ext
    exact Algebra.smul_mul_assoc c g.1 f.1

noncomputable instance primitiveCornerCategoryHomFinite
    (P : S.PrimitiveProjectivePresentation)
    (p q : P.PrimitiveCornerCategory) :
    Module.Finite k (p ⟶ q) := by
  apply Module.Finite.of_injective
    (idempotentCorner (k := k) P.idempotent
      (P.cornerVertex q) (P.cornerVertex p)).subtype
  exact Subtype.val_injective

/-- The corner Hom space is linearly equivalent to the corresponding
selected-projective Hom space. -/
def primitiveCornerHomLinearEquiv
    (P : S.PrimitiveProjectivePresentation)
    (p q : P.PrimitiveCornerCategory) :
    (p ⟶ q) ≃ₗ[k]
      (S.ordinaryProjectiveObj (P.cornerVertex p) ⟶
        S.ordinaryProjectiveObj (P.cornerVertex q)) where
  toFun f := P.projectiveHomOfCoordinate f.1
    (P.primitiveCornerCategory_idempotent_mul_val f)
    (P.primitiveCornerCategory_val_mul_idempotent f)
  invFun f := by
    refine ⟨P.projectiveHomCoordinate f,
      (mem_idempotentCorner_iff (k := k) P.idempotent
        (P.cornerVertex q) (P.cornerVertex p)
        (P.projectiveHomCoordinate f)).2 ?_⟩
    have h : P.idempotent (P.cornerVertex q) *
        P.projectiveHomCoordinate f * P.idempotent (P.cornerVertex p) =
          P.projectiveHomCoordinate f := by
      rw [P.idempotent_mul_projectiveHomCoordinate,
        P.projectiveHomCoordinate_mul_idempotent]
    exact ⟨P.projectiveHomCoordinate f, h⟩
  left_inv f := by
    apply Subtype.ext
    exact P.projectiveHomCoordinate_projectiveHomOfCoordinate _ _ _
  right_inv f := by
    apply P.projectiveHomCoordinate_injective
    change P.projectiveHomCoordinate
        (P.projectiveHomOfCoordinate (P.projectiveHomCoordinate f) _ _) =
      P.projectiveHomCoordinate f
    rw [P.projectiveHomCoordinate_projectiveHomOfCoordinate]
  map_add' f g := by
    apply P.projectiveHomCoordinate_injective
    change P.projectiveHomCoordinate
        (P.projectiveHomOfCoordinate (f + g).1 _ _) =
      P.projectiveHomCoordinate
        (P.projectiveHomOfCoordinate f.1 _ _ +
          P.projectiveHomOfCoordinate g.1 _ _)
    rw [P.projectiveHomCoordinate_projectiveHomOfCoordinate,
      P.projectiveHomCoordinate_add,
      P.projectiveHomCoordinate_projectiveHomOfCoordinate,
      P.projectiveHomCoordinate_projectiveHomOfCoordinate]
    rfl
  map_smul' c f := by
    apply P.projectiveHomCoordinate_injective
    change P.projectiveHomCoordinate
        (P.projectiveHomOfCoordinate (c • f).1 _ _) =
      P.projectiveHomCoordinate
        (c • P.projectiveHomOfCoordinate f.1 _ _)
    rw [P.projectiveHomCoordinate_projectiveHomOfCoordinate,
      P.projectiveHomCoordinate_smul,
      P.projectiveHomCoordinate_projectiveHomOfCoordinate]
    rfl

@[simp]
theorem projectiveHomCoordinate_primitiveCornerHomLinearEquiv
    (P : S.PrimitiveProjectivePresentation)
    {p q : P.PrimitiveCornerCategory} (f : p ⟶ q) :
    P.projectiveHomCoordinate (P.primitiveCornerHomLinearEquiv p q f) = f.1 :=
  P.projectiveHomCoordinate_projectiveHomOfCoordinate f.1
    (P.primitiveCornerCategory_idempotent_mul_val f)
    (P.primitiveCornerCategory_val_mul_idempotent f)

/-- The coordinate realization as a linear functor to the existing selected
projective category. -/
def primitiveCornerToProjective
    (P : S.PrimitiveProjectivePresentation) :
    P.PrimitiveCornerCategory ⥤ S.ProjectiveCategory where
  obj p := S.ordinaryProjectiveObj (P.cornerVertex p)
  map {p q} f := P.primitiveCornerHomLinearEquiv p q f
  map_id p := by
    apply P.projectiveHomCoordinate_injective
    change P.projectiveHomCoordinate
        (P.primitiveCornerHomLinearEquiv p p (𝟙 p)) =
      P.projectiveHomCoordinate
        (𝟙 (S.ordinaryProjectiveObj (P.cornerVertex p)))
    rw [P.projectiveHomCoordinate_primitiveCornerHomLinearEquiv,
      P.projectiveHomCoordinate_id,
      P.primitiveCornerCategory_id_val]
  map_comp f g := by
    apply P.projectiveHomCoordinate_injective
    change P.projectiveHomCoordinate
        (P.primitiveCornerHomLinearEquiv _ _ (f ≫ g)) =
      P.projectiveHomCoordinate
        (P.primitiveCornerHomLinearEquiv _ _ f ≫
          P.primitiveCornerHomLinearEquiv _ _ g)
    rw [P.projectiveHomCoordinate_primitiveCornerHomLinearEquiv,
      P.projectiveHomCoordinate_comp,
      P.projectiveHomCoordinate_primitiveCornerHomLinearEquiv,
      P.projectiveHomCoordinate_primitiveCornerHomLinearEquiv,
      P.primitiveCornerCategory_comp_val]

noncomputable instance primitiveCornerToProjective_additive
    (P : S.PrimitiveProjectivePresentation) :
    P.primitiveCornerToProjective.Additive where
  map_add := by
    intro p q f g
    exact (P.primitiveCornerHomLinearEquiv p q).map_add f g

noncomputable instance primitiveCornerToProjective_linear
    (P : S.PrimitiveProjectivePresentation) :
    P.primitiveCornerToProjective.Linear k where
  map_smul := by
    intro p q f c
    exact (P.primitiveCornerHomLinearEquiv p q).map_smul c f

noncomputable instance primitiveCornerToProjective_full
    (P : S.PrimitiveProjectivePresentation) :
    P.primitiveCornerToProjective.Full where
  map_surjective := by
    intro p q f
    exact (P.primitiveCornerHomLinearEquiv p q).surjective f

noncomputable instance primitiveCornerToProjective_faithful
    (P : S.PrimitiveProjectivePresentation) :
    P.primitiveCornerToProjective.Faithful where
  map_injective := by
    intro p q
    exact (P.primitiveCornerHomLinearEquiv p q).injective

/-- Every concrete primitive-corner endomorphism ring is local. -/
noncomputable instance primitiveCornerCategoryEndLocal
    (P : S.PrimitiveProjectivePresentation)
    (p : P.PrimitiveCornerCategory) : IsLocalRing (End p) := by
  letI : IsLocalRing
      (End (S.ordinaryProjectiveObj (P.cornerVertex p))) := by
    have hfg : IsLocalRing
        (End (S.projectiveInclusion.obj
          (S.ordinaryProjectiveObj (P.cornerVertex p)))) := by
      change IsLocalRing (End (S.fgObj (P.cornerVertex p).label))
      exact S.fgObj_end_isLocalRing (P.cornerVertex p).label
    exact RingEquiv.isLocalRing_noncomm
      (CategoryTheory.Functor.endRingEquivOfFullyFaithful
        S.projectiveInclusion
        (S.ordinaryProjectiveObj (P.cornerVertex p))).symm
  letI : IsLocalRing
      (End (P.primitiveCornerToProjective.obj p)) := by
    change IsLocalRing
      (End (S.ordinaryProjectiveObj (P.cornerVertex p)))
    infer_instance
  exact RingEquiv.isLocalRing_noncomm
    (CategoryTheory.Functor.endRingEquivOfFullyFaithful
      P.primitiveCornerToProjective p).symm

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
