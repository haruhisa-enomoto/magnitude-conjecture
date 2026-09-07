import MagnitudeConjecture.Algebra.RightModuleOppositeProjectivePresentation

/-!
# Algebra coordinates for selected primitive projectives

A complete primitive-projective presentation identifies every selected
projective with a principal right ideal.  Evaluation at its idempotent
generator then turns a morphism between selected projectives into its literal
corner element of the ambient algebra.

These coordinates reverse categorical composition: if `f` is followed by
`g`, the coordinate of `f ≫ g` is the coordinate of `g` times the coordinate
of `f`.  Recording this variance once is the bridge needed to translate the
Skowroński--Waschbüsch corner calculations into the right-module convention.
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

/-- Transport a selected-projective morphism to the literal principal right
ideals supplied by the primitive-projective presentation. -/
def projectiveHomTransport (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    RightModule.rightIdealFGObj (P.idempotent p) ⟶
      RightModule.rightIdealFGObj (P.idempotent q) :=
  ((P.primitiveProjectiveIso p).homCongr
    (P.primitiveProjectiveIso q)).symm
      (S.projectiveInclusion.map f)

/-- Transport respects composition between the literal principal right
ideals. -/
@[simp]
theorem projectiveHomTransport_comp
    (P : S.PrimitiveProjectivePresentation)
    {p q r : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q)
    (g : S.ordinaryProjectiveObj q ⟶ S.ordinaryProjectiveObj r) :
    P.projectiveHomTransport (f ≫ g) =
      P.projectiveHomTransport f ≫ P.projectiveHomTransport g := by
  apply ((P.primitiveProjectiveIso p).homCongr
    (P.primitiveProjectiveIso r)).injective
  rw [Iso.homCongr_comp
    (P.primitiveProjectiveIso p)
    (P.primitiveProjectiveIso q)
    (P.primitiveProjectiveIso r)]
  simp only [projectiveHomTransport, Equiv.apply_symm_apply]
  exact S.projectiveInclusion.map_comp f g

/-- The linear coordinate equivalence from a selected-projective Hom-space
to the corresponding literal corner `e_q A e_p`.  The codomain is kept in
Mathlib's nested right-ideal/idempotent-coordinate form so both corner support
conditions remain part of the type. -/
def projectiveHomCoordinateEquiv
    (P : S.PrimitiveProjectivePresentation)
    (p q : S.ProjectiveLabel) :
    (S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) ≃ₗ[k]
      RightModule.idempotentCoordinate (k := k) (P.idempotent p)
        (RightModule.rightIdealFGObj (P.idempotent q)) :=
  ((InducedCategory.homLinearEquiv (R := k)
      (F := fun r : S.ProjectiveLabel ↦ S.fgObj r.label)).trans
    (CategoryTheory.Linear.homCongr k
      (P.primitiveProjectiveIso p)
      (P.primitiveProjectiveIso q)).symm).trans
    (RightModule.rightIdealHomCoordinateEquiv (k := k)
      (P.primitive p).idempotent
      (RightModule.rightIdealFGObj (P.idempotent q)))

/-- The ambient algebra element representing a selected-projective
morphism. -/
def projectiveHomCoordinate (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) : A :=
  (P.projectiveHomCoordinateEquiv p q f).1.1

/-- Equality of algebra coordinates reflects equality of selected-projective
morphisms. -/
theorem projectiveHomCoordinate_injective
    (P : S.PrimitiveProjectivePresentation)
    (p q : S.ProjectiveLabel) :
    Function.Injective (fun f : S.ordinaryProjectiveObj p ⟶
      S.ordinaryProjectiveObj q ↦ P.projectiveHomCoordinate f) := by
  intro f g hfg
  apply (P.projectiveHomCoordinateEquiv p q).injective
  apply Subtype.ext
  apply Subtype.ext
  exact hfg

@[simp]
theorem projectiveHomCoordinate_zero
    (P : S.PrimitiveProjectivePresentation)
    (p q : S.ProjectiveLabel) :
    P.projectiveHomCoordinate
      (0 : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) = 0 := by
  change ((P.projectiveHomCoordinateEquiv p q) 0).1.1 = 0
  rw [map_zero]
  rfl

@[simp]
theorem projectiveHomCoordinate_add
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f g : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    P.projectiveHomCoordinate (f + g) =
      P.projectiveHomCoordinate f + P.projectiveHomCoordinate g := by
  change ((P.projectiveHomCoordinateEquiv p q) (f + g)).1.1 = _
  rw [map_add]
  rfl

@[simp]
theorem projectiveHomCoordinate_neg
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    P.projectiveHomCoordinate (-f) = -P.projectiveHomCoordinate f := by
  change ((P.projectiveHomCoordinateEquiv p q) (-f)).1.1 = _
  rw [map_neg]
  rfl

@[simp]
theorem projectiveHomCoordinate_smul
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel} (c : k)
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    P.projectiveHomCoordinate (c • f) =
      c • P.projectiveHomCoordinate f := by
  change ((P.projectiveHomCoordinateEquiv p q) (c • f)).1.1 = _
  rw [map_smul]
  change P.projectiveHomCoordinate f * algebraMap k A c =
    c • P.projectiveHomCoordinate f
  rw [Algebra.smul_def, Algebra.commutes]

@[simp]
theorem projectiveHomCoordinate_id
    (P : S.PrimitiveProjectivePresentation)
    (p : S.ProjectiveLabel) :
    P.projectiveHomCoordinate (𝟙 (S.ordinaryProjectiveObj p)) =
      P.idempotent p := by
  change
    ((RightModule.rightIdealHomCoordinateEquiv (k := k)
      (P.primitive p).idempotent
      (RightModule.rightIdealFGObj (P.idempotent p)))
        (P.projectiveHomTransport (𝟙 (S.ordinaryProjectiveObj p)))).1.1 = _
  have htransport :
      P.projectiveHomTransport (𝟙 (S.ordinaryProjectiveObj p)) =
        𝟙 (RightModule.rightIdealFGObj (P.idempotent p)) := by
    apply ((P.primitiveProjectiveIso p).homCongr
      (P.primitiveProjectiveIso p)).injective
    simp only [projectiveHomTransport, Equiv.apply_symm_apply,
      Iso.homCongr_apply]
    calc
      S.projectiveInclusion.map (𝟙 (S.ordinaryProjectiveObj p)) =
          𝟙 (S.fgObj p.label) :=
        S.projectiveInclusion.map_id (S.ordinaryProjectiveObj p)
      _ = (P.primitiveProjectiveIso p).inv ≫
          𝟙 (RightModule.rightIdealFGObj (P.idempotent p)) ≫
            (P.primitiveProjectiveIso p).hom := by simp
  rw [htransport]
  rfl

/-- A selected-projective morphism vanishes exactly when its literal algebra
coordinate vanishes. -/
theorem projectiveHomCoordinate_eq_zero_iff
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    P.projectiveHomCoordinate f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply P.projectiveHomCoordinate_injective p q
    simpa using hf
  · rintro rfl
    exact P.projectiveHomCoordinate_zero p q

/-- The left corner idempotent fixes the coordinate. -/
theorem idempotent_mul_projectiveHomCoordinate
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    P.idempotent q * P.projectiveHomCoordinate f =
      P.projectiveHomCoordinate f := by
  exact RightModule.rightIdeal_fixed (P.primitive q).idempotent
    (P.projectiveHomCoordinateEquiv p q f).1

/-- The right corner idempotent fixes the coordinate. -/
theorem projectiveHomCoordinate_mul_idempotent
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q) :
    P.projectiveHomCoordinate f * P.idempotent p =
      P.projectiveHomCoordinate f := by
  exact congrArg
    (fun z : RightModule.rightIdeal (P.idempotent q) ↦ z.1)
    (RightModule.idempotentCoordinate_fixed
      (P.primitive p).idempotent
      (RightModule.rightIdealFGObj (P.idempotent q))
      (P.projectiveHomCoordinateEquiv p q f))

/-- Turn an algebra element with the two required corner support identities
back into a selected-projective morphism. -/
def projectiveHomOfCoordinate
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel} (z : A)
    (hleft : P.idempotent q * z = z)
    (hright : z * P.idempotent p = z) :
    S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q := by
  let zr : RightModule.rightIdeal (P.idempotent q) :=
    ⟨z, ⟨z, hleft⟩⟩
  let zc : RightModule.idempotentCoordinate (k := k) (P.idempotent p)
      (RightModule.rightIdealFGObj (P.idempotent q)) :=
    ⟨zr, ⟨zr, by
      apply Subtype.ext
      exact hright⟩⟩
  exact (P.projectiveHomCoordinateEquiv p q).symm zc

@[simp]
theorem projectiveHomCoordinate_projectiveHomOfCoordinate
    (P : S.PrimitiveProjectivePresentation)
    {p q : S.ProjectiveLabel} (z : A)
    (hleft : P.idempotent q * z = z)
    (hright : z * P.idempotent p = z) :
    P.projectiveHomCoordinate
      (P.projectiveHomOfCoordinate z hleft hright) = z := by
  change ((P.projectiveHomCoordinateEquiv p q)
    ((P.projectiveHomCoordinateEquiv p q).symm _)).1.1 = z
  rw [LinearEquiv.apply_symm_apply]

/-- Categorical composition is multiplication in reverse order in the
literal right-ideal coordinates. -/
@[simp]
theorem projectiveHomCoordinate_comp
    (P : S.PrimitiveProjectivePresentation)
    {p q r : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj p ⟶ S.ordinaryProjectiveObj q)
    (g : S.ordinaryProjectiveObj q ⟶ S.ordinaryProjectiveObj r) :
    P.projectiveHomCoordinate (f ≫ g) =
      P.projectiveHomCoordinate g * P.projectiveHomCoordinate f := by
  change
    ((RightModule.rightIdealHomCoordinateEquiv (k := k)
      (P.primitive p).idempotent
      (RightModule.rightIdealFGObj (P.idempotent r)))
        (P.projectiveHomTransport (f ≫ g))).1.1 = _
  rw [P.projectiveHomTransport_comp f g]
  rw [RightModule.rightIdealHomCoordinateEquiv_comp_apply
    (k := k) (P.primitive p).idempotent (P.primitive q).idempotent]
  rfl

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
