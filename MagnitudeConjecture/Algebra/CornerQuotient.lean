import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent

/-!
# Primitive idempotents under surjective ring maps

This file isolates the small ring-theoretic fact needed for literal support
quotients.  The corner of a primitive idempotent is identified with the
endomorphism ring of its indecomposable principal right ideal, hence is local.
A surjective ring map is surjective on the corresponding corners, and a
nonzero image of a primitive idempotent is therefore primitive.
-/

set_option autoImplicit false
noncomputable section

open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v

/-- A ring homomorphism restricts to the corresponding idempotent corners. -/
def idempotentCornerMap
    {R : Type u} {T : Type v} [Ring R] [Ring T]
    (f : R →+* T) {e : R} (he : IsIdempotentElem e) :
    he.Corner →+* (he.map f).Corner where
  toFun c :=
    ⟨f c.1, by
      apply (Subsemigroup.mem_corner_iff (he.map f)).2
      have hc := (Subsemigroup.mem_corner_iff he).1 c.2
      exact ⟨by simpa only [map_mul] using congrArg f hc.1,
        by simpa only [map_mul] using congrArg f hc.2⟩⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' c d := by apply Subtype.ext; exact map_mul f c.1 d.1
  map_zero' := by apply Subtype.ext; exact map_zero f
  map_add' c d := by apply Subtype.ext; exact map_add f c.1 d.1

/-- A surjective ring map is surjective on every corresponding corner. -/
theorem idempotentCornerMap_surjective
    {R : Type u} {T : Type v} [Ring R] [Ring T]
    (f : R →+* T) (hf : Function.Surjective f)
    {e : R} (he : IsIdempotentElem e) :
    Function.Surjective (idempotentCornerMap f he) := by
  rintro ⟨y, hy⟩
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨r, rfl⟩ := hf s
  refine ⟨⟨e * r * e, ⟨r, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change f (e * r * e) = f e * f r * f e
  rw [map_mul, map_mul]

/-- Left multiplication identifies an idempotent corner with the
endomorphism ring of its principal right ideal. -/
def RightModule.cornerEndRingEquiv
    {k A : Type u} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
    {e : A} (he : IsIdempotentElem e) :
    he.Corner ≃+* Module.End Aᵐᵒᵖ (RightModule.rightIdeal e) where
  toFun c :=
    { toFun := fun x ↦
        ⟨c.1 * x.1, by
          refine ⟨c.1 * x.1, ?_⟩
          rw [RightModule.rightRegularLeftMul_apply, ← mul_assoc,
            (Subsemigroup.mem_corner_iff he).1 c.2 |>.1]⟩
      map_add' := fun x y ↦ Subtype.ext (mul_add c.1 x.1 y.1)
      map_smul' := fun r x ↦ Subtype.ext (mul_assoc c.1 x.1 r.unop).symm }
  invFun g := by
    let b := g (RightModule.rightIdealGenerator e)
    refine ⟨b.1, (Subsemigroup.mem_corner_iff he).2 ⟨?_, ?_⟩⟩
    · exact RightModule.rightIdeal_fixed he b
    · have hgen : (MulOpposite.op e) •
          RightModule.rightIdealGenerator e =
          RightModule.rightIdealGenerator e := by
        apply Subtype.ext
        exact he.eq
      have hlinear := g.map_smul (MulOpposite.op e)
        (RightModule.rightIdealGenerator e)
      rw [hgen] at hlinear
      exact congrArg Subtype.val hlinear.symm
  left_inv c := by
    apply Subtype.ext
    exact (Subsemigroup.mem_corner_iff he).1 c.2 |>.2
  right_inv g := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := x.2
    change e * a = x.1 at ha
    have hgen : (MulOpposite.op e) •
          RightModule.rightIdealGenerator e =
          RightModule.rightIdealGenerator e := by
      apply Subtype.ext
      exact he.eq
    have hlinear := g.map_smul (MulOpposite.op e)
      (RightModule.rightIdealGenerator e)
    rw [hgen] at hlinear
    have hbe : (g (RightModule.rightIdealGenerator e)).1 * e =
        (g (RightModule.rightIdealGenerator e)).1 :=
      congrArg Subtype.val hlinear.symm
    apply Subtype.ext
    have hx : (MulOpposite.op a) • RightModule.rightIdealGenerator e = x := by
      apply Subtype.ext
      exact ha
    rw [← hx, g.map_smul]
    change (g (RightModule.rightIdealGenerator e)).1 * (e * a) =
      (g (RightModule.rightIdealGenerator e)).1 * a
    rw [← mul_assoc, hbe]
  map_mul' c d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact mul_assoc c.1 d.1 x.1
  map_add' c d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact add_mul c.1 d.1 x.1

/-- The noncommutative quotient of a local ring by a surjective ring map is
local, provided the target is nontrivial. -/
theorem isLocalRing_of_surjective
    {R : Type u} {T : Type v} [Ring R] [Ring T]
    [IsLocalRing R] [Nontrivial T]
    (f : R →+* T) (hf : Function.Surjective f) : IsLocalRing T := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro y
  obtain ⟨x, rfl⟩ := hf y
  simpa only [map_one, map_sub] using
    (IsLocalRing.isUnit_or_isUnit_of_isUnit_add
      (show IsUnit (x + (1 - x)) by simp)).imp
      (IsUnit.map f) (IsUnit.map f)

/-- The corner of a primitive idempotent in a finite-dimensional algebra is
local. -/
theorem RightModule.PrimitiveIdempotentData.corner_isLocalRing
    {k A : Type u} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
    {e : A} (D : RightModule.PrimitiveIdempotentData e) :
    IsLocalRing D.idempotent.Corner := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  letI : Module.Finite Aᵐᵒᵖ A :=
    Module.Finite.equiv RightModule.rightRegularLinearEquiv
  letI : IsNoetherian Aᵐᵒᵖ A := inferInstance
  letI : Module.Finite Aᵐᵒᵖ (RightModule.rightIdeal e) := inferInstance
  have hfinite : IsFiniteLength Aᵐᵒᵖ (RightModule.rightIdeal e) :=
    ((IsArtinianRing.tfae Aᵐᵒᵖ (RightModule.rightIdeal e)).out 0 3).mp
      (inferInstance : Module.Finite Aᵐᵒᵖ (RightModule.rightIdeal e))
  letI : IsLocalRing (Module.End Aᵐᵒᵖ (RightModule.rightIdeal e)) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      hfinite
      (RightModule.rightIdeal_isIndecomposableModule D)
  letI : Nontrivial D.idempotent.Corner :=
    ⟨⟨0, 1, by
      intro h
      apply D.nonzero
      exact (congrArg Subtype.val h).symm⟩⟩
  let E := RightModule.cornerEndRingEquiv (k := k) D.idempotent
  exact isLocalRing_of_surjective
    (R := Module.End Aᵐᵒᵖ (RightModule.rightIdeal e))
    (T := D.idempotent.Corner)
    (E.symm : Module.End Aᵐᵒᵖ (RightModule.rightIdeal e) →+*
      D.idempotent.Corner)
    E.symm.surjective

/-- A nonzero image of a primitive idempotent under a surjective ring map is
again primitive. -/
theorem RightModule.PrimitiveIdempotentData.map_of_surjective
    {k A : Type u} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
    {T : Type v} [Ring T]
    {e : A} (D : RightModule.PrimitiveIdempotentData e)
    (f : A →+* T) (hf : Function.Surjective f) (hne : f e ≠ 0) :
    RightModule.PrimitiveIdempotentData (f e) where
  idempotent := D.idempotent.map f
  nonzero := hne
  corner_idempotent b hb hleft hright := by
    let he' : IsIdempotentElem (f e) := D.idempotent.map f
    let bc : he'.Corner :=
      ⟨b, (Subsemigroup.mem_corner_iff he').2 ⟨hleft, hright⟩⟩
    have hbc : IsIdempotentElem bc := by
      apply Subtype.ext
      exact hb.eq
    letI : Nontrivial he'.Corner :=
      ⟨⟨0, 1, by
        intro h
        apply hne
        exact (congrArg Subtype.val h).symm⟩⟩
    letI : IsLocalRing D.idempotent.Corner := D.corner_isLocalRing (k := k)
    letI : IsLocalRing he'.Corner :=
      isLocalRing_of_surjective
        (idempotentCornerMap f D.idempotent)
        (idempotentCornerMap_surjective f hf D.idempotent)
    rcases
        QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem
          hbc with hzero | hone
    · left
      exact congrArg Subtype.val hzero
    · right
      exact congrArg Subtype.val hone

end MagnitudeConjecture
