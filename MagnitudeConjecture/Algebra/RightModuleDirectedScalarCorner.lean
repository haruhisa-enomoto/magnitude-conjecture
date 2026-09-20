import MagnitudeConjecture.Algebra.RightModuleGeneratedCoordinateEquality
import MagnitudeConjecture.Algebra.RightModuleDirected

/-! # The primitive corner is scalar in a directed module category -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Scalar endomorphisms of eA force every eae to be a scalar multiple of e. -/
theorem corner_scalar_of_rightIdeal_endomorphisms
    {e : A} (he : IsIdempotentElem e)
    (hP : ∀ f : rightIdealFGObj e ⟶ rightIdealFGObj e,
      ∃ c : k, c • 𝟙 (rightIdealFGObj e) = f) (a : A) :
    ∃ c : k, e * a * e = algebraMap k A c * e := by
  let y : rightIdeal e := ⟨e * a * e, ⟨a * e, by simp [rightRegularLeftMul, mul_assoc]⟩⟩
  let x : idempotentCoordinate (k := k) e (rightIdealFGObj e) :=
    ⟨y, ⟨y, by
      apply Subtype.ext
      change (e * a * e) * e = e * a * e
      rw [mul_assoc, he.eq]⟩⟩
  let E := rightIdealHomCoordinateEquiv (k := k) he (rightIdealFGObj e)
  let f := E.symm x
  obtain ⟨c, hc⟩ := hP f
  have hc' : c • E (𝟙 (rightIdealFGObj e)) = x := by
    rw [← E.map_smul, hc]
    exact E.apply_symm_apply x
  have hv := congrArg (fun z : idempotentCoordinate (k := k) e (rightIdealFGObj e) ↦
    (z.1.1 : A)) hc'
  have hs : ∀ z : idempotentCoordinate (k := k) e (rightIdealFGObj e),
      ((c • z).1.1 : A) = algebraMap k A c * z.1.1 := by
    intro z
    change (z.1.1 : A) * algebraMap k A c = algebraMap k A c * z.1.1
    exact (Algebra.commutes c z.1.1).symm
  have hid : ((E (𝟙 (rightIdealFGObj e))).1.1 : A) = e := rfl
  rw [hs, hid] at hv
  exact ⟨c, hv.symm⟩

namespace FiniteIndecomposableSkeleton
variable (S : FiniteIndecomposableSkeleton k A) [IsAlgClosed k]

/-- Directedness supplies scalar endomorphisms on the literal primitive
projective, by transport from its selected skeleton representative. -/
theorem primitiveProjective_endomorphism_scalar
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (f : rightIdealFGObj e ⟶ rightIdealFGObj e) :
    ∃ c : k, c • 𝟙 (rightIdealFGObj e) = f := by
  let i := S.primitiveSourceIso D
  obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S (S.primitiveSourceLabel D)
    (i.inv ≫ f ≫ i.hom)
  refine ⟨c, ?_⟩
  have h := congrArg (fun g ↦ i.hom ≫ g ≫ i.inv) hc
  simpa using h

/-- The scalar-corner condition in right-module (opposite-ring) convention. -/
theorem primitive_opposite_corner_scalar
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e) (a : Aᵐᵒᵖ) :
    ∃ c : k, MulOpposite.op e * a * MulOpposite.op e =
      algebraMap k Aᵐᵒᵖ c * MulOpposite.op e := by
  obtain ⟨c, hc⟩ := corner_scalar_of_rightIdeal_endomorphisms D.idempotent
    (S.primitiveProjective_endomorphism_scalar H D) a.unop
  refine ⟨c, ?_⟩
  apply MulOpposite.unop_injective
  change e * (a.unop * e) = e * algebraMap k A c
  rw [← mul_assoc, hc, Algebra.commutes c e]

/-- Coordinate membership for the generated relation module, with the scalar
corner condition discharged by directedness. -/
theorem generatedCoordinateRelations_coordinate_iff
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (V : FinitelyGeneratedCategory A)
    (R : Submodule k (idempotentCoordinate (k := k) e V))
    (x : idempotentCoordinate (k := k) e V) :
    (x : V) ∈ generatedCoordinateRelations e V R ↔ x ∈ R :=
  mem_generatedCoordinateRelations_iff D.idempotent
    (S.primitive_opposite_corner_scalar H D) V R x

end FiniteIndecomposableSkeleton
end MagnitudeConjecture.RightModule
