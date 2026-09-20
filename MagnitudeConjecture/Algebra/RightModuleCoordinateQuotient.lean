import MagnitudeConjecture.Algebra.RightModuleGeneratedCoordinateEquality
import MagnitudeConjecture.Algebra.CoordinateThinModule
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Idempotent coordinates of quotient modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- A right-module map restricted to the idempotent coordinates. -/
def idempotentCoordinateMap (e : A) {X Y : FinitelyGeneratedCategory A}
    (f : X ⟶ Y) : idempotentCoordinate (k := k) e X →ₗ[k]
      idempotentCoordinate (k := k) e Y :=
  ((f.hom.hom.restrictScalars k).comp (idempotentCoordinate e X).subtype).codRestrict
    (idempotentCoordinate e Y) (by
      rintro ⟨x, y, hy⟩
      refine ⟨f y, ?_⟩
      change MulOpposite.op e • f.hom.hom y = f.hom.hom x
      rw [← f.hom.hom.map_smul]
      exact congrArg f hy)

/-- Surjective module maps remain surjective on an idempotent coordinate. -/
theorem idempotentCoordinateMap_surjective (e : A)
    {X Y : FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hf : Function.Surjective f) :
    Function.Surjective (idempotentCoordinateMap (k := k) e f) := by
  rintro ⟨y, z, hz⟩
  obtain ⟨x, hx⟩ := hf z
  change f.hom.hom x = z at hx
  refine ⟨⟨MulOpposite.op e • x, ⟨x, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change f.hom.hom (MulOpposite.op e • x) = y
  rw [f.hom.hom.map_smul, hx]
  exact hz

/-- The canonical quotient morphism in the finite module category. -/
def quotientFGMap (V : FinitelyGeneratedCategory A) (K : Submodule Aᵐᵒᵖ V) :
    V ⟶ quotientFGObj V K := ⟨ModuleCat.ofHom K.mkQ⟩

/-- Coordinate vectors killed by the quotient are precisely those in K. -/
theorem coordinateQuotientMap_eq_zero_iff (e : A)
    (V : FinitelyGeneratedCategory A) (K : Submodule Aᵐᵒᵖ V)
    (x : idempotentCoordinate (k := k) e V) :
    idempotentCoordinateMap e (quotientFGMap V K) x = 0 ↔ (x : V) ∈ K := by
  rw [← Subtype.val_inj]
  change K.mkQ (x : V) = 0 ↔ (x : V) ∈ K
  exact Submodule.Quotient.mk_eq_zero K

/-- No additional coordinate relations appear in the quotient by generated
relations at a scalar corner. -/
theorem generatedRelations_coordinateMap_ker
    {e : A} (he : IsIdempotentElem e)
    (hcorner : ∀ a : Aᵐᵒᵖ, ∃ c : k,
      MulOpposite.op e * a * MulOpposite.op e = algebraMap k Aᵐᵒᵖ c * MulOpposite.op e)
    (V : FinitelyGeneratedCategory A)
    (R : Submodule k (idempotentCoordinate (k := k) e V)) :
    LinearMap.ker (idempotentCoordinateMap e
      (quotientFGMap V (generatedCoordinateRelations e V R))) = R := by
  ext x
  exact (coordinateQuotientMap_eq_zero_iff e V _ x).trans
    (mem_generatedCoordinateRelations_iff he hcorner V R x)

/-- The quotient by generated relations has coordinate Ve/R. -/
def generatedRelations_coordinateEquiv
    {e : A} (he : IsIdempotentElem e)
    (hcorner : ∀ a : Aᵐᵒᵖ, ∃ c : k,
      MulOpposite.op e * a * MulOpposite.op e = algebraMap k Aᵐᵒᵖ c * MulOpposite.op e)
    (V : FinitelyGeneratedCategory A)
    (R : Submodule k (idempotentCoordinate (k := k) e V)) :
    (idempotentCoordinate (k := k) e V ⧸ R) ≃ₗ[k]
      idempotentCoordinate (k := k) e
        (quotientFGObj V (generatedCoordinateRelations e V R)) := by
  let K := generatedCoordinateRelations e V R
  let f := idempotentCoordinateMap (k := k) e (quotientFGMap V K)
  have hf : Function.Surjective f :=
    idempotentCoordinateMap_surjective e _ K.mkQ_surjective
  exact (Submodule.quotEquivOfEq R (LinearMap.ker f)
    (generatedRelations_coordinateMap_ker he hcorner V R).symm).trans
    (f.quotKerEquivOfSurjective hf)

/-- The coordinate equivalence sends a vector class to its module quotient
class. -/
theorem generatedRelations_coordinateEquiv_mk
    {e : A} (he : IsIdempotentElem e)
    (hcorner : ∀ a : Aᵐᵒᵖ, ∃ c : k,
      MulOpposite.op e * a * MulOpposite.op e = algebraMap k Aᵐᵒᵖ c * MulOpposite.op e)
    (V : FinitelyGeneratedCategory A)
    (R : Submodule k (idempotentCoordinate (k := k) e V))
    (x : idempotentCoordinate (k := k) e V) :
    generatedRelations_coordinateEquiv he hcorner V R (Submodule.Quotient.mk x) =
      idempotentCoordinateMap e (quotientFGMap V (generatedCoordinateRelations e V R)) x := by
  rfl

/-- A surjection π from Ve onto W identifies the coordinate of V/(ker π)A
with W. -/
def generatedRelations_coordinateEquivTarget
    {e : A} (he : IsIdempotentElem e)
    (hcorner : ∀ a : Aᵐᵒᵖ, ∃ c : k,
      MulOpposite.op e * a * MulOpposite.op e = algebraMap k Aᵐᵒᵖ c * MulOpposite.op e)
    (V : FinitelyGeneratedCategory A)
    {W : Type u} [AddCommGroup W] [Module k W]
    (π : idempotentCoordinate (k := k) e V →ₗ[k] W) (hπ : Function.Surjective π) :
    idempotentCoordinate (k := k) e
      (quotientFGObj V (generatedCoordinateRelations e V (LinearMap.ker π))) ≃ₗ[k] W :=
  (generatedRelations_coordinateEquiv he hcorner V (LinearMap.ker π)).symm.trans
    (π.quotKerEquivOfSurjective hπ)

/-- Under the target identification, the coordinate quotient map is exactly π. -/
theorem generatedRelations_coordinateEquivTarget_map
    {e : A} (he : IsIdempotentElem e)
    (hcorner : ∀ a : Aᵐᵒᵖ, ∃ c : k,
      MulOpposite.op e * a * MulOpposite.op e = algebraMap k Aᵐᵒᵖ c * MulOpposite.op e)
    (V : FinitelyGeneratedCategory A)
    {W : Type u} [AddCommGroup W] [Module k W]
    (π : idempotentCoordinate (k := k) e V →ₗ[k] W) (hπ : Function.Surjective π)
    (x : idempotentCoordinate (k := k) e V) :
    generatedRelations_coordinateEquivTarget he hcorner V π hπ
      (idempotentCoordinateMap e
        (quotientFGMap V (generatedCoordinateRelations e V (LinearMap.ker π))) x) = π x := by
  rw [← generatedRelations_coordinateEquiv_mk he hcorner V (LinearMap.ker π) x]
  simp [generatedRelations_coordinateEquivTarget]

end MagnitudeConjecture.RightModule
