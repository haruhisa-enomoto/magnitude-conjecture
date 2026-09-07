import MagnitudeConjecture.Algebra.IdempotentSaturation
import MagnitudeConjecture.Algebra.RightModuleBoundaryGenerator

/-!
# The boundary idempotent and Iyama saturation

The boundary projective generator `U` is a retract of the full surviving
additive generator `G`.  Its projector defines an idempotent `e` in the
factor Auslander ring `(End G)ᵐᵒᵖ`, and the represented module `Hom(G,U)` is
the principal left ideal `Γ e`.

Together with `IdempotentSaturation`, this translates Iyama's condition
`HomΓ(Hom(G,U), M/L) = 0` into the explicit condition that `e` annihilates
the quotient.  The next layer will apply this saturation to the lifted image
inside the represented full-support projective.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The factor Auslander ring attached to the full surviving additive
generator. -/
abbrev factorAuslanderRing (K : Set (Fin S.n)) :=
  (End (S.factorAdditiveGenerator K))ᵐᵒᵖ

/-- The endomorphism algebra of the finite factor generator is finite over
the coefficient field. -/
noncomputable instance factorAdditiveGeneratorEnd_moduleFinite
    (K : Set (Fin S.n)) :
    Module.Finite k (End (S.factorAdditiveGenerator K)) :=
  S.factorCategoryHomFinite K _ _

/-- Hence the factor Auslander ring is Noetherian. -/
noncomputable instance factorAuslanderRing_isNoetherian
    (K : Set (Fin S.n)) :
    IsNoetherianRing (S.factorAuslanderRing K) :=
  IsNoetherianRing.of_finite k _

/-- Every full-generator representable is a finitely generated projective
module over the factor Auslander ring. -/
theorem factorAuslanderRepresentable_finiteProjective
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    CategoryTheory.finiteProjectiveModules (S.factorAuslanderRing K)
      ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj X) := by
  let G := S.factorAdditiveGenerator K
  have hXadd : CategoryTheory.finiteAddClosure G X :=
    S.factorAdditiveGenerator_isFiniteAddGenerator K X
  have hRepresentableAdd :
      CategoryTheory.finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G)
        ((preadditiveCoyonedaObj G).obj X) :=
    ⟨CategoryTheory.homFromGenerator_obj_finiteAddPresentation G
      ⟨X, hXadd⟩⟩
  rw [← CategoryTheory.finiteAddClosure_homSelf_eq_finiteProjective G]
  exact hRepresentableAdd

/-- Full-generator representables are finite modules. -/
noncomputable instance factorAuslanderRepresentable_moduleFinite
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    Module.Finite (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ X) :=
  (S.factorAuslanderRepresentable_finiteProjective K X).1

/-- The represented boundary generator, bundled in the finitely generated
module category of the factor Auslander algebra. -/
abbrev factorBoundaryRepresentableFGObj (K : Set (Fin S.n)) :
    FGModuleCat.{u} (S.factorAuslanderRing K) :=
  FGModuleCat.of (S.factorAuslanderRing K)
    (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K)

/-- The represented boundary generator is projective. -/
noncomputable instance factorBoundaryRepresentableFGObj_projective
    (K : Set (Fin S.n)) :
    Projective (S.factorBoundaryRepresentableFGObj K) := by
  letI : Projective
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K)) :=
    (S.factorAuslanderRepresentable_finiteProjective K
      (S.factorProjectiveGenerator K)).2
  let hmodule : Module.Projective (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) :=
    ModuleCat.projective_of_module_projective
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K))
  exact MagnitudeConjecture.fgProjective_of_moduleProjective
    (S.factorBoundaryRepresentableFGObj K) hmodule

/-- The boundary projector, viewed as an idempotent in the factor Auslander
ring. -/
def factorBoundaryIdempotent (K : Set (Fin S.n)) :
    S.factorAuslanderRing K :=
  MulOpposite.op
    (End.of
      ((S.factorProjectiveGeneratorRetract K).r ≫
        (S.factorProjectiveGeneratorRetract K).i))

/-- The boundary projector is idempotent. -/
theorem factorBoundaryIdempotent_isIdempotentElem
    (K : Set (Fin S.n)) :
    IsIdempotentElem (S.factorBoundaryIdempotent K) := by
  let R := S.factorProjectiveGeneratorRetract K
  apply MulOpposite.unop_injective
  change
    End.of
        ((R.r ≫ R.i) ≫ (R.r ≫ R.i)) =
      End.of
        (R.r ≫ R.i)
  rw [Category.assoc, ← Category.assoc R.i R.r R.i,
    R.retract, Category.id_comp]

/-- Embed the represented boundary projective in the regular Auslander
module by postcomposing with the retract inclusion. -/
def factorProjectiveRepresentableToLeftIdeal
    (K : Set (Fin S.n))
    (q : S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) :
    IdempotentSaturation.principalLeftIdeal
      (S.factorBoundaryIdempotent K) := by
  let R := S.factorProjectiveGeneratorRetract K
  let e := S.factorBoundaryIdempotent K
  let x : S.factorAuslanderRing K :=
    MulOpposite.op (End.of (q ≫ R.i))
  refine ⟨x, ⟨x, ?_⟩⟩
  change x * e = x
  apply MulOpposite.unop_injective
  change
    End.of ((q ≫ R.i) ≫ (R.r ≫ R.i)) =
      End.of (q ≫ R.i)
  rw [Category.assoc, ← Category.assoc R.i R.r R.i,
    R.retract, Category.id_comp]

/-- Recover a boundary morphism from its principal-left-ideal coordinate. -/
def factorProjectiveRepresentableFromLeftIdeal
    (K : Set (Fin S.n))
    (y : IdempotentSaturation.principalLeftIdeal
      (S.factorBoundaryIdempotent K)) :
    S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K :=
  End.asHom y.1.unop ≫ (S.factorProjectiveGeneratorRetract K).r

private theorem factorProjectiveRepresentable_left_inv
    (K : Set (Fin S.n))
    (q : S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) :
    S.factorProjectiveRepresentableFromLeftIdeal K
        (S.factorProjectiveRepresentableToLeftIdeal K q) = q := by
  let R := S.factorProjectiveGeneratorRetract K
  change (q ≫ R.i) ≫ R.r = q
  rw [Category.assoc, R.retract, Category.comp_id]

private theorem factorProjectiveRepresentable_right_inv
    (K : Set (Fin S.n))
    (y : IdempotentSaturation.principalLeftIdeal
      (S.factorBoundaryIdempotent K)) :
    S.factorProjectiveRepresentableToLeftIdeal K
        (S.factorProjectiveRepresentableFromLeftIdeal K y) = y := by
  let R := S.factorProjectiveGeneratorRetract K
  apply Subtype.ext
  dsimp only [factorProjectiveRepresentableToLeftIdeal,
    factorProjectiveRepresentableFromLeftIdeal]
  change
    MulOpposite.op
        (End.of ((End.asHom y.1.unop ≫ R.r) ≫ R.i)) =
      y.1
  rw [Category.assoc]
  change y.1 * S.factorBoundaryIdempotent K = y.1
  exact IdempotentSaturation.principalLeftIdeal_fixed
    (S.factorBoundaryIdempotent_isIdempotentElem K) y

private theorem factorProjectiveRepresentable_map_add
    (K : Set (Fin S.n))
    (q r : S.factorAdditiveGenerator K ⟶
      S.factorProjectiveGenerator K) :
    S.factorProjectiveRepresentableToLeftIdeal K (q + r) =
      S.factorProjectiveRepresentableToLeftIdeal K q +
        S.factorProjectiveRepresentableToLeftIdeal K r := by
  apply Subtype.ext
  dsimp only [factorProjectiveRepresentableToLeftIdeal]
  apply MulOpposite.unop_injective
  change End.of ((q + r) ≫
      (S.factorProjectiveGeneratorRetract K).i) =
    End.of (q ≫ (S.factorProjectiveGeneratorRetract K).i) +
      End.of (r ≫ (S.factorProjectiveGeneratorRetract K).i)
  rw [Preadditive.add_comp]

private theorem factorProjectiveRepresentable_map_smul
    (K : Set (Fin S.n)) (a : S.factorAuslanderRing K)
    (q : S.factorAdditiveGenerator K ⟶
      S.factorProjectiveGenerator K) :
    S.factorProjectiveRepresentableToLeftIdeal K (a • q) =
      a • S.factorProjectiveRepresentableToLeftIdeal K q := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change
    End.of ((End.asHom a.unop ≫ q) ≫
        (S.factorProjectiveGeneratorRetract K).i) =
      End.of (End.asHom a.unop ≫
        q ≫ (S.factorProjectiveGeneratorRetract K).i)
  rw [Category.assoc]

/-- Under the full-generator representable functor, the boundary projective
generator is the principal left ideal cut out by the boundary idempotent. -/
def factorProjectiveRepresentableLinearEquiv
    (K : Set (Fin S.n)) :
    (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) ≃ₗ[
      S.factorAuslanderRing K]
      IdempotentSaturation.principalLeftIdeal
        (S.factorBoundaryIdempotent K) where
  toFun := S.factorProjectiveRepresentableToLeftIdeal K
  invFun := S.factorProjectiveRepresentableFromLeftIdeal K
  left_inv := S.factorProjectiveRepresentable_left_inv K
  right_inv := S.factorProjectiveRepresentable_right_inv K
  map_add' := S.factorProjectiveRepresentable_map_add K
  map_smul' := S.factorProjectiveRepresentable_map_smul K

/-- Iyama's vanishing condition for the boundary projective is exactly
annihilation by the boundary idempotent. -/
theorem factorProjectiveRepresentable_hom_eq_zero_iff
    (K : Set (Fin S.n))
    {N : Type u} [AddCommGroup N] [Module (S.factorAuslanderRing K) N] :
    (∀ f :
        (S.factorAdditiveGenerator K ⟶ S.factorProjectiveGenerator K) →ₗ[
          S.factorAuslanderRing K] N,
        f = 0) ↔
      ∀ x : N, S.factorBoundaryIdempotent K • x = 0 :=
  (IdempotentSaturation.forall_linearMap_eq_zero_congr
      (S.factorProjectiveRepresentableLinearEquiv K)).trans
    (IdempotentSaturation.principalLeftIdeal_hom_eq_zero_iff
      (S.factorBoundaryIdempotent_isIdempotentElem K))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
