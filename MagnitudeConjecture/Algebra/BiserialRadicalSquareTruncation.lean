import MagnitudeConjecture.Algebra.BiserialRadicalTruncation

/-!
# Radical-square truncations in the biserial induction

The second Pogorzały--Skowroński reduction replaces a local module `L` by
`L / rad² L`.  This file packages that literal quotient and the canonical
identification of its radical with `rad L / rad² L`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The second ring-radical layer of a finitely generated right module. -/
def radicalSquareSubmodule (L : FinitelyGeneratedCategory A) :
    Submodule Aᵐᵒᵖ L :=
  Ring.jacobson Aᵐᵒᵖ ^ 2 • (⊤ : Submodule Aᵐᵒᵖ L)

/-- The literal radical-square truncation `L / rad² L`. -/
def radicalSquareTruncationFGObj (L : FinitelyGeneratedCategory A) :
    FinitelyGeneratedCategory A :=
  quotientFGObj L (radicalSquareSubmodule L)

/-- The quotient map to `L / rad² L`. -/
def radicalSquareTruncationMkQ (L : FinitelyGeneratedCategory A) :
    L →ₗ[Aᵐᵒᵖ] radicalSquareTruncationFGObj L :=
  quotientFGMkQ L (radicalSquareSubmodule L)

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem radicalSquareTruncationMkQ_apply
    (L : FinitelyGeneratedCategory A) (x : L) :
    radicalSquareTruncationMkQ L x = (radicalSquareSubmodule L).mkQ x := rfl

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The square of the ring radical annihilates `L / rad² L`. -/
theorem ringJacobson_square_smul_top_radicalSquareTruncation_eq_bot
    (L : FinitelyGeneratedCategory A) :
    Ring.jacobson Aᵐᵒᵖ ^ 2 •
        (⊤ : Submodule Aᵐᵒᵖ (radicalSquareTruncationFGObj L)) = ⊥ := by
  exact ideal_smul_top_quotient_eq_bot_of_le
    (Ring.jacobson Aᵐᵒᵖ ^ 2) (radicalSquareSubmodule L) le_rfl

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The radical of `L / rad² L` is the image of the radical of `L`. -/
theorem moduleJacobson_radicalSquareTruncation_eq_map
    (L : FinitelyGeneratedCategory A) :
    Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L) =
      (Module.jacobson Aᵐᵒᵖ L).map (radicalSquareTruncationMkQ L) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  rw [moduleJacobson_eq_ringJacobson_smul_top,
    moduleJacobson_eq_ringJacobson_smul_top]
  change Ring.jacobson Aᵐᵒᵖ •
      (⊤ : Submodule Aᵐᵒᵖ (L ⧸ radicalSquareSubmodule L)) =
    (Ring.jacobson Aᵐᵒᵖ • (⊤ : Submodule Aᵐᵒᵖ L)).map
      (radicalSquareSubmodule L).mkQ
  exact (map_ideal_smul_top_quotient
    (Ring.jacobson Aᵐᵒᵖ) (radicalSquareSubmodule L)).symm

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The second radical layer of `L` lies in its first radical. -/
theorem radicalSquareSubmodule_le_moduleJacobson
    (L : FinitelyGeneratedCategory A) :
    radicalSquareSubmodule L ≤ Module.jacobson Aᵐᵒᵖ L := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  rw [moduleJacobson_eq_ringJacobson_smul_top]
  exact Submodule.smul_mono (Ideal.pow_le_self (by norm_num)) le_rfl

/-- The top of `L / rad² L` is canonically the top of `L`. -/
def radicalSquareTruncationTopLinearEquiv
    (L : FinitelyGeneratedCategory A) :
    quotientFGObj (radicalSquareTruncationFGObj L)
        (Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L)) ≃ₗ[Aᵐᵒᵖ]
      quotientFGObj L (Module.jacobson Aᵐᵒᵖ L) :=
  (Submodule.quotEquivOfEq _ _
      (moduleJacobson_radicalSquareTruncation_eq_map (k := k) L)).trans
    (Submodule.quotientQuotientEquivQuotient
      (radicalSquareSubmodule L) (Module.jacobson Aᵐᵒᵖ L)
      (radicalSquareSubmodule_le_moduleJacobson (k := k) L))

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Radical-square truncation preserves simplicity of the module top. -/
theorem isSimpleModule_top_radicalSquareTruncation_iff
    (L : FinitelyGeneratedCategory A) :
    IsSimpleModule Aᵐᵒᵖ
        (quotientFGObj (radicalSquareTruncationFGObj L)
          (Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L))) ↔
      IsSimpleModule Aᵐᵒᵖ
        (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)) :=
  (radicalSquareTruncationTopLinearEquiv (k := k) L).isSimpleModule_iff

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The canonical embedding of `rad L / rad² L` into `L / rad² L`. -/
def radicalTopToSquareTruncationMap
    (L : FinitelyGeneratedCategory A) :
    (Module.jacobson Aᵐᵒᵖ L ⧸
      Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)) →ₗ[Aᵐᵒᵖ]
      radicalSquareTruncationFGObj L := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let J := Module.jacobson Aᵐᵒᵖ L
  let K := Module.jacobson Aᵐᵒᵖ J
  let f : J →ₗ[Aᵐᵒᵖ] L := J.subtype
  let q := radicalSquareTruncationMkQ L
  let g : J →ₗ[Aᵐᵒᵖ] radicalSquareTruncationFGObj L := q.comp f
  have hf : Function.Injective f := J.subtype_injective
  have hmapK : K.map f = radicalSquareSubmodule L := by
    exact map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top
  have hker : g.ker = K := by
    dsimp only [g]
    rw [LinearMap.ker_comp, show q.ker = radicalSquareSubmodule L by
      exact (radicalSquareSubmodule L).ker_mkQ,
      ← hmapK, Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr hf, sup_bot_eq]
  let equivRange : (J ⧸ K) ≃ₗ[Aᵐᵒᵖ] LinearMap.range g :=
    (Submodule.quotEquivOfEq K g.ker hker.symm).trans g.quotKerEquivRange
  exact (LinearMap.range g).subtype.comp equivRange.toLinearMap

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The map from `rad L / rad² L` into `L / rad² L` is injective. -/
theorem radicalTopToSquareTruncationMap_injective
    (L : FinitelyGeneratedCategory A) :
    Function.Injective (radicalTopToSquareTruncationMap (k := k) L) := by
  dsimp [radicalTopToSquareTruncationMap]
  exact (LinearMap.range _).subtype_injective.comp (LinearEquiv.injective _)

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The image of `rad L / rad² L` is the radical of `L / rad² L`. -/
theorem radicalTopToSquareTruncationMap_range
    (L : FinitelyGeneratedCategory A) :
    LinearMap.range (radicalTopToSquareTruncationMap (k := k) L) =
      Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  dsimp [radicalTopToSquareTruncationMap]
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]
  rw [LinearMap.range_comp, Submodule.range_subtype]
  exact (moduleJacobson_radicalSquareTruncation_eq_map (k := k) L).symm

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The first radical of `L / rad² L` has zero module radical. -/
theorem moduleJacobson_jacobson_radicalSquareTruncation_eq_bot
    (L : FinitelyGeneratedCategory A) :
    Module.jacobson Aᵐᵒᵖ
        (Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L)) = ⊥ := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let X := radicalSquareTruncationFGObj L
  let JX := Module.jacobson Aᵐᵒᵖ X
  apply Submodule.map_injective_of_injective JX.subtype_injective
  rw [map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top,
    ringJacobson_square_smul_top_radicalSquareTruncation_eq_bot,
    Submodule.map_bot]

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The radical top of `L` is canonically the radical top of `L / rad² L`. -/
def radicalTopSquareTruncationLinearEquiv
    (L : FinitelyGeneratedCategory A) :
    (Module.jacobson Aᵐᵒᵖ L ⧸
      Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)) ≃ₗ[Aᵐᵒᵖ]
      (Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L) ⧸
        Module.jacobson Aᵐᵒᵖ
          (Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L))) := by
  let φ := radicalTopToSquareTruncationMap (k := k) L
  let JX := Module.jacobson Aᵐᵒᵖ (radicalSquareTruncationFGObj L)
  let eRange :
      (Module.jacobson Aᵐᵒᵖ L ⧸
        Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)) ≃ₗ[Aᵐᵒᵖ]
        LinearMap.range φ :=
    LinearEquiv.ofInjective φ (radicalTopToSquareTruncationMap_injective (k := k) L)
  let eJX : LinearMap.range φ ≃ₗ[Aᵐᵒᵖ] JX :=
    LinearEquiv.ofEq _ _ (radicalTopToSquareTruncationMap_range (k := k) L)
  exact (eRange.trans eJX).trans
    ((Module.jacobson Aᵐᵒᵖ JX).quotEquivOfEqBot
      (moduleJacobson_jacobson_radicalSquareTruncation_eq_bot (k := k) L)).symm

end MagnitudeConjecture.RightModule
