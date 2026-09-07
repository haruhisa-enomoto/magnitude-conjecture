import MagnitudeConjecture.Algebra.JacobsonRadicalAction
import MagnitudeConjecture.Algebra.CoordinateThinModule

/-!
# Radical-cube truncations in the biserial induction

The first Pogorzały--Skowroński obstruction replaces a local module `L` by
the literal quotient `X = L / rad³ L`.  This file packages that quotient and
proves the three structural facts used downstream: the third ring-radical
layer vanishes, the second layer is its image from `L`, and the simple top is
unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An ideal-generated layer commutes with a module quotient. -/
theorem map_ideal_smul_top_quotient
    (I : Ideal R) (K : Submodule R M) :
    (I • (⊤ : Submodule R M)).map K.mkQ =
      I • (⊤ : Submodule R (M ⧸ K)) := by
  rw [Submodule.map_smul'', Submodule.map_top, K.range_mkQ]

/-- Quotienting by a submodule containing an ideal-generated layer kills
that layer. -/
theorem ideal_smul_top_quotient_eq_bot_of_le
    (I : Ideal R) (K : Submodule R M)
    (hIK : I • (⊤ : Submodule R M) ≤ K) :
    I • (⊤ : Submodule R (M ⧸ K)) = ⊥ := by
  rw [← map_ideal_smul_top_quotient I K]
  exact le_antisymm
    ((Submodule.map_mono hIK).trans_eq K.mkQ_map_self)
    bot_le

/-- If an injective linear map sends a submodule to a simple module, then
the original submodule is simple. -/
theorem isSimpleModule_of_map_of_injective
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : Submodule R M) (hP : IsSimpleModule R (P.map f)) :
    IsSimpleModule R P := by
  let g := f.domRestrict P
  let e : P ≃ₗ[R] LinearMap.range g :=
    LinearEquiv.ofInjective g (hf.comp P.subtype_injective)
  have hrange : LinearMap.range g = P.map f := by
    ext y
    simp [g]
  rw [← hrange] at hP
  letI : IsSimpleModule R (LinearMap.range g) := hP
  exact IsSimpleModule.congr e

/-- An injective linear map identifies a submodule with its image. -/
def submoduleMapLinearEquivOfInjective
    {N : Type v} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (P : Submodule R M) :
    P ≃ₗ[R] P.map f :=
  (LinearEquiv.ofInjective (f.domRestrict P)
      (hf.comp P.subtype_injective)).trans
    (LinearEquiv.ofEq (LinearMap.range (f.domRestrict P)) (P.map f)
      (LinearMap.range_domRestrict P f))

/-- The quotient of one submodule by its intersection with another is the
image of the first submodule in the ambient quotient by the second. -/
def submoduleQuotientLinearEquivMap
    (P Q : Submodule R M) :
    (P ⧸ Q.comap P.subtype) ≃ₗ[R] P.map Q.mkQ := by
  let f : P →ₗ[R] (M ⧸ Q) := Q.mkQ.comp P.subtype
  have hker : f.ker = Q.comap P.subtype := by
    ext x
    change Q.mkQ x.1 = 0 ↔ x.1 ∈ Q
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hrange : f.range = P.map Q.mkQ := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  exact
    (Submodule.quotEquivOfEq (Q.comap P.subtype) f.ker hker.symm).trans
      (f.quotKerEquivRange.trans (LinearEquiv.ofEq f.range _ hrange))

/-- A submodule disjoint from the quotient denominator is canonically
equivalent to its image in the quotient. -/
def submoduleLinearEquivMapQuotientOfInfEqBot
    (P Q : Submodule R M) (hinf : P ⊓ Q = ⊥) :
    P ≃ₗ[R] P.map Q.mkQ := by
  have hcomap : Q.comap P.subtype = ⊥ := by
    apply Submodule.map_injective_of_injective P.subtype_injective
    rw [Submodule.map_comap_subtype, hinf, Submodule.map_bot]
  exact ((Q.comap P.subtype).quotEquivOfEqBot hcomap).symm.trans
    (submoduleQuotientLinearEquivMap P Q)

/-- Quotienting an ambient module by `Q` and then taking the top of the
image of `P` does not change the top of `P`, provided the part of `Q` lying
in `P` is radical. -/
def moduleTopOfMappedSubmoduleQuotientLinearEquiv
    (P Q : Submodule R M)
    (hQrad : Q.comap P.subtype ≤ Module.jacobson R P) :
    ((P.map Q.mkQ) ⧸ Module.jacobson R (P.map Q.mkQ)) ≃ₗ[R]
      (P ⧸ Module.jacobson R P) := by
  let K : Submodule R P := Q.comap P.subtype
  let X := P ⧸ K
  let e : X ≃ₗ[R] P.map Q.mkQ :=
    submoduleQuotientLinearEquivMap P Q
  have hradX : Module.jacobson R X =
      (Module.jacobson R P).map K.mkQ :=
    Module.jacobson_quotient_of_le hQrad
  exact (moduleTopLinearEquiv e).symm.trans
    ((Submodule.quotEquivOfEq _ _ hradX).trans
      (Submodule.quotientQuotientEquivQuotient
        K (Module.jacobson R P) hQrad))

/-- Two disjoint submodules identify their product with their sum. -/
def submoduleProdSupLinearEquiv
    (P Q : Submodule R M) (hinf : P ⊓ Q = ⊥) :
    (P × Q) ≃ₗ[R] ↑(P ⊔ Q : Submodule R M) := by
  let f : (P × Q) →ₗ[R] M := P.subtype.coprod Q.subtype
  have hrange : LinearMap.range f = P ⊔ Q := by
    dsimp only [f]
    rw [LinearMap.range_coprod, Submodule.range_subtype,
      Submodule.range_subtype]
  let g : (P × Q) →ₗ[R] ↑(P ⊔ Q : Submodule R M) :=
    f.codRestrict (P ⊔ Q) (by
      intro x
      rw [← hrange]
      exact ⟨x, rfl⟩)
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y hxy
    have hf : Function.Injective f := LinearMap.ker_eq_bot.mp (by
      dsimp only [f]
      rw [LinearMap.ker_coprod_of_disjoint_range,
        Submodule.ker_subtype, Submodule.ker_subtype, Submodule.prod_bot]
      simpa [Submodule.range_subtype, disjoint_iff] using hinf)
    exact hf (congrArg Subtype.val hxy)
  · intro y
    have hy : (y : M) ∈ LinearMap.range f := hrange.symm ▸ y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- The sum of two disjoint simple submodules has composition length two. -/
theorem length_sup_eq_two_of_disjoint_simple
    (P Q : Submodule R M) (hinf : P ⊓ Q = ⊥)
    (hP : IsSimpleModule R P) (hQ : IsSimpleModule R Q) :
    Module.length R ↑(P ⊔ Q : Submodule R M) = 2 := by
  rw [← (submoduleProdSupLinearEquiv P Q hinf).length_eq,
    Module.length_prod, Module.length_eq_one_iff.mpr hP,
    Module.length_eq_one_iff.mpr hQ]
  norm_num

/-- A module with one simple top layer, one simple middle radical layer,
and a bottom layer that is the sum of two disjoint simples has composition
length four. -/
theorem length_eq_four_of_three_simple_radical_layers
    [IsArtinian R M] [IsNoetherian R M]
    (S T : Submodule R M)
    (hinf : S ⊓ T = ⊥)
    (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (hSTJ : S ⊔ T ≤ Module.jacobson R M)
    (hJquot : IsSimpleModule R
      (Module.jacobson R M ⧸
        (S ⊔ T).comap (Module.jacobson R M).subtype))
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    Module.length R M = 4 := by
  let J := Module.jacobson R M
  let U : Submodule R J := (S ⊔ T).comap J.subtype
  have hUlength : Module.length R U = 2 := by
    calc
      Module.length R U = Module.length R ↑(S ⊔ T : Submodule R M) :=
        (Submodule.comapSubtypeEquivOfLe hSTJ).length_eq
      _ = 2 := length_sup_eq_two_of_disjoint_simple S T hinf hS hT
  have hJquotLength : Module.length R (J ⧸ U) = 1 :=
    Module.length_eq_one_iff.mpr hJquot
  have hJexact : Module.length R J =
      Module.length R U + Module.length R (J ⧸ U) :=
    Module.length_eq_add_of_exact U.subtype U.mkQ
      U.subtype_injective U.mkQ_surjective
      (LinearMap.exact_subtype_mkQ U)
  have hJlength : Module.length R J = 3 := by
    rw [hUlength, hJquotLength] at hJexact
    norm_num at hJexact ⊢
    exact hJexact
  have htopLength : Module.length R (M ⧸ J) = 1 :=
    Module.length_eq_one_iff.mpr htop
  have hMexact : Module.length R M =
      Module.length R J + Module.length R (M ⧸ J) :=
    Module.length_eq_add_of_exact J.subtype J.mkQ
      J.subtype_injective J.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J)
  rw [hJlength, htopLength] at hMexact
  norm_num at hMexact ⊢
  exact hMexact

end MagnitudeConjecture

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The third ring-radical layer of a finitely generated right module. -/
def radicalCubeSubmodule (L : FinitelyGeneratedCategory A) :
    Submodule Aᵐᵒᵖ L :=
  Ring.jacobson Aᵐᵒᵖ ^ 3 • (⊤ : Submodule Aᵐᵒᵖ L)

/-- The literal radical-cube truncation `L / rad³ L` used in the
Pogorzały--Skowroński induction. -/
def radicalCubeTruncationFGObj (L : FinitelyGeneratedCategory A) :
    FinitelyGeneratedCategory A :=
  quotientFGObj L (radicalCubeSubmodule L)

/-- The quotient map to the radical-cube truncation. -/
def radicalCubeTruncationMkQ (L : FinitelyGeneratedCategory A) :
    L →ₗ[Aᵐᵒᵖ] radicalCubeTruncationFGObj L :=
  quotientFGMkQ L (radicalCubeSubmodule L)

omit [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem radicalCubeTruncationMkQ_apply
    (L : FinitelyGeneratedCategory A) (x : L) :
    radicalCubeTruncationMkQ L x = (radicalCubeSubmodule L).mkQ x := rfl

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The third ring-radical layer vanishes in `L / rad³ L`. -/
theorem ringJacobson_cube_smul_top_radicalCubeTruncation_eq_bot
    (L : FinitelyGeneratedCategory A) :
    Ring.jacobson Aᵐᵒᵖ ^ 3 •
        (⊤ : Submodule Aᵐᵒᵖ (radicalCubeTruncationFGObj L)) = ⊥ := by
  exact ideal_smul_top_quotient_eq_bot_of_le
    (Ring.jacobson Aᵐᵒᵖ ^ 3) (radicalCubeSubmodule L) le_rfl

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The second ring-radical layer of `L / rad³ L` is exactly the image
of the second layer of `L`. -/
theorem map_ringJacobson_square_smul_top_radicalCubeTruncation
    (L : FinitelyGeneratedCategory A) :
    (Ring.jacobson Aᵐᵒᵖ ^ 2 • (⊤ : Submodule Aᵐᵒᵖ L)).map
        (radicalCubeTruncationMkQ L) =
      Ring.jacobson Aᵐᵒᵖ ^ 2 •
        (⊤ : Submodule Aᵐᵒᵖ (radicalCubeTruncationFGObj L)) := by
  exact map_ideal_smul_top_quotient
    (Ring.jacobson Aᵐᵒᵖ ^ 2) (radicalCubeSubmodule L)

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The canonical embedding of `rad² L / rad³ L` into the literal
radical-cube truncation `L / rad³ L`. -/
def radicalSecondTopToCubeTruncationMap
    (L : FinitelyGeneratedCategory A) :
    (Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L) ⧸
      Module.jacobson Aᵐᵒᵖ
        (Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L))) →ₗ[Aᵐᵒᵖ]
      radicalCubeTruncationFGObj L := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let J := Module.jacobson Aᵐᵒᵖ L
  let JJ := Module.jacobson Aᵐᵒᵖ J
  let K := Module.jacobson Aᵐᵒᵖ JJ
  let f : JJ →ₗ[Aᵐᵒᵖ] L := J.subtype.comp JJ.subtype
  let q := radicalCubeTruncationMkQ L
  let g : JJ →ₗ[Aᵐᵒᵖ] radicalCubeTruncationFGObj L := q.comp f
  have hf : Function.Injective f :=
    J.subtype_injective.comp JJ.subtype_injective
  have hmapK : K.map f = radicalCubeSubmodule L := by
    exact map_thriceIteratedModuleJacobson_eq_ringJacobson_cube_smul_top
  have hker : g.ker = K := by
    dsimp only [g]
    rw [LinearMap.ker_comp, show q.ker = radicalCubeSubmodule L by
      exact (radicalCubeSubmodule L).ker_mkQ,
      ← hmapK, Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr hf, sup_bot_eq]
  let equivRange : (JJ ⧸ K) ≃ₗ[Aᵐᵒᵖ] LinearMap.range g :=
    (Submodule.quotEquivOfEq K g.ker hker.symm).trans g.quotKerEquivRange
  exact (LinearMap.range g).subtype.comp equivRange.toLinearMap

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The map from `rad² L / rad³ L` into `L / rad³ L` is injective. -/
theorem radicalSecondTopToCubeTruncationMap_injective
    (L : FinitelyGeneratedCategory A) :
    Function.Injective (radicalSecondTopToCubeTruncationMap (k := k) L) := by
  dsimp [radicalSecondTopToCubeTruncationMap]
  exact (LinearMap.range _).subtype_injective.comp (LinearEquiv.injective _)

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The image of `rad² L / rad³ L` is exactly the second radical layer
of `L / rad³ L`. -/
theorem radicalSecondTopToCubeTruncationMap_range
    (L : FinitelyGeneratedCategory A) :
    LinearMap.range (radicalSecondTopToCubeTruncationMap (k := k) L) =
      Ring.jacobson Aᵐᵒᵖ ^ 2 •
        (⊤ : Submodule Aᵐᵒᵖ (radicalCubeTruncationFGObj L)) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  dsimp [radicalSecondTopToCubeTruncationMap]
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]
  rw [LinearMap.range_comp, LinearMap.range_comp,
    Submodule.range_subtype]
  rw [map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top]
  exact map_ringJacobson_square_smul_top_radicalCubeTruncation L

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The radical of `L / rad³ L` is the image of the radical of `L`. -/
theorem moduleJacobson_radicalCubeTruncation_eq_map
    (L : FinitelyGeneratedCategory A) :
    Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L) =
      (Module.jacobson Aᵐᵒᵖ L).map (radicalCubeTruncationMkQ L) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  rw [moduleJacobson_eq_ringJacobson_smul_top,
    moduleJacobson_eq_ringJacobson_smul_top]
  change Ring.jacobson Aᵐᵒᵖ •
      (⊤ : Submodule Aᵐᵒᵖ (L ⧸ radicalCubeSubmodule L)) =
    (Ring.jacobson Aᵐᵒᵖ • (⊤ : Submodule Aᵐᵒᵖ L)).map
      (radicalCubeSubmodule L).mkQ
  exact (map_ideal_smul_top_quotient
    (Ring.jacobson Aᵐᵒᵖ) (radicalCubeSubmodule L)).symm

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The third radical layer of `L` lies in its first radical. -/
theorem radicalCubeSubmodule_le_moduleJacobson
    (L : FinitelyGeneratedCategory A) :
    radicalCubeSubmodule L ≤ Module.jacobson Aᵐᵒᵖ L := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  rw [moduleJacobson_eq_ringJacobson_smul_top]
  exact Submodule.smul_mono (Ideal.pow_le_self (by norm_num)) le_rfl

/-- The top of `L / rad³ L` is canonically the top of `L`. -/
def radicalCubeTruncationTopLinearEquiv
    (L : FinitelyGeneratedCategory A) :
    quotientFGObj (radicalCubeTruncationFGObj L)
        (Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L)) ≃ₗ[Aᵐᵒᵖ]
      quotientFGObj L (Module.jacobson Aᵐᵒᵖ L) :=
  (Submodule.quotEquivOfEq _ _
      (moduleJacobson_radicalCubeTruncation_eq_map (k := k) L)).trans
    (Submodule.quotientQuotientEquivQuotient
      (radicalCubeSubmodule L) (Module.jacobson Aᵐᵒᵖ L)
      (radicalCubeSubmodule_le_moduleJacobson (k := k) L))

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Radical-cube truncation preserves simplicity of the module top. -/
theorem isSimpleModule_top_radicalCubeTruncation_iff
    (L : FinitelyGeneratedCategory A) :
    IsSimpleModule Aᵐᵒᵖ
        (quotientFGObj (radicalCubeTruncationFGObj L)
          (Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L))) ↔
      IsSimpleModule Aᵐᵒᵖ
        (quotientFGObj L (Module.jacobson Aᵐᵒᵖ L)) :=
  (radicalCubeTruncationTopLinearEquiv (k := k) L).isSimpleModule_iff

include k in
omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- If `rad L / rad² L` is simple, then it is the simple intervening
radical layer inside `L / rad³ L`. -/
theorem isSimpleModule_radicalLayer_radicalCubeTruncation
    (L : FinitelyGeneratedCategory A)
    (hJtop : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ L ⧸
        Module.jacobson Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L))) :
    IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (radicalCubeTruncationFGObj L) ⧸
        (Ring.jacobson Aᵐᵒᵖ ^ 2 •
          (⊤ : Submodule Aᵐᵒᵖ
            (radicalCubeTruncationFGObj L))).comap
          (Module.jacobson Aᵐᵒᵖ
            (radicalCubeTruncationFGObj L)).subtype) := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  let R := Aᵐᵒᵖ
  let X := radicalCubeTruncationFGObj L
  let J := Module.jacobson R L
  let JX := Module.jacobson R X
  let q := radicalCubeTruncationMkQ L
  let g : J →ₗ[R] X := q.comp J.subtype
  have hkerLe : g.ker ≤ Module.jacobson R J := by
    rw [show g.ker = (radicalCubeSubmodule L).comap J.subtype by
      dsimp only [g]
      rw [LinearMap.ker_comp]
      change (radicalCubeSubmodule L).mkQ.ker.comap J.subtype = _
      rw [(radicalCubeSubmodule L).ker_mkQ]]
    intro x hx
    rw [← Submodule.comap_map_eq_self
      (f := J.subtype) (p := Module.jacobson R J)
      (by rw [LinearMap.ker_eq_bot.mpr J.subtype_injective]; exact bot_le),
      map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top]
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (by norm_num : 2 ≤ 3))
      le_rfl hx
  have hquotientTop : IsSimpleModule R
      ((J ⧸ g.ker) ⧸ Module.jacobson R (J ⧸ g.ker)) :=
    isSimpleModule_top_quotient_of_le_jacobson g.ker hkerLe hJtop
  have hrange : LinearMap.range g = JX := by
    dsimp only [g, q, JX, X]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact (moduleJacobson_radicalCubeTruncation_eq_map (k := k) L).symm
  let equivJ : (J ⧸ g.ker) ≃ₗ[R] JX :=
    g.quotKerEquivRange.trans
      (LinearEquiv.ofEq (LinearMap.range g) JX hrange)
  have hJXtop : IsSimpleModule R (JX ⧸ Module.jacobson R JX) :=
    isSimpleModule_top_congr equivJ hquotientTop
  have hdenom : Module.jacobson R JX =
      (Ring.jacobson R ^ 2 • (⊤ : Submodule R X)).comap JX.subtype := by
    apply Submodule.map_injective_of_injective JX.subtype_injective
    rw [map_iteratedModuleJacobson_eq_ringJacobson_sq_smul_top,
      Submodule.map_comap_subtype]
    apply Eq.symm
    apply inf_eq_right.mpr
    change Ring.jacobson R ^ 2 • (⊤ : Submodule R X) ≤
      Module.jacobson R X
    rw [moduleJacobson_eq_ringJacobson_smul_top (R := R) (M := X)]
    exact Submodule.smul_mono
      (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) le_rfl
  rw [← hdenom]
  exact hJXtop

end MagnitudeConjecture.RightModule
