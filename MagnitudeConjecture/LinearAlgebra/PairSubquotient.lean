import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# Moving a two-filtration subquotient across a linear map

For nested subspaces `A⁻ ≤ A⁺` in the source and `B⁻ ≤ B⁺` in the target,
a linear map identifies the two naturally corresponding subquotients built
from image and preimage.  This is the linear-algebra step in Ringel's proof
that a string detector does not depend on the chosen split position.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.LinearAlgebra.PairSubquotient

universe u

variable {k V W : Type u} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

variable (f : V →ₗ[k] W)
variable (Aminus Aplus : Submodule k V) (Bminus Bplus : Submodule k W)

/-- Transport a subquotient across equal numerator and denominator
submodules. -/
def quotientEquivOfEq
    (U U' D D' : Submodule k V) (hU : U = U') (hD : D = D') :
    (U ⧸ D.comap U.subtype) ≃ₗ[k]
      (U' ⧸ D'.comap U'.subtype) := by
  subst U'
  subst D'
  exact LinearEquiv.refl k _

@[simp]
theorem quotientEquivOfEq_apply_mk
    (U U' D D' : Submodule k V) (hU : U = U') (hD : D = D')
    (x : U) :
    quotientEquivOfEq U U' D D' hU hD (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨x, by rw [← hU]; exact x.2⟩ : U') := by
  subst U'
  subst D'
  rfl

/-- Numerator before moving across `f`. -/
def sourceNumerator : Submodule k V :=
  Aplus ⊓ Bplus.comap f

/-- Denominator before moving across `f`. -/
def sourceDenominator : Submodule k V :=
  (Aplus ⊓ Bminus.comap f) ⊔ (Aminus ⊓ Bplus.comap f)

/-- Numerator after moving across `f`. -/
def targetNumerator : Submodule k W :=
  Aplus.map f ⊓ Bplus

/-- Denominator after moving across `f`. -/
def targetDenominator : Submodule k W :=
  (Aplus.map f ⊓ Bminus) ⊔ (Aminus.map f ⊓ Bplus)

theorem sourceDenominator_le_sourceNumerator
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    sourceDenominator f Aminus Aplus Bminus Bplus ≤
      sourceNumerator f Aplus Bplus := by
  apply sup_le
  · exact inf_le_inf le_rfl (Submodule.comap_mono hB)
  · exact inf_le_inf hA le_rfl

theorem targetDenominator_le_targetNumerator
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    targetDenominator f Aminus Aplus Bminus Bplus ≤
      targetNumerator f Aplus Bplus := by
  apply sup_le
  · exact inf_le_inf le_rfl hB
  · exact inf_le_inf (Submodule.map_mono hA) le_rfl

/-- The source denominator inside its numerator. -/
def sourceDenominatorInNumerator :
    Submodule k (sourceNumerator f Aplus Bplus) :=
  (sourceDenominator f Aminus Aplus Bminus Bplus).comap
    (sourceNumerator f Aplus Bplus).subtype

/-- The target denominator inside its numerator. -/
def targetDenominatorInNumerator :
    Submodule k (targetNumerator f Aplus Bplus) :=
  (targetDenominator f Aminus Aplus Bminus Bplus).comap
    (targetNumerator f Aplus Bplus).subtype

/-- Restriction of `f` to the two numerators. -/
def numeratorMap :
    sourceNumerator f Aplus Bplus →ₗ[k]
      targetNumerator f Aplus Bplus :=
  LinearMap.codRestrict (targetNumerator f Aplus Bplus)
    (f.domRestrict (sourceNumerator f Aplus Bplus)) (by
      intro x
      exact ⟨⟨x, x.2.1, rfl⟩, x.2.2⟩)

@[simp]
theorem numeratorMap_coe (x : sourceNumerator f Aplus Bplus) :
    (numeratorMap f Aplus Bplus x : W) = f x :=
  rfl

theorem denominator_map_le
    (_hA : Aminus ≤ Aplus) (_hB : Bminus ≤ Bplus) :
    (sourceDenominatorInNumerator f Aminus Aplus Bminus Bplus).map
        (numeratorMap f Aplus Bplus) ≤
      targetDenominatorInNumerator f Aminus Aplus Bminus Bplus := by
  rintro y ⟨x, hx, rfl⟩
  change (numeratorMap f Aplus Bplus x : W) ∈
    targetDenominator f Aminus Aplus Bminus Bplus
  rw [numeratorMap_coe]
  change (x : V) ∈ sourceDenominator f Aminus Aplus Bminus Bplus at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  apply Submodule.mem_sup.mpr
  refine ⟨f a, ⟨⟨a, ha.1, rfl⟩, ha.2⟩,
    f b, ⟨⟨b, hb.1, rfl⟩, hb.2⟩, ?_⟩
  rw [← map_add, hab]

/-- The linear map between the two subquotients. -/
def quotientMap
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    (sourceNumerator f Aplus Bplus ⧸
        sourceDenominatorInNumerator f Aminus Aplus Bminus Bplus) →ₗ[k]
      (targetNumerator f Aplus Bplus ⧸
        targetDenominatorInNumerator f Aminus Aplus Bminus Bplus) :=
  Submodule.mapQ
    (sourceDenominatorInNumerator f Aminus Aplus Bminus Bplus)
    (targetDenominatorInNumerator f Aminus Aplus Bminus Bplus)
    (numeratorMap f Aplus Bplus)
    (by
      rw [← Submodule.map_le_iff_le_comap]
      exact denominator_map_le f Aminus Aplus Bminus Bplus hA hB)

@[simp]
theorem quotientMap_mk
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus)
    (x : sourceNumerator f Aplus Bplus) :
    quotientMap f Aminus Aplus Bminus Bplus hA hB
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (numeratorMap f Aplus Bplus x) := by
  exact Submodule.mapQ_apply _ _ _ x

theorem quotientMap_surjective
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    Function.Surjective
      (quotientMap f Aminus Aplus Bminus Bplus hA hB) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
      rcases y.2.1 with ⟨x, hxA, hfx⟩
      let xnum : sourceNumerator f Aplus Bplus :=
        ⟨x, hxA, by
          change f x ∈ Bplus
          rw [hfx]
          exact y.2.2⟩
      refine ⟨Submodule.Quotient.mk xnum, ?_⟩
      rw [quotientMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact hfx

theorem quotientMap_injective
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    Function.Injective
      (quotientMap f Aminus Aplus Bminus Bplus hA hB) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [quotientMap_mk] at hq
      have hfxNumerator := (Submodule.Quotient.mk_eq_zero
        (targetDenominatorInNumerator f Aminus Aplus Bminus Bplus)).mp hq
      change (numeratorMap f Aplus Bplus x : W) ∈
        targetDenominator f Aminus Aplus Bminus Bplus at hfxNumerator
      have hfx : f (x : V) ∈
          targetDenominator f Aminus Aplus Bminus Bplus := by
        simpa only [numeratorMap_coe] using hfxNumerator
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hfx
      rcases hy.1 with ⟨a, haA, hfa⟩
      rcases hz.1 with ⟨b, hbAminus, hfb⟩
      let r : V := (x : V) - a - b
      have hrA : r ∈ Aplus := by
        exact Aplus.sub_mem (Aplus.sub_mem x.2.1 haA) (hA hbAminus)
      have hfra : f (r + a) = y := by
        calc
          f (r + a) = f (x : V) - f a - f b + f a := by
            simp only [map_add, map_sub, r]
          _ = f (x : V) - f b := by abel
          _ = (y + z) - z := by rw [← hyz, hfb]
          _ = y := add_sub_cancel_right y z
      have hraA : r + a ∈ Aplus := Aplus.add_mem hrA haA
      have hraBminus : f (r + a) ∈ Bminus := hfra ▸ hy.2
      have hbBplus : f b ∈ Bplus := hfb ▸ hz.2
      have hxden : (x : V) ∈
          sourceDenominator f Aminus Aplus Bminus Bplus := by
        apply Submodule.mem_sup.mpr
        refine ⟨r + a, ⟨hraA, hraBminus⟩,
          b, ⟨hbAminus, hbBplus⟩, ?_⟩
        dsimp only [r]
        abel
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (x : V) ∈ sourceDenominator f Aminus Aplus Bminus Bplus
      exact hxden

/-- Moving the split across one linear map gives a linear equivalence of the
two pair subquotients. -/
def quotientEquiv
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    (sourceNumerator f Aplus Bplus ⧸
        sourceDenominatorInNumerator f Aminus Aplus Bminus Bplus) ≃ₗ[k]
      (targetNumerator f Aplus Bplus ⧸
        targetDenominatorInNumerator f Aminus Aplus Bminus Bplus) :=
  LinearEquiv.ofBijective
    (quotientMap f Aminus Aplus Bminus Bplus hA hB)
    ⟨quotientMap_injective f Aminus Aplus Bminus Bplus hA hB,
      quotientMap_surjective f Aminus Aplus Bminus Bplus hA hB⟩

/-- Source numerator with the two filtrations written in the opposite
order. -/
def swappedSourceNumerator : Submodule k V :=
  Bplus.comap f ⊓ Aplus

/-- Source denominator with the two filtrations written in the opposite
order. -/
def swappedSourceDenominator : Submodule k V :=
  (Bplus.comap f ⊓ Aminus) ⊔ (Bminus.comap f ⊓ Aplus)

/-- Target numerator with the two filtrations written in the opposite
order. -/
def swappedTargetNumerator : Submodule k W :=
  Bplus ⊓ Aplus.map f

/-- Target denominator with the two filtrations written in the opposite
order. -/
def swappedTargetDenominator : Submodule k W :=
  (Bplus ⊓ Aminus.map f) ⊔ (Bminus ⊓ Aplus.map f)

/-- Restriction of `f` between the swapped numerators. -/
def swappedNumeratorMap :
    swappedSourceNumerator f Aplus Bplus →ₗ[k]
      swappedTargetNumerator f Aplus Bplus :=
  LinearMap.codRestrict (swappedTargetNumerator f Aplus Bplus)
    (f.domRestrict (swappedSourceNumerator f Aplus Bplus)) (by
      intro x
      exact ⟨x.2.1, ⟨x, x.2.2, rfl⟩⟩)

@[simp]
theorem swappedNumeratorMap_coe
    (x : swappedSourceNumerator f Aplus Bplus) :
    (swappedNumeratorMap f Aplus Bplus x : W) = f x :=
  rfl

/-- Swapped source denominator inside its numerator. -/
def swappedSourceDenominatorInNumerator :
    Submodule k (swappedSourceNumerator f Aplus Bplus) :=
  (swappedSourceDenominator f Aminus Aplus Bminus Bplus).comap
    (swappedSourceNumerator f Aplus Bplus).subtype

/-- Swapped target denominator inside its numerator. -/
def swappedTargetDenominatorInNumerator :
    Submodule k (swappedTargetNumerator f Aplus Bplus) :=
  (swappedTargetDenominator f Aminus Aplus Bminus Bplus).comap
    (swappedTargetNumerator f Aplus Bplus).subtype

theorem swappedDenominator_map_le :
    (swappedSourceDenominatorInNumerator
        f Aminus Aplus Bminus Bplus).map
        (swappedNumeratorMap f Aplus Bplus) ≤
      swappedTargetDenominatorInNumerator
        f Aminus Aplus Bminus Bplus := by
  rintro y ⟨x, hx, rfl⟩
  change (swappedNumeratorMap f Aplus Bplus x : W) ∈
    swappedTargetDenominator f Aminus Aplus Bminus Bplus
  rw [swappedNumeratorMap_coe]
  change (x : V) ∈
    swappedSourceDenominator f Aminus Aplus Bminus Bplus at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  apply Submodule.mem_sup.mpr
  refine ⟨f a, ⟨ha.1, ⟨a, ha.2, rfl⟩⟩,
    f b, ⟨hb.1, ⟨b, hb.2, rfl⟩⟩, ?_⟩
  rw [← map_add, hab]

/-- Explicit quotient map between the swapped pair subquotients. -/
def swappedQuotientMap :
    (swappedSourceNumerator f Aplus Bplus ⧸
        swappedSourceDenominatorInNumerator
          f Aminus Aplus Bminus Bplus) →ₗ[k]
      (swappedTargetNumerator f Aplus Bplus ⧸
        swappedTargetDenominatorInNumerator
          f Aminus Aplus Bminus Bplus) :=
  Submodule.mapQ
    (swappedSourceDenominatorInNumerator
      f Aminus Aplus Bminus Bplus)
    (swappedTargetDenominatorInNumerator
      f Aminus Aplus Bminus Bplus)
    (swappedNumeratorMap f Aplus Bplus)
    (by
      rw [← Submodule.map_le_iff_le_comap]
      exact swappedDenominator_map_le f Aminus Aplus Bminus Bplus)

@[simp]
theorem swappedQuotientMap_mk
    (x : swappedSourceNumerator f Aplus Bplus) :
    swappedQuotientMap f Aminus Aplus Bminus Bplus
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (swappedNumeratorMap f Aplus Bplus x) := by
  exact Submodule.mapQ_apply _ _ _ x

theorem swappedQuotientMap_surjective :
    Function.Surjective
      (swappedQuotientMap f Aminus Aplus Bminus Bplus) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
      rcases y.2.2 with ⟨x, hxA, hfx⟩
      let xnum : swappedSourceNumerator f Aplus Bplus :=
        ⟨x, by
          change f x ∈ Bplus
          rw [hfx]
          exact y.2.1, hxA⟩
      refine ⟨Submodule.Quotient.mk xnum, ?_⟩
      rw [swappedQuotientMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact hfx

theorem swappedQuotientMap_injective
    (hA : Aminus ≤ Aplus) :
    Function.Injective
      (swappedQuotientMap f Aminus Aplus Bminus Bplus) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [swappedQuotientMap_mk] at hq
      have hfxNumerator := (Submodule.Quotient.mk_eq_zero
        (swappedTargetDenominatorInNumerator
          f Aminus Aplus Bminus Bplus)).mp hq
      change (swappedNumeratorMap f Aplus Bplus x : W) ∈
        swappedTargetDenominator f Aminus Aplus Bminus Bplus at hfxNumerator
      have hfx : f (x : V) ∈
          swappedTargetDenominator f Aminus Aplus Bminus Bplus := by
        simpa only [swappedNumeratorMap_coe] using hfxNumerator
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hfx
      rcases hy.2 with ⟨a, haAminus, hfa⟩
      rcases hz.2 with ⟨b, hbA, hfb⟩
      let r : V := (x : V) - a - b
      have hrA : r ∈ Aplus := by
        exact Aplus.sub_mem (Aplus.sub_mem x.2.2 (hA haAminus)) hbA
      have hfrb : f (r + b) = z := by
        calc
          f (r + b) = f (x : V) - f a - f b + f b := by
            simp only [map_add, map_sub, r]
          _ = f (x : V) - f a := by abel
          _ = (y + z) - y := by rw [← hyz, hfa]
          _ = z := add_sub_cancel_left y z
      have haBplus : f a ∈ Bplus := hfa ▸ hy.1
      have hrbA : r + b ∈ Aplus := Aplus.add_mem hrA hbA
      have hrbBminus : f (r + b) ∈ Bminus := hfrb ▸ hz.1
      have hxden : (x : V) ∈
          swappedSourceDenominator f Aminus Aplus Bminus Bplus := by
        apply Submodule.mem_sup.mpr
        refine ⟨a, ⟨haBplus, haAminus⟩,
          r + b, ⟨hrbBminus, hrbA⟩, ?_⟩
        dsimp only [r]
        abel
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (x : V) ∈
        swappedSourceDenominator f Aminus Aplus Bminus Bplus
      exact hxden

/-- The same image/preimage equivalence when both pair filtrations are
written in the opposite order. -/
def quotientEquivSwapped
    (hA : Aminus ≤ Aplus) (_hB : Bminus ≤ Bplus) :
    (swappedSourceNumerator f Aplus Bplus ⧸
        (swappedSourceDenominator f Aminus Aplus Bminus Bplus).comap
          (swappedSourceNumerator f Aplus Bplus).subtype) ≃ₗ[k]
      (swappedTargetNumerator f Aplus Bplus ⧸
        (swappedTargetDenominator f Aminus Aplus Bminus Bplus).comap
          (swappedTargetNumerator f Aplus Bplus).subtype) :=
  LinearEquiv.ofBijective
    (swappedQuotientMap f Aminus Aplus Bminus Bplus)
    ⟨swappedQuotientMap_injective f Aminus Aplus Bminus Bplus hA,
      swappedQuotientMap_surjective f Aminus Aplus Bminus Bplus⟩

@[simp]
theorem quotientEquiv_apply_mk
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus)
    (x : sourceNumerator f Aplus Bplus) :
    quotientEquiv f Aminus Aplus Bminus Bplus hA hB
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (numeratorMap f Aplus Bplus x) := by
  exact quotientMap_mk f Aminus Aplus Bminus Bplus hA hB x

@[simp]
theorem quotientEquivSwapped_apply_mk
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus)
    (x : swappedSourceNumerator f Aplus Bplus) :
    quotientEquivSwapped f Aminus Aplus Bminus Bplus hA hB
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (swappedNumeratorMap f Aplus Bplus x) := by
  exact swappedQuotientMap_mk f Aminus Aplus Bminus Bplus x

/-- Move a pair subquotient across `f` after identifying the displayed source
and target numerators and denominators with the generic image/preimage pair. -/
def quotientEquivIdentified
    (U D : Submodule k V) (U' D' : Submodule k W)
    (hSourceNum : U = sourceNumerator f Aplus Bplus)
    (hSourceDen : D = sourceDenominator f Aminus Aplus Bminus Bplus)
    (hTargetNum : targetNumerator f Aplus Bplus = U')
    (hTargetDen : targetDenominator f Aminus Aplus Bminus Bplus = D')
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    (U ⧸ D.comap U.subtype) ≃ₗ[k]
      (U' ⧸ D'.comap U'.subtype) :=
  (quotientEquivOfEq U (sourceNumerator f Aplus Bplus)
      D (sourceDenominator f Aminus Aplus Bminus Bplus)
      hSourceNum hSourceDen).trans
    ((quotientEquiv f Aminus Aplus Bminus Bplus hA hB).trans
      (quotientEquivOfEq (targetNumerator f Aplus Bplus) U'
        (targetDenominator f Aminus Aplus Bminus Bplus) D'
        hTargetNum hTargetDen))

@[simp]
theorem quotientEquivIdentified_apply_mk
    (U D : Submodule k V) (U' D' : Submodule k W)
    (hSourceNum : U = sourceNumerator f Aplus Bplus)
    (hSourceDen : D = sourceDenominator f Aminus Aplus Bminus Bplus)
    (hTargetNum : targetNumerator f Aplus Bplus = U')
    (hTargetDen : targetDenominator f Aminus Aplus Bminus Bplus = D')
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) (x : U) :
    quotientEquivIdentified f Aminus Aplus Bminus Bplus U D U' D'
        hSourceNum hSourceDen hTargetNum hTargetDen hA hB
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f x.1, by
          rw [← hTargetNum]
          exact (numeratorMap f Aplus Bplus
            (⟨x.1, by rw [← hSourceNum]; exact x.2⟩ :
              sourceNumerator f Aplus Bplus)).2⟩ : U') := by
  let xSource : sourceNumerator f Aplus Bplus :=
    ⟨x.1, by rw [← hSourceNum]; exact x.2⟩
  let sourceTransport := quotientEquivOfEq U
    (sourceNumerator f Aplus Bplus) D
    (sourceDenominator f Aminus Aplus Bminus Bplus)
    hSourceNum hSourceDen
  let middle := quotientEquiv f Aminus Aplus Bminus Bplus hA hB
  let targetTransport := quotientEquivOfEq
    (targetNumerator f Aplus Bplus) U'
    (targetDenominator f Aminus Aplus Bminus Bplus) D'
    hTargetNum hTargetDen
  change (sourceTransport.trans (middle.trans targetTransport))
    (Submodule.Quotient.mk x) = _
  calc
    _ = targetTransport (middle
        (sourceTransport (Submodule.Quotient.mk x))) := rfl
    _ = targetTransport (middle (Submodule.Quotient.mk xSource)) := by
      rw [quotientEquivOfEq_apply_mk]
      apply congrArg (fun q ↦ targetTransport (middle q))
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      rfl
    _ = targetTransport
        (Submodule.Quotient.mk (numeratorMap f Aplus Bplus xSource)) := by
      rw [quotientEquiv_apply_mk]
      apply congrArg targetTransport
      rfl
    _ = _ := by
      rw [quotientEquivOfEq_apply_mk]
      rfl

/-- The identified form of `quotientEquivSwapped`. -/
def quotientEquivSwappedIdentified
    (U D : Submodule k V) (U' D' : Submodule k W)
    (hSourceNum : U = swappedSourceNumerator f Aplus Bplus)
    (hSourceDen : D = swappedSourceDenominator f Aminus Aplus Bminus Bplus)
    (hTargetNum : swappedTargetNumerator f Aplus Bplus = U')
    (hTargetDen : swappedTargetDenominator f Aminus Aplus Bminus Bplus = D')
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) :
    (U ⧸ D.comap U.subtype) ≃ₗ[k]
      (U' ⧸ D'.comap U'.subtype) :=
  (quotientEquivOfEq U (swappedSourceNumerator f Aplus Bplus)
      D (swappedSourceDenominator f Aminus Aplus Bminus Bplus)
      hSourceNum hSourceDen).trans
    ((quotientEquivSwapped f Aminus Aplus Bminus Bplus hA hB).trans
      (quotientEquivOfEq (swappedTargetNumerator f Aplus Bplus) U'
        (swappedTargetDenominator f Aminus Aplus Bminus Bplus) D'
        hTargetNum hTargetDen))

@[simp]
theorem quotientEquivSwappedIdentified_apply_mk
    (U D : Submodule k V) (U' D' : Submodule k W)
    (hSourceNum : U = swappedSourceNumerator f Aplus Bplus)
    (hSourceDen : D = swappedSourceDenominator f Aminus Aplus Bminus Bplus)
    (hTargetNum : swappedTargetNumerator f Aplus Bplus = U')
    (hTargetDen : swappedTargetDenominator f Aminus Aplus Bminus Bplus = D')
    (hA : Aminus ≤ Aplus) (hB : Bminus ≤ Bplus) (x : U) :
    quotientEquivSwappedIdentified f Aminus Aplus Bminus Bplus U D U' D'
        hSourceNum hSourceDen hTargetNum hTargetDen hA hB
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f x.1, by
          rw [← hTargetNum]
          exact (swappedNumeratorMap f Aplus Bplus
            (⟨x.1, by rw [← hSourceNum]; exact x.2⟩ :
              swappedSourceNumerator f Aplus Bplus)).2⟩ : U') := by
  let xSource : swappedSourceNumerator f Aplus Bplus :=
    ⟨x.1, by rw [← hSourceNum]; exact x.2⟩
  let sourceTransport := quotientEquivOfEq U
    (swappedSourceNumerator f Aplus Bplus) D
    (swappedSourceDenominator f Aminus Aplus Bminus Bplus)
    hSourceNum hSourceDen
  let middle := quotientEquivSwapped f Aminus Aplus Bminus Bplus hA hB
  let targetTransport := quotientEquivOfEq
    (swappedTargetNumerator f Aplus Bplus) U'
    (swappedTargetDenominator f Aminus Aplus Bminus Bplus) D'
    hTargetNum hTargetDen
  change (sourceTransport.trans (middle.trans targetTransport))
    (Submodule.Quotient.mk x) = _
  calc
    _ = targetTransport (middle
        (sourceTransport (Submodule.Quotient.mk x))) := rfl
    _ = targetTransport (middle (Submodule.Quotient.mk xSource)) := by
      rw [quotientEquivOfEq_apply_mk]
    _ = targetTransport
        (Submodule.Quotient.mk (swappedNumeratorMap f Aplus Bplus xSource)) := by
      rw [quotientEquivSwapped_apply_mk]
    _ = _ := by
      rw [quotientEquivOfEq_apply_mk]
      rfl

end MagnitudeConjecture.LinearAlgebra.PairSubquotient
