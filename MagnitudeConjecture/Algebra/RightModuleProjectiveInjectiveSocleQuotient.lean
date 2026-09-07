import MagnitudeConjecture.Algebra.RightModuleInjectiveSocleQuotient
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleIdeal
import MagnitudeConjecture.Algebra.RightModuleSimpleTop

/-!
# The replacement projective after socle rejection

For a non-simple primitive projective-injective `eA`, this file realizes
`eA / soc(eA)` as an indecomposable projective over the literal quotient
algebra `A / soc(eA)`.  Projectivity is proved directly in the annihilated
ambient full subcategory; indecomposability follows from preservation of the
simple top.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- The literal ambient module `e_p A / soc(e_p A)`. -/
abbrev primitiveProjectiveSocleQuotientFGObj
    (p : S.ProjectiveLabel) :
    RightModule.FinitelyGeneratedCategory A :=
  moduleSocleQuotientFGObj
    (RightModule.rightIdealFGObj (P.idempotent p))

/-- The canonical quotient map `e_p A → e_p A / soc(e_p A)`. -/
abbrev primitiveProjectiveSocleQuotientProjection
    (p : S.ProjectiveLabel) :
    RightModule.rightIdealFGObj (P.idempotent p) ⟶
      P.primitiveProjectiveSocleQuotientFGObj p :=
  moduleSocleQuotientProjection
    (RightModule.rightIdealFGObj (P.idempotent p))

/-- The quotient map to `e_p A / soc(e_p A)` is epic. -/
theorem primitiveProjectiveSocleQuotientProjection_epi
    (p : S.ProjectiveLabel) :
    Epi (P.primitiveProjectiveSocleQuotientProjection p) :=
  moduleSocleQuotientProjection_epi
    (RightModule.rightIdealFGObj (P.idempotent p))

/-- The canonical quotient is the minimal left almost-split map out of the
selected primitive projective-injective. -/
theorem primitiveProjectiveSocleQuotientProjection_isLeftAlmostSplit
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    IsLeftAlmostSplit
      (P.primitiveProjectiveSocleQuotientProjection p) := by
  let pIso := P.primitiveProjectiveIso p
  letI : Injective
      (RightModule.rightIdealFGObj (P.idempotent p)) :=
    Injective.of_iso pIso.symm hpInjective
  exact moduleSocleQuotientProjection_isLeftAlmostSplit (k := k) _
    (RightModule.rightIdealFGObj_indecomposable (P.primitive p))

/-- The canonical quotient map is left minimal. -/
theorem primitiveProjectiveSocleQuotientProjection_isLeftMinimal
    (p : S.ProjectiveLabel) :
    IsLeftMinimal
      (P.primitiveProjectiveSocleQuotientProjection p) :=
  moduleSocleQuotientProjection_isLeftMinimal _

/-- The embedded socle ideal annihilates the quotient
`e_p A / soc(e_p A)`. -/
theorem primitiveProjectiveSocleQuotient_isAnnihilatedBy
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective)
      (P.primitiveProjectiveSocleQuotientFGObj p) := by
  intro x a ha
  let E := RightModule.rightIdealFGObj (P.idempotent p)
  let L := moduleSocle Aᵐᵒᵖ E
  obtain ⟨y, rfl⟩ := RightModule.quotientFGMkQ_surjective E L x
  change (MulOpposite.op a) • L.mkQ y = 0
  rw [← L.mkQ.map_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  have hprod : y.1 * a ∈
      P.primitiveProjectiveSocleIdeal p hpInjective :=
    (P.primitiveProjectiveSocleIdeal p hpInjective).mul_mem_left
      y.1 a ha
  have hprodSub : y.1 * a ∈
      P.primitiveProjectiveSocleSubmodule p :=
    (P.mem_primitiveProjectiveSocleIdeal p hpInjective (y.1 * a)).1
      hprod
  change y.1 * a ∈ L.map
    (RightModule.rightIdeal (P.idempotent p)).subtype at hprodSub
  obtain ⟨z, hz, hzval⟩ := hprodSub
  have hza : (MulOpposite.op a) • y = z := by
    apply Subtype.ext
    exact hzval.symm
  rw [hza]
  exact hz

/-- The replacement quotient, bundled in the full ambient subcategory
annihilated by the embedded socle ideal. -/
def primitiveProjectiveSocleQuotientObj
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    RightModule.IdealQuotientSubcategory
      (P.primitiveProjectiveSocleIdeal p hpInjective) :=
  ⟨P.primitiveProjectiveSocleQuotientFGObj p,
    P.primitiveProjectiveSocleQuotient_isAnnihilatedBy p hpInjective⟩

/-- The replacement quotient is projective in the full subcategory of
ambient modules annihilated by the embedded socle ideal. -/
theorem primitiveProjectiveSocleQuotientObj_projective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    Projective (P.primitiveProjectiveSocleQuotientObj p hpInjective) := by
  apply Projective.mk
  intro E X f q _
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let P₀ := RightModule.rightIdealFGObj (P.idempotent p)
  let L := moduleSocle Aᵐᵒᵖ P₀
  let Q := P.primitiveProjectiveSocleQuotientFGObj p
  let π : P₀ ⟶ Q :=
    P.primitiveProjectiveSocleQuotientProjection p
  letI : Epi π :=
    P.primitiveProjectiveSocleQuotientProjection_epi p
  letI : Epi q.hom :=
    RightModule.idealQuotientSubcategory_epi_ambient I q
  letI : Projective P₀ :=
    RightModule.rightIdealFGObj_projective (P.primitive p).idempotent
  obtain ⟨h, hh⟩ := Projective.factors (π ≫ f.hom) q.hom
  have hsocle : L ≤ h.hom.hom.ker := by
    intro z hz
    change h.hom.hom z = 0
    have hzIdeal : z.1 ∈ I := by
      change z.1 ∈
        P.primitiveProjectiveSocleIdeal p hpInjective
      rw [P.mem_primitiveProjectiveSocleIdeal]
      change z.1 ∈ L.map
        (RightModule.rightIdeal (P.idempotent p)).subtype
      exact ⟨z, hz, rfl⟩
    have hzero := E.property
      (h.hom.hom (RightModule.rightIdealGenerator (P.idempotent p)))
      z.1 hzIdeal
    calc
      h.hom.hom z =
          h.hom.hom ((MulOpposite.op z.1) •
            RightModule.rightIdealGenerator (P.idempotent p)) := by
        congr 1
        apply Subtype.ext
        exact (RightModule.rightIdeal_fixed
          (P.primitive p).idempotent z).symm
      _ = (MulOpposite.op z.1) •
          h.hom.hom
            (RightModule.rightIdealGenerator (P.idempotent p)) :=
        h.hom.hom.map_smul _ _
      _ = 0 := hzero
  let hbarLinear : Q →ₗ[Aᵐᵒᵖ] E.obj :=
    RightModule.quotientFGLift P₀ E.obj L h.hom.hom hsocle
  let hbar : Q ⟶ E.obj := FGModuleCat.ofHom hbarLinear
  have hπ : π ≫ hbar = h := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact RightModule.quotientFGLift_apply_mkQ
      P₀ E.obj L h.hom.hom hsocle y
  refine ⟨ObjectProperty.homMk hbar, ?_⟩
  apply ObjectProperty.hom_ext
  change hbar ≫ q.hom = f.hom
  apply (cancel_epi π).1
  change (π ≫ hbar) ≫ q.hom = π ≫ f.hom
  rw [hπ, hh]

/-- The literal primitive right ideal has simple top. -/
theorem primitiveProjective_top_isSimpleModule
    (p : S.ProjectiveLabel) :
    IsSimpleModule Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p) ⧸
        Module.jacobson Aᵐᵒᵖ
          (RightModule.rightIdealFGObj (P.idempotent p))) := by
  exact isSimpleModule_top_congr
    (FGModuleCat.isoToLinearEquiv (P.primitiveProjectiveIso p).symm)
    (S.projectiveSimpleTop_isSimpleModule p)

/-- Non-simplicity of the selected skeletal projective is equivalent in the
direction needed for its literal primitive-right-ideal realization. -/
theorem primitiveProjective_not_isSimpleModule
    (p : S.ProjectiveLabel)
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    ¬ IsSimpleModule Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p)) := by
  intro hsimple
  letI : IsSimpleModule Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p)) := hsimple
  exact hnotSimple <|
    IsSimpleModule.congr
      (FGModuleCat.isoToLinearEquiv (P.primitiveProjectiveIso p).symm)

/-- For a non-simple selected projective, its socle is contained in its
module Jacobson radical. -/
theorem primitiveProjective_moduleSocle_le_jacobson
    (p : S.ProjectiveLabel)
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    moduleSocle Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p)) ≤
      Module.jacobson Aᵐᵒᵖ
        (RightModule.rightIdealFGObj (P.idempotent p)) :=
  moduleSocle_le_jacobson_of_simpleTop_of_not_simple
    (P.primitiveProjective_top_isSimpleModule p)
    (P.primitiveProjective_not_isSimpleModule p hnotSimple)

/-- The replacement quotient retains the simple top of the selected
primitive projective. -/
theorem primitiveProjectiveSocleQuotient_top_isSimpleModule
    (p : S.ProjectiveLabel)
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    IsSimpleModule Aᵐᵒᵖ
      (P.primitiveProjectiveSocleQuotientFGObj p ⧸
        Module.jacobson Aᵐᵒᵖ
          (P.primitiveProjectiveSocleQuotientFGObj p)) := by
  exact isSimpleModule_top_quotient_of_le_jacobson
    (moduleSocle Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p)))
    (P.primitiveProjective_moduleSocle_le_jacobson p hnotSimple)
    (P.primitiveProjective_top_isSimpleModule p)

/-- If the selected projective is non-simple, `e_p A / soc(e_p A)` is
indecomposable as an ambient right `A`-module. -/
theorem primitiveProjectiveSocleQuotient_isIndecomposableModule
    (p : S.ProjectiveLabel)
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Foundation.IsIndecomposableModule Aᵐᵒᵖ
      (P.primitiveProjectiveSocleQuotientFGObj p) :=
  IsUniserialModule.isIndecomposableModule_of_simpleTop
    (P.primitiveProjectiveSocleQuotient_top_isSimpleModule p hnotSimple)

/-- The replacement module, transported to a literal right module over
`A / soc(e_p A)`. -/
def primitiveProjectiveSocleQuotientAlgebraFGObj
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    RightModule.FinitelyGeneratedCategory
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective)) :=
  (RightModule.idealQuotientEquivalence (k := k)
    (P.primitiveProjectiveSocleIdeal p hpInjective)).functor.obj
      (P.primitiveProjectiveSocleQuotientObj p hpInjective)

/-- The transported replacement is projective over the literal socle
quotient algebra. -/
theorem primitiveProjectiveSocleQuotientAlgebraFGObj_projective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    Projective
      (P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let E := RightModule.idealQuotientEquivalence (k := k) I
  exact (E.map_projective_iff
    (P.primitiveProjectiveSocleQuotientObj p hpInjective)).2
      (P.primitiveProjectiveSocleQuotientObj_projective p hpInjective)

/-- If the selected projective is non-simple, the transported replacement
is indecomposable over the literal socle quotient algebra. -/
theorem primitiveProjectiveSocleQuotientAlgebraFGObj_isIndecomposableModule
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Foundation.IsIndecomposableModule
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ
      (P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  letI : IsNoetherianRing
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let E := RightModule.idealQuotientEquivalence (k := k) I
  let C := RightModule.IdealQuotientSubcategory I
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  have hambient : Indecomposable
      (P.primitiveProjectiveSocleQuotientFGObj p) :=
    (fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A)
      (P.primitiveProjectiveSocleQuotientFGObj p)).1
        (P.primitiveProjectiveSocleQuotient_isIndecomposableModule
          p hnotSimple)
  have hsub : Indecomposable
      (P.primitiveProjectiveSocleQuotientObj p hpInjective) :=
    (idealQuotientSubcategory_indecomposable_iff_ambient
      I (P.primitiveProjectiveSocleQuotientObj p hpInjective)).2
        hambient
  have hquot : Indecomposable
      (P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor
      (P.primitiveProjectiveSocleQuotientObj p hpInjective)).2 hsub
  exact (fgModule_isIndecomposableModule_iff_indecomposable
    (k := k) (A := RightModule.idealQuotientAlgebra I)
    (P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective)).2
      hquot

/-- The intrinsic quotient-skeleton label represented by
`e_p A / soc(e_p A)`. -/
def socleQuotientReplacementLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    S.IdealQuotientLabel
      (P.primitiveProjectiveSocleIdeal p hpInjective) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  letI : IsNoetherianRing
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact Classical.choose <|
    (S.idealQuotientAlmostSplitSkeleton I).complete
      (P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective)
      (P.primitiveProjectiveSocleQuotientAlgebraFGObj_isIndecomposableModule
        p hpInjective hnotSimple)

/-- The replacement module is isomorphic to its chosen intrinsic quotient
skeleton representative. -/
def primitiveProjectiveSocleQuotientReplacementIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective ≅
      S.idealQuotientFGObj
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientReplacementLabel p hpInjective hnotSimple) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  letI : IsNoetherianRing
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact Classical.choice <|
    Classical.choose_spec <|
      (S.idealQuotientAlmostSplitSkeleton I).complete
        (P.primitiveProjectiveSocleQuotientAlgebraFGObj p hpInjective)
        (P.primitiveProjectiveSocleQuotientAlgebraFGObj_isIndecomposableModule
          p hpInjective hnotSimple)

/-- The replacement quotient-skeleton representative is projective. -/
theorem socleQuotientReplacementLabel_projective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Projective
      (S.idealQuotientFGObj
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientReplacementLabel p hpInjective hnotSimple)) :=
  Projective.of_iso
    (P.primitiveProjectiveSocleQuotientReplacementIso
      p hpInjective hnotSimple)
    (P.primitiveProjectiveSocleQuotientAlgebraFGObj_projective
      p hpInjective)

/-- The replacement label is not the rejected projective label. -/
theorem socleQuotientReplacementLabel_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    (P.socleQuotientReplacementLabel p hpInjective hnotSimple).1 ≠
      p.label :=
  (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
    p hpInjective
    (P.socleQuotientReplacementLabel p hpInjective hnotSimple).1).1
      (P.socleQuotientReplacementLabel p hpInjective hnotSimple).2

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
