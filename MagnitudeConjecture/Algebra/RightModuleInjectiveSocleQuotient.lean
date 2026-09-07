import MagnitudeConjecture.Algebra.CoordinateThinModule
import MagnitudeConjecture.Algebra.RightModuleInjectiveSocle

/-!
# The left almost-split boundary of an injective module

For an indecomposable injective finite right module `I`, the canonical map
`I → I / soc(I)` is left almost split and left minimal.  The factorization
argument uses essentiality of the simple socle: any map out of `I` which does
not split as a monomorphism must kill the socle and hence descend through the
quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

/-- The quotient of a finite right module by its module socle. -/
def moduleSocleQuotientFGObj (I : FGModuleCat.{u} Bᵐᵒᵖ) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  RightModule.quotientFGObj I (moduleSocle Bᵐᵒᵖ I)

/-- The canonical projection `I → I / soc(I)`. -/
def moduleSocleQuotientProjection (I : FGModuleCat.{u} Bᵐᵒᵖ) :
    I ⟶ moduleSocleQuotientFGObj I := by
  letI : Module.Finite Bᵐᵒᵖ I := I.property
  exact FGModuleCat.ofHom <|
    RightModule.quotientFGMkQ I (moduleSocle Bᵐᵒᵖ I)

omit [IsNoetherianRing Bᵐᵒᵖ] in
/-- The canonical socle-quotient projection is epic. -/
theorem moduleSocleQuotientProjection_epi
    (I : FGModuleCat.{u} Bᵐᵒᵖ) :
    Epi (moduleSocleQuotientProjection I) := by
  apply
    (IndecomposableSkeleton.fg_epi_iff_surjective
      (moduleSocleQuotientProjection I)).2
  exact RightModule.quotientFGMkQ_surjective I (moduleSocle Bᵐᵒᵖ I)

include k in
/-- For an indecomposable injective module, the canonical quotient by its
socle is left almost split. -/
theorem moduleSocleQuotientProjection_isLeftAlmostSplit
    (I : FGModuleCat.{u} Bᵐᵒᵖ) [Injective I]
    (hI : Indecomposable I) :
    IsLeftAlmostSplit (moduleSocleQuotientProjection I) := by
  let L := moduleSocle Bᵐᵒᵖ I
  let Q := moduleSocleQuotientFGObj I
  let q : I ⟶ Q := moduleSocleQuotientProjection I
  have hsocle : IsSimpleModule Bᵐᵒᵖ L :=
    moduleSocle_isSimple_of_injective_indecomposable (k := k) I hI
  have hlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := B) I
  letI : IsArtinian Bᵐᵒᵖ I :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  constructor
  · intro hsplit
    letI : IsSplitMono q := hsplit
    have hinjective : Function.Injective q.hom.hom :=
      (IndecomposableSkeleton.fg_mono_iff_injective q).1 inferInstance
    letI : Nontrivial L := hsocle.nontrivial
    obtain ⟨z, hz⟩ := exists_ne (0 : L)
    apply hz
    apply Subtype.ext
    apply hinjective
    have hzq : q.hom.hom z.1 = 0 := by
      change L.mkQ z.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact z.2
    exact hzq.trans q.hom.hom.map_zero.symm
  · intro X f hf
    have hnotInjective : ¬ Function.Injective f.hom.hom := by
      intro hinjective
      apply hf
      letI : Mono f :=
        (IndecomposableSkeleton.fg_mono_iff_injective f).2 hinjective
      exact IsSplitMono.mk'
        { retraction := Injective.factorThru (𝟙 I) f
          id := Injective.comp_factorThru (𝟙 I) f }
    have hkill : L ≤ f.hom.hom.ker :=
      moduleSocle_le_ker_of_not_injective hsocle f.hom.hom hnotInjective
    let fbar : Q ⟶ X := FGModuleCat.ofHom <|
      RightModule.quotientFGLift I X L f.hom.hom hkill
    refine ⟨fbar, ?_⟩
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact RightModule.quotientFGLift_apply_mkQ
      I X L f.hom.hom hkill x

omit [IsNoetherianRing Bᵐᵒᵖ] in
/-- The canonical socle-quotient projection is left minimal. -/
theorem moduleSocleQuotientProjection_isLeftMinimal
    (I : FGModuleCat.{u} Bᵐᵒᵖ) :
    IsLeftMinimal (moduleSocleQuotientProjection I) := by
  let q := moduleSocleQuotientProjection I
  letI : Epi q := moduleSocleQuotientProjection_epi I
  intro e he
  have heq : e = 𝟙 _ := by
    apply (cancel_epi q).1
    simpa using he
  subst e
  infer_instance

include k in
/-- The Jacobson radical of a non-simple indecomposable injective module
with simple top is indecomposable. -/
theorem jacobson_isIndecomposableModule_of_injective
    (I : FGModuleCat.{u} Bᵐᵒᵖ) [Injective I]
    (hI : Indecomposable I)
    (hTop : IsSimpleModule Bᵐᵒᵖ
      (I ⧸ Module.jacobson Bᵐᵒᵖ I))
    (hnotSimple : ¬ IsSimpleModule Bᵐᵒᵖ I) :
    Foundation.IsIndecomposableModule Bᵐᵒᵖ
      (Module.jacobson Bᵐᵒᵖ I) := by
  let J := Module.jacobson Bᵐᵒᵖ I
  have hsocle : IsSimpleModule Bᵐᵒᵖ (moduleSocle Bᵐᵒᵖ I) :=
    moduleSocle_isSimple_of_injective_indecomposable (k := k) I hI
  have hsocleLe : moduleSocle Bᵐᵒᵖ I ≤ J :=
    moduleSocle_le_jacobson_of_simpleTop_of_not_simple hTop hnotSimple
  have hJne : J ≠ ⊥ := by
    intro hJ
    have hsocleBot : moduleSocle Bᵐᵒᵖ I = ⊥ :=
      le_antisymm (hJ ▸ hsocleLe) bot_le
    exact (isSimpleModule_iff_isAtom.mp hsocle).ne_bot hsocleBot
  letI : Nontrivial J := Submodule.nontrivial_iff_ne_bot.mpr hJne
  have hlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := B) I
  letI : IsArtinian Bᵐᵒᵖ I :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  have hJsocle : IsSimpleModule Bᵐᵒᵖ (moduleSocle Bᵐᵒᵖ J) :=
    moduleSocle_isSimple_of_injective J.subtype J.subtype_injective hsocle
  exact isIndecomposableModule_of_simpleSocle hJsocle

end MagnitudeConjecture
