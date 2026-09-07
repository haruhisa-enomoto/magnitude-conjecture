import MagnitudeConjecture.Algebra.RightModuleAlmostSplitSocle
import MagnitudeConjecture.Algebra.RightModuleSimpleTop
import MagnitudeConjecture.Algebra.SocleModule
import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix

/-!
# Simple socles of indecomposable injective right modules

A nonzero simple submodule of an indecomposable injective module is an
essential submodule: injectivity and the local endomorphism ring turn its
inclusion into an injective envelope.  Consequently every simple submodule
lies in it, so it is the whole socle.
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

/-- The socle of a finitely generated right module, bundled again as a
finitely generated right module. -/
def moduleSocleFGObj (I : FGModuleCat.{u} Bᵐᵒᵖ) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  FGModuleCat.of Bᵐᵒᵖ (moduleSocle Bᵐᵒᵖ I)

/-- The canonical inclusion of the bundled socle. -/
def moduleSocleInclusion (I : FGModuleCat.{u} Bᵐᵒᵖ) :
    moduleSocleFGObj I ⟶ I :=
  FGModuleCat.ofHom (moduleSocle Bᵐᵒᵖ I).subtype

@[simp]
theorem moduleSocleInclusion_apply_val
    (I : FGModuleCat.{u} Bᵐᵒᵖ) (x : moduleSocleFGObj I) :
    (moduleSocleInclusion I).hom.hom x = x.1 :=
  rfl

instance moduleSocleInclusion_mono
    (I : FGModuleCat.{u} Bᵐᵒᵖ) : Mono (moduleSocleInclusion I) :=
  (IndecomposableSkeleton.fg_mono_iff_injective _).2
    (moduleSocle Bᵐᵒᵖ I).subtype_injective

include k in
/-- An indecomposable injective finitely generated right module has simple
socle. -/
theorem moduleSocle_isSimple_of_injective_indecomposable
    (I : FGModuleCat.{u} Bᵐᵒᵖ) [Injective I]
    (hI : Indecomposable I) :
    IsSimpleModule Bᵐᵒᵖ (moduleSocle Bᵐᵒᵖ I) := by
  letI : IsLocalRing (End I) :=
    fgEnd_isLocalRing_of_indecomposable (k := k) I hI
  have hInontrivial : Nontrivial I := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply hI.1
    rw [IsZero.iff_id_eq_zero]
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  letI : Nontrivial I := hInontrivial
  have hlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := B) I
  letI : IsArtinian Bᵐᵒᵖ I :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  obtain ⟨S, hSsimple, _hSle⟩ :=
    exists_simple_submodule_le (⊤ : Submodule Bᵐᵒᵖ I) top_ne_bot
  letI : IsSimpleModule Bᵐᵒᵖ S := hSsimple
  let Sfg : FGModuleCat.{u} Bᵐᵒᵖ := FGModuleCat.of Bᵐᵒᵖ S
  let s : Sfg ⟶ I := FGModuleCat.ofHom S.subtype
  letI : Simple Sfg := by
    exact RightModule.fgModule_simple_of_isSimpleModule Sfg
  have hs : s ≠ 0 := by
    intro hzero
    have hSne : S ≠ ⊥ :=
      (isSimpleModule_iff_isAtom.mp hSsimple).ne_bot
    apply hSne
    apply le_antisymm
    · intro x hx
      change x = 0
      let y : Sfg := ⟨x, hx⟩
      have hy := congrArg (fun f : Sfg ⟶ I ↦ f.hom.hom y) hzero
      exact hy
    · exact bot_le
  haveI : Mono s :=
    (IndecomposableSkeleton.fg_mono_iff_injective s).2 S.subtype_injective
  have hessential : IsEssentialMono s :=
    isEssentialMono_of_mono_nonzero_of_injective_local_end s hs
  have hsocleLe : moduleSocle Bᵐᵒᵖ I ≤ S := by
    unfold moduleSocle
    apply sSup_le
    intro T hTsimple
    letI : IsSimpleModule Bᵐᵒᵖ T := hTsimple
    let Tfg : FGModuleCat.{u} Bᵐᵒᵖ := FGModuleCat.of Bᵐᵒᵖ T
    let t : Tfg ⟶ I := FGModuleCat.ofHom T.subtype
    letI : Simple Tfg := by
      exact RightModule.fgModule_simple_of_isSimpleModule Tfg
    have ht : t ≠ 0 := by
      intro hzero
      have hTne : T ≠ ⊥ :=
        (isSimpleModule_iff_isAtom.mp hTsimple).ne_bot
      apply hTne
      apply le_antisymm
      · intro x hx
        change x = 0
        let y : Tfg := ⟨x, hx⟩
        have hy := congrArg (fun f : Tfg ⟶ I ↦ f.hom.hom y) hzero
        exact hy
      · exact bot_le
    haveI : Mono t :=
      (IndecomposableSkeleton.fg_mono_iff_injective t).2 T.subtype_injective
    obtain ⟨a, ha⟩ :=
      exists_factor_thru_of_isEssentialMono_of_simple s hessential t ht
    intro x hx
    let y : Tfg := ⟨x, hx⟩
    have hy := congrArg (fun f : Tfg ⟶ I ↦ f.hom.hom y) ha
    have hval : (a.hom.hom y).1 = x := hy
    exact hval ▸ (a.hom.hom y).2
  have hSleSocle : S ≤ moduleSocle Bᵐᵒᵖ I :=
    le_moduleSocle_of_simple S hSsimple
  rw [show moduleSocle Bᵐᵒᵖ I = S from
    le_antisymm hsocleLe hSleSocle]
  exact hSsimple

include k in
/-- For an indecomposable injective right module, its canonical socle
inclusion is essential. -/
theorem moduleSocleInclusion_isEssential_of_injective_indecomposable
    (I : FGModuleCat.{u} Bᵐᵒᵖ) [Injective I]
    (hI : Indecomposable I) :
    IsEssentialMono (moduleSocleInclusion I) := by
  letI : IsLocalRing (End I) :=
    fgEnd_isLocalRing_of_indecomposable (k := k) I hI
  have hsocleSimple :=
    moduleSocle_isSimple_of_injective_indecomposable (k := k) I hI
  have hs : moduleSocleInclusion I ≠ 0 := by
    letI : Nontrivial (moduleSocle Bᵐᵒᵖ I) := hsocleSimple.nontrivial
    obtain ⟨x, hx⟩ := exists_ne (0 : moduleSocle Bᵐᵒᵖ I)
    intro hzero
    apply hx
    apply Subtype.ext
    have hvalue := congrArg
      (fun f : moduleSocleFGObj I ⟶ I ↦ f.hom.hom x) hzero
    simpa using hvalue
  exact isEssentialMono_of_mono_nonzero_of_injective_local_end
    (moduleSocleInclusion I) hs

include k in
/-- Every map from an indecomposable injective module to a nonisomorphic
indecomposable module kills the injective module's socle. -/
theorem moduleSocleInclusion_comp_eq_zero_of_not_iso
    (I M : FGModuleCat.{u} Bᵐᵒᵖ) [Injective I]
    (hI : Indecomposable I) (hM : Indecomposable M)
    (hnoniso : ¬ Nonempty (I ≅ M)) (f : I ⟶ M) :
    moduleSocleInclusion I ≫ f = 0 := by
  have hessential : IsEssentialMono (moduleSocleInclusion I) :=
    moduleSocleInclusion_isEssential_of_injective_indecomposable
      (k := k) I hI
  have hsocleSimple : Simple (moduleSocleFGObj I) := by
    letI : IsSimpleModule Bᵐᵒᵖ (moduleSocleFGObj I) := by
      change IsSimpleModule Bᵐᵒᵖ (moduleSocle Bᵐᵒᵖ I)
      exact moduleSocle_isSimple_of_injective_indecomposable
        (k := k) I hI
    exact RightModule.fgModule_simple_of_isSimpleModule _
  by_contra hzero
  letI : Simple (moduleSocleFGObj I) := hsocleSimple
  haveI : Mono (moduleSocleInclusion I ≫ f) :=
    mono_of_nonzero_from_simple hzero
  haveI : Mono f := hessential.2 f inferInstance
  letI : IsSplitMono f := IsSplitMono.mk'
    { retraction := Injective.factorThru (𝟙 I) f
      id := Injective.comp_factorThru (𝟙 I) f }
  letI : IsIso f :=
    MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
      hM f hI.1
  exact hnoniso ⟨asIso f⟩

namespace RightModule

/-- The Nakayama image of an indecomposable finite projective right module
is indecomposable. -/
theorem projectiveNakayamaFGObj_indecomposable
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (hP : Indecomposable P) :
    Indecomposable (projectiveNakayamaFGObj (k := k) P) := by
  letI : IsLocalRing (End P) :=
    fgEnd_isLocalRing_of_indecomposable (k := k) P hP
  letI : IsLocalRing (End (projectiveNakayamaFGObj (k := k) P)) :=
    RingEquiv.isLocalRing_noncomm
      (projectiveNakayamaEndRingEquiv (k := k) P)
  exact CategoryTheory.indecomposable_of_local_end _

/-- The Nakayama image of an indecomposable finite projective right module
has simple socle. -/
theorem projectiveNakayamaFGObj_moduleSocle_isSimple
    (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
    (hP : Indecomposable P) :
    IsSimpleModule Bᵐᵒᵖ
      (moduleSocle Bᵐᵒᵖ (projectiveNakayamaFGObj (k := k) P)) := by
  letI : Injective (projectiveNakayamaFGObj (k := k) P) :=
    projectiveNakayamaFGObj_injective (k := k) P
  exact moduleSocle_isSimple_of_injective_indecomposable
    (k := k) _ (projectiveNakayamaFGObj_indecomposable (k := k) P hP)

end RightModule

end MagnitudeConjecture
