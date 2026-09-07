import MagnitudeConjecture.Algebra.RightModuleCoherentCoduality
import MagnitudeConjecture.Algebra.RightModuleProjectiveStableCovariantUniserial

/-!
# The representable resolution of a covariant defect

For a short exact sequence `0 → A → B → C → 0`, the covariant
representables form the exact sequence

`0 → Hom(C,-) → Hom(B,-) → Hom(A,-) → G → 0`.

This file splits that resolution into the two short exact sequences used to
compute the reverse coherent dual of `G`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The three covariant representables induced by a module short complex,
in their contravariant order. -/
def finiteCovariantRepresentableComplex
    (K : ShortComplex (FG (A := A))) :
    ShortComplex S.FiniteCovariantFunctor :=
  ShortComplex.mk
    (S.finiteRestrictedCovariantRepresentableMap K.g)
    (S.finiteRestrictedCovariantRepresentableMap K.f) (by
      rw [← S.finiteRestrictedCovariantRepresentableMap_comp,
        K.zero, S.finiteRestrictedCovariantRepresentableMap_zero])

/-- A covariant representable map induced by an epimorphism is monic. -/
theorem finiteRestrictedCovariantRepresentableMap_mono_of_epi
    {X Y : FG (A := A)} (f : X ⟶ Y) [Epi f] :
    Mono (S.finiteRestrictedCovariantRepresentableMap f) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategory) k).ι
  haveI hmonoApp (Z : S.IndecCategory) : Mono
      ((I.map (J.map
        (S.finiteRestrictedCovariantRepresentableMap f))).app Z) := by
    rw [ModuleCat.mono_iff_injective]
    intro p q hpq
    change f.hom ≫ p = f.hom ≫ q at hpq
    have hpq' :
        f ≫ (ObjectProperty.homMk p : Y ⟶ S.fgObj Z) =
          f ≫ (ObjectProperty.homMk q : Y ⟶ S.fgObj Z) := by
      apply ObjectProperty.hom_ext
      exact hpq
    have := (cancel_epi f).1 hpq'
    exact congrArg (fun t : Y ⟶ S.fgObj Z ↦ t.hom) this
  haveI : Mono (I.map (J.map
      (S.finiteRestrictedCovariantRepresentableMap f))) :=
    NatTrans.mono_of_mono_app _
  haveI : Mono (J.map
      (S.finiteRestrictedCovariantRepresentableMap f)) :=
    I.mono_of_mono_map inferInstance
  exact J.mono_of_mono_map inferInstance

/-- Covariant Yoneda carries a short exact module sequence to an exact
sequence at the middle representable. -/
theorem finiteCovariantRepresentableComplex_exact
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    (S.finiteCovariantRepresentableComplex K).Exact := by
  letI : Epi K.g := hK.epi_g
  let T := S.finiteCovariantRepresentableComplex K
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategory) k).ι
  apply J.reflects_exact_of_faithful T
  apply I.reflects_exact_of_faithful (T.map J)
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  change LinearMap.range
      ((S.finiteRestrictedCovariantRepresentableMap K.g).hom.hom.app X).hom =
    LinearMap.ker
      ((S.finiteRestrictedCovariantRepresentableMap K.f).hom.hom.app X).hom
  change LinearMap.range
      (CategoryTheory.Linear.leftComp k (S.inclusion.obj X) K.g.hom) =
    LinearMap.ker
      (CategoryTheory.Linear.leftComp k (S.inclusion.obj X) K.f.hom)
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change K.f.hom ≫ (K.g.hom ≫ a) = 0
    have hzero := congrArg
      (fun t : K.X₁ ⟶ K.X₃ ↦ t.hom) K.zero
    change K.f.hom ≫ K.g.hom = 0 at hzero
    rw [← Category.assoc, hzero, zero_comp]
  · intro hq
    rw [LinearMap.mem_ker] at hq
    change K.f.hom ≫ q = 0 at hq
    let qfg : K.X₂ ⟶ S.fgObj X := ObjectProperty.homMk q
    have qfgzero : K.f ≫ qfg = 0 := by
      apply ObjectProperty.hom_ext
      exact hq
    obtain ⟨a, ha⟩ := hK.exact.desc' qfg qfgzero
    refine ⟨a.hom, ?_⟩
    exact congrArg (fun t : K.X₂ ⟶ S.fgObj X ↦ t.hom) ha

/-- The first syzygy in the projective resolution of a covariant defect. -/
abbrev finiteCovariantDefectSyzygy
    (K : ShortComplex (FG (A := A))) :=
  cokernel (S.finiteRestrictedCovariantRepresentableMap K.g)

/-- Exactness lets the second covariant-representable map descend through
the first cokernel. -/
def finiteCovariantDefectSyzygyι
    (K : ShortComplex (FG (A := A))) :
    S.finiteCovariantDefectSyzygy K ⟶
      S.finiteRestrictedCovariantRepresentable K.X₁ :=
  cokernel.desc (S.finiteRestrictedCovariantRepresentableMap K.g)
    (S.finiteRestrictedCovariantRepresentableMap K.f)
    (S.finiteCovariantRepresentableComplex K).zero

@[reassoc (attr := simp)]
theorem finiteCovariantDefectSyzygyπ_comp_ι
    (K : ShortComplex (FG (A := A))) :
    cokernel.π (S.finiteRestrictedCovariantRepresentableMap K.g) ≫
        S.finiteCovariantDefectSyzygyι K =
      S.finiteRestrictedCovariantRepresentableMap K.f := by
  exact cokernel.π_desc _ _ _

/-- For a short exact module sequence, the descended map from the first
syzygy into the last covariant representable is monic. -/
theorem finiteCovariantDefectSyzygyι_mono
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    Mono (S.finiteCovariantDefectSyzygyι K) := by
  exact (S.finiteCovariantRepresentableComplex_exact hK).mono_cokernelDesc

/-- The left half of the covariant representable resolution. -/
def finiteCovariantDefectLeftShortComplex
    (K : ShortComplex (FG (A := A))) :
    ShortComplex S.FiniteCovariantFunctor :=
  ShortComplex.mk
    (S.finiteRestrictedCovariantRepresentableMap K.g)
    (cokernel.π (S.finiteRestrictedCovariantRepresentableMap K.g))
    (cokernel.condition _)

/-- The left half is short exact. -/
theorem finiteCovariantDefectLeftShortComplex_shortExact
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    (S.finiteCovariantDefectLeftShortComplex K).ShortExact := by
  letI : Epi K.g := hK.epi_g
  letI : Mono (S.finiteRestrictedCovariantRepresentableMap K.g) :=
    S.finiteRestrictedCovariantRepresentableMap_mono_of_epi K.g
  have hmono : Mono (S.finiteCovariantDefectLeftShortComplex K).f := by
    change Mono (S.finiteRestrictedCovariantRepresentableMap K.g)
    infer_instance
  have hepi : Epi (S.finiteCovariantDefectLeftShortComplex K).g := by
    change Epi
      (cokernel.π (S.finiteRestrictedCovariantRepresentableMap K.g))
    infer_instance
  exact
    { exact := ShortComplex.exact_cokernel _
      mono_f := hmono
      epi_g := hepi }

/-- The right half of the covariant representable resolution. -/
def finiteCovariantDefectRightShortComplex
    (K : ShortComplex (FG (A := A))) :
    ShortComplex S.FiniteCovariantFunctor :=
  ShortComplex.mk
    (S.finiteCovariantDefectSyzygyι K)
    (cokernel.π (S.finiteRestrictedCovariantRepresentableMap K.f)) (by
      apply (cancel_epi
        (cokernel.π
          (S.finiteRestrictedCovariantRepresentableMap K.g))).1
      rw [← Category.assoc,
        S.finiteCovariantDefectSyzygyπ_comp_ι,
        cokernel.condition, comp_zero])

/-- The right half is short exact. -/
theorem finiteCovariantDefectRightShortComplex_shortExact
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    (S.finiteCovariantDefectRightShortComplex K).ShortExact := by
  letI : Mono (S.finiteCovariantDefectSyzygyι K) :=
    S.finiteCovariantDefectSyzygyι_mono hK
  let T := S.finiteCovariantDefectRightShortComplex K
  have hCokernel : IsColimit (CokernelCofork.ofπ T.g T.zero) :=
    isCokernelOfComp
      (cokernel.π (S.finiteRestrictedCovariantRepresentableMap K.g))
      (S.finiteRestrictedCovariantRepresentableMap K.f)
      (cokernelIsCokernel
        (S.finiteRestrictedCovariantRepresentableMap K.f))
      T.zero
      (S.finiteCovariantDefectSyzygyπ_comp_ι K)
  have hExactEpi : T.Exact ∧ Epi T.g :=
    T.exact_and_epi_g_iff_g_is_cokernel.2 ⟨hCokernel⟩
  have hmono : Mono T.f := by
    change Mono (S.finiteCovariantDefectSyzygyι K)
    infer_instance
  exact
    { exact := hExactEpi.1
      mono_f := hmono
      epi_g := hExactEpi.2 }

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
