import MagnitudeConjecture.Algebra.RightModuleProjectivePresentationExt
import MagnitudeConjecture.Algebra.RightModuleStableRepresentableSocleInduction

/-!
# The two defects of a short exact right-module presentation

For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, Auslander's coherent
duality exchanges the contravariant defect

`coker(Hom(-, B) ⟶ Hom(-, C))`

with the covariant defect

`coker(Hom(B, -) ⟶ Hom(A, -))`.

This file fixes those two literal cokernel objects on the finite
indecomposable skeleton.  For a projective cover it identifies them with
`Hom̲(-, C)` and `Ext¹(C, -)`, respectively.  The later coherent-duality
file will prove that the two exact-presentation constructions form inverse
contravariant equivalences on the corresponding defect subcategories.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The contravariant defect of a composable two-term module complex.  When
the complex is short exact, this is the object occurring on the
contravariant side of Auslander's exact-presentation duality. -/
def finiteContravariantDefect
    (K : ShortComplex (FG (A := A))) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k :=
  cokernel (S.finiteRestrictedContravariantRepresentableMap K.g)

/-- The covariant defect of a composable two-term module complex.  When the
complex is short exact, this is the coherent dual of
`finiteContravariantDefect`. -/
def finiteCovariantDefect
    (K : ShortComplex (FG (A := A))) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  cokernel (S.finiteRestrictedCovariantRepresentableMap K.f)

/-- The three representable terms induced by a module short complex. -/
def finiteContravariantRepresentableComplex
    (K : ShortComplex (FG (A := A))) :
    ShortComplex
      (CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
  ShortComplex.mk
    (S.finiteRestrictedContravariantRepresentableMap K.f)
    (S.finiteRestrictedContravariantRepresentableMap K.g) (by
      rw [← S.finiteRestrictedContravariantRepresentableMap_comp,
        K.zero, S.finiteRestrictedContravariantRepresentableMap_zero])

/-- Restricted contravariant Yoneda preserves monomorphisms. -/
theorem finiteRestrictedContravariantRepresentableMap_mono
    {X Y : FG (A := A)} (f : X ⟶ Y) [Mono f] :
    Mono (S.finiteRestrictedContravariantRepresentableMap f) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  haveI hmonoApp (Z : S.IndecCategoryᵒᵖ) : Mono
      ((I.map (J.map
        (S.finiteRestrictedContravariantRepresentableMap f))).app Z) := by
    rw [ModuleCat.mono_iff_injective]
    intro p q hpq
    change p ≫ f.hom = q ≫ f.hom at hpq
    have hpq' :
        (ObjectProperty.homMk p : S.fgObj Z.unop ⟶ X) ≫ f =
          (ObjectProperty.homMk q : S.fgObj Z.unop ⟶ X) ≫ f := by
      apply ObjectProperty.hom_ext
      exact hpq
    have := (cancel_mono f).1 hpq'
    exact congrArg
      (fun t : S.fgObj Z.unop ⟶ X ↦ t.hom) this
  haveI : Mono (I.map (J.map
      (S.finiteRestrictedContravariantRepresentableMap f))) :=
    NatTrans.mono_of_mono_app _
  haveI : Mono (J.map
      (S.finiteRestrictedContravariantRepresentableMap f)) :=
    I.mono_of_mono_map inferInstance
  exact J.mono_of_mono_map inferInstance

/-- Restricted contravariant Yoneda carries a short exact module sequence to
an exact sequence at its middle representable term. -/
theorem finiteContravariantRepresentableComplex_exact
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    (S.finiteContravariantRepresentableComplex K).Exact := by
  letI : Mono K.f := hK.mono_f
  let T := S.finiteContravariantRepresentableComplex K
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  apply J.reflects_exact_of_faithful T
  apply I.reflects_exact_of_faithful (T.map J)
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  change LinearMap.range
      ((S.finiteRestrictedContravariantRepresentableMap K.f).hom.hom.app X).hom =
    LinearMap.ker
      ((S.finiteRestrictedContravariantRepresentableMap K.g).hom.hom.app X).hom
  change LinearMap.range
      (CategoryTheory.Linear.rightComp k (S.inclusion.obj X.unop) K.f.hom) =
    LinearMap.ker
      (CategoryTheory.Linear.rightComp k (S.inclusion.obj X.unop) K.g.hom)
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change (a ≫ K.f.hom) ≫ K.g.hom = 0
    have hzero := congrArg
      (fun t : K.X₁ ⟶ K.X₃ ↦ t.hom) K.zero
    change K.f.hom ≫ K.g.hom = 0 at hzero
    rw [Category.assoc, hzero, comp_zero]
  · intro hq
    rw [LinearMap.mem_ker] at hq
    change q ≫ K.g.hom = 0 at hq
    let qfg : S.fgObj X.unop ⟶ K.X₂ := ObjectProperty.homMk q
    have qfgzero : qfg ≫ K.g = 0 := by
      apply ObjectProperty.hom_ext
      exact hq
    obtain ⟨a, ha⟩ := hK.exact.lift' qfg qfgzero
    refine ⟨a.hom, ?_⟩
    exact congrArg (fun t : S.fgObj X.unop ⟶ K.X₂ ↦ t.hom) ha

/-- The first syzygy in the representable resolution of a contravariant
defect. -/
abbrev finiteContravariantDefectSyzygy
    (K : ShortComplex (FG (A := A))) :=
  cokernel (S.finiteRestrictedContravariantRepresentableMap K.f)

/-- Exactness lets the second representable map descend through the first
cokernel. -/
def finiteContravariantDefectSyzygyι
    (K : ShortComplex (FG (A := A))) :
    S.finiteContravariantDefectSyzygy K ⟶
      S.finiteRestrictedContravariantRepresentable K.X₃ :=
  cokernel.desc (S.finiteRestrictedContravariantRepresentableMap K.f)
    (S.finiteRestrictedContravariantRepresentableMap K.g)
    (S.finiteContravariantRepresentableComplex K).zero

@[reassoc (attr := simp)]
theorem finiteContravariantDefectSyzygyπ_comp_ι
    (K : ShortComplex (FG (A := A))) :
    cokernel.π (S.finiteRestrictedContravariantRepresentableMap K.f) ≫
        S.finiteContravariantDefectSyzygyι K =
      S.finiteRestrictedContravariantRepresentableMap K.g := by
  exact cokernel.π_desc _ _ _

/-- For a short exact module sequence, the descended map from the first
syzygy into the third representable is monic. -/
theorem finiteContravariantDefectSyzygyι_mono
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    Mono (S.finiteContravariantDefectSyzygyι K) := by
  exact (S.finiteContravariantRepresentableComplex_exact hK).mono_cokernelDesc

/-- The left short exact sequence obtained by splitting the four-term
representable resolution at its first syzygy. -/
def finiteContravariantDefectLeftShortComplex
    (K : ShortComplex (FG (A := A))) :
    ShortComplex
      (CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
  ShortComplex.mk
    (S.finiteRestrictedContravariantRepresentableMap K.f)
    (cokernel.π (S.finiteRestrictedContravariantRepresentableMap K.f))
    (cokernel.condition _)

/-- The left syzygy sequence is short exact when the module sequence is. -/
theorem finiteContravariantDefectLeftShortComplex_shortExact
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    (S.finiteContravariantDefectLeftShortComplex K).ShortExact := by
  letI : Mono K.f := hK.mono_f
  letI : Mono (S.finiteRestrictedContravariantRepresentableMap K.f) :=
    S.finiteRestrictedContravariantRepresentableMap_mono K.f
  have hmono : Mono (S.finiteContravariantDefectLeftShortComplex K).f := by
    change Mono (S.finiteRestrictedContravariantRepresentableMap K.f)
    infer_instance
  have hepi : Epi (S.finiteContravariantDefectLeftShortComplex K).g := by
    change Epi
      (cokernel.π (S.finiteRestrictedContravariantRepresentableMap K.f))
    infer_instance
  exact
    { exact := ShortComplex.exact_cokernel _
      mono_f := hmono
      epi_g := hepi }

/-- The right short complex from the first syzygy to the contravariant
defect. -/
def finiteContravariantDefectRightShortComplex
    (K : ShortComplex (FG (A := A))) :
    ShortComplex
      (CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
  ShortComplex.mk
    (S.finiteContravariantDefectSyzygyι K)
    (cokernel.π (S.finiteRestrictedContravariantRepresentableMap K.g)) (by
      apply (cancel_epi
        (cokernel.π
          (S.finiteRestrictedContravariantRepresentableMap K.f))).1
      rw [← Category.assoc,
        S.finiteContravariantDefectSyzygyπ_comp_ι,
        cokernel.condition, comp_zero])

/-- The right syzygy sequence is short exact when the module sequence is. -/
theorem finiteContravariantDefectRightShortComplex_shortExact
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    (S.finiteContravariantDefectRightShortComplex K).ShortExact := by
  letI : Mono (S.finiteContravariantDefectSyzygyι K) :=
    S.finiteContravariantDefectSyzygyι_mono hK
  let T := S.finiteContravariantDefectRightShortComplex K
  have hCokernel : IsColimit (CokernelCofork.ofπ T.g T.zero) :=
    isCokernelOfComp
      (cokernel.π (S.finiteRestrictedContravariantRepresentableMap K.f))
      (S.finiteRestrictedContravariantRepresentableMap K.g)
      (cokernelIsCokernel
        (S.finiteRestrictedContravariantRepresentableMap K.g))
      T.zero
      (S.finiteContravariantDefectSyzygyπ_comp_ι K)
  have hExactEpi : T.Exact ∧ Epi T.g :=
    T.exact_and_epi_g_iff_g_is_cokernel.2 ⟨hCokernel⟩
  have hmono : Mono T.f := by
    change Mono (S.finiteContravariantDefectSyzygyι K)
    infer_instance
  exact
    { exact := hExactEpi.1
      mono_f := hmono
      epi_g := hExactEpi.2 }

/-- The exact-presentation condition on the contravariant side of Auslander's
coherent duality.  An object has this property when it is isomorphic to the
contravariant defect of some short exact sequence of finitely generated right
modules. -/
def IsFiniteContravariantDefect :
    ObjectProperty
      (CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
  fun F ↦ ∃ K : ShortComplex (FG (A := A)),
    K.ShortExact ∧ Nonempty (S.finiteContravariantDefect K ≅ F)

/-- The full subcategory of finite contravariant functors admitting an exact
representable presentation. -/
abbrev FiniteContravariantDefectCategory :=
  S.IsFiniteContravariantDefect.FullSubcategory

/-- The exact-presentation condition on the covariant side of Auslander's
coherent duality. -/
def IsFiniteCovariantDefect :
    ObjectProperty
      (CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k) :=
  fun F ↦ ∃ K : ShortComplex (FG (A := A)),
    K.ShortExact ∧ Nonempty (S.finiteCovariantDefect K ≅ F)

/-- The full subcategory of finite covariant functors admitting an exact
representable presentation. -/
abbrev FiniteCovariantDefectCategory :=
  S.IsFiniteCovariantDefect.FullSubcategory

/-- For a projective cover, the contravariant defect is the projective-stable
representable of the target. -/
def finiteContravariantDefectIsoProjectiveStable
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.finiteContravariantDefect (projectiveCoverShortComplex P) ≅
      S.finiteProjectiveStableContravariantRepresentable X := by
  let hProjective : Projective P.p.obj :=
    (FGExtRealization.inclusion (R := Aᵐᵒᵖ)).projective_obj_of_projective
      inferInstance
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel
      (S.finiteRestrictedContravariantRepresentableMap P.f))
    (S.finiteRestrictedMap_stableQuotient_isCokernel
      P.f hProjective)

/-- Uniseriality of the contravariant defect of a projective cover is
equivalent to uniseriality of its stable representable. -/
theorem finiteContravariantDefect_isUniserial_iff_projectiveStable
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    IsUniserialObject
        (S.finiteContravariantDefect (projectiveCoverShortComplex P)) ↔
      IsUniserialObject
        (S.finiteProjectiveStableContravariantRepresentable X) := by
  constructor
  · intro h
    exact h.congr (S.finiteContravariantDefectIsoProjectiveStable P)
  · intro h
    exact h.congr
      (S.finiteContravariantDefectIsoProjectiveStable P).symm

/-- A projective-stable contravariant representable, equipped with the exact
presentation supplied by a projective cover. -/
def finiteProjectiveStableContravariantDefectObj
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.FiniteContravariantDefectCategory :=
  ⟨S.finiteProjectiveStableContravariantRepresentable X,
    ⟨projectiveCoverShortComplex P,
      (by
        dsimp [projectiveCoverShortComplex]
        exact
          { exact := ShortComplex.exact_kernel P.f
            mono_f := inferInstance
            epi_g := inferInstance }),
      ⟨S.finiteContravariantDefectIsoProjectiveStable P⟩⟩⟩

variable [HasExt.{u} (FG (A := A))]

/-- For a projective cover, the covariant defect is the restricted
degree-one Ext functor of its target. -/
def finiteCovariantDefectIsoRestrictedExtOne
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.finiteCovariantDefect (projectiveCoverShortComplex P) ≅
      S.finiteRestrictedExtOne P := by
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel
      (S.finiteRestrictedCovariantRepresentableMap (kernel.ι P.f)))
    (S.finiteRestrictedCovariantConnecting_isCokernel P)

/-- Uniseriality of the covariant defect of a projective cover is equivalent
to uniseriality of its restricted degree-one Ext functor. -/
theorem finiteCovariantDefect_isUniserial_iff_restrictedExtOne
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    IsUniserialObject
        (S.finiteCovariantDefect (projectiveCoverShortComplex P)) ↔
      IsUniserialObject (S.finiteRestrictedExtOne P) := by
  constructor
  · intro h
    exact h.congr (S.finiteCovariantDefectIsoRestrictedExtOne P)
  · intro h
    exact h.congr
      (S.finiteCovariantDefectIsoRestrictedExtOne P).symm

/-- The restricted degree-one Ext functor, equipped with the exact
presentation supplied by a projective cover. -/
def finiteRestrictedExtOneCovariantDefectObj
    {X : FG (A := A)} (P : MinimalProjectivePresentation X) :
    S.FiniteCovariantDefectCategory :=
  ⟨S.finiteRestrictedExtOne P,
    ⟨projectiveCoverShortComplex P,
      projectiveCoverShortComplex_shortExact P,
      ⟨S.finiteCovariantDefectIsoRestrictedExtOne P⟩⟩⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
