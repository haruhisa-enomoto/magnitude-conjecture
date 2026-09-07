import MagnitudeConjecture.Algebra.RightModuleIrreducibleProjectiveQuotient
import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.Algebra.RightModuleStableRepresentable
import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.AlmostSplitPullback
import MagnitudeConjecture.CategoryTheory.AlmostSplitSummandIrreducible
import MagnitudeConjecture.CategoryTheory.SimpleProjectiveTop
import MagnitudeConjecture.CategoryTheory.SplitEpiCokernelKernel
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import QuotientSubmoduleEquidistribution.CategoryTheory.SplitMorphismComplement

/-!
# Initial stable-socle map from an irreducible projective submodule

An irreducible inclusion `U ⟶ P` into an indecomposable projective extends
through the minimal left almost-split map starting at `U`.  The resulting
split epimorphism from the almost-split middle onto `P` induces a map from
the opposite endpoint to `P/U`.  This is the distinguished nonzero stable
map which initializes Auslander--Reiten Corollary 3.8.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A nonzero stable map into the quotient by an irreducible projective
submodule contains the projective quotient map as a factor.  This is the
stable-functor form of Auslander--Reiten IV, Proposition 2.7. -/
theorem irreducibleIntoProjective_cokernel_factorization_of_stable_nonzero
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (i : S.IndecCategory)
    (h : S.fgObj i ⟶ cokernel g)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    ∃ r : S.fgObj p ⟶ S.fgObj i, r ≫ h = cokernel.π g := by
  apply S.irreducibleIntoProjective_cokernel_factorization p g hg hp h
  rintro ⟨l, hlift⟩
  apply hstable
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  have hpObj : Projective (S.fgObj p).obj := inferInstance
  rw [← hlift, finiteRestrictedToProjectiveStableMap,
    S.finiteRestrictedContravariantRepresentableMap_comp, Category.assoc,
    S.finiteRestrictedMap_comp_stableQuotient_eq_zero (cokernel.π g) hpObj,
    comp_zero]

/-- Consequently, a nonzero stable map into this quotient is epic. -/
theorem irreducibleIntoProjective_cokernel_epi_of_stable_nonzero
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (i : S.IndecCategory)
    (h : S.fgObj i ⟶ cokernel g)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    Epi h := by
  obtain ⟨r, hr⟩ := S.irreducibleIntoProjective_cokernel_factorization_of_stable_nonzero
    p g hg hp i h hstable
  exact epi_of_epi_fac hr

/-- The Proposition 2.7 factorization is invariant under the chosen
indecomposable coordinates for the cokernel. -/
theorem irreducibleIntoProjective_selectedQuotient_factorization_of_stable_nonzero
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (i : S.IndecCategory)
    (h : S.fgObj i ⟶ S.fgObj
      (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    ∃ r : S.fgObj p ⟶ S.fgObj i,
      r ≫ h = S.irreducibleIntoProjective_quotientMap p g hg hp := by
  let e := S.irreducibleIntoProjective_cokernelIso p g hg hp
  let hRaw : S.fgObj i ⟶ cokernel g := h ≫ e.inv
  have hnot : ¬ ∃ l : S.fgObj i ⟶ S.fgObj p,
      l ≫ cokernel.π g = hRaw := by
    rintro ⟨l, hl⟩
    apply hstable
    rw [finiteRestrictedToProjectiveStableMap]
    have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
      MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
    letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
    letI : Projective (S.fgObj p).obj := inferInstance
    have hl' : l ≫ S.irreducibleIntoProjective_quotientMap p g hg hp = h := by
      dsimp only [irreducibleIntoProjective_quotientMap]
      rw [← Category.assoc, hl]
      dsimp only [hRaw, e]
      simp
    rw [← hl', S.finiteRestrictedContravariantRepresentableMap_comp,
      Category.assoc,
      S.finiteRestrictedMap_comp_stableQuotient_eq_zero
        (S.irreducibleIntoProjective_quotientMap p g hg hp) inferInstance,
      comp_zero]
  obtain ⟨r, hr⟩ := S.irreducibleIntoProjective_cokernel_factorization
    p g hg hp hRaw hnot
  refine ⟨r, ?_⟩
  dsimp only [hRaw, e] at hr
  rw [← cancel_mono (S.irreducibleIntoProjective_cokernelIso p g hg hp).inv]
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    irreducibleIntoProjective_quotientMap] using hr


/-! A useful functor-category consequence of the Proposition 2.7 factor:
the factor from the projective target annihilates every simple generator of a
stable subfunctor. -/

theorem irreducibleIntoProjective_factor_comp_simpleGenerator_eq_zero
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (i : S.IndecCategory)
    (h : S.fgObj i ⟶ cokernel g)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable
      (cokernel g)) [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h)
    (r : S.fgObj p ⟶ S.fgObj i)
    (hr : r ≫ h = cokernel.π g) :
    S.finiteRestrictedContravariantRepresentableMap r ≫ pmap = 0 := by
  apply (cancel_mono t).1
  rw [Category.assoc, hpt]
  rw [S.finiteRestrictedContravariantRepresentableMap_comp_stableMap]
  rw [hr]
  rw [zero_comp, finiteRestrictedToProjectiveStableMap]
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  letI : Projective (S.fgObj p).obj := inferInstance
  exact S.finiteRestrictedMap_comp_stableQuotient_eq_zero
    (cokernel.π g) inferInstance

/-- Every simple quotient of a restricted indecomposable representable kills
its categorical radical. -/
theorem finiteRestrictedContravariantRepresentableRadicalInclusion_comp_nonzero_to_simple_eq_zero
    (i : S.IndecCategory)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hp : p ≠ 0) :
    S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫ p = 0 := by
  letI : IsLocalRing
      (End (S.finiteRestrictedContravariantRepresentable (S.fgObj i))) :=
    S.finiteRestrictedContravariantRepresentableFgObj_end_isLocalRing i
  exact MagnitudeConjecture.CategoryTheory.rightAlmostSplit_comp_nonzero_to_simple_eq_zero
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i)
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i)
    p hp

/-- Consequently every nonretraction into the representing indecomposable is
killed by a nonzero simple quotient of its restricted representable. -/
theorem finiteRestrictedContravariantRepresentableMap_comp_nonzero_to_simple_eq_zero
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (d : C ⟶ S.fgObj i)
    (hd : ¬ IsSplitEpi d)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hp : p ≠ 0) :
    S.finiteRestrictedContravariantRepresentableMap d ≫ p = 0 := by
  obtain ⟨a, ha⟩ :=
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i).factors
      (S.finiteRestrictedContravariantRepresentableMap d)
      (S.finiteRestrictedContravariantRepresentableMap_to_fgObj_not_isSplitEpi
        i d hd)
  rw [← ha, Category.assoc,
    S.finiteRestrictedContravariantRepresentableRadicalInclusion_comp_nonzero_to_simple_eq_zero
      i p hp,
    comp_zero]

/-- A stable class generating a simple subfunctor vanishes after
precomposition by every nonretraction into its representing indecomposable. -/
theorem nonretraction_comp_simpleStableGenerator_eq_zero
    {C : RightModule.FinitelyGeneratedCategory A}
    (i j : S.IndecCategory) (d : S.fgObj j ⟶ S.fgObj i)
    (hd : ¬ IsSplitEpi d) (h : S.fgObj i ⟶ C)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable C) [Mono t]
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hp : p ≠ 0)
    (hpt : p ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    S.finiteRestrictedToProjectiveStableMap j (d ≫ h) = 0 := by
  rw [← S.finiteRestrictedContravariantRepresentableMap_comp_stableMap]
  rw [← hpt]
  calc
    S.finiteRestrictedContravariantRepresentableMap d ≫ p ≫ t =
        (S.finiteRestrictedContravariantRepresentableMap d ≫ p) ≫ t :=
      (Category.assoc _ _ _).symm
    _ = 0 := by
      rw [S.finiteRestrictedContravariantRepresentableMap_comp_nonzero_to_simple_eq_zero
        i d hd p hp, zero_comp]

/-- The chosen minimal right almost-split map at a simple stable generator
becomes liftable through any projective epimorphism presenting the ambient
stable representable. -/
theorem rightAlmostSplit_comp_simpleStableGenerator_factors_projectiveEpi
    {P C : RightModule.FinitelyGeneratedCategory A}
    (q : P ⟶ C) [Epi q] (hP : Projective P)
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable C) [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpmap : pmap ≠ 0)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    let B := S.minimalRightAlmostSplitAt i
    ∃ a : B.middle ⟶ P, a ≫ q = B.map ≫ h := by
  let B := S.minimalRightAlmostSplitAt i
  let d : B.middle ⟶ S.fgObj i := B.map
  have hkill :
      S.finiteRestrictedContravariantRepresentableMap d ≫ pmap = 0 :=
    S.finiteRestrictedContravariantRepresentableMap_comp_nonzero_to_simple_eq_zero
      i d B.rightAlmostSplit.not_isSplitEpi pmap hpmap
  have hnat :
      S.finiteRestrictedContravariantRepresentableMap (d ≫ h) ≫
          S.finiteProjectiveStableQuotient C = 0 := by
    rw [S.finiteRestrictedContravariantRepresentableMap_comp,
      Category.assoc, ← finiteRestrictedToProjectiveStableMap, ← hpt,
      ← Category.assoc, hkill, zero_comp]
  let inc (x : B.index) :
      S.almostSplitSkeleton.obj (B.label x) ⟶ B.middle :=
    biproduct.ι (fun y : B.index ↦
      S.almostSplitSkeleton.obj (B.label y)) x ≫
      B.decomposition.inv
  have hcomponent (x : B.index) :
      ∃ a : S.almostSplitSkeleton.obj (B.label x) ⟶ P,
        a ≫ q = inc x ≫ B.map ≫ h := by
    have happ := congrArg
      (fun f ↦ f.hom.hom.app (Opposite.op (B.label x)) (inc x).hom)
      hnat
    have hstable : ProjectiveStable.mk (k := k)
        ((inc x ≫ B.map ≫ h).hom) = 0 := by
      exact happ
    have hmem : (inc x ≫ B.map ≫ h).hom ∈
        ProjectiveStable.factorSubmodule (k := k)
          (S.fgObj (B.label x)).obj C.obj :=
      (Submodule.Quotient.mk_eq_zero _).1 hstable
    have hPModule : Module.Projective Aᵐᵒᵖ P :=
      MagnitudeConjecture.moduleProjective_of_fgProjective P hP
    letI : Module.Projective Aᵐᵒᵖ P := hPModule
    have hqSurjective : Function.Surjective q.hom :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        q).1 inferInstance
    letI : Epi q.hom := (ModuleCat.epi_iff_surjective q.hom).2 hqSurjective
    rw [ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
      (k := k) q.hom (S.fgObj (B.label x)).obj] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨ObjectProperty.homMk a, ?_⟩
    apply ObjectProperty.hom_ext
    exact ha
  let aComponent (x : B.index) :
      S.almostSplitSkeleton.obj (B.label x) ⟶ P :=
    Classical.choose (hcomponent x)
  let a : B.middle ⟶ P :=
    B.decomposition.hom ≫ biproduct.desc aComponent
  refine ⟨a, ?_⟩
  apply (cancel_epi B.decomposition.inv).1
  apply biproduct.hom_ext'
  intro x
  simp only [a, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, biproduct.ι_desc]
  simpa only [aComponent, inc, Category.assoc] using
    Classical.choose_spec (hcomponent x)

/-- A morphism representing a nonzero generator of a simple stable
subfunctor cannot lift through a projective epimorphism. -/
theorem simpleStableGenerator_not_factors_projectiveEpi
    {P C : RightModule.FinitelyGeneratedCategory A}
    (q : P ⟶ C) [Epi q] (hP : Projective P)
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable C) [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpmap : pmap ≠ 0)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    ¬ ∃ a : S.fgObj i ⟶ P, a ≫ q = h := by
  have hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0 := by
    intro hzero
    apply hpmap
    apply (cancel_mono t).1
    rw [zero_comp, hpt, hzero]
  rintro ⟨a, ha⟩
  apply hstable
  rw [← ha, finiteRestrictedToProjectiveStableMap,
    S.finiteRestrictedContravariantRepresentableMap_comp, Category.assoc]
  have hPModule : Module.Projective Aᵐᵒᵖ P :=
    MagnitudeConjecture.moduleProjective_of_fgProjective P hP
  letI : Module.Projective Aᵐᵒᵖ P := hPModule
  letI : Projective P.obj := inferInstance
  rw [S.finiteRestrictedMap_comp_stableQuotient_eq_zero q inferInstance,
    comp_zero]

/-- Pulling the irreducible projective quotient back along a generator of
a simple stable subfunctor produces a right almost-split epimorphism. -/
theorem irreducibleIntoProjective_simpleStableGenerator_pullback_isRightAlmostSplit
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory) (h : S.fgObj i ⟶ cokernel g)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable (cokernel g))
    [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpmap : pmap ≠ 0)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    IsRightAlmostSplit (pullback.snd (cokernel.π g) h) := by
  let q := cokernel.π g
  let B := S.minimalRightAlmostSplitAt i
  obtain ⟨a, ha⟩ :=
    S.rightAlmostSplit_comp_simpleStableGenerator_factors_projectiveEpi
      q hp i h t pmap hpmap hpt
  exact
    MagnitudeConjecture.CategoryTheory.pullback_snd_isRightAlmostSplit_of_rightAlmostSplit_lifts
      q h
      (S.simpleStableGenerator_not_factors_projectiveEpi
        q hp i h t pmap hpmap hpt)
      B.map B.rightAlmostSplit a ha

/-- Any right almost-split pullback projection along the irreducible
projective quotient is already right minimal: its kernel is the
indecomposable source of the irreducible inclusion. -/
theorem irreducibleIntoProjective_pullback_isRightMinimal_of_isRightAlmostSplit
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory) (h : S.fgObj i ⟶ cokernel g)
    (hAS : IsRightAlmostSplit (pullback.snd (cokernel.π g) h)) :
    IsRightMinimal (pullback.snd (cokernel.π g) h) := by
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  let q := cokernel.π g
  let f := pullback.snd q h
  let e : kernel f ≅ S.fgObj u :=
    (MagnitudeConjecture.CategoryTheory.pullbackCokernelKernelSourceIso
      g h).symm
  letI : IsLocalRing (End (S.fgObj u)) := S.fgObj_end_isLocalRing u
  letI : IsLocalRing (End (kernel f)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (MagnitudeConjecture.CategoryTheory.endomorphismRingEquivOfIso e.symm)
  exact
    MagnitudeConjecture.CategoryTheory.rightAlmostSplit_isRightMinimal_of_kernel_local
      f hAS

/-- The pullback projection attached to a simple stable generator is right
minimal. -/
theorem irreducibleIntoProjective_simpleStableGenerator_pullback_isRightMinimal
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory) (h : S.fgObj i ⟶ cokernel g)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable (cokernel g))
    [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpmap : pmap ≠ 0)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    IsRightMinimal (pullback.snd (cokernel.π g) h) := by
  apply S.irreducibleIntoProjective_pullback_isRightMinimal_of_isRightAlmostSplit
    u p g hg hp i h
  exact
    S.irreducibleIntoProjective_simpleStableGenerator_pullback_isRightAlmostSplit
      u p g hg hp i h t pmap hpmap hpt

theorem irreducibleIntoProjective_factor_not_isSplitEpi
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (i : S.IndecCategory)
    (h : S.fgObj i ⟶ cokernel g)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (r : S.fgObj p ⟶ S.fgObj i)
    (hr : r ≫ h = cokernel.π g) :
    ¬ IsSplitEpi r := by
  intro hrs
  letI : IsSplitEpi r := hrs
  apply hstable
  rw [finiteRestrictedToProjectiveStableMap]
  change S.finiteRestrictedContravariantRepresentableMap h ≫
      S.finiteProjectiveStableQuotient (cokernel g) = 0
  have hfac : h = section_ r ≫ cokernel.π g := by
    rw [← Category.id_comp h, ← IsSplitEpi.id r, Category.assoc, hr]
  rw [hfac, S.finiteRestrictedContravariantRepresentableMap_comp,
    Category.assoc]
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  letI : Projective (S.fgObj p).obj := inferInstance
  rw [S.finiteRestrictedMap_comp_stableQuotient_eq_zero
    (cokernel.π g) inferInstance, comp_zero]

theorem irreducibleIntoProjective_factor_thru_radical
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (i : S.IndecCategory)
    (h : S.fgObj i ⟶ cokernel g)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (r : S.fgObj p ⟶ S.fgObj i)
    (hr : r ≫ h = cokernel.π g) :
    ∃ l : S.finiteRestrictedContravariantRepresentable (S.fgObj p) ⟶
        S.finiteRestrictedContravariantRepresentableRadical i,
      l ≫ S.finiteRestrictedContravariantRepresentableRadicalInclusion i =
        S.finiteRestrictedContravariantRepresentableMap r := by
  apply (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i).factors
  exact S.finiteRestrictedContravariantRepresentableMap_not_isSplitEpi r
    (S.irreducibleIntoProjective_factor_not_isSplitEpi p g hg hp i h hstable r hr)

/-- The source of an irreducible monomorphism cannot be injective. -/
theorem irreducibleIntoProjective_source_not_injective
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    ¬ Injective (S.fgObj u) := by
  intro hu
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  letI : Injective (S.fgObj u) := hu
  exact hg.not_isSplitMono
    (IsSplitMono.mk'
      { retraction := Injective.factorThru (𝟙 (S.fgObj u)) g
        id := Injective.comp_factorThru (𝟙 (S.fgObj u)) g })

/-- The factor from the chosen left almost-split middle to the projective
target. -/
noncomputable def irreducibleIntoProjective_leftExtensionFactor
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) :
    (S.minimalLeftAlmostSplitAt u).middle ⟶ S.fgObj p :=
  Classical.choose
    ((S.minimalLeftAlmostSplitAt u).leftAlmostSplit.factors g
      hg.not_isSplitMono)

@[reassoc]
theorem irreducibleIntoProjective_leftExtensionFactor_comp
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) :
    (S.minimalLeftAlmostSplitAt u).map ≫
        S.irreducibleIntoProjective_leftExtensionFactor u p g hg = g :=
  Classical.choose_spec
    ((S.minimalLeftAlmostSplitAt u).leftAlmostSplit.factors g
      hg.not_isSplitMono)

instance irreducibleIntoProjective_leftExtensionFactor_isSplitEpi
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) :
    IsSplitEpi
      (S.irreducibleIntoProjective_leftExtensionFactor u p g hg) := by
  apply (hg.factorization
    (S.minimalLeftAlmostSplitAt u).map
    (S.irreducibleIntoProjective_leftExtensionFactor u p g hg)
    (S.irreducibleIntoProjective_leftExtensionFactor_comp u p g hg)).resolve_left
  exact (S.minimalLeftAlmostSplitAt u).leftAlmostSplit.not_isSplitMono

/-- The complement to the projective summand in the left almost-split
middle. -/
noncomputable def irreducibleIntoProjective_leftExtensionComplement
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) :
    SplitEpiComplement
      (S.irreducibleIntoProjective_leftExtensionFactor u p g hg) :=
  splitEpiComplement
    (S.irreducibleIntoProjective_leftExtensionFactor u p g hg)

/-- The map from the cokernel of the left almost-split inclusion to the
selected quotient `P/U`. -/
noncomputable def irreducibleIntoProjective_initialStableMap
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    cokernel (S.minimalLeftAlmostSplitAt u).map ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp) :=
  cokernel.desc (S.minimalLeftAlmostSplitAt u).map
    (S.irreducibleIntoProjective_leftExtensionFactor u p g hg ≫
      S.irreducibleIntoProjective_quotientMap p g hg hp) (by
        have hfactor :
            (S.minimalLeftAlmostSplitAt u).map ≫
                S.irreducibleIntoProjective_leftExtensionFactor u p g hg =
              (g : S.fgObj u ⟶ S.fgObj p) :=
          S.irreducibleIntoProjective_leftExtensionFactor_comp u p g hg
        rw [← Category.assoc, hfactor]
        exact S.irreducibleIntoProjective_comp_quotientMap p g hg hp)

@[reassoc]
theorem irreducibleIntoProjective_cokernelπ_comp_initialStableMap
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    cokernel.π (S.minimalLeftAlmostSplitAt u).map ≫
        S.irreducibleIntoProjective_initialStableMap u p g hg hp =
      S.irreducibleIntoProjective_leftExtensionFactor u p g hg ≫
        S.irreducibleIntoProjective_quotientMap p g hg hp :=
  cokernel.π_desc _ _ _

/-! The following raw version is useful for the socle argument, before
transporting the quotient to the chosen skeleton coordinates. -/

/-- The distinguished stable map before transporting the quotient to the
chosen skeleton coordinates. -/
noncomputable def irreducibleIntoProjective_initialStableMapRaw
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) :
    cokernel (S.minimalLeftAlmostSplitAt u).map ⟶ cokernel g :=
  cokernel.desc (S.minimalLeftAlmostSplitAt u).map
    (S.irreducibleIntoProjective_leftExtensionFactor u p g hg ≫ cokernel.π g) (by
      rw [← Category.assoc,
        S.irreducibleIntoProjective_leftExtensionFactor_comp]
      exact cokernel.condition g)

@[reassoc]
theorem irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) :
    cokernel.π (S.minimalLeftAlmostSplitAt u).map ≫
        S.irreducibleIntoProjective_initialStableMapRaw u p g hg =
      S.irreducibleIntoProjective_leftExtensionFactor u p g hg ≫ cokernel.π g :=
  cokernel.π_desc _ _ _

/-- Transporting the raw distinguished map across the selected cokernel
isomorphism gives the distinguished map in skeleton coordinates. -/
@[reassoc]
theorem irreducibleIntoProjective_initialStableMapRaw_comp_cokernelIso
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.irreducibleIntoProjective_initialStableMapRaw u p g hg ≫
        (S.irreducibleIntoProjective_cokernelIso p g hg hp).hom =
      S.irreducibleIntoProjective_initialStableMap u p g hg hp := by
  apply (cancel_epi (cokernel.π (S.minimalLeftAlmostSplitAt u).map)).1
  rw [← Category.assoc,
    S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw,
    S.irreducibleIntoProjective_cokernelπ_comp_initialStableMap]
  rfl

/-- The kernel identity underlying the one-summand pullback diagram in
Auslander--Reiten Proposition 2.4.  The kernel of the induced endpoint map
to `P/U` is the restriction of the upper cokernel map to the kernel of the
split epimorphism onto `P`. -/
noncomputable def irreducibleIntoProjective_initialStableMapRaw_kernel
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    let a := (S.minimalLeftAlmostSplitAt u).map
    let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
    let b := cokernel.π a
    let h := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
    IsLimit (KernelFork.ofι (kernel.ι t ≫ b) (by
      rw [Category.assoc,
        S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw,
        ← Category.assoc, kernel.condition, zero_comp])) := by
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    ⟨u, S.irreducibleIntoProjective_source_not_injective u p g hg hp⟩
  let a := (S.minimalLeftAlmostSplitAt u).map
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let b := cokernel.π a
  let q := cokernel.π g
  let h := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
  letI : Mono a := S.noninjectiveLeftAlmostSplit_mono x
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  haveI : Mono (a ≫ t) := by
    rw [show a ≫ t = g from
      S.irreducibleIntoProjective_leftExtensionFactor_comp u p g hg]
    exact irreducibleIntoProjective_mono g hg hp
  let hab : a ≫ b = 0 := cokernel.condition a
  exact MagnitudeConjecture.CategoryTheory.kernelLimit_of_splitEpi_cokernel_rows
    (a := a) (t := t) (b := b) (q := q) (h := h)
    (hab := hab)
    (ha := Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ b hab) (cokernelIsCokernel a))
    (hq := fun r hr =>
      CokernelCofork.IsColimit.desc' (cokernelIsCokernel g) r (by
        rw [← S.irreducibleIntoProjective_leftExtensionFactor_comp u p g hg]
        exact hr))
    (hsq := S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw
      u p g hg)

/-- The one-summand square used in Auslander--Reiten Proposition 2.4 is a
pullback: the middle split epimorphism and the induced maps on the two
cokernels recover the upper middle object. -/
theorem irreducibleIntoProjective_initialStableMapRaw_isPullback
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    let a := (S.minimalLeftAlmostSplitAt u).map
    let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
    let b := cokernel.π a
    let q := cokernel.π g
    let h := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
    IsPullback t b q h := by
  let a := (S.minimalLeftAlmostSplitAt u).map
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let b := cokernel.π a
  let q := cokernel.π g
  let h := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
  exact MagnitudeConjecture.CategoryTheory.isPullback_of_splitEpi_of_kernel_restriction
    t b q h
    (S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw u p g hg)
    (S.irreducibleIntoProjective_initialStableMapRaw_kernel u p g hg hp)

/-- The first-socle right almost-split middle is the direct sum of the
distinguished projective arm and the kernel of the raw stable generator.
This is the object-level `B ⊕ DTr C₂` decomposition in the first minimal
presentation of Auslander--Reiten Theorem 3.7. -/
noncomputable def irreducibleIntoProjective_initialMiddleIsoProjectiveBiprodKernelRaw
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    (S.minimalLeftAlmostSplitAt u).middle ≅
      S.fgObj p ⊞
        kernel (S.irreducibleIntoProjective_initialStableMapRaw u p g hg) := by
  let a := (S.minimalLeftAlmostSplitAt u).map
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let b := cokernel.π a
  let q := cokernel.π g
  let h := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
  let s : S.fgObj p ⟶ cokernel a := section_ t ≫ b
  have hs : s ≫ h = q := by
    dsimp only [s]
    rw [Category.assoc,
      S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw,
      ← Category.assoc, IsSplitEpi.id, Category.id_comp]
  let sq : IsPullback t b q h :=
    S.irreducibleIntoProjective_initialStableMapRaw_isPullback u p g hg hp
  exact sq.isoPullback ≪≫
    MagnitudeConjecture.CategoryTheory.pullbackIsoBiprodKernelOfFac q h s hs

/-- The split complement of the distinguished projective arm is the kernel
of the raw first-socle generator.  This identifies the two descriptions of
the nonprojective part of the first almost-split middle used in
Auslander--Reiten Proposition 2.6 and Theorem 3.7. -/
noncomputable def
irreducibleIntoProjective_leftExtensionComplementIsoInitialStableMapRawKernel
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    (S.irreducibleIntoProjective_leftExtensionComplement
        u p g hg).complement ≅
      kernel (S.irreducibleIntoProjective_initialStableMapRaw u p g hg) := by
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let b := cokernel.π (S.minimalLeftAlmostSplitAt u).map
  let h := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
  let D := S.irreducibleIntoProjective_leftExtensionComplement u p g hg
  let eD : D.complement ≅ kernel t :=
    MagnitudeConjecture.CategoryTheory.splitEpiComplementIsoKernel t D
  let ht :=
    S.irreducibleIntoProjective_initialStableMapRaw_kernel u p g hg hp
  let kh : kernel t ⟶ kernel h :=
    kernel.lift h (kernel.ι t ≫ b) (by
      rw [Category.assoc,
        S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw,
        ← Category.assoc, kernel.condition, zero_comp])
  let canonicalFork : KernelFork h :=
    KernelFork.ofι (kernel.ι h) (kernel.condition h)
  let hk : kernel h ⟶ kernel t := ht.lift canonicalFork
  have hhk : hk ≫ (kernel.ι t ≫ b) = kernel.ι h :=
    ht.fac canonicalFork WalkingParallelPair.zero
  let eK : kernel t ≅ kernel h :=
    { hom := kh
      inv := hk
      hom_inv_id := by
        letI : Mono (kernel.ι t ≫ b) := Fork.IsLimit.mono ht
        apply (cancel_mono (kernel.ι t ≫ b)).1
        rw [Category.assoc, hhk]
        exact (kernel.lift_ι h (kernel.ι t ≫ b) _).trans
          (Category.id_comp _).symm
      inv_hom_id := by
        apply (cancel_mono (kernel.ι h)).1
        rw [Category.assoc]
        change hk ≫ (kh ≫ kernel.ι h) = 𝟙 (kernel h) ≫ kernel.ι h
        rw [show kh ≫ kernel.ι h = kernel.ι t ≫ b from
          kernel.lift_ι h (kernel.ι t ≫ b) _, hhk, Category.id_comp] }
  exact eD ≪≫ eK

/-- Every generator of a simple stable subfunctor is, up to an isomorphism
of its indecomposable source and a morphism through the projective middle,
the distinguished generator constructed from the left almost-split sequence
at `U`.  This is the one-summand form of the comparison in
Auslander--Reiten Proposition 2.4 and Lemma 2.3. -/
theorem irreducibleIntoProjective_simpleStableGenerator_compare_raw_of_lift
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.almostSplitSkeleton.obj i ⟶ cokernel g)
    (hnot : ¬ ∃ a : S.almostSplitSkeleton.obj i ⟶ S.fgObj p,
      a ≫ cokernel.π g = h)
    (a : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj p)
    (ha : a ≫ cokernel.π g =
      (S.minimalRightAlmostSplitAt i).map ≫ h) :
    ∃ (e : S.almostSplitSkeleton.obj i ≅
        cokernel (S.minimalLeftAlmostSplitAt u).map)
      (r : S.almostSplitSkeleton.obj i ⟶ S.fgObj p),
      h = e.hom ≫ S.irreducibleIntoProjective_initialStableMapRaw u p g hg +
        r ≫ cokernel.π g := by
  let q := cokernel.π g
  let f : pullback q h ⟶ S.almostSplitSkeleton.obj i :=
    pullback.snd q h
  let top := pullback.fst q h
  let L := S.minimalLeftAlmostSplitAt u
  let b := cokernel.π L.map
  let h₀ := S.irreducibleIntoProjective_initialStableMapRaw u p g hg
  let t₀ := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  letI : Epi q := inferInstance
  letI : Epi f := by
    change Epi (pullback.snd q h)
    exact Abelian.epi_pullback_of_epi_f q h
  have hfAS : IsRightAlmostSplit f :=
    MagnitudeConjecture.CategoryTheory.pullback_snd_isRightAlmostSplit_of_rightAlmostSplit_lifts
      q h hnot (S.minimalRightAlmostSplitAt i).map
      (S.minimalRightAlmostSplitAt i).rightAlmostSplit a ha
  have hfMin : IsRightMinimal f :=
    S.irreducibleIntoProjective_pullback_isRightMinimal_of_isRightAlmostSplit
      u p g hg hp i h hfAS
  have hkAS : IsLeftAlmostSplit (kernel.ι f) :=
    hfAS.kernel_ι_isLeftAlmostSplit f hfMin
  have hkMin : IsLeftMinimal (kernel.ι f) :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.IsRightAlmostSplit.kernel_ι_isLeftMinimal_obj
      S.almostSplitSkeleton f hfAS hkAS
  let eK : S.almostSplitSkeleton.obj u ≅ kernel f :=
    MagnitudeConjecture.CategoryTheory.pullbackCokernelKernelSourceIso g h
  let j : S.almostSplitSkeleton.obj u ⟶ pullback q h :=
    eK.hom ≫ kernel.ι f
  have hjAS : IsLeftAlmostSplit j := hkAS.precomp_iso eK
  have hjMin : IsLeftMinimal j := hkMin.precomp_iso eK
  obtain ⟨eMiddle, heMiddle⟩ := exists_leftAlmostSplit_middleIso
    hjAS hjMin L.leftAlmostSplit L.leftMinimal
  let eJ : cokernel j ≅ cokernel (kernel.ι f) :=
    cokernel.mapIso j (kernel.ι f) eK (Iso.refl _) (by simp [j])
  let eF : cokernel (kernel.ι f) ≅ S.almostSplitSkeleton.obj i :=
    cokernelKernelIsoTarget f
  let eL : cokernel j ≅ cokernel L.map :=
    cokernel.mapIso j L.map (Iso.refl _) eMiddle (by
      simpa using heMiddle)
  let e : S.almostSplitSkeleton.obj i ≅ cokernel L.map :=
    eF.symm ≪≫ eJ.symm ≪≫ eL
  have heF : cokernel.π (kernel.ι f) ≫ eF.hom = f := by
    dsimp only [eF, cokernelKernelIsoTarget]
    exact colimit.isoColimitCocone_ι_hom _ WalkingParallelPair.one
  have he : f ≫ e.hom = eMiddle.hom ≫ b := by
    calc
      f ≫ e.hom =
          (cokernel.π (kernel.ι f) ≫ eF.hom) ≫ e.hom := by
            rw [heF]
      _ = cokernel.π (kernel.ι f) ≫ eJ.inv ≫ eL.hom := by
        simp [e, Category.assoc]
      _ = cokernel.π j ≫ eL.hom := by
        simp [eJ, Category.assoc]
      _ = eMiddle.hom ≫ b := by
        simp [eL, b]
  let δ : pullback q h ⟶ S.fgObj p := top - eMiddle.hom ≫ t₀
  have hjδ : j ≫ δ = 0 := by
    let gu : S.almostSplitSkeleton.obj u ⟶ S.fgObj p := g
    have hjtop : j ≫ top = gu := by
      dsimp only [j, top, q, f, eK]
      exact
        MagnitudeConjecture.CategoryTheory.pullbackCokernelKernelSourceIso_hom_comp_kernel_ι_comp_fst
          g h
    have hjt₀ : j ≫ (eMiddle.hom ≫ t₀) = gu := by
      rw [← Category.assoc, heMiddle]
      exact S.irreducibleIntoProjective_leftExtensionFactor_comp u p g hg
    dsimp only [δ]
    rw [Preadditive.comp_sub, hjtop, hjt₀]
    exact sub_self gu
  have hkδ : kernel.ι f ≫ δ = 0 := by
    apply (cancel_epi eK.hom).1
    simpa only [j, Category.assoc, comp_zero] using hjδ
  let r : S.almostSplitSkeleton.obj i ⟶ S.fgObj p :=
    Abelian.epiDesc f δ hkδ
  have hfr : f ≫ r = δ := Abelian.comp_epiDesc f δ hkδ
  refine ⟨e, r, ?_⟩
  apply (cancel_epi f).1
  calc
    f ≫ h = top ≫ q := pullback.condition.symm
    _ = eMiddle.hom ≫ t₀ ≫ q + δ ≫ q := by
      dsimp only [δ]
      rw [Preadditive.sub_comp]
      rw [← Category.assoc eMiddle.hom t₀ q]
      abel_nf
    _ = (f ≫ e.hom) ≫ h₀ + (f ≫ r) ≫ q := by
      rw [he, hfr, Category.assoc]
      rw [show b ≫ h₀ = t₀ ≫ q from
        S.irreducibleIntoProjective_cokernelπ_comp_initialStableMapRaw u p g hg]
    _ = f ≫ (e.hom ≫ h₀ + r ≫ q) := by
      simp only [Preadditive.comp_add, Category.assoc]

/-- Functor-category form of the raw comparison, with the lift and
non-lift hypotheses supplied by a nonzero generator of a simple stable
subfunctor. -/
theorem irreducibleIntoProjective_simpleStableGenerator_compare_raw
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.almostSplitSkeleton.obj i ⟶ cokernel g)
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable (cokernel g))
    [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpmap : pmap ≠ 0)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    ∃ (e : S.almostSplitSkeleton.obj i ≅
        cokernel (S.minimalLeftAlmostSplitAt u).map)
      (r : S.almostSplitSkeleton.obj i ⟶ S.fgObj p),
      h = e.hom ≫ S.irreducibleIntoProjective_initialStableMapRaw u p g hg +
        r ≫ cokernel.π g := by
  obtain ⟨a, ha⟩ :=
    S.rightAlmostSplit_comp_simpleStableGenerator_factors_projectiveEpi
      (cokernel.π g) hp i h t pmap hpmap hpt
  exact S.irreducibleIntoProjective_simpleStableGenerator_compare_raw_of_lift
    u p g hg hp i h
      (S.simpleStableGenerator_not_factors_projectiveEpi
        (cokernel.π g) hp i h t pmap hpmap hpt)
      a ha

/- The apparent module-level lift here is intentionally not asserted: the
  composite through the irreducible map is only zero in the projective-stable
  quotient, so the remaining factorization must be formulated there. -/

/-- The distinguished map from the opposite endpoint of the left
almost-split sequence survives in projective-stable Hom. -/
theorem irreducibleIntoProjective_initialStableMap_stableClass_ne_zero
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    ProjectiveStable.mk (k := k)
        (S.irreducibleIntoProjective_initialStableMap u p g hg hp) ≠ 0 := by
  letI : Projective (S.fgObj p) := hp
  let q := S.irreducibleIntoProjective_quotientMap p g hg hp
  let h := S.irreducibleIntoProjective_initialStableMap u p g hg hp
  intro hstable
  have hmem : h ∈ ProjectiveStable.factorSubmodule (k := k)
      (cokernel (S.minimalLeftAlmostSplitAt u).map)
      (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) :=
    (Submodule.Quotient.mk_eq_zero _).1 hstable
  rw [ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
    (k := k) q (cokernel (S.minimalLeftAlmostSplitAt u).map)] at hmem
  obtain ⟨l, hl⟩ := hmem
  change l ≫ q = h at hl
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let d := t - cokernel.π (S.minimalLeftAlmostSplitAt u).map ≫ l
  have hdq : d ≫ q = 0 := by
    dsimp only [d, t]
    rw [Preadditive.sub_comp, Category.assoc, hl]
    rw [S.irreducibleIntoProjective_cokernelπ_comp_initialStableMap
      u p g hg hp]
    simpa only [almostSplitSkeleton] using
      (sub_self
        (S.irreducibleIntoProjective_leftExtensionFactor u p g hg ≫ q))
  have hdπ : d ≫ cokernel.π g = 0 := by
    apply (cancel_mono
      (S.irreducibleIntoProjective_cokernelIso p g hg hp).hom).1
    simpa only [q, Category.assoc, zero_comp,
      irreducibleIntoProjective_quotientMap] using hdq
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  let r := Abelian.monoLift g d hdπ
  have hrg : r ≫ g = d := Abelian.monoLift_comp g d hdπ
  have har : (S.minimalLeftAlmostSplitAt u).map ≫ r =
      𝟙 (S.fgObj u) := by
    apply (cancel_mono g).1
    rw [Category.assoc, hrg]
    dsimp only [d, t]
    rw [Preadditive.comp_sub,
      S.irreducibleIntoProjective_leftExtensionFactor_comp u p g hg]
    have hzero :
        (S.minimalLeftAlmostSplitAt u).map ≫
            (cokernel.π (S.minimalLeftAlmostSplitAt u).map ≫ l) = 0 := by
      rw [← Category.assoc, cokernel.condition, zero_comp]
    rw [hzero]
    change g - (0 : S.fgObj u ⟶ S.fgObj p) = g
    exact sub_zero g
  exact (S.minimalLeftAlmostSplitAt u).leftAlmostSplit.not_isSplitMono
    (IsSplitMono.mk' { retraction := r, id := har })

/-- The opposite endpoint of the chosen left almost-split sequence is
indecomposable. -/
theorem irreducibleIntoProjective_leftCokernel_indecomposable
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    Indecomposable (cokernel (S.minimalLeftAlmostSplitAt u).map) := by
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    ⟨u, S.irreducibleIntoProjective_source_not_injective u p g hg hp⟩
  exact (fgModule_isIndecomposableModule_iff_indecomposable
    (k := k) (A := A)
    (cokernel (S.minimalLeftAlmostSplitAt u).map)).1
      (rightAlmostSplit_target_isIndecomposableModule
        (cokernel.π (S.minimalLeftAlmostSplitAt u).map)
        (S.noninjectiveLeftCokernel_rightAlmostSplit x))

/-- The selected label of the opposite endpoint of the left almost-split
sequence starting at the irreducible projective submodule. -/
noncomputable def irreducibleIntoProjective_leftCokernelLabel
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    Fin S.n :=
  Classical.choose (S.fgObj_complete
    (cokernel (S.minimalLeftAlmostSplitAt u).map)
    (S.irreducibleIntoProjective_leftCokernel_indecomposable
      u p g hg hp))

/-- The opposite endpoint in the coordinates of the chosen skeleton. -/
noncomputable def irreducibleIntoProjective_leftCokernelIso
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    cokernel (S.minimalLeftAlmostSplitAt u).map ≅
      S.fgObj (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) :=
  Classical.choice (Classical.choose_spec (S.fgObj_complete
    (cokernel (S.minimalLeftAlmostSplitAt u).map)
    (S.irreducibleIntoProjective_leftCokernel_indecomposable
      u p g hg hp)))

/-- The distinguished stable-socle map with its source expressed in the
chosen indecomposable skeleton. -/
noncomputable def irreducibleIntoProjective_selectedInitialStableMap
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.fgObj (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp) :=
  (S.irreducibleIntoProjective_leftCokernelIso u p g hg hp).inv ≫
    S.irreducibleIntoProjective_initialStableMap u p g hg hp

/-- In selected skeleton coordinates, every generator of a simple stable
subfunctor differs from the distinguished generator only by a source
isomorphism and a morphism through the projective quotient. -/
theorem irreducibleIntoProjective_simpleStableGenerator_compare_selected
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    {T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k} [Simple T]
    (t : T ⟶ S.finiteProjectiveStableContravariantRepresentable
      (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)))
    [Mono t]
    (pmap : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hpmap : pmap ≠ 0)
    (hpt : pmap ≫ t = S.finiteRestrictedToProjectiveStableMap i h) :
    ∃ (e : S.fgObj i ≅
        S.fgObj (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp))
      (r : S.fgObj i ⟶ S.fgObj p),
      h = e.hom ≫
          S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp +
        r ≫ S.irreducibleIntoProjective_quotientMap p g hg hp := by
  let eQ := S.irreducibleIntoProjective_cokernelIso p g hg hp
  let q := S.irreducibleIntoProjective_quotientMap p g hg hp
  let hRaw : S.fgObj i ⟶ cokernel g := h ≫ eQ.inv
  let B := S.minimalRightAlmostSplitAt i
  obtain ⟨a, ha⟩ :=
    S.rightAlmostSplit_comp_simpleStableGenerator_factors_projectiveEpi
      q hp i h t pmap hpmap hpt
  have hRaw_comp_cokernelIso : hRaw ≫ eQ.hom = h := by
    dsimp only [hRaw]
    rw [Category.assoc, eQ.inv_hom_id, Category.comp_id]
  have hnotRaw : ¬ ∃ l : S.fgObj i ⟶ S.fgObj p,
      l ≫ cokernel.π g = hRaw := by
    rintro ⟨l, hl⟩
    apply S.simpleStableGenerator_not_factors_projectiveEpi
      q hp i h t pmap hpmap hpt
    refine ⟨l, ?_⟩
    calc
      l ≫ q = (l ≫ cokernel.π g) ≫ eQ.hom := by
        rfl
      _ = hRaw ≫ eQ.hom := by rw [hl]
      _ = h := hRaw_comp_cokernelIso
  have haRaw : a ≫ cokernel.π g = B.map ≫ hRaw := by
    apply (cancel_mono eQ.hom).1
    calc
      (a ≫ cokernel.π g) ≫ eQ.hom = a ≫ q := by
        rfl
      _ = B.map ≫ h := ha
      _ = (B.map ≫ hRaw) ≫ eQ.hom := by
        symm
        calc
          (B.map ≫ hRaw) ≫ eQ.hom =
              B.map ≫ (hRaw ≫ eQ.hom) := Category.assoc _ _ _
          _ = B.map ≫ h := congrArg (fun f => B.map ≫ f)
            hRaw_comp_cokernelIso
  obtain ⟨eRaw, r, hRawEq⟩ :=
    S.irreducibleIntoProjective_simpleStableGenerator_compare_raw_of_lift
      u p g hg hp i hRaw hnotRaw a haRaw
  let eRawFG : S.fgObj i ≅
      cokernel (S.minimalLeftAlmostSplitAt u).map := eRaw
  let rFG : S.fgObj i ⟶ S.fgObj p := r
  change hRaw = eRawFG.hom ≫
      S.irreducibleIntoProjective_initialStableMapRaw u p g hg +
      rFG ≫ cokernel.π g at hRawEq
  let e : S.fgObj i ≅
      S.fgObj (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) :=
    eRawFG ≪≫
    S.irreducibleIntoProjective_leftCokernelIso u p g hg hp
  refine ⟨e, rFG, ?_⟩
  have hInitialBack :
      S.irreducibleIntoProjective_initialStableMap u p g hg hp ≫ eQ.inv =
        S.irreducibleIntoProjective_initialStableMapRaw u p g hg := by
    rw [← S.irreducibleIntoProjective_initialStableMapRaw_comp_cokernelIso
      u p g hg hp]
    simp [eQ, Category.assoc]
  apply (cancel_mono eQ.inv).1
  rw [Preadditive.add_comp]
  calc
    h ≫ eQ.inv = hRaw := rfl
    _ = eRawFG.hom ≫
          S.irreducibleIntoProjective_initialStableMapRaw u p g hg +
        rFG ≫ cokernel.π g := hRawEq
    _ = (e.hom ≫
          S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp) ≫
          eQ.inv + (rFG ≫ q) ≫ eQ.inv := by
      dsimp only [e, irreducibleIntoProjective_selectedInitialStableMap]
      simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc,
        hInitialBack]
      dsimp only [q, irreducibleIntoProjective_quotientMap, eQ]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Changing the source to the chosen skeleton coordinates does not kill
the distinguished stable class. -/
theorem irreducibleIntoProjective_selectedInitialStableMap_stableClass_ne_zero
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    ProjectiveStable.mk (k := k)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ≠ 0 := by
  intro hzero
  apply S.irreducibleIntoProjective_initialStableMap_stableClass_ne_zero
    u p g hg hp
  have hpre := congrArg
    (ProjectiveStable.precomp (k := k)
      (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
      (S.irreducibleIntoProjective_leftCokernelIso u p g hg hp).hom)
    hzero
  simpa only [ProjectiveStable.precomp_mk, map_zero,
    irreducibleIntoProjective_selectedInitialStableMap,
    Category.assoc, Iso.hom_inv_id_assoc] using hpre

/-- The same distinguished morphism is nonzero in stable Hom after
forgetting to the ambient module category. -/
theorem irreducibleIntoProjective_selectedInitialStableMap_obj_stableClass_ne_zero
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    ProjectiveStable.mk (k := k)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp).hom ≠ 0 := by
  let q := S.irreducibleIntoProjective_quotientMap p g hg hp
  let h := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  intro hzero
  have hmem : h.hom ∈ ProjectiveStable.factorSubmodule (k := k)
      (S.fgObj
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)).obj
      (S.fgObj
        (S.irreducibleIntoProjective_cokernelLabel p g hg hp)).obj :=
    (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  have hpObj : Projective (S.fgObj p).obj := inferInstance
  have hqSurjective : Function.Surjective q.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      q).1 inferInstance
  letI : Epi q.hom := (ModuleCat.epi_iff_surjective q.hom).2 hqSurjective
  rw [ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
    (k := k) q.hom
    (S.fgObj
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)).obj]
    at hmem
  obtain ⟨l, hl⟩ := hmem
  apply S.irreducibleIntoProjective_selectedInitialStableMap_stableClass_ne_zero
    u p g hg hp
  apply (Submodule.Quotient.mk_eq_zero _).2
  rw [ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
    (k := k) q
    (S.fgObj
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp))]
  let lfg : S.fgObj
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) ⟶
      S.fgObj p := ObjectProperty.homMk l
  refine ⟨lfg, ?_⟩
  apply ObjectProperty.hom_ext
  exact hl

/-- The right almost-split quotient map of the left almost-split sequence,
transported to the chosen endpoint. -/
noncomputable def irreducibleIntoProjective_selectedLeftCokernelMap
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    (S.minimalLeftAlmostSplitAt u).middle ⟶
      S.fgObj (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) :=
  cokernel.π (S.minimalLeftAlmostSplitAt u).map ≫
    (S.irreducibleIntoProjective_leftCokernelIso u p g hg hp).hom

/-- The transported cokernel map is right almost split. -/
theorem irreducibleIntoProjective_selectedLeftCokernelMap_isRightAlmostSplit
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsRightAlmostSplit
      (S.irreducibleIntoProjective_selectedLeftCokernelMap
        u p g hg hp) := by
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    ⟨u, S.irreducibleIntoProjective_source_not_injective u p g hg hp⟩
  exact (S.noninjectiveLeftCokernel_rightAlmostSplit x).postcomp_iso
    (S.irreducibleIntoProjective_leftCokernelIso u p g hg hp)

/-- The transported cokernel map remains right minimal. -/
theorem irreducibleIntoProjective_selectedLeftCokernelMap_isRightMinimal
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsRightMinimal
      (S.irreducibleIntoProjective_selectedLeftCokernelMap
        u p g hg hp) := by
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    ⟨u, S.irreducibleIntoProjective_source_not_injective u p g hg hp⟩
  exact (S.noninjectiveLeftCokernel_rightMinimal x).postcomp_iso
    (S.irreducibleIntoProjective_leftCokernelIso u p g hg hp)

/-- The projective summand of the left almost-split middle supplies an
irreducible incoming arm at the selected opposite endpoint. -/
noncomputable def irreducibleIntoProjective_initialProjectiveArm
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.fgObj p ⟶
      S.fgObj (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) :=
  section_ (S.irreducibleIntoProjective_leftExtensionFactor u p g hg) ≫
    S.irreducibleIntoProjective_selectedLeftCokernelMap u p g hg hp

/-- The projective arm is irreducible. -/
theorem irreducibleIntoProjective_initialProjectiveArm_isIrreducible
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsIrreducibleMorphism
      (S.irreducibleIntoProjective_initialProjectiveArm
        u p g hg hp) := by
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let b := S.irreducibleIntoProjective_selectedLeftCokernelMap u p g hg hp
  exact
    (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightAlmostSplit
      u p g hg hp).irreducible_comp_of_splitSummand b
        (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightMinimal
          u p g hg hp)
        (section_ t) t (IsSplitEpi.id t)
        (S.fgObj_indecomposable p)
        (S.fgObj_indecomposable
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp))

/-- The transported right almost-split map followed by the distinguished
map factors through the projective quotient. -/
@[reassoc]
theorem irreducibleIntoProjective_selectedLeftCokernelMap_comp_selectedInitialStableMap
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.irreducibleIntoProjective_selectedLeftCokernelMap u p g hg hp ≫
        S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp =
      S.irreducibleIntoProjective_leftExtensionFactor u p g hg ≫
        S.irreducibleIntoProjective_quotientMap p g hg hp := by
  dsimp only [irreducibleIntoProjective_selectedLeftCokernelMap,
    irreducibleIntoProjective_selectedInitialStableMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact S.irreducibleIntoProjective_cokernelπ_comp_initialStableMap
    u p g hg hp

/-- The selected distinguished morphism induces a nonzero map from its
restricted representable into the stable representable. -/
theorem irreducibleIntoProjective_selectedInitialStableNaturalMap_ne_zero
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.finiteRestrictedToProjectiveStableMap
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ≠ 0 := by
  intro hzero
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let q := S.irreducibleIntoProjective_quotientMap p g hg hp
  let h := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  have happ := congrArg
    (fun f ↦ f.hom.hom.app
      (Opposite.op
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp))
      (𝟙 (S.inclusion.obj
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp))))
    hzero
  change ProjectiveStable.mk (k := k)
    (𝟙 (S.inclusion.obj
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)) ≫
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp).hom) = 0 at happ
  have hstable : ProjectiveStable.mk (k := k)
      (𝟙 (S.inclusion.obj c) ≫ h.hom) = 0 := happ
  have hmem : (𝟙 (S.inclusion.obj c) ≫ h.hom) ∈
      ProjectiveStable.factorSubmodule (k := k)
        (S.inclusion.obj c)
        (S.fgObj
          (S.irreducibleIntoProjective_cokernelLabel p g hg hp)).obj :=
    (Submodule.Quotient.mk_eq_zero _).1 hstable
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  have hqSurjective : Function.Surjective q.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      q).1 inferInstance
  letI : Epi q.hom := (ModuleCat.epi_iff_surjective q.hom).2 hqSurjective
  rw [ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
    (k := k) q.hom (S.inclusion.obj c)] at hmem
  obtain ⟨l, hl⟩ := hmem
  change l ≫ q.hom = h.hom at hl
  apply S.irreducibleIntoProjective_selectedInitialStableMap_stableClass_ne_zero
    u p g hg hp
  apply (Submodule.Quotient.mk_eq_zero _).2
  rw [ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
    (k := k) q (S.fgObj c)]
  let lfg : S.fgObj c ⟶ S.fgObj p := ObjectProperty.homMk l
  refine ⟨lfg, ?_⟩
  apply ObjectProperty.hom_ext
  exact hl

/-- The whole right almost-split map at the opposite endpoint is killed by
the distinguished map in the projective-stable quotient. -/
theorem irreducibleIntoProjective_selectedLeftCokernelMap_comp_selectedInitialStableNaturalMap_eq_zero
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.finiteRestrictedContravariantRepresentableMap
        (S.irreducibleIntoProjective_selectedLeftCokernelMap
          u p g hg hp) ≫
      S.finiteRestrictedToProjectiveStableMap
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) = 0 := by
  let q := S.irreducibleIntoProjective_quotientMap p g hg hp
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  rw [finiteRestrictedToProjectiveStableMap, ← Category.assoc,
    ← S.finiteRestrictedContravariantRepresentableMap_comp]
  rw [S.irreducibleIntoProjective_selectedLeftCokernelMap_comp_selectedInitialStableMap
    u p g hg hp]
  rw [S.finiteRestrictedContravariantRepresentableMap_comp, Category.assoc]
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  have hpObj : Projective (S.fgObj p).obj := inferInstance
  rw [S.finiteRestrictedMap_comp_stableQuotient_eq_zero q hpObj,
    comp_zero]

/-- The distinguished map kills the radical of its representing
indecomposable. -/
theorem irreducibleIntoProjective_selectedInitialStableMap_killsRadical
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.finiteRestrictedContravariantRepresentableRadicalInclusion
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) ≫
      S.finiteRestrictedToProjectiveStableMap
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) = 0 := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let b := S.irreducibleIntoProjective_selectedLeftCokernelMap u p g hg hp
  let v := S.finiteRestrictedToProjectiveStableMap c
    (S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp)
  have hbzero :
      S.finiteRestrictedContravariantRepresentableMap b ≫ v = 0 :=
    S.irreducibleIntoProjective_selectedLeftCokernelMap_comp_selectedInitialStableNaturalMap_eq_zero
      u p g hg hp
  have himage :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      c b
      (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightAlmostSplit
        u p g hg hp) v
  have himageBot : imageSubobject
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion c ≫ v) =
        ⊥ := by
    rw [himage, hbzero, imageSubobject_zero]
  let f := S.finiteRestrictedContravariantRepresentableRadicalInclusion c ≫ v
  have harrow : (imageSubobject f).arrow = 0 := by
    rw [show imageSubobject f = ⊥ from himageBot, Subobject.bot_arrow]
  change f = 0
  rw [← imageSubobject_arrow_comp f, harrow, comp_zero]

/-- The image generated by the distinguished stable class is simple.  This
is the first socle layer in Auslander--Reiten Theorem 3.7. -/
theorem irreducibleIntoProjective_selectedInitialStableImage_simple
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    Simple (S.finiteProjectiveStableImage
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
      (S.irreducibleIntoProjective_selectedInitialStableMap
        u p g hg hp)) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let r := S.finiteRestrictedContravariantRepresentableRadicalInclusion c
  let v := S.finiteRestrictedToProjectiveStableMap c h
  let F := S.finiteProjectiveStableImage c h
  let π := S.finiteProjectiveStableImagePresentation c h
  have hrπ : r ≫ π = 0 := by
    apply (cancel_mono (S.finiteProjectiveStableImageInclusion c h)).1
    rw [Category.assoc,
      S.finiteProjectiveStableImagePresentation_comp_inclusion,
      S.irreducibleIntoProjective_selectedInitialStableMap_killsRadical
        u p g hg hp, zero_comp]
  let e : cokernel r ⟶ F := cokernel.desc r π hrπ
  have heπ : cokernel.π r ≫ e = π := cokernel.π_desc r π hrπ
  haveI : Simple (cokernel r) :=
    MagnitudeConjecture.CategoryTheory.simple_cokernel_of_mono_rightAlmostSplit_projective r
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit c)
  haveI : Epi e := epi_of_epi_fac heπ
  have he : e ≠ 0 := by
    intro hezero
    apply S.finiteProjectiveStableImagePresentation_ne_zero c h
      (S.irreducibleIntoProjective_selectedInitialStableNaturalMap_ne_zero
        u p g hg hp)
    change π = 0
    rw [← heπ, hezero, comp_zero]
  letI : IsIso e := isIso_of_epi_of_nonzero he
  exact Simple.of_iso (asIso e).symm

/-- The distinguished simple cyclic image is the essential socle of the
stable representable of `P/U`.  Equivalently, every simple subfunctor
factors through this one image. -/
theorem irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsEssentialMono
      (S.finiteProjectiveStableImageInclusion
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp)) := by
  let z := S.irreducibleIntoProjective_cokernelLabel p g hg hp
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let L := S.finiteProjectiveStableImage c h₀
  let l := S.finiteProjectiveStableImageInclusion c h₀
  letI : Simple L :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  apply S.finiteDimensionalModule_isEssentialMono_of_simple_restrictedRepresentable_factors
    l
  intro T _ t _ i pmap hpmap
  obtain ⟨h, hh⟩ := S.exists_finiteRestrictedToProjectiveStableMap_eq
    i z (pmap ≫ t)
  obtain ⟨e, r, her⟩ :=
    S.irreducibleIntoProjective_simpleStableGenerator_compare_selected
      u p g hg hp i h t pmap hpmap hh.symm
  let a := S.finiteRestrictedContravariantRepresentableMap e.hom ≫
    S.finiteProjectiveStableImagePresentation c h₀
  refine ⟨a, ?_⟩
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  letI : Projective (S.fgObj p).obj := inferInstance
  have hstable : S.finiteRestrictedToProjectiveStableMap i h =
      S.finiteRestrictedToProjectiveStableMap i (e.hom ≫ h₀) := by
    rw [her, finiteRestrictedToProjectiveStableMap,
      S.finiteRestrictedContravariantRepresentableMap_add,
      Preadditive.add_comp,
      S.finiteRestrictedContravariantRepresentableMap_comp,
      S.finiteRestrictedContravariantRepresentableMap_comp,
      Category.assoc,
      Category.assoc,
      S.finiteRestrictedMap_comp_stableQuotient_eq_zero
        (S.irreducibleIntoProjective_quotientMap p g hg hp) inferInstance,
      comp_zero, add_zero]
    rfl
  dsimp only [a, l]
  rw [Category.assoc,
    S.finiteProjectiveStableImagePresentation_comp_inclusion,
    S.finiteRestrictedContravariantRepresentableMap_comp_stableMap,
    ← hstable, hh]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
