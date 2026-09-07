import MagnitudeConjecture.Algebra.RightModuleBasicSimpleDimension
import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverDegree
import MagnitudeConjecture.Algebra.BiserialProjectivePresentation

/-!
# Projective irreducibles and first radical layers

The internal irreducible quotient between selected indecomposable projectives
is identified with the Hom space into the first radical layer of the target.
For a biserial complete primitive-projective presentation this gives the
ordinary-quiver out-degree bound.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The underlying finitely generated module map of a morphism in the selected
projective subcategory. -/
def ordinaryProjectiveFGHom {x y : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :
    S.fgObj y.label ⟶ S.fgObj x.label :=
  f.hom

theorem range_le_jacobson_of_mem_projectiveRadical
    {x y : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x)
    (hf : f ∈ S.projectiveRadicalSubmodule x y) :
    LinearMap.range (S.ordinaryProjectiveFGHom f).hom.hom ≤
      Module.jacobson Aᵐᵒᵖ (S.fgObj x.label) := by
  have hrad : IsRadicalMorphism (S.ordinaryProjectiveFGHom f) :=
    (S.fgNilpotentRadicalData.mem_ideal_iff
      (S.ordinaryProjectiveFGHom f)).1 hf
  have hnot : ¬ IsSplitEpi (S.ordinaryProjectiveFGHom f) :=
    (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (S.ordinaryProjectiveFGHom f)).1 hrad
  obtain ⟨l, hl⟩ :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      x.label x.projective).factors (S.ordinaryProjectiveFGHom f) hnot
  rintro z ⟨w, rfl⟩
  change (S.ordinaryProjectiveFGHom f).hom.hom w ∈
    Module.jacobson Aᵐᵒᵖ (S.fgObj x.label)
  rw [← congrArg (fun q : S.fgObj y.label ⟶ S.fgObj x.label ↦
    q.hom.hom w) hl]
  exact (l.hom.hom w).2

theorem mem_projectiveRadical_of_range_le_jacobson
    {x y : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x)
    (hf : LinearMap.range (S.ordinaryProjectiveFGHom f).hom.hom ≤
      Module.jacobson Aᵐᵒᵖ (S.fgObj x.label)) :
    f ∈ S.projectiveRadicalSubmodule x y := by
  let l : S.fgObj y.label ⟶ S.projectiveBoundaryRadical x.label :=
    ConcreteCategory.ofHom
      (LinearMap.codRestrict
        (Module.jacobson Aᵐᵒᵖ (S.fgObj x.label))
        (S.ordinaryProjectiveFGHom f).hom.hom
        (fun z ↦ hf (LinearMap.mem_range_self
          (S.ordinaryProjectiveFGHom f).hom.hom z)))
  have hl : l ≫ S.projectiveBoundaryRadicalInclusion x.label =
      S.ordinaryProjectiveFGHom f := by
    apply FGModuleCat.hom_ext
    ext z
    simp only [l, ordinaryProjectiveFGHom]
    rfl
  have hincRadical : IsRadicalMorphism
      (S.projectiveBoundaryRadicalInclusion x.label) :=
    (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (S.projectiveBoundaryRadicalInclusion x.label)).2
      (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
        x.label x.projective).not_isSplitEpi
  have hinc : S.projectiveBoundaryRadicalInclusion x.label ∈
      S.fgNilpotentRadicalData.ideal.hom _ _ :=
    (S.fgNilpotentRadicalData.mem_ideal_iff
      (S.projectiveBoundaryRadicalInclusion x.label)).2 hincRadical
  change S.ordinaryProjectiveFGHom f ∈
    S.fgNilpotentRadicalData.ideal.hom _ _
  rw [← hl]
  exact S.fgNilpotentRadicalData.ideal.precomp l hinc

theorem mem_projectiveRadical_iff_range_le_jacobson
    {x y : S.ProjectiveLabel}
    (f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :
    f ∈ S.projectiveRadicalSubmodule x y ↔
      LinearMap.range (S.ordinaryProjectiveFGHom f).hom.hom ≤
        Module.jacobson Aᵐᵒᵖ (S.fgObj x.label) :=
  ⟨S.range_le_jacobson_of_mem_projectiveRadical f,
    S.mem_projectiveRadical_of_range_le_jacobson f⟩

/-- Radical maps between selected projectives are canonically the maps into
the boundary radical of the target projective. -/
def projectiveRadicalBoundaryHomEquiv (x y : S.ProjectiveLabel) :
    S.projectiveRadicalSubmodule x y ≃ₗ[k]
      (S.fgObj y.label ⟶ S.projectiveBoundaryRadical x.label) where
  toFun f := ConcreteCategory.ofHom <|
    LinearMap.codRestrict
      (Module.jacobson Aᵐᵒᵖ (S.fgObj x.label))
      (S.ordinaryProjectiveFGHom f.1).hom.hom
      (fun z ↦ S.range_le_jacobson_of_mem_projectiveRadical f.1 f.2
        (LinearMap.mem_range_self
          (S.ordinaryProjectiveFGHom f.1).hom.hom z))
  invFun g := by
    let f : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x :=
      InducedCategory.homMk
        (g ≫ S.projectiveBoundaryRadicalInclusion x.label)
    refine ⟨f, S.mem_projectiveRadical_of_range_le_jacobson f ?_⟩
    rintro z ⟨w, rfl⟩
    exact (g.hom.hom w).2
  map_add' f g := by
    apply FGModuleCat.hom_ext
    ext z
    rfl
  map_smul' r f := by
    apply FGModuleCat.hom_ext
    ext z
    rfl
  left_inv f := by
    apply Subtype.ext
    apply InducedCategory.hom_ext
    apply FGModuleCat.hom_ext
    ext z
    rfl
  right_inv g := by
    apply FGModuleCat.hom_ext
    ext z
    rfl

/-- The first radical layer of a selected projective. -/
abbrev projectiveBoundaryRadicalTop (x : S.ProjectiveLabel) :=
  radicalQuotientFGObj (S.projectiveBoundaryRadical x.label)

/-- A radical projective map, factored through the boundary radical, and
then projected to the first radical layer. -/
def projectiveRadicalToBoundaryTopHom (x y : S.ProjectiveLabel) :
    S.projectiveRadicalSubmodule x y →ₗ[k]
      (S.fgObj y.label ⟶ S.projectiveBoundaryRadicalTop x) where
  toFun f := S.projectiveRadicalBoundaryHomEquiv x y f ≫
    radicalQuotientFGObjProjection (S.projectiveBoundaryRadical x.label)
  map_add' f g := by
    rw [LinearEquiv.map_add, Preadditive.add_comp]
  map_smul' r f := by
    apply FGModuleCat.hom_ext
    ext z
    rfl

/-- Projectivity of the source makes the map from radical morphisms onto
maps into the first boundary-radical layer surjective. -/
theorem projectiveRadicalToBoundaryTopHom_surjective
    (x y : S.ProjectiveLabel) :
    Function.Surjective (S.projectiveRadicalToBoundaryTopHom x y) := by
  intro g
  letI : Projective (S.fgObj y.label) := y.projective
  let q := radicalQuotientFGObjProjection
    (S.projectiveBoundaryRadical x.label)
  letI : Epi q := by
    apply (IndecomposableSkeleton.fg_epi_iff_surjective q).2
    exact (Module.jacobson Aᵐᵒᵖ
      (S.projectiveBoundaryRadical x.label)).mkQ_surjective
  obtain ⟨h, hh⟩ := Projective.factors g q
  refine ⟨(S.projectiveRadicalBoundaryHomEquiv x y).symm h, ?_⟩
  exact hh

theorem projectiveRadicalToBoundaryTopHom_comp_eq_zero
    {x y z : S.ProjectiveLabel}
    (g : S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj z)
    (h : S.ordinaryProjectiveObj z ⟶ S.ordinaryProjectiveObj x)
    (hg : g ∈ S.projectiveRadicalSubmodule z y)
    (hh : h ∈ S.projectiveRadicalSubmodule x z) :
    S.projectiveRadicalToBoundaryTopHom x y
      ⟨g ≫ h, S.projectiveRadicalSquare_le_radical x y (by
        change g ≫ h ∈
          (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
        rw [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
          HomIdeal.pow_one]
        exact HomIdeal.comp_mem_mul hg hh)⟩ = 0 := by
  let hbar := S.projectiveRadicalBoundaryHomEquiv x z ⟨h, hh⟩
  have hgRange := S.range_le_jacobson_of_mem_projectiveRadical g hg
  have hmap := Module.map_jacobson_le hbar.hom.hom
  apply FGModuleCat.hom_ext
  ext w
  change (Module.jacobson Aᵐᵒᵖ
    (S.projectiveBoundaryRadical x.label)).mkQ
      (hbar.hom.hom ((S.ordinaryProjectiveFGHom g).hom.hom w)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hmap ⟨(S.ordinaryProjectiveFGHom g).hom.hom w,
    hgRange (LinearMap.mem_range_self
      (S.ordinaryProjectiveFGHom g).hom.hom w), rfl⟩

/-- Every product of two radical maps between selected projectives vanishes
after passage to the first radical layer of the target. -/
theorem projectiveRadicalSquareInRadical_le_ker_boundaryTop
    (x y : S.ProjectiveLabel) :
    S.projectiveRadicalSquareInRadicalSubmodule x y ≤
      LinearMap.ker (S.projectiveRadicalToBoundaryTopHom x y) := by
  intro f hf
  rw [LinearMap.mem_ker]
  let I := S.projectiveNilpotentRadicalData.ideal
  let L := S.projectiveRadicalToBoundaryTopHom x y
  have hkill : ∀ q :
      (S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x),
      (hq : q ∈ (I ⋆ᵢ I).hom _ _) →
        L ⟨q, S.projectiveRadicalSquare_le_radical x y (by
          change q ∈ (I.pow 2).hom _ _
          rw [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
            HomIdeal.pow_one]
          exact hq)⟩ = 0 := by
    intro q hq
    induction hq using AddSubgroup.closure_induction with
    | mem q hq =>
        obtain ⟨z, g, h, hg, hh, rfl⟩ := hq
        exact S.projectiveRadicalToBoundaryTopHom_comp_eq_zero
          g h hg hh
    | zero =>
        exact LinearMap.map_zero L
    | add q r _ _ hq hr =>
        have hqrad : q ∈ S.projectiveRadicalSubmodule x y :=
          S.projectiveRadicalSquare_le_radical x y (by
            change q ∈ (I.pow 2).hom _ _
            rw [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
              HomIdeal.pow_one]
            assumption)
        have hrrad : r ∈ S.projectiveRadicalSubmodule x y :=
          S.projectiveRadicalSquare_le_radical x y (by
            change r ∈ (I.pow 2).hom _ _
            rw [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
              HomIdeal.pow_one]
            assumption)
        rw [show (⟨q + r, _⟩ : S.projectiveRadicalSubmodule x y) =
          ⟨q, hqrad⟩ + ⟨r, hrrad⟩ by rfl,
          LinearMap.map_add, hq, hr, add_zero]
    | neg q _ hq =>
        have hqrad : q ∈ S.projectiveRadicalSubmodule x y :=
          S.projectiveRadicalSquare_le_radical x y (by
            change q ∈ (I.pow 2).hom _ _
            rw [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
              HomIdeal.pow_one]
            assumption)
        rw [show (⟨-q, _⟩ : S.projectiveRadicalSubmodule x y) =
          -⟨q, hqrad⟩ by rfl, LinearMap.map_neg, hq, neg_zero]
  apply hkill f.1
  change f.1 ∈ (I.pow 2).hom _ _ at hf
  simpa [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
    HomIdeal.pow_one] using hf

/-- The canonical map from the internal projective irreducible quotient to
maps into the first radical layer. -/
def projectiveIrrToBoundaryTopHom (x y : S.ProjectiveLabel) :
    S.projectiveIrreducibleHomSpace x y →ₗ[k]
      (S.fgObj y.label ⟶ S.projectiveBoundaryRadicalTop x) :=
  (S.projectiveRadicalSquareInRadicalSubmodule x y).liftQ
    (S.projectiveRadicalToBoundaryTopHom x y)
    (S.projectiveRadicalSquareInRadical_le_ker_boundaryTop x y)

/-- Every map from a selected projective into the first radical layer lifts
to an internal irreducible class. -/
theorem projectiveIrrToBoundaryTopHom_surjective
    (x y : S.ProjectiveLabel) :
    Function.Surjective (S.projectiveIrrToBoundaryTopHom x y) := by
  intro g
  obtain ⟨f, hf⟩ :=
    S.projectiveRadicalToBoundaryTopHom_surjective x y g
  refine ⟨(S.projectiveRadicalSquareInRadicalSubmodule x y).mkQ f, ?_⟩
  exact hf

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

namespace MagnitudeConjecture.MinimalProjectivePresentation

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- The kernel of a projective cover lies in the Jacobson radical of its
projective source. -/
theorem kernel_le_jacobson {M : FGModuleCat.{u} R}
    (P : MinimalProjectivePresentation M) :
    LinearMap.ker P.f.hom.hom ≤ Module.jacobson R P.p := by
  rw [Module.jacobson, le_sInf_iff]
  intro N hN
  by_contra hker
  have hsupNe : N ⊔ LinearMap.ker P.f.hom.hom ≠ N := by
    intro hsup
    apply hker
    intro z hz
    have hzsup : z ∈ N ⊔ LinearMap.ker P.f.hom.hom :=
      Submodule.mem_sup_right hz
    rwa [hsup] at hzsup
  have hsup : N ⊔ LinearMap.ker P.f.hom.hom = ⊤ :=
    (hN.ne_iff_eq_top le_sup_left).1 hsupNe
  let Nfg : FGModuleCat.{u} R := FGModuleCat.of R N
  let i : Nfg ⟶ P.p := ConcreteCategory.ofHom N.subtype
  have hcompSurj : Function.Surjective (i ≫ P.f).hom.hom := by
    have hqSurj : Function.Surjective P.f.hom.hom :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        P.f).1 inferInstance
    intro m
    obtain ⟨p, hp⟩ := hqSurj m
    have hpSup : p ∈ N ⊔ LinearMap.ker P.f.hom.hom := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp hpSup
    refine ⟨⟨n, hn⟩, ?_⟩
    change P.f.hom.hom n = m
    have hzZero : P.f.hom.hom z = 0 := hz
    calc
      P.f.hom.hom n = P.f.hom.hom (n + z) := by
        rw [map_add, hzZero, add_zero]
      _ = P.f.hom.hom p := congrArg P.f.hom.hom hnz
      _ = m := hp
  haveI : Epi (i ≫ P.f) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      (i ≫ P.f)).2 hcompSurj
  have hessential : IsEssentialEpi P.f :=
    isEssentialEpi_of_isRightMinimal P.f P.rightMinimal
  haveI : Epi i := hessential.2 i inferInstance
  have hiSurj : Function.Surjective i.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      i).1 inferInstance
  apply hN.ne_top
  apply top_unique
  intro p _
  obtain ⟨n, hn⟩ := hiSurj p
  change p ∈ N
  rw [← hn]
  exact n.2

/-- A projective cover pulls the Jacobson radical of its target back to the
Jacobson radical of its projective source. -/
theorem comap_jacobson_eq {M : FGModuleCat.{u} R}
    (P : MinimalProjectivePresentation M) :
    (Module.jacobson R M).comap P.f.hom.hom =
      Module.jacobson R P.p := by
  apply Module.comap_jacobson_of_ker_le
  · exact
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        P.f).1 inferInstance
  · exact P.kernel_le_jacobson

/-- A projective cover maps the Jacobson radical of its source onto that of
its target. -/
theorem map_jacobson_eq {M : FGModuleCat.{u} R}
    (P : MinimalProjectivePresentation M) :
    (Module.jacobson R P.p).map P.f.hom.hom =
      Module.jacobson R M := by
  apply Module.map_jacobson_of_ker_le
  · exact
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        P.f).1 inferInstance
  · exact P.kernel_le_jacobson

end MagnitudeConjecture.MinimalProjectivePresentation

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

open CategoryTheory.Limits
open scoped BigOperators

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

local instance boundaryRestrictedModule
    (X : RightModule.FinitelyGeneratedCategory A) : Module k X :=
  Module.restrictScalars k Aᵐᵒᵖ X

local instance boundaryRestrictedScalarTower
    (X : RightModule.FinitelyGeneratedCategory A) :
    IsScalarTower k Aᵐᵒᵖ X :=
  IsScalarTower.restrictScalars k Aᵐᵒᵖ X

set_option backward.isDefEq.respectTransparency false in
/-- A map into the boundary radical whose image lies in its Jacobson
radical becomes a product of two radical maps in the selected-projective
subcategory. -/
theorem boundaryHom_comp_inclusion_mem_projectiveRadicalSquare
    {x y : S.ProjectiveLabel}
    (a : S.fgObj y.label ⟶ S.projectiveBoundaryRadical x.label)
    (ha : LinearMap.range a.hom.hom ≤
      Module.jacobson Aᵐᵒᵖ (S.projectiveBoundaryRadical x.label)) :
    (InducedCategory.homMk
      (a ≫ S.projectiveBoundaryRadicalInclusion x.label) :
        S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) ∈
        S.projectiveRadicalSquareSubmodule x y := by
  classical
  let Jx := S.projectiveBoundaryRadical x.label
  let inc := S.projectiveBoundaryRadicalInclusion x.label
  obtain ⟨Q⟩ := minimalProjectivePresentation_nonempty k Jx
  letI : Projective (S.fgObj y.label) := y.projective
  obtain ⟨s, hs⟩ := Projective.factors a Q.f
  have hsRange : LinearMap.range s.hom.hom ≤
      Module.jacobson Aᵐᵒᵖ Q.p := by
    rintro z ⟨w, rfl⟩
    rw [← Q.comap_jacobson_eq]
    change Q.f.hom.hom (s.hom.hom w) ∈
      Module.jacobson Aᵐᵒᵖ Jx
    have hsw := congrArg
      (fun q : S.fgObj y.label ⟶ Jx ↦ q.hom.hom w) hs
    change Q.f.hom.hom (s.hom.hom w) = a.hom.hom w at hsw
    rw [hsw]
    exact ha (LinearMap.mem_range_self a.hom.hom w)
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition Q.p
  let F : Fin n → RightModule.FinitelyGeneratedCategory A :=
    fun i ↦ S.fgObj (label i)
  have hprojective (i : Fin n) : Projective (F i) := by
    let inclusion : F i ⟶ Q.p := biproduct.ι F i ≫ e.inv
    let retraction : Q.p ⟶ F i := e.hom ≫ biproduct.π F i
    apply projective_of_retract (inferInstance : Projective Q.p)
      inclusion retraction
    simp [inclusion, retraction, Category.assoc]
  let p (i : Fin n) : S.ProjectiveLabel :=
    ⟨label i, hprojective i⟩
  let g (i : Fin n) :
      S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj (p i) :=
    InducedCategory.homMk
      (s ≫ e.hom ≫ biproduct.π F i)
  let h (i : Fin n) :
      S.ordinaryProjectiveObj (p i) ⟶ S.ordinaryProjectiveObj x :=
    InducedCategory.homMk
      (biproduct.ι F i ≫ e.inv ≫ Q.f ≫ inc)
  have hg (i : Fin n) :
      g i ∈ S.projectiveRadicalSubmodule (p i) y := by
    apply S.mem_projectiveRadical_of_range_le_jacobson
    rintro z ⟨w, rfl⟩
    let t : Q.p ⟶ F i := e.hom ≫ biproduct.π F i
    have ht := Module.map_jacobson_le t.hom.hom
    exact ht ⟨s.hom.hom w,
      hsRange (LinearMap.mem_range_self s.hom.hom w), rfl⟩
  have hh (i : Fin n) :
      h i ∈ S.projectiveRadicalSubmodule x (p i) := by
    apply S.mem_projectiveRadical_of_range_le_jacobson
    rintro z ⟨w, rfl⟩
    let v : Jx :=
      (biproduct.ι F i ≫ e.inv ≫ Q.f).hom.hom w
    exact v.2
  have hsum : ∑ i, g i ≫ h i =
      (InducedCategory.homMk (a ≫ inc) :
        S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) := by
    apply (InducedCategory.homLinearEquiv (R := k)).injective
    rw [map_sum]
    simp only [InducedCategory.homLinearEquiv_apply,
      InducedCategory.homMk_hom]
    simp only [g, h]
    change (∑ i,
      (s ≫ e.hom ≫ biproduct.π F i) ≫
        (biproduct.ι F i ≫ e.inv ≫ Q.f ≫ inc)) = a ≫ inc
    calc
      _ = s ≫ e.hom ≫
          (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫
            e.inv ≫ Q.f ≫ inc := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp,
          Category.assoc]
      _ = a ≫ inc := by
        rw [biproduct.total, Category.id_comp,
          e.hom_inv_id_assoc, ← Category.assoc, hs]
  rw [← hsum]
  apply (S.projectiveRadicalSquareSubmodule x y).sum_mem
  intro i _
  change g i ≫ h i ∈
    (S.projectiveNilpotentRadicalData.ideal.pow 2).hom _ _
  rw [show 2 = 1 + 1 by omega, HomIdeal.pow_add,
    HomIdeal.pow_one]
  exact HomIdeal.comp_mem_mul (hg i) (hh i)

/-- A radical map killed on the first boundary-radical layer already lies in
the square of the radical formed inside the selected-projective category. -/
theorem ker_boundaryTop_le_projectiveRadicalSquareInRadical
    (x y : S.ProjectiveLabel) :
    LinearMap.ker (S.projectiveRadicalToBoundaryTopHom x y) ≤
      S.projectiveRadicalSquareInRadicalSubmodule x y := by
  intro f hf
  rw [LinearMap.mem_ker] at hf
  let a := S.projectiveRadicalBoundaryHomEquiv x y f
  have hf' : a ≫ radicalQuotientFGObjProjection
      (S.projectiveBoundaryRadical x.label) = 0 := by
    change S.projectiveRadicalBoundaryHomEquiv x y f ≫
      radicalQuotientFGObjProjection
        (S.projectiveBoundaryRadical x.label) = 0 at hf
    exact hf
  have ha : LinearMap.range a.hom.hom ≤
      Module.jacobson Aᵐᵒᵖ (S.projectiveBoundaryRadical x.label) := by
    rintro z ⟨w, rfl⟩
    rw [← Submodule.Quotient.mk_eq_zero]
    have hw := congrArg
      (fun q : S.fgObj y.label ⟶ S.projectiveBoundaryRadicalTop x ↦
        q.hom.hom w) hf'
    change (Module.jacobson Aᵐᵒᵖ
      (S.projectiveBoundaryRadical x.label)).mkQ
        (a.hom.hom w) = 0 at hw
    exact hw
  have hsq :=
    S.boundaryHom_comp_inclusion_mem_projectiveRadicalSquare a ha
  change f.1 ∈ S.projectiveRadicalSquareSubmodule x y
  have heq :
      (InducedCategory.homMk
        (a ≫ S.projectiveBoundaryRadicalInclusion x.label) :
          S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) = f.1 := by
    apply InducedCategory.hom_ext
    apply FGModuleCat.hom_ext
    ext w
    rfl
  rw [← heq]
  exact hsq

/-- The kernel of restriction to the first boundary-radical layer is exactly
the internal square of the selected-projective radical. -/
theorem ker_projectiveRadicalToBoundaryTopHom
    (x y : S.ProjectiveLabel) :
    LinearMap.ker (S.projectiveRadicalToBoundaryTopHom x y) =
      S.projectiveRadicalSquareInRadicalSubmodule x y := by
  apply le_antisymm
  · exact S.ker_boundaryTop_le_projectiveRadicalSquareInRadical x y
  · exact S.projectiveRadicalSquareInRadical_le_ker_boundaryTop x y

/-- The map from internal irreducible classes to the first boundary-radical
layer is injective. -/
theorem projectiveIrrToBoundaryTopHom_injective
    (x y : S.ProjectiveLabel) :
    Function.Injective (S.projectiveIrrToBoundaryTopHom x y) := by
  apply (LinearMap.ker_eq_bot).1
  apply le_antisymm
  · intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ f =>
        rw [LinearMap.mem_ker, projectiveIrrToBoundaryTopHom,
          Submodule.liftQ_apply] at hq
        rw [Submodule.mem_bot,
          Submodule.Quotient.mk_eq_zero]
        rw [← S.ker_projectiveRadicalToBoundaryTopHom x y]
        exact hq
  · exact bot_le

/-- Internal irreducible maps into a selected projective are canonically the
maps from the source projective into the first radical layer of the target. -/
def projectiveIrrBoundaryTopHomEquiv (x y : S.ProjectiveLabel) :
    S.projectiveIrreducibleHomSpace x y ≃ₗ[k]
      (S.fgObj y.label ⟶ S.projectiveBoundaryRadicalTop x) :=
  LinearEquiv.ofBijective (S.projectiveIrrToBoundaryTopHom x y)
    ⟨S.projectiveIrrToBoundaryTopHom_injective x y,
      S.projectiveIrrToBoundaryTopHom_surjective x y⟩

/-- Summing the dimensions of all internal irreducible maps into a selected
projective recovers the dimension of its first radical layer. -/
theorem sum_finrank_projectiveIrreducibleHomSpace_eq_boundaryTop_finrank
    (P : S.PrimitiveProjectivePresentation) (x : S.ProjectiveLabel) :
    ∑ y : S.ProjectiveLabel,
        Module.finrank k (S.projectiveIrreducibleHomSpace x y) =
      Module.finrank k (S.projectiveBoundaryRadicalTop x) := by
  rw [RightModule.finrank_eq_sum_finrank_idempotentCoordinate
    (S.projectiveBoundaryRadicalTop x) P.idempotent P.complete]
  apply Finset.sum_congr rfl
  intro y _
  rw [(S.projectiveIrrBoundaryTopHomEquiv x y).finrank_eq]
  have hlabel : S.primitiveSourceLabel (P.primitive y) = y.label :=
    congrArg ProjectiveLabel.label (P.sourceLabel y)
  have hcoord :=
    (S.primitiveSourceHomCoordinateEquiv
      (P.primitive y) (S.projectiveBoundaryRadicalTop x)).finrank_eq
  rw [hlabel] at hcoord
  exact hcoord

variable [IsNoetherianRing A]

/-- Biseriality of the complete primitive presentation bounds the composition
length of the first radical layer of each selected projective. -/
theorem PrimitiveProjectivePresentation.boundaryRadicalTop_length_le_two_of_isBiserial
    (P : S.PrimitiveProjectivePresentation) (hP : P.IsBiserial)
    (x : S.ProjectiveLabel) :
    Module.length Aᵐᵒᵖ (S.projectiveBoundaryRadicalTop x) ≤ 2 := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  apply top_jacobson_length_le_two_of_biserial
  let e : RightModule.rightIdealFGObj (P.idempotent x) ≃ₗ[Aᵐᵒᵖ]
      S.fgObj x.label :=
    FGModuleCat.isoToLinearEquiv (P.primitiveProjectiveIso x)
  exact IsBiserialModule.congr e
    (IsBiserialObject.toIsBiserialModule_of_fg _ (hP.1 x))

/-- Over the algebraically closed ground field, the first radical layer of a
biserial selected projective has vector-space dimension at most two. -/
theorem PrimitiveProjectivePresentation.boundaryRadicalTop_finrank_le_two_of_isBiserial
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation) (hP : P.IsBiserial)
    (x : S.ProjectiveLabel) :
    Module.finrank k (S.projectiveBoundaryRadicalTop x) ≤ 2 := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  letI : IsSemisimpleModule Aᵐᵒᵖ
      (S.projectiveBoundaryRadicalTop x) := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson Aᵐᵒᵖ
      (S.projectiveBoundaryRadical x.label)
  exact PrimitiveProjectivePresentation.finrank_le_two_of_semisimple_of_length_le_two
    S P (S.projectiveBoundaryRadicalTop x)
    (PrimitiveProjectivePresentation.boundaryRadicalTop_length_le_two_of_isBiserial
      S P hP x)

/-- A biserial complete primitive presentation has ordinary-quiver
out-degree at most two at every selected projective. -/
theorem ordinaryStar_card_le_two_of_primitiveProjectivePresentation_isBiserial
    [IsAlgClosed k]
    (P : S.PrimitiveProjectivePresentation) (hP : P.IsBiserial)
    (x : S.ProjectiveLabel) :
    Nat.card (Quiver.Star x) ≤ 2 := by
  rw [S.ordinaryStar_card_eq_sum_finrank,
    S.sum_finrank_projectiveIrreducibleHomSpace_eq_boundaryTop_finrank P]
  exact
    PrimitiveProjectivePresentation.boundaryRadicalTop_finrank_le_two_of_isBiserial
      S P hP x

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
