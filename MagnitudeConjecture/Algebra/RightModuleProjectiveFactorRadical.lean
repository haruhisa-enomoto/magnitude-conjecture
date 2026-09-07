import MagnitudeConjecture.Algebra.IteratedJacobsonRadical
import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.ProjectiveStableHom
import MagnitudeConjecture.CategoryTheory.ProjectiveCover

/-!
# Projective factorizations from indecomposable nonprojectives

This file isolates the second elementary module-theoretic ingredient in
Auslander--Reiten, Proposition 1.1(a).  A map from an indecomposable
nonprojective finite module into a finite projective has radical image.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

include k

/-- A map from an indecomposable nonprojective finitely generated module to
a finite projective module has image in the target radical. -/
theorem range_le_jacobson_of_map_to_fgProjective
    {X P : RightModule.FinitelyGeneratedCategory A}
    (hX : Indecomposable X) (hXnonprojective : ¬ Projective X)
    (hP : Projective P) (f : X ⟶ P) :
    LinearMap.range f.hom.hom ≤ Module.jacobson Aᵐᵒᵖ P := by
  classical
  letI : Module.Finite k P :=
    RightModule.finite_over_field_of_finitelyGenerated k A P
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) P
  let projection (j : Fin d.n) : P ⟶ d.summand j :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand j
  let inclusion (j : Fin d.n) : d.summand j ⟶ P :=
    biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  have hprojective (j : Fin d.n) : Projective (d.summand j) := by
    apply projective_of_retract (P := P) (Q := d.summand j)
      hP (inclusion j) (projection j)
    simp [inclusion, projection, Category.assoc]
  have hcomponent (j : Fin d.n) :
      LinearMap.range (f ≫ projection j).hom.hom ≤
        Module.jacobson Aᵐᵒᵖ (d.summand j) := by
    let q : X ⟶ d.summand j := f ≫ projection j
    letI : Module.Finite k (d.summand j) :=
      RightModule.finite_over_field_of_finitelyGenerated k A (d.summand j)
    letI : Projective (d.summand j) := hprojective j
    letI : Module.Projective Aᵐᵒᵖ (d.summand j) :=
      moduleProjective_of_fgProjective (d.summand j) (hprojective j)
    have hIndecObj : Indecomposable (d.summand j).obj :=
      (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := A) (d.summand j)).mp (d.indecomposable j)
    have hnsub : ¬ Subsingleton (d.summand j) :=
      (not_iff_not.mpr ModuleCat.isZero_iff_subsingleton).mp hIndecObj.1
    letI : Nontrivial (d.summand j) :=
      not_subsingleton_iff_nontrivial.mp hnsub
    letI : IsLocalRing (End (d.summand j).obj) :=
      moduleCat_end_isLocalRing (k := k) (A := Aᵐᵒᵖ)
        (d.summand j).obj hIndecObj
    letI : IsLocalRing (Module.End Aᵐᵒᵖ (d.summand j)) :=
      RingEquiv.isLocalRing_noncomm
        (ModuleCat.endRingEquiv (d.summand j).obj)
    have hradCoatom : IsCoatom
        (Module.jacobson Aᵐᵒᵖ (d.summand j)) :=
      jacobson_isCoatom_of_projective_local_end
    by_contra hnot
    have hsup : Module.jacobson Aᵐᵒᵖ (d.summand j) ⊔
        LinearMap.range q.hom.hom = ⊤ :=
      hradCoatom.2 _ (lt_of_le_of_ne le_sup_left (fun heq ↦
        hnot (heq ▸ le_sup_right)))
    have hquotSurj : Function.Surjective
        ((Module.jacobson Aᵐᵒᵖ (d.summand j)).mkQ.comp q.hom.hom) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_comp]
      exact ((Module.jacobson Aᵐᵒᵖ (d.summand j)).map_mkQ_eq_top
        (LinearMap.range q.hom.hom)).mpr hsup
    have hqSurj : Function.Surjective q.hom.hom :=
      surjective_of_quotient_comp_surjective
        hradCoatom.ne_top q.hom.hom hquotSurj
    letI : Epi q :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        q).mpr hqSurj
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (d.summand j)) q
    letI : IsSplitEpi q := IsSplitEpi.mk'
      { section_ := s
        id := hs }
    letI : IsIso q :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
        hX q (d.indecomposable j).1
    apply hXnonprojective
    exact Projective.of_iso (asIso q).symm (hprojective j)
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  have hterm (j : Fin d.n) :
      (inclusion j).hom.hom ((f ≫ projection j).hom.hom x) ∈
        Module.jacobson Aᵐᵒᵖ P := by
    exact Module.map_jacobson_le (inclusion j).hom.hom
      (Submodule.mem_map_of_mem
        (hcomponent j (LinearMap.mem_range_self _ x)))
  have hdecomp : f.hom.hom x =
      ∑ j, (inclusion j).hom.hom ((f ≫ projection j).hom.hom x) := by
    have htotal : ∑ j, projection j ≫ inclusion j = 𝟙 P := by
      calc
        ∑ j, projection j ≫ inclusion j =
            d.isoBiproduct.hom ≫
              (∑ j, biproduct.π d.summand j ≫
                biproduct.ι d.summand j) ≫ d.isoBiproduct.inv := by
          simp only [projection, inclusion, Category.assoc,
            Preadditive.comp_sum, Preadditive.sum_comp]
        _ = 𝟙 P := by rw [biproduct.total]; simp
    have hfTotal : ∑ j, f ≫ projection j ≫ inclusion j = f := by
      rw [← Preadditive.comp_sum, htotal, Category.comp_id]
    have hsumApply :
        ((∑ j, f ≫ projection j ≫ inclusion j).hom.hom) x =
          ∑ j, (f ≫ projection j ≫ inclusion j).hom.hom x := by
      have hmap :
          (∑ j, f ≫ projection j ≫ inclusion j).hom =
            ∑ j, (f ≫ projection j ≫ inclusion j).hom :=
        map_sum
          (InducedCategory.homAddEquiv :
            (X ⟶ P) ≃+ (X.obj ⟶ P.obj))
          (fun j ↦ f ≫ projection j ≫ inclusion j) Finset.univ
      rw [hmap, ModuleCat.hom_sum]
      exact LinearMap.sum_apply _ _ x
    have happ := congrArg (fun g : X ⟶ P ↦ g.hom.hom x) hfTotal
    rw [hsumApply] at happ
    simpa only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply] using happ.symm
  rw [hdecomp]
  exact Submodule.sum_mem _ (fun j _ ↦ hterm j)

/-- A map from an indecomposable nonprojective finitely generated module
which factors through an arbitrary projective in the ambient module category
has radical image.  The ambient factorization is first lifted through a
finite free epimorphism onto the target. -/
theorem range_le_jacobson_of_factorsThroughProjective
    {X Y : RightModule.FinitelyGeneratedCategory A}
    (hX : Indecomposable X) (hXnonprojective : ¬ Projective X)
    {f : X ⟶ Y}
    (hfactor : ProjectiveStable.FactorsThroughProjective f.hom) :
    LinearMap.range f.hom.hom ≤ Module.jacobson Aᵐᵒᵖ Y := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Aᵐᵒᵖ Y
  let F : RightModule.FinitelyGeneratedCategory A :=
    FGModuleCat.of Aᵐᵒᵖ (Fin n → Aᵐᵒᵖ)
  let q : F ⟶ Y := FGModuleCat.ofHom p
  have hF : Projective F := by
    apply fgProjective_of_moduleProjective F
    exact Module.Projective.of_basis (Pi.basisFun Aᵐᵒᵖ (Fin n))
  letI : Epi q.hom := (ModuleCat.epi_iff_surjective q.hom).mpr hp
  letI : Projective hfactor.middle := hfactor.projective
  obtain ⟨l, hl⟩ := Projective.factors hfactor.right q.hom
  let a : X ⟶ F := FGModuleCat.ofHom (hfactor.left ≫ l).hom
  have haf : a.hom ≫ q.hom = f.hom := by
    calc
      a.hom ≫ q.hom = hfactor.left ≫ l ≫ q.hom := rfl
      _ = hfactor.left ≫ hfactor.right := by rw [hl]
      _ = f.hom := hfactor.fac
  have ha : LinearMap.range a.hom.hom ≤ Module.jacobson Aᵐᵒᵖ F :=
    range_le_jacobson_of_map_to_fgProjective
      (k := k) hX hXnonprojective hF a
  rintro _ ⟨x, rfl⟩
  have hax : a.hom.hom x ∈ Module.jacobson Aᵐᵒᵖ F :=
    ha (LinearMap.mem_range_self _ x)
  have hqx : q.hom.hom (a.hom.hom x) ∈ Module.jacobson Aᵐᵒᵖ Y :=
    Module.map_jacobson_le q.hom.hom (Submodule.mem_map_of_mem hax)
  have happ := congrArg (fun g : X.obj ⟶ Y.obj ↦ g.hom x) haf
  simpa only [Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply] using
    happ ▸ hqx

end MagnitudeConjecture
