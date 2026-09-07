import MagnitudeConjecture.Algebra.StringArrowCokernelRadical

/-!
# Irreducible morphisms into string-arrow cokernels

For a displayed arrow `a : x ⟶ y`, its range is one direct summand of the
radical of the represented projective `P(y)`.  Projection away from this
summand gives a canonical linear section from the radical of `V(a)` back to
the radical of `P(y)`.  Consequently every proper monomorphism into `V(a)`
lifts through its projective cover.  An irreducible monomorphism would then
split on the left; indecomposability of `P(y)` forces the lift either to vanish
or to split on the right, and both alternatives are impossible.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance arrowIrreducibleAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowIrreducibleAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option maxHeartbeats 1200000 in
/-- No irreducible morphism from a nonzero finite module into `V(a)` can be
monic.  The complement of the killed branch lifts the whole radical of
`V(a)` back to its indecomposable projective cover. -/
theorem not_mono_of_isIrreducibleMorphism_to_arrowCokernel
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {X : FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ} [Nontrivial X]
    (f : X ⟶ P.arrowCokernelFGObj a)
    (hf : IsIrreducibleMorphism f) :
    ¬ Mono f := by
  intro hfMono
  letI : Mono f := hfMono
  let R := P.quotientCategoryAlgebraᵐᵒᵖ
  let T := P.representedVertexModule y
  let V := P.arrowCokernelFGObj a
  let J := Module.jacobson R T
  let JV := Module.jacobson R V
  have hfNotEpi : ¬ Epi f := by
    intro hfEpi
    letI : Epi f := hfEpi
    letI : IsIso f := isIso_of_mono_of_epi f
    exact hf.not_isSplitEpi inferInstance
  have hfrangeNeTop : LinearMap.range f.hom.hom ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective f.hom.hom :=
      LinearMap.range_eq_top.mp htop
    exact hfNotEpi
      ((QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
        f).2 hsurj)
  have hfrangeLe : LinearMap.range f.hom.hom ≤ JV :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
      (P.arrowCokernelFGObj_top_isSimple a) hfrangeNeTop
  let fRadLinear : X →ₗ[R] JV :=
    f.hom.hom.codRestrict JV (fun z =>
      hfrangeLe (LinearMap.mem_range_self f.hom.hom z))
  let fRad : X ⟶ FGModuleCat.of R JV :=
    FGModuleCat.ofHom fRadLinear
  let sectionRad : FGModuleCat.of R JV ⟶
      P.representedVertexRadicalFGObj y :=
    FGModuleCat.ofHom (P.arrowCokernelRadicalSection a)
  let l : X ⟶ T :=
    fRad ≫ sectionRad ≫ P.representedVertexRadicalInclusion y
  have hlf : l ≫ P.arrowCokernelProjectionHom a = f := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change P.arrowCokernelProjection a
        ((P.arrowCokernelRadicalSection a (fRadLinear z)).1) =
      f.hom.hom z
    have hsection := LinearMap.congr_fun
      (P.arrowCokernelRadicalMap_section a) (fRadLinear z)
    exact congrArg Subtype.val hsection
  have hqNotSplit : ¬ IsSplitEpi (P.arrowCokernelProjectionHom a) := by
    intro hsplit
    letI : IsSplitEpi (P.arrowCokernelProjectionHom a) := hsplit
    apply P.arrowCokernelFGObj_not_projective a
    letI : Projective T := P.representedVertexModule_projective y
    let r : Retract V T :=
      { i := section_ (P.arrowCokernelProjectionHom a)
        r := P.arrowCokernelProjectionHom a
        retract := IsSplitEpi.id (P.arrowCokernelProjectionHom a) }
    exact r.projective
  have hlSplit : IsSplitMono l :=
    (hf.factorization l (P.arrowCokernelProjectionHom a) hlf).resolve_right
      hqNotSplit
  letI : IsSplitMono l := hlSplit
  let r : T ⟶ X := retraction l
  let e : End T := r ≫ l
  have he : IsIdempotentElem e := by
    rw [IsIdempotentElem, End.mul_def]
    dsimp only [e, r]
    rw [Category.assoc, ← Category.assoc l (retraction l) l,
      IsSplitMono.id, Category.id_comp]
  have heModule : IsIdempotentElem e.hom.hom :=
    congrArg (fun q : End T => q.hom.hom) he
  have hTind :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R T :=
    IsUniserialModule.isIndecomposableModule_of_simpleTop
      (P.representedVertexModule_top_isSimple y)
  rcases hTind.eq_zero_or_eq_one_of_isIdempotentElem heModule with
      hezeroModule | heoneModule
  · have hlzero : l = 0 := by
      have hle : l ≫ e = l := by
        change l ≫ (r ≫ l) = l
        rw [← Category.assoc, show l ≫ r = 𝟙 X from IsSplitMono.id l,
          Category.id_comp]
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have hpoint := congrArg (fun q : X ⟶ T => q.hom.hom z) hle
      have hepoint := LinearMap.congr_fun hezeroModule (l.hom.hom z)
      exact hpoint.symm.trans hepoint
    have hfzero : f = 0 := by
      rw [← hlf, hlzero, zero_comp]
    have hfinj : Function.Injective f.hom.hom :=
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
        f).1 inferInstance
    have hsub : Subsingleton X := by
      constructor
      intro z w
      apply hfinj
      rw [hfzero]
      rfl
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub
  · have heone : e = 𝟙 T := by
      apply FGModuleCat.hom_ext
      exact heoneModule
    have hrid : r ≫ l = 𝟙 T := heone
    haveI : IsSplitEpi l := IsSplitEpi.mk'
      { section_ := r
        id := hrid }
    haveI : Epi f := by
      rw [← hlf]
      infer_instance
    letI : IsIso f := isIso_of_mono_of_epi f
    exact hf.not_isSplitEpi inferInstance

end StringPresentation
end MagnitudeConjecture.BoundQuiver
