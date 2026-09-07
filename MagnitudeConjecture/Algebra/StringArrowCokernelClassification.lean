import MagnitudeConjecture.Algebra.StringArrowCokernel

/-!
# Classification of string-arrow cokernels

For a displayed arrow `a : x ⟶ y`, the quotient `V(a)` has the literal
two-step minimal projective presentation

`P(x) ⟶ P(y) ⟶ V(a)`.

Uniqueness of minimal projective covers therefore turns an isomorphism
`V(a) ≅ V(b)` into an invertible square between the two represented arrow
maps.  Passing back through the fully faithful category-algebra realization
and reducing modulo paths of length at least two recovers the displayed
arrow.  Thus the Butler--Ringel modules `V(a)` are pairwise nonisomorphic.
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

noncomputable local instance arrowClassificationAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowClassificationAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The represented projective morphism induced by a displayed arrow. -/
def representedArrowHom
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.representedVertexModule x ⟶ P.representedVertexModule y :=
  ConcreteCategory.ofHom (P.representedArrowLinearMap a)

theorem representedArrowHom_hom
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (P.representedArrowHom a).hom.hom =
      P.representedArrowLinearMap a :=
  rfl

/-- The represented arrow map is killed by the canonical projection onto
its cokernel. -/
theorem representedArrowHom_comp_arrowCokernelProjectionHom
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.representedArrowHom a ≫ P.arrowCokernelProjectionHom a = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (P.arrowCokernelSubmodule a).mkQ
      (P.representedArrowLinearMap a z) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨z, rfl⟩

/-- The arrow map, corestricted to the categorical kernel of its cokernel
projection. -/
def arrowCokernelKernelCoverHom
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.representedVertexModule x ⟶
      kernel (P.arrowCokernelProjectionHom a) :=
  kernel.lift (P.arrowCokernelProjectionHom a)
    (P.representedArrowHom a)
    (P.representedArrowHom_comp_arrowCokernelProjectionHom a)

@[reassoc]
theorem arrowCokernelKernelCoverHom_comp_kernel_ι
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.arrowCokernelKernelCoverHom a ≫
        kernel.ι (P.arrowCokernelProjectionHom a) =
      P.representedArrowHom a :=
  kernel.lift_ι _ _ _

/-- The represented source projective surjects onto the kernel of the
canonical projection onto `V(a)`. -/
theorem arrowCokernelKernelCoverHom_surjective
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Function.Surjective (P.arrowCokernelKernelCoverHom a).hom.hom := by
  intro z
  let q := P.arrowCokernelProjectionHom a
  have hzzero :
      q.hom.hom ((kernel.ι q).hom.hom z) = 0 := by
    have h := congrArg (fun f : kernel q ⟶ P.arrowCokernelFGObj a ↦
      f.hom.hom z) (kernel.condition q)
    exact h
  have hzmem :
      (kernel.ι q).hom.hom z ∈ P.arrowCokernelSubmodule a := by
    rw [← P.arrowCokernelProjection_ker a, LinearMap.mem_ker]
    exact hzzero
  obtain ⟨w, hw⟩ := hzmem
  refine ⟨w, ?_⟩
  apply
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective
      (kernel.ι q)).1 inferInstance
  have h := congrArg
    (fun f : P.representedVertexModule x ⟶ P.representedVertexModule y ↦
      f.hom.hom w)
    (P.arrowCokernelKernelCoverHom_comp_kernel_ι a)
  have h' :
      (kernel.ι q).hom.hom
          ((P.arrowCokernelKernelCoverHom a).hom.hom w) =
        P.representedArrowLinearMap a w := by
    rw [← P.representedArrowHom_hom a]
    simpa [q] using h
  rw [h']
  exact hw

/-- The represented morphism of a displayed arrow is nonzero. -/
theorem representedArrowHom_ne_zero
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.representedArrowHom a ≠ 0 := by
  intro hzero
  have hlinearZero : P.representedArrowLinearMap a = 0 := by
    rw [← P.representedArrowHom_hom a]
    exact congrArg (fun f : P.representedVertexModule x ⟶
      P.representedVertexModule y ↦ f.hom.hom) hzero
  apply P.arrowCokernelSubmodule_ne_bot a
  apply LinearMap.range_eq_bot.mpr
  exact hlinearZero

/-- The induced cover of the kernel is nonzero. -/
theorem arrowCokernelKernelCoverHom_ne_zero
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.arrowCokernelKernelCoverHom a ≠ 0 := by
  intro hzero
  apply P.representedArrowHom_ne_zero a
  rw [← P.arrowCokernelKernelCoverHom_comp_kernel_ι a, hzero,
    zero_comp]

instance arrowCokernelKernelCoverHom_epi
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Epi (P.arrowCokernelKernelCoverHom a) :=
  (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
    (P.arrowCokernelKernelCoverHom a)).2
      (P.arrowCokernelKernelCoverHom_surjective a)

/-- The represented source projective is the projective cover of the first
syzygy of `V(a)`. -/
theorem arrowCokernelKernelCoverHom_isRightMinimal
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    IsRightMinimal (P.arrowCokernelKernelCoverHom a) := by
  letI : IsLocalRing
      (Module.End P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule x)) :=
    P.representedVertexModuleEnd_isLocalRing x
  letI : IsLocalRing (End (P.representedVertexModule x)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (RightModule.FiniteIndecomposableSkeleton.fgEndModuleEndRingEquiv
        (P.representedVertexModule x)).symm
  exact isRightMinimal_of_localEnd_of_ne_zero
    (P.arrowCokernelKernelCoverHom a)
      (P.arrowCokernelKernelCoverHom_ne_zero a)

/-- The minimal projective cover of the first syzygy of `V(a)`. -/
def arrowCokernelKernelMinimalProjectivePresentation
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    MinimalProjectivePresentation
      (kernel (P.arrowCokernelProjectionHom a)) where
  p := P.representedVertexModule x
  f := P.arrowCokernelKernelCoverHom a
  projective := P.representedVertexModule_projective x
  epi := inferInstance
  rightMinimal := P.arrowCokernelKernelCoverHom_isRightMinimal a

/-- The literal two-step minimal projective presentation
`P(x) ⟶ P(y) ⟶ V(a)`. -/
def arrowCokernelTwoStepMinimalProjectivePresentation
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    TwoStepMinimalProjectivePresentation (P.arrowCokernelFGObj a) where
  augmentation := P.arrowCokernelMinimalProjectivePresentation a
  syzygyPresentation := P.arrowCokernelKernelMinimalProjectivePresentation a

theorem arrowCokernelTwoStepMinimalProjectivePresentation_differential
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (P.arrowCokernelTwoStepMinimalProjectivePresentation a).differential =
      P.representedArrowHom a :=
  P.arrowCokernelKernelCoverHom_comp_kernel_ι a

/-- An invertible commuting square between represented arrow maps determines
the displayed arrow. -/
theorem arrow_eq_of_representedArrow_iso_square
    (P : StringPresentation k A Q) {x y : Q} (a b : x ⟶ y)
    (ex : P.representedVertexModule x ≅ P.representedVertexModule x)
    (ey : P.representedVertexModule y ≅ P.representedVertexModule y)
    (hcomm :
      ex.hom ≫ P.representedArrowHom b =
        P.representedArrowHom a ≫ ey.hom) :
    a = b := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let F := CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor hP
  let exRepresentable :
      P.quotientRepresentable (obj P.toPresentation.relations x) ≅
        P.quotientRepresentable (obj P.toPresentation.relations x) :=
    F.preimageIso ex
  let eyRepresentable :
      P.quotientRepresentable (obj P.toPresentation.relations y) ≅
      P.quotientRepresentable (obj P.toPresentation.relations y) :=
    F.preimageIso ey
  let daRepresentable := F.preimage (P.representedArrowHom a)
  let dbRepresentable := F.preimage (P.representedArrowHom b)
  have hcommRepresentable :
      exRepresentable.hom ≫ dbRepresentable =
        daRepresentable ≫ eyRepresentable.hom := by
    apply F.map_injective
    simpa [exRepresentable, eyRepresentable, daRepresentable,
      dbRepresentable, F] using hcomm
  have hdaRepresentable :
      daRepresentable = P.arrowRepresentableMap a := by
    apply F.map_injective
    rw [F.map_preimage]
    apply FGModuleCat.hom_ext
    rfl
  have hdbRepresentable :
      dbRepresentable = P.arrowRepresentableMap b := by
    apply F.map_injective
    rw [F.map_preimage]
    apply FGModuleCat.hom_ext
    rfl
  rw [hdaRepresentable, hdbRepresentable] at hcommRepresentable
  let J := CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP
  letI : J.Full := by
    dsimp [J, CoveringHom.finiteDimensionalLinearCoyonedaFunctor,
      CoveringHom.linearCoyonedaLinearModuleFunctor]
    infer_instance
  letI : J.Faithful := by
    dsimp [J, CoveringHom.finiteDimensionalLinearCoyonedaFunctor,
      CoveringHom.linearCoyonedaLinearModuleFunctor]
    infer_instance
  let exOpposite := J.preimageIso exRepresentable
  let eyOpposite := J.preimageIso eyRepresentable
  have hcommOpposite :
      exOpposite.hom ≫
          (arrowMap P.toPresentation.relations b).op =
        (arrowMap P.toPresentation.relations a).op ≫
          eyOpposite.hom := by
    apply J.map_injective
    simpa [exOpposite, eyOpposite, J, arrowRepresentableMap] using
      hcommRepresentable
  have hcommUnop :
      arrowMap P.toPresentation.relations b ≫ exOpposite.unop.hom =
        eyOpposite.unop.hom ≫
          arrowMap P.toPresentation.relations a := by
    simpa using congrArg Quiver.Hom.unop hcommOpposite
  exact (P.arrow_eq_of_iso_square b a exOpposite.unop
    eyOpposite.unop hcommUnop).symm

/-- Butler--Ringel's module attached to a displayed arrow. -/
abbrev displayedArrowCokernelFGObj
    (P : StringPresentation k A Q) (a : DisplayedArrow Q) :=
  P.arrowCokernelFGObj a.2.2

/-- Distinct displayed arrows have nonisomorphic Butler--Ringel cokernels. -/
theorem displayedArrow_eq_of_arrowCokernel_iso
    (P : StringPresentation k A Q) (a b : DisplayedArrow Q)
    (e : P.displayedArrowCokernelFGObj a ≅
      P.displayedArrowCokernelFGObj b) :
    a = b := by
  rcases a with ⟨y, x, a⟩
  rcases b with ⟨y', x', b⟩
  let Ta := P.arrowCokernelTwoStepMinimalProjectivePresentation a
  let Tb := P.arrowCokernelTwoStepMinimalProjectivePresentation b
  let ey : P.representedVertexModule y ≅
      P.representedVertexModule y' :=
    Ta.augmentationObjectIsoOfTargetIso Tb e
  have hyy : y = y' := P.eq_of_representedVertexModule_iso ey
  subst y'
  let ex : P.representedVertexModule x ≅
      P.representedVertexModule x' :=
    Ta.syzygyObjectIsoOfTargetIso Tb e
  have hxx : x = x' := P.eq_of_representedVertexModule_iso ex
  subst x'
  have hcomm :
      ex.hom ≫ P.representedArrowHom b =
        P.representedArrowHom a ≫ ey.hom := by
    have h := Ta.syzygyObjectIsoOfTargetIso_hom_comp_differential Tb e
    have hTa : Ta.differential = P.representedArrowHom a :=
      P.arrowCokernelTwoStepMinimalProjectivePresentation_differential a
    have hTb : Tb.differential = P.representedArrowHom b :=
      P.arrowCokernelTwoStepMinimalProjectivePresentation_differential b
    rw [hTa, hTb] at h
    dsimp [ex, ey]
    exact h
  have hab : a = b :=
    P.arrow_eq_of_representedArrow_iso_square a b ex ey hcomm
  subst b
  rfl

end StringPresentation
end MagnitudeConjecture.BoundQuiver
