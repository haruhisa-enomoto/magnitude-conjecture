import MagnitudeConjecture.Algebra.RightModuleGabrielBetaComparison
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.IrreducibleAbelian
import MagnitudeConjecture.CategoryTheory.IrreducibleKernelFactorization

/-!
# Quotients by irreducible submodules of indecomposable projectives

This file packages the categorical initialization of Auslander--Reiten
Corollary 3.8.  An irreducible morphism into a projective cannot be epic, so
it is monic.  Its cokernel is a nonzero quotient of an indecomposable
projective and hence is indecomposable.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- An irreducible morphism into a projective object is monic. -/
theorem irreducibleIntoProjective_mono
    {U P : RightModule.FinitelyGeneratedCategory A}
    (g : U ⟶ P) (hg : IsIrreducibleMorphism g) (hP : Projective P) :
    Mono g := by
  rcases hg.mono_or_epi with hmono | hepi
  · exact hmono
  · letI : Epi g := hepi
    letI : Projective P := hP
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 P) g
    exact False.elim (hg.not_isSplitEpi
      (IsSplitEpi.mk' { section_ := s, id := hs }))

/-- A map into the cokernel of an irreducible inclusion into a projective
which does not lift to that projective contains the cokernel projection as a
factor.  This is the projective-cokernel form of the pullback argument in
Auslander--Reiten IV, Proposition 2.7. -/
theorem irreducibleIntoProjective_cokernel_factorization
    {U X : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) (h : X ⟶ cokernel g)
    (hnot : ¬ ∃ l : X ⟶ S.fgObj p, l ≫ cokernel.π g = h) :
    ∃ r : S.fgObj p ⟶ X, r ≫ h = cokernel.π g := by
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  let T := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have hT : T.Exact := T.exact_of_g_is_cokernel (cokernelIsCokernel g)
  exact exists_factor_thru_of_not_exists_lift_of_irreducible_kernel
      g (cokernel.π g) (cokernel.condition g) hT.fIsKernel hg h hnot

/-- The cokernel of an irreducible morphism into a projective is nonzero. -/
theorem irreducibleIntoProjective_cokernel_not_isZero
    {U P : RightModule.FinitelyGeneratedCategory A}
    (g : U ⟶ P) (hg : IsIrreducibleMorphism g) (hP : Projective P) :
    ¬ IsZero (cokernel g) := by
  intro hzero
  have hπ : cokernel.π g = 0 := hzero.eq_of_tgt _ _
  letI : Epi g := Abelian.epi_of_cokernel_π_eq_zero g hπ
  letI : Projective P := hP
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 P) g
  exact hg.not_isSplitEpi
    (IsSplitEpi.mk' { section_ := s, id := hs })

/-- If the target is a selected indecomposable projective, the cokernel of
an irreducible morphism into it is indecomposable. -/
theorem irreducibleIntoProjective_cokernel_indecomposable
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    Indecomposable (cokernel g) := by
  have htop : IsSimpleModule Aᵐᵒᵖ
      (S.fgObj p ⧸ Module.jacobson Aᵐᵒᵖ (S.fgObj p)) :=
    isSimpleModule_iff_isCoatom.mpr
      (S.projectiveBoundary_jacobson_isCoatom p hp)
  exact MagnitudeConjecture.indecomposable_of_epi_from_simpleTop
    (k := k) (A := A)
    (S.fgObj p) (cokernel g) htop
    (irreducibleIntoProjective_cokernel_not_isZero g hg hp)
    (cokernel.π g)

/-- The canonical projective quotient is right minimal. -/
theorem irreducibleIntoProjective_cokernelπ_isRightMinimal
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    IsRightMinimal (cokernel.π g) := by
  letI : IsLocalRing (End (S.fgObj p)) :=
    S.fgObj_end_isLocalRing p
  apply isRightMinimal_of_localEnd_of_ne_zero
  intro hzero
  exact (irreducibleIntoProjective_cokernel_not_isZero g hg hp)
    (IsZero.of_epi_eq_zero (cokernel.π g) hzero)

/-- The cokernel projection, bundled as the minimal projective presentation
of the quotient. -/
def irreducibleIntoProjective_cokernelProjectivePresentation
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    MinimalProjectivePresentation (cokernel g) where
  p := S.fgObj p
  projective := hp
  f := cokernel.π g
  epi := inferInstance
  rightMinimal :=
    S.irreducibleIntoProjective_cokernelπ_isRightMinimal p g hg hp

/-- The quotient cannot itself be projective, since otherwise its defining
short exact sequence would split and the irreducible inclusion would be a
section. -/
theorem irreducibleIntoProjective_cokernel_not_projective
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    ¬ Projective (cokernel g) := by
  intro hC
  letI : Projective (cokernel g) := hC
  letI : Mono g := irreducibleIntoProjective_mono g hg hp
  let q := cokernel.π g
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 (cokernel g)) q
  let T := ShortComplex.mk g q (cokernel.condition g)
  have hT : T.Exact := T.exact_of_g_is_cokernel (cokernelIsCokernel g)
  let splitting : T.Splitting :=
    ShortComplex.Splitting.ofExactOfSection T hT s hs inferInstance
  exact hg.not_isSplitMono
    (IsSplitMono.mk' { retraction := splitting.r, id := splitting.f_r })

/-- The selected label of the indecomposable quotient. -/
noncomputable def irreducibleIntoProjective_cokernelLabel
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) : Fin S.n :=
  Classical.choose (S.fgObj_complete (cokernel g)
    (S.irreducibleIntoProjective_cokernel_indecomposable p g hg hp))

/-- The quotient in the coordinates of the chosen finite skeleton. -/
noncomputable def irreducibleIntoProjective_cokernelIso
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    cokernel g ≅ S.fgObj
      (S.irreducibleIntoProjective_cokernelLabel p g hg hp) :=
  Classical.choice (Classical.choose_spec (S.fgObj_complete (cokernel g)
    (S.irreducibleIntoProjective_cokernel_indecomposable p g hg hp)))

/-- The canonical projective quotient map in the chosen skeleton
coordinates. -/
noncomputable def irreducibleIntoProjective_quotientMap
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    S.fgObj p ⟶ S.fgObj
      (S.irreducibleIntoProjective_cokernelLabel p g hg hp) :=
  cokernel.π g ≫
    (S.irreducibleIntoProjective_cokernelIso p g hg hp).hom

instance irreducibleIntoProjective_quotientMap_epi
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    Epi (S.irreducibleIntoProjective_quotientMap p g hg hp) := by
  dsimp only [irreducibleIntoProjective_quotientMap]
  infer_instance

@[reassoc]
theorem irreducibleIntoProjective_comp_quotientMap
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    g ≫ S.irreducibleIntoProjective_quotientMap p g hg hp = 0 := by
  dsimp only [irreducibleIntoProjective_quotientMap]
  rw [← Category.assoc, cokernel.condition, zero_comp]

/-- The selected quotient label is nonprojective. -/
theorem irreducibleIntoProjective_quotientLabel_not_projective
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    ¬ Projective (S.fgObj
      (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) := by
  intro hQ
  have hC : Projective (cokernel g) :=
    Projective.of_iso
      (S.irreducibleIntoProjective_cokernelIso p g hg hp).symm hQ
  exact S.irreducibleIntoProjective_cokernel_not_projective p g hg hp hC

/-- The selected projective quotient remains right minimal. -/
theorem irreducibleIntoProjective_quotientMap_isRightMinimal
    {U : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (g : U ⟶ S.fgObj p) (hg : IsIrreducibleMorphism g)
    (hp : Projective (S.fgObj p)) :
    IsRightMinimal
      (S.irreducibleIntoProjective_quotientMap p g hg hp) := by
  exact (S.irreducibleIntoProjective_cokernelπ_isRightMinimal p g hg hp).postcomp_iso
    (S.irreducibleIntoProjective_cokernelIso p g hg hp)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
