import MagnitudeConjecture.Algebra.RightModuleStandardFormRiedtmannDuality
import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshExtVanishing
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleInjectiveEnvelope
import MagnitudeConjecture.CategoryTheory.InjectivePresentationExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Minimal injective resolutions over the standard mesh category

Every finite contravariant module over the standard mesh category has a
two-step minimal injective presentation.  In particular, each contravariant
representable has a chosen exact complex `Pₓ ⟶ I₀ ⟶ I₁` whose two injective
maps are essential.  These are the objects whose indecomposable summands are
identified by the Bongartz--Gabriel socle and degree-one Ext arguments.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormInjectiveResolutionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormInjectiveResolutionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormInjectiveResolutionDoubleOppositeFintype :
    Fintype
      ((S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ)ᵒᵖ) :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

/-- Representables on the opposite of the opposite vertex category are
finite-dimensional.  This is the hypothesis needed to construct injective
envelopes in the category of contravariant standard-mesh modules. -/
theorem standardFormFiniteDoubleOppositeRepresentables :
    ∀ X : (S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ)ᵒᵖ,
      IsFiniteDimensionalModule
        (C := (S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ)ᵒᵖ) k
        (linearCoyonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k (Y.unop ⟶ X.unop) := by
      letI : FiniteDimensional k
          (MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop.unop ⟶
            MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.unop) :=
        S.standardFormMeshHomFinite
          (MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop.unop)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.unop)
      letI : FiniteDimensional k (X.unop.unop ⟶ Y.unop.unop) :=
        FiniteDimensional.of_injective
          InducedCategory.homLinearEquiv.toLinearMap
          InducedCategory.homLinearEquiv.injective
      exact FiniteDimensional.of_injective
        (oppositeHomLinearEquiv Y.unop X.unop).toLinearMap
        (oppositeHomLinearEquiv Y.unop X.unop).injective
    exact FiniteDimensional.of_injective
      (oppositeHomLinearEquiv X Y).toLinearMap
      (oppositeHomLinearEquiv X Y).injective
  · exact Set.toFinite _

/-- Every finite contravariant standard-mesh module admits a two-step
minimal injective presentation. -/
theorem standardFormFiniteContravariantModule_twoStepMinimalInjectivePresentation_nonempty
    (M : FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k) :
    Nonempty (TwoStepMinimalInjectivePresentation M) :=
  finiteDimensionalModule_twoStepMinimalInjectivePresentation_nonempty
    S.standardFormFiniteDoubleOppositeRepresentables M

/-- A chosen minimal two-step injective presentation of the contravariant
representable at a standard-mesh vertex. -/
noncomputable def standardFormContravariantRepresentableMinimalInjectivePresentation
    (x : Fin S.n) :
    TwoStepMinimalInjectivePresentation
      (S.standardFormRightMeshData.contravariantRepresentableFiniteModule
        (k := k) S.standardFormFiniteContravariantRepresentables x) :=
  Classical.choice
    (S.standardFormFiniteContravariantModule_twoStepMinimalInjectivePresentation_nonempty
      (S.standardFormRightMeshData.contravariantRepresentableFiniteModule
        (k := k) S.standardFormFiniteContravariantRepresentables x))

/-- The degree-zero injective term in the chosen minimal presentation. -/
abbrev standardFormContravariantRepresentableInjectiveTermZero (x : Fin S.n) :=
  (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).augmentation.J

/-- The degree-one injective term in the chosen minimal presentation. -/
abbrev standardFormContravariantRepresentableInjectiveTermOne (x : Fin S.n) :=
  (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).cosyzygyPresentation.J

instance standardFormContravariantRepresentableInjectiveTermZero_injective
    (x : Fin S.n) :
    Injective (S.standardFormContravariantRepresentableInjectiveTermZero x) :=
  inferInstance

instance standardFormContravariantRepresentableInjectiveTermOne_injective
    (x : Fin S.n) :
    Injective (S.standardFormContravariantRepresentableInjectiveTermOne x) :=
  inferInstance

/-- The chosen representable-to-injective map is an essential
monomorphism. -/
theorem standardFormContravariantRepresentableInjectiveTermZero_essential
    (x : Fin S.n) :
    IsEssentialMono
      (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).augmentation.f :=
  (finiteDimensionalModule_isEssentialMono_iff_isLeftMinimal
    (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).augmentation.f).2
      (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).augmentation.leftMinimal

/-- The chosen first-cosyzygy-to-injective map is an essential
monomorphism. -/
theorem standardFormContravariantRepresentableInjectiveTermOne_essential
    (x : Fin S.n) :
    IsEssentialMono
      (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).cosyzygyPresentation.f :=
  (finiteDimensionalModule_isEssentialMono_iff_isLeftMinimal
    (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).cosyzygyPresentation.f).2
      (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).cosyzygyPresentation.leftMinimal

/-- The chosen complex `Pₓ ⟶ I₀ ⟶ I₁` is exact. -/
theorem standardFormContravariantRepresentableMinimalInjectivePresentation_exact
    (x : Fin S.n) :
    (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).presentationComplex.Exact :=
  (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).presentationComplex_exact

/-- A nonzero map from a mesh simple into a standard contravariant
representable can only start at a projective vertex. -/
theorem standardForm_mem_projective_of_nonzero_map_simple_to_contravariantRepresentable
    {z y : Fin S.n}
    (f : S.standardFormRightMeshData.simpleFiniteModule (k := k) z ⟶
      S.standardFormRightMeshData.contravariantRepresentableFiniteModule
        (k := k) S.standardFormFiniteContravariantRepresentables y)
    (hf : f ≠ 0) :
    z ∈ S.standardFormProjectiveSet :=
  S.standardFormRightMeshData.mem_projective_of_nonzero_map_simple_to_contravariantRepresentable
    (k := k) S.standardFormFiniteContravariantRepresentables
    S.standardFormRiedtmannConditionB f hf

/-- The degree-zero injective term in the minimal injective presentation of
a contravariant representable is projective. -/
theorem standardFormContravariantRepresentableInjectiveTermZero_projective
    (x : Fin S.n) :
    Projective (S.standardFormContravariantRepresentableInjectiveTermZero x) := by
  apply S.standardFormFiniteContravariantInjective_projective_of_conditionC_coordinates
  intro N hN hNinjective i r hir
  letI : Injective N := hNinjective
  obtain ⟨X, ⟨e⟩⟩ :=
    indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
      S.standardFormFiniteContravariantDualCorepresentables
      S.standardFormOppositeVertexCategoryEndLocal N hN
  rcases X with ⟨p⟩
  letI hiSplit : IsSplitMono i :=
    IsSplitMono.mk' { retraction := r, id := hir }
  letI hi : Mono i := inferInstance
  let a := (S.standardFormContravariantDualSocleIsoSimple p).inv ≫
    S.standardFormContravariantDualSocleInclusion (k := k) p
  let b := e.hom ≫ i
  haveI ha : Mono a := by
    dsimp only [a]
    exact mono_comp _ _
  haveI hb : Mono b := by
    dsimp only [b]
    exact mono_comp _ _
  let s : S.standardFormRightMeshData.simpleFiniteModule (k := k) p ⟶
      S.standardFormContravariantRepresentableInjectiveTermZero x :=
    a ≫ b
  haveI hsMono : Mono s := by
    dsimp only [s]
    exact @mono_comp _ _ _ _ _ a ha b hb
  have hs : s ≠ 0 := by
    intro hzero
    apply S.standardFormContravariantDualSocleInclusion_ne_zero p
    apply (cancel_epi (S.standardFormContravariantDualSocleIsoSimple p).inv).1
    apply (cancel_mono b).1
    calc
      ((S.standardFormContravariantDualSocleIsoSimple p).inv ≫
          S.standardFormContravariantDualSocleInclusion (k := k) p) ≫ b =
        s := by rfl
      _ = 0 := hzero
      _ = ((S.standardFormContravariantDualSocleIsoSimple p).inv ≫ 0) ≫ b := by
        simp
  obtain ⟨t, ht⟩ := exists_factor_thru_of_isEssentialMono_of_simple
    (S.standardFormContravariantRepresentableMinimalInjectivePresentation x).augmentation.f
    (S.standardFormContravariantRepresentableInjectiveTermZero_essential x)
    s hs
  have ht_ne : t ≠ 0 := by
    intro hzero
    apply hs
    rw [← ht, hzero]
    simp
  have hp : p ∈ S.standardFormProjectiveSet :=
    S.standardForm_mem_projective_of_nonzero_map_simple_to_contravariantRepresentable
      t ht_ne
  exact ⟨⟨p, (S.mem_standardFormProjectiveSet_iff p).1 hp⟩, ⟨e⟩⟩

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
/-- The degree-one injective term in the minimal injective presentation of
a contravariant representable is projective. -/
theorem standardFormContravariantRepresentableInjectiveTermOne_projective
    (x : Fin S.n) :
    Projective (S.standardFormContravariantRepresentableInjectiveTermOne x) := by
  let T := S.standardFormRightMeshData
  let hP := S.standardFormFiniteContravariantRepresentables
  let I := S.standardFormContravariantRepresentableMinimalInjectivePresentation x
  letI : EnoughProjectives (FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : HasExt.{u} (FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  apply S.standardFormFiniteContravariantInjective_projective_of_conditionC_coordinates
  intro N hN hNinjective i r hir
  change N ⟶ I.cosyzygyPresentation.J at i
  change I.cosyzygyPresentation.J ⟶ N at r
  letI : Injective N := hNinjective
  obtain ⟨X, ⟨e⟩⟩ :=
    indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
      S.standardFormFiniteContravariantDualCorepresentables
      S.standardFormOppositeVertexCategoryEndLocal N hN
  rcases X with ⟨p⟩
  letI hiSplit : IsSplitMono i :=
    IsSplitMono.mk' { retraction := r, id := hir }
  letI hi : Mono i := inferInstance
  let a := (S.standardFormContravariantDualSocleIsoSimple p).inv ≫
    S.standardFormContravariantDualSocleInclusion (k := k) p
  let b := e.hom ≫ i
  haveI ha : Mono a := by
    dsimp only [a]
    exact mono_comp _ _
  haveI hb : Mono b := by
    dsimp only [b]
    exact mono_comp _ _
  let s : T.simpleFiniteModule (k := k) p ⟶ I.cosyzygyPresentation.J :=
    a ≫ b
  have hs : s ≠ 0 := by
    intro hzero
    change a ≫ b = 0 at hzero
    have haZero : a = 0 := by
      apply (cancel_mono b).1
      simpa only [zero_comp] using hzero
    apply S.standardFormContravariantDualSocleInclusion_ne_zero p
    apply (cancel_epi (S.standardFormContravariantDualSocleIsoSimple p).inv).1
    change a = (S.standardFormContravariantDualSocleIsoSimple p).inv ≫ 0
    rw [haZero]
    simp
  letI hsMono : Mono s := mono_of_nonzero_from_simple hs
  obtain ⟨t, ht⟩ := exists_factor_thru_of_isEssentialMono_of_simple
    I.cosyzygyPresentation.f
    (S.standardFormContravariantRepresentableInjectiveTermOne_essential x)
    s hs
  change T.simpleFiniteModule (k := k) p ⟶ cokernel I.augmentation.f at t
  have ht_ne : t ≠ 0 := by
    intro hzero
    apply hs
    rw [← ht, hzero]
    simp
  have hp : p ∈ S.standardFormProjectiveSet := by
    by_contra hp
    let z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} := ⟨p, hp⟩
    letI : Subsingleton
        (Ext.{u} (T.simpleFiniteModule (k := k) p)
          (T.contravariantRepresentableFiniteModule (k := k) hP x) 1) :=
      S.standardFormSimple_extOne_contravariantRepresentable_subsingleton
        hP z x
    exact ht_ne
      (InjectivePresentationExt.simple_to_cokernel_eq_zero_of_extOne_subsingleton
        I.augmentation.f
        (S.standardFormContravariantRepresentableInjectiveTermZero_essential x)
        t)
  exact ⟨⟨p, (S.mem_standardFormProjectiveSet_iff p).1 hp⟩, ⟨e⟩⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
