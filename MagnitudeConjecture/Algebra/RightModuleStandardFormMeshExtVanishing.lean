import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Mesh Ext vanishing in standard form

The Hom exactness for the standard mesh-simple resolution implies the Ext¹
vanishing used in Bongartz--Gabriel Lemma 2.6(c).
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u w

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshExtFinalQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshExtFinalArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false in
/-- Bongartz--Gabriel Lemma 2.6(c) for the standard-form mesh category:
`Ext¹` from a nonprojective mesh simple to every contravariant representable
vanishes. -/
theorem standardFormSimple_extOne_contravariantRepresentable_subsingleton
    [HasExt.{w} (FiniteDimensionalModuleCategory
      (C := (S.standardFormRightMeshData.VertexCategory (k := k))ᵒᵖ) k)]
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n) :
    Subsingleton
      (Ext.{w}
        (S.standardFormRightMeshData.simpleFiniteModule (k := k) z.1)
        (S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x) 1) := by
  let T := S.standardFormRightMeshData
  let P := T.simplePositiveFiniteShortComplex (k := k) hP z.1
  let R := T.simpleTranslationFiniteShortComplex (k := k) hP z
  let C₀ : ShortComplex (FiniteDimensionalModuleCategory
      (C := (T.VertexCategory (k := k))ᵒᵖ) k) :=
    ShortComplex.mk (Abelian.image.ι P.f) P.g
      (Abelian.image_ι_comp_eq_zero P.zero)
  have hPexact : P.Exact :=
    T.simplePositiveFiniteShortComplex_exact (k := k) hP z.1
  have hC₀ : C₀.ShortExact := by
    letI : Mono C₀.f := by
      dsimp [C₀]
      infer_instance
    letI : Epi C₀.g := by
      change Epi (T.simpleProjectionFinite (k := k) hP z.1)
      infer_instance
    refine { exact := ?_ }
    dsimp [C₀]
    exact ShortComplex.exact_of_f_is_kernel _ hPexact.isLimitImage
  have hP₀ : Projective C₀.X₂ := by
    change Projective
      (T.contravariantRepresentableFiniteModule (k := k) hP z.1)
    infer_instance
  letI : Projective C₀.X₂ := hP₀
  have hzero (xi : Ext.{w} C₀.X₃
      (T.contravariantRepresentableFiniteModule (k := k) hP x) 1) : xi = 0 := by
    obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₃ hC₀
      (T.contravariantRepresentableFiniteModule (k := k) hP x) xi
      (Ext.eq_zero_of_projective _) (rfl : 1 + 0 = 1)
    let aHom : C₀.X₁ ⟶
        T.contravariantRepresentableFiniteModule (k := k) hP x :=
      Ext.addEquiv₀ a
    change Abelian.image P.f ⟶
      T.contravariantRepresentableFiniteModule (k := k) hP x at aHom
    let hIncoming : P.X₁ ⟶
        T.contravariantRepresentableFiniteModule (k := k) hP x :=
      Abelian.factorThruImage P.f ≫ aHom
    have hRPzero : R.f ≫ P.f = 0 := by
      change R.f ≫ R.g = 0
      exact R.zero
    have hh : R.f ≫ hIncoming = 0 := by
      dsimp only [hIncoming]
      rw [← Category.assoc]
      have hfactor : R.f ≫ Abelian.factorThruImage P.f = 0 := by
        apply (cancel_mono (Abelian.image.ι P.f)).1
        rw [Category.assoc, Abelian.image.fac, hRPzero, zero_comp]
      rw [hfactor, zero_comp]
    obtain ⟨b, hb⟩ :=
      S.standardFormSimpleResolution_hom_exact hP z x hIncoming hh
    have hab : C₀.f ≫ b = aHom := by
      change Abelian.image.ι P.f ≫ b = aHom
      apply (cancel_epi (Abelian.factorThruImage P.f)).1
      rw [← Category.assoc, Abelian.image.fac]
      change P.f ≫ b = Abelian.factorThruImage P.f ≫ aHom
      exact hb
    rw [← ha]
    rw [← Ext.mk₀_addEquiv₀_apply a]
    change hC₀.extClass.comp (Ext.mk₀ aHom) (rfl : 1 + 0 = 1) = 0
    rw [← hab]
    rw [← Ext.mk₀_comp_mk₀]
    exact hC₀.extClass_comp_assoc (Ext.mk₀ b)
  constructor
  intro xi eta
  rw [hzero xi, hzero eta]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
