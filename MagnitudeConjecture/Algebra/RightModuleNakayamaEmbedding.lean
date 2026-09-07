import MagnitudeConjecture.Algebra.RightModuleNakayamaHom
import MagnitudeConjecture.CategoryTheory.ProjectiveDimensionBiproduct
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# Finite Nakayama evaluation embeddings

Let `P` be a finite projective right module and `Y` a finite right module.
Finite-dimensional Nakayama--Hom duality identifies maps

`Y ⟶ νP`

with linear functionals on `Hom(P,Y)`.  Choosing the coordinate functionals
of a basis therefore gives a canonical finite family of maps from `Y` to
copies of the injective module `νP`.  Its kernel is the largest submodule of
`Y` invisible to `P`.

This is the finite, explicit replacement for an arbitrary injective-envelope
construction in Iyama's saturation argument.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]

variable (P Y : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]

/-- The chosen finite basis of `Hom(P,Y)`. -/
abbrev nakayamaEmbeddingHomBasis :
    Module.Basis (Fin (Module.finrank k (P ⟶ Y))) k (P ⟶ Y) :=
  Module.finBasis k (P ⟶ Y)

/-- The map `Y ⟶ νP` corresponding to one coordinate functional on
`Hom(P,Y)`. -/
def nakayamaEmbeddingCoordinateMap
    (i : Fin (Module.finrank k (P ⟶ Y))) :
    Y ⟶ projectiveNakayamaFGObj (k := k) P :=
  (fieldNakayamaHomEquiv (k := k) P Y).symm
    ((nakayamaEmbeddingHomBasis (k := k) P Y).coord i)

/-- The simultaneous evaluation map into a finite product of copies of
`νP`. -/
def nakayamaEmbeddingMap :
    Y →ₗ[Bᵐᵒᵖ]
      (Fin (Module.finrank k (P ⟶ Y)) →
        projectiveNakayamaFGObj (k := k) P) where
  toFun y i :=
    (nakayamaEmbeddingCoordinateMap (k := k) P Y i).hom.hom y
  map_add' y z := by
    funext i
    exact map_add _ _ _
  map_smul' b y := by
    funext i
    exact map_smul _ _ _

@[simp]
theorem nakayamaEmbeddingMap_apply
    (y : Y) (i : Fin (Module.finrank k (P ⟶ Y))) :
    nakayamaEmbeddingMap (k := k) P Y y i =
      (nakayamaEmbeddingCoordinateMap (k := k) P Y i).hom.hom y :=
  rfl

/-- Every map from `P` to the kernel of simultaneous Nakayama evaluation
is zero. -/
theorem hom_to_nakayamaEmbeddingKernel_eq_zero :
    ∀ f : P ⟶ FGModuleCat.of Bᵐᵒᵖ
      (LinearMap.ker (nakayamaEmbeddingMap (k := k) P Y)),
      f = 0 := by
  intro f
  let K := LinearMap.ker (nakayamaEmbeddingMap (k := k) P Y)
  let j : FGModuleCat.of Bᵐᵒᵖ K ⟶ Y :=
    FGModuleCat.ofHom K.subtype
  have hfj : f ≫ j = 0 := by
    apply (nakayamaEmbeddingHomBasis (k := k) P Y).ext_elem
    intro i
    have hja : j ≫ nakayamaEmbeddingCoordinateMap (k := k) P Y i = 0 := by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      have hz := z.2
      change nakayamaEmbeddingMap (k := k) P Y z.1 = 0 at hz
      have hzi := congrFun hz i
      exact hzi
    have hcoord :
        (nakayamaEmbeddingHomBasis (k := k) P Y).coord i (f ≫ j) = 0 := by
      calc
        (nakayamaEmbeddingHomBasis (k := k) P Y).coord i (f ≫ j) =
            fieldNakayamaHomEquiv (k := k) P Y
              (nakayamaEmbeddingCoordinateMap (k := k) P Y i) (f ≫ j) := by
          symm
          exact LinearMap.congr_fun
            ((fieldNakayamaHomEquiv (k := k) P Y).apply_symm_apply
              ((nakayamaEmbeddingHomBasis (k := k) P Y).coord i))
            (f ≫ j)
        _ = fieldNakayamaHomEquiv (k := k) P (FGModuleCat.of Bᵐᵒᵖ K)
            (j ≫ nakayamaEmbeddingCoordinateMap (k := k) P Y i) f := by
          symm
          exact fieldNakayamaHomEquiv_naturality
            (k := k) P j
              (nakayamaEmbeddingCoordinateMap (k := k) P Y i) f
        _ = 0 := by simp [hja]
    simpa using hcoord
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  have hp := congrArg (fun q : P ⟶ Y ↦ q.hom.hom p) hfj
  exact hp

/-- If `Y` has no nonzero submodule invisible to `P`, simultaneous
Nakayama evaluation embeds `Y` into a finite product of copies of `νP`. -/
theorem nakayamaEmbeddingMap_injective
    (hvisible : ∀ N : Submodule Bᵐᵒᵖ Y,
      (∀ f : P ⟶ FGModuleCat.of Bᵐᵒᵖ N, f = 0) → N = ⊥) :
    Function.Injective (nakayamaEmbeddingMap (k := k) P Y) := by
  rw [← LinearMap.ker_eq_bot]
  exact hvisible _ (hom_to_nakayamaEmbeddingKernel_eq_zero
    (k := k) P Y)

omit [IsNoetherianRing Bᵐᵒᵖ] [Projective P] in
/-- A finite product of copies of `νP` has projective dimension at most
one whenever `νP` does. -/
theorem nakayamaEmbeddingTarget_projectiveDimensionLE_one
    (hnu : HasProjectiveDimensionLE
      (ModuleCat.of Bᵐᵒᵖ (projectiveNakayamaFGObj (k := k) P)) 1) :
    HasProjectiveDimensionLE
      (ModuleCat.of Bᵐᵒᵖ
        (Fin (Module.finrank k (P ⟶ Y)) →
          projectiveNakayamaFGObj (k := k) P)) 1 := by
  let F : Fin (Module.finrank k (P ⟶ Y)) → ModuleCat.{u} Bᵐᵒᵖ :=
    fun _ ↦ ModuleCat.of Bᵐᵒᵖ (projectiveNakayamaFGObj (k := k) P)
  have hsum : HasProjectiveDimensionLE (⨁ F) 1 :=
    MagnitudeConjecture.CategoryTheory.hasProjectiveDimensionLT_biproduct
      F 2 (fun _ ↦ hnu)
  letI : HasProjectiveDimensionLE (⨁ F) 1 := hsum
  exact hasProjectiveDimensionLT_of_iso
    (ModuleCat.biproductIsoPi F) 2

end MagnitudeConjecture.RightModule
