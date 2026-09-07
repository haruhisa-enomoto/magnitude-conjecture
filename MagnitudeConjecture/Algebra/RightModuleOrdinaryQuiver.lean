import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleAlmostSplit
import MagnitudeConjecture.Algebra.RightModuleRadical
import MagnitudeConjecture.CategoryTheory.HomIdealComap
import MagnitudeConjecture.CategoryTheory.LinearPathIdealPower
import MagnitudeConjecture.CategoryTheory.LinearPathLift
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# The ordinary quiver of a finite right-module category

The vertices are the chosen indecomposable projective right modules.  Arrows
from `x` to `y` index a basis of the radical quotient
`rad(P_y,P_x) / rad²(P_y,P_x)` formed inside the full subcategory on those
projectives.  Choosing radical lifts realizes this quiver in the projective
subcategory.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k : Type u} [Field k]
variable {A : Type u} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance restrictedModule (i : Fin S.n) :
    Module k (S.almostSplitSkeleton.obj i) :=
  Module.restrictScalars k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i)

local instance restrictedScalarTower (i : Fin S.n) :
    IsScalarTower k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i) :=
  IsScalarTower.restrictScalars k Aᵐᵒᵖ (S.almostSplitSkeleton.obj i)

local instance objFinite (i : Fin S.n) :
    Module.Finite k (S.almostSplitSkeleton.obj i) :=
  RightModule.finite_over_field_of_finitelyGenerated k A (S.fgObj i)

/-- The full category on the selected indecomposable projectives. -/
def ProjectiveCategory :=
  InducedCategory (RightModule.FinitelyGeneratedCategory A)
    (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)

noncomputable instance projectiveCategoryCategory :
    CategoryTheory.Category S.ProjectiveCategory := by
  exact inferInstanceAs (CategoryTheory.Category
    (InducedCategory (RightModule.FinitelyGeneratedCategory A)
      (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)))

noncomputable instance projectiveCategoryPreadditive :
    Preadditive S.ProjectiveCategory := by
  exact inferInstanceAs (Preadditive
    (InducedCategory (RightModule.FinitelyGeneratedCategory A)
      (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)))

noncomputable instance projectiveCategoryLinear :
    Linear k S.ProjectiveCategory := by
  exact inferInstanceAs (Linear k
    (InducedCategory (RightModule.FinitelyGeneratedCategory A)
      (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)))

/-- A projective label regarded as an object of the selected projective
subcategory. -/
def ordinaryProjectiveObj (p : S.ProjectiveLabel) : S.ProjectiveCategory :=
  p

/-- The selected projective represented by a label, as an ambient finitely
generated right module. -/
def ordinaryProjectiveFGObj (p : S.ProjectiveLabel) :
    RightModule.FinitelyGeneratedCategory A :=
  S.fgObj p.label

noncomputable instance projectiveCategoryHomFinite
    (x y : S.ProjectiveCategory) :
    Module.Finite k
      (x ⟶ y) :=
  Module.Finite.of_injective
    (InducedCategory.homLinearEquiv (R := k)).toLinearMap
    (InducedCategory.homLinearEquiv (R := k)).injective

/-- Inclusion of the selected projective category into finitely generated
right modules. -/
def projectiveInclusion :
    S.ProjectiveCategory ⥤ RightModule.FinitelyGeneratedCategory A :=
  inducedFunctor (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)

noncomputable instance projectiveInclusion_additive :
    S.projectiveInclusion.Additive where
  map_add := by
    intro X Y f g
    rfl

noncomputable instance projectiveInclusion_linear :
    S.projectiveInclusion.Linear k where
  map_smul := by
    intro X Y f r
    rfl

noncomputable instance projectiveInclusion_full :
    S.projectiveInclusion.Full := by
  change (inducedFunctor
    (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)).Full
  exact (fullyFaithfulInducedFunctor
    (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)).full

noncomputable instance projectiveInclusion_faithful :
    S.projectiveInclusion.Faithful := by
  change (inducedFunctor
    (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)).Faithful
  exact (fullyFaithfulInducedFunctor
    (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)).faithful

/-- Endomorphism rings in the selected-projective category are local. -/
noncomputable instance projectiveCategoryEndLocal
    (X : S.ProjectiveCategory) : IsLocalRing (End X) := by
  have hfg : IsLocalRing (End (S.projectiveInclusion.obj X)) := by
    change IsLocalRing (End (S.fgObj X.label))
    exact S.fgObj_end_isLocalRing X.label
  exact RingEquiv.isLocalRing_noncomm
    (CategoryTheory.Functor.endRingEquivOfFullyFaithful
      S.projectiveInclusion X).symm

/-- The categorical radical pulled back to the full subcategory on selected
projectives. -/
def projectiveRadicalIdeal : HomIdeal S.ProjectiveCategory :=
  HomIdeal.comap S.projectiveInclusion S.fgNilpotentRadicalData.ideal

@[simp]
theorem mem_projectiveRadicalIdeal_iff
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y) :
    f ∈ S.projectiveRadicalIdeal.hom X Y ↔
      S.projectiveInclusion.map f ∈
        S.fgNilpotentRadicalData.ideal.hom
          (S.projectiveInclusion.obj X) (S.projectiveInclusion.obj Y) :=
  Iff.rfl

/-- The projective radical is nilpotent.  Its powers only factor through
selected projectives, while their images lie in the corresponding powers of
the ambient categorical radical. -/
def projectiveNilpotentRadicalData :
    CategoricalRadical.NilpotentRadicalData S.ProjectiveCategory where
  ideal := S.projectiveRadicalIdeal
  mem_iff := by
    intro X Y f
    change S.projectiveInclusion.map f ∈
        S.fgNilpotentRadicalData.ideal.hom
          (S.projectiveInclusion.obj X) (S.projectiveInclusion.obj Y) ↔ _
    rw [S.fgNilpotentRadicalData.mem_ideal_iff]
    exact (isRadicalMorphism_iff_map_of_fullyFaithful
      S.projectiveInclusion
      (CategoryTheory.fullyFaithfulInducedFunctor _) f).symm
  nilpotent := by
    obtain ⟨N, hN⟩ := S.fgNilpotentRadicalData.nilpotent
    refine ⟨N, ?_⟩
    apply HomIdeal.ext_hom
    intro X Y
    apply le_antisymm ?_ bot_le
    intro f hf
    change f = 0
    apply InducedCategory.hom_ext
    have hmap := HomIdeal.map_mem_pow_of_mem_comap_pow
      S.projectiveInclusion S.fgNilpotentRadicalData.ideal N hf
    rw [hN] at hmap
    change S.projectiveInclusion.map f = 0 at hmap
    exact hmap

/-- The projective radical as a linear submodule of a selected-projective
Hom-space. -/
def projectiveRadicalSubmodule (x y : S.ProjectiveLabel) :
    Submodule k (S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :=
  HomIdeal.homSubmodule S.projectiveNilpotentRadicalData.ideal
    (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x)

/-- The square of the radical formed inside the selected-projective
subcategory. -/
def projectiveRadicalSquareSubmodule (x y : S.ProjectiveLabel) :
    Submodule k (S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x) :=
  HomIdeal.homSubmodule (S.projectiveNilpotentRadicalData.ideal.pow 2)
    (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x)

theorem projectiveRadicalSquare_le_radical (x y : S.ProjectiveLabel) :
    S.projectiveRadicalSquareSubmodule x y ≤
      S.projectiveRadicalSubmodule x y := by
  intro f hf
  change f ∈ S.projectiveNilpotentRadicalData.ideal.hom _ _
  simpa only [HomIdeal.pow_one] using (HomIdeal.pow_le_pow_of_le
    S.projectiveNilpotentRadicalData.ideal
      (m := 1) (n := 2) (by omega)) _ _ hf

def projectiveRadicalSquareInRadicalSubmodule
    (x y : S.ProjectiveLabel) :
    Submodule k (S.projectiveRadicalSubmodule x y) :=
  (S.projectiveRadicalSquareSubmodule x y).comap
    (S.projectiveRadicalSubmodule x y).subtype

/-- The irreducible projective-morphism space used by the ordinary quiver. -/
abbrev projectiveIrreducibleHomSpace (x y : S.ProjectiveLabel) :=
  (S.projectiveRadicalSubmodule x y) ⧸
    S.projectiveRadicalSquareInRadicalSubmodule x y

/-- The ordinary-quiver arrow type, with direction opposite to module maps. -/
abbrev OrdinaryArrow (x y : S.ProjectiveLabel) :=
  ULift.{u} (Fin (Module.finrank k (S.projectiveIrreducibleHomSpace x y)))

instance ordinaryQuiver : Quiver.{u} S.ProjectiveLabel where
  Hom := S.OrdinaryArrow

instance ordinaryArrowFintype (x y : S.ProjectiveLabel) :
    Fintype (S.OrdinaryArrow x y) := inferInstance

/-- The chosen finite basis of an ordinary-quiver arrow space. -/
def ordinaryArrowBasis (x y : S.ProjectiveLabel) :
    Module.Basis (S.OrdinaryArrow x y) k
      (S.projectiveIrreducibleHomSpace x y) :=
  (Module.finBasis k _).reindex Equiv.ulift.symm

/-- The irreducible class indexed by a displayed ordinary-quiver arrow. -/
def ordinaryArrowClass {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.projectiveIrreducibleHomSpace x y :=
  S.ordinaryArrowBasis x y a

theorem ordinaryArrowClass_linearIndependent (x y : S.ProjectiveLabel) :
    LinearIndependent k
      (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowClass a) :=
  (S.ordinaryArrowBasis x y).linearIndependent

/-- A chosen projective-radical representative of a displayed arrow. -/
def ordinaryArrowRadical {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.projectiveRadicalSubmodule x y :=
  Classical.choose
    ((S.projectiveRadicalSquareInRadicalSubmodule x y).mkQ_surjective
      (S.ordinaryArrowClass a))

@[simp]
theorem ordinaryArrowRadical_mkQ {x y : S.ProjectiveLabel}
    (a : S.OrdinaryArrow x y) :
    Submodule.Quotient.mk (S.ordinaryArrowRadical a) =
      S.ordinaryArrowClass a :=
  Classical.choose_spec
    ((S.projectiveRadicalSquareInRadicalSubmodule x y).mkQ_surjective
      (S.ordinaryArrowClass a))

theorem ordinaryArrowRadical_linearIndependent (x y : S.ProjectiveLabel) :
    LinearIndependent k
      (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowRadical a) := by
  apply LinearIndependent.of_comp
    (S.projectiveRadicalSquareInRadicalSubmodule x y).mkQ
  rw [show
    (S.projectiveRadicalSquareInRadicalSubmodule x y).mkQ ∘
        (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowRadical a) =
      (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowClass a) by
    funext a
    exact S.ordinaryArrowRadical_mkQ a]
  exact S.ordinaryArrowClass_linearIndependent x y

/-- The projective morphism realizing a displayed ordinary-quiver arrow. -/
def ordinaryArrowHom {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.ordinaryProjectiveObj y ⟶ S.ordinaryProjectiveObj x :=
  (S.ordinaryArrowRadical a).1

/-- The same displayed arrow in the ambient finitely generated module
category. -/
def ordinaryArrowFGHom {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.ordinaryProjectiveFGObj y ⟶ S.ordinaryProjectiveFGObj x :=
  (S.ordinaryArrowHom a).hom

theorem ordinaryArrowHom_mem_projectiveRadical
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.ordinaryArrowHom a ∈ S.projectiveNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) :=
  (S.ordinaryArrowRadical a).2

theorem ordinaryArrowFGHom_mem_radical
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.ordinaryArrowFGHom a ∈ S.fgNilpotentRadicalData.ideal.hom
      (S.ordinaryProjectiveFGObj y) (S.ordinaryProjectiveFGObj x) :=
  (S.ordinaryArrowRadical a).2

/-- A realized path belongs to the power of the projective radical indexed by
its length. -/
theorem ordinaryPathMap_mem_radicalPow
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    LinearPathCategory.pathMap S.ordinaryProjectiveObj
        (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowHom a) p ∈
      (S.projectiveNilpotentRadicalData.ideal.pow p.length).hom
        (S.ordinaryProjectiveObj y) (S.ordinaryProjectiveObj x) :=
  LinearPathCategory.pathMap_mem_ideal_pow
    S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowHom a)
    S.projectiveNilpotentRadicalData.ideal
    (fun {_ _} a ↦ S.ordinaryArrowHom_mem_projectiveRadical a) p

/-- Taking the underlying ambient module map commutes with reversed path
evaluation. -/
theorem ordinaryPathMap_hom {x y : S.ProjectiveLabel}
    (p : Quiver.Path x y) :
    (LinearPathCategory.pathMap S.ordinaryProjectiveObj
        (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowHom a) p).hom =
      LinearPathCategory.pathMap S.ordinaryProjectiveFGObj
        (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowFGHom a) p := by
  induction p with
  | nil =>
      rw [LinearPathCategory.pathMap_nil,
        LinearPathCategory.pathMap_nil]
      change (𝟙 (S.fgObj x.label)) = 𝟙 (S.fgObj x.label)
      rfl
  | cons p a ih =>
      rw [LinearPathCategory.pathMap_cons,
        LinearPathCategory.pathMap_cons]
      change
        (S.ordinaryArrowHom a).hom ≫
            (LinearPathCategory.pathMap S.ordinaryProjectiveObj
              (fun {_ _} (b : S.OrdinaryArrow _ _) ↦
                S.ordinaryArrowHom b) p).hom =
          S.ordinaryArrowFGHom a ≫
            LinearPathCategory.pathMap S.ordinaryProjectiveFGObj
              (fun {_ _} (b : S.OrdinaryArrow _ _) ↦
                S.ordinaryArrowFGHom b) p
      rw [ih]
      rfl

theorem ordinaryArrowHom_linearIndependent (x y : S.ProjectiveLabel) :
    LinearIndependent k
      (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowHom a) := by
  have h := (S.ordinaryArrowRadical_linearIndependent x y).map'
    (S.projectiveRadicalSubmodule x y).subtype
    (LinearMap.ker_eq_bot.mpr fun f g h ↦ Subtype.ext h)
  rw [show
      (S.projectiveRadicalSubmodule x y).subtype ∘
          (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowRadical a) =
        (fun a : S.OrdinaryArrow x y ↦ S.ordinaryArrowHom a) by
      funext a
      rfl] at h
  exact h

/-- The free linear path realization of the selected ordinary quiver. -/
def ordinaryQuiverRealization :
    LinearPathCategory.Category k S.ProjectiveLabel ⥤ S.ProjectiveCategory :=
  LinearPathCategory.lift
    S.ordinaryProjectiveObj
    (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowHom a)

noncomputable instance ordinaryQuiverRealization_additive :
    S.ordinaryQuiverRealization.Additive := by
  dsimp only [ordinaryQuiverRealization]
  infer_instance

noncomputable instance ordinaryQuiverRealization_linear :
    S.ordinaryQuiverRealization.Linear k := by
  dsimp only [ordinaryQuiverRealization]
  infer_instance

/-- The free ordinary-quiver realization in the ambient finitely generated
module category. -/
def ordinaryFGQuiverRealization :
    LinearPathCategory.Category k S.ProjectiveLabel ⥤
      RightModule.FinitelyGeneratedCategory A :=
  S.ordinaryQuiverRealization ⋙ S.projectiveInclusion

theorem ordinaryFGQuiverRealization_map
    {X Y : LinearPathCategory.Category k S.ProjectiveLabel} (f : X ⟶ Y) :
    S.ordinaryFGQuiverRealization.map f =
      (S.ordinaryQuiverRealization.map f).hom :=
  rfl

theorem ordinaryFGQuiverRealization_map_pathHom
    {x y : S.ProjectiveLabel} (p : Quiver.Path x y) :
    S.ordinaryFGQuiverRealization.map
        (LinearPathCategory.pathHom p) =
      LinearPathCategory.pathMap
        S.ordinaryProjectiveFGObj
        (fun {_ _} (a : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowFGHom a)
        p := by
  rw [S.ordinaryFGQuiverRealization_map]
  simp only [ordinaryQuiverRealization,
    LinearPathCategory.lift_map_pathHom]
  exact S.ordinaryPathMap_hom p

@[simp]
theorem ordinaryQuiverRealization_map_arrow
    {x y : S.ProjectiveLabel} (a : S.OrdinaryArrow x y) :
    S.ordinaryQuiverRealization.map
        (LinearPathCategory.pathHom
          (show Quiver.Path x y from
            (show x ⟶ y from a).toPath)) =
      S.ordinaryArrowHom a := by
  simp only [ordinaryQuiverRealization,
    LinearPathCategory.lift_map_pathHom]
  rw [show (show x ⟶ y from a).toPath = Quiver.Path.nil.cons a by rfl]
  change
    LinearPathCategory.pathMap
        S.ordinaryProjectiveObj
        (fun {_ _} (b : S.OrdinaryArrow _ _) ↦ S.ordinaryArrowHom b)
        (Quiver.Path.nil.cons a) =
      S.ordinaryArrowHom a
  rw [LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
    Category.comp_id]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
