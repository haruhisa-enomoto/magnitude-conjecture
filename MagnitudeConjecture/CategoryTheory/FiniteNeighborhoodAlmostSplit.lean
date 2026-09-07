import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import MagnitudeConjecture.CategoryTheory.RadicalMinimality
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Almost-split maps from finite Hom neighborhoods

Finite radical evaluation does not require a globally finite
indecomposable skeleton.  For a fixed indecomposable source or target it is
enough to have finitely many indecomposable representatives covering the
other endpoints of its nonzero morphisms.  These are the local forms needed
for a locally representation-finite covering category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CategoryTheory

universe s u v

variable (k : Type s) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]

/-- The categorical radical as a linear subspace of a Hom space. -/
def radicalHomSubmodule (X Y : C) : Submodule k (X ⟶ Y) where
  carrier := {f | IsRadicalMorphism f}
  zero_mem' := isRadicalMorphism_zero
  add_mem' := fun hf hg ↦ isRadicalMorphism_add hf hg
  smul_mem' := by
    intro c f hf
    rw [show c • f = (c • 𝟙 X) ≫ f by simp]
    exact isRadicalMorphism_precomp (c • 𝟙 X) hf

/-- A finite list of indecomposable targets covering every nonzero morphism
from `M` to an indecomposable object. -/
structure FiniteIndecomposableTargetNeighborhood (M : C) where
  n : ℕ
  obj : Fin n → C
  indecomposable : ∀ j, Indecomposable (obj j)
  covers : ∀ {Y : C}, Indecomposable Y →
    ∀ f : M ⟶ Y, f ≠ 0 → ∃ j, Nonempty (obj j ≅ Y)

/-- A finite list of indecomposable sources covering every nonzero morphism
from an indecomposable object to `M`. -/
structure FiniteIndecomposableSourceNeighborhood (M : C) where
  n : ℕ
  obj : Fin n → C
  indecomposable : ∀ j, Indecomposable (obj j)
  covers : ∀ {X : C}, Indecomposable X →
    ∀ f : X ⟶ M, f ≠ 0 → ∃ j, Nonempty (obj j ≅ X)

/-- Finite radical evaluation over a target neighborhood gives a left
almost-split map from the chosen indecomposable source. -/
theorem exists_leftAlmostSplit_of_finiteIndecomposableTargetNeighborhood
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (decomposition : ∀ X : C,
      Nonempty (FiniteIndecomposableDecomposition X))
    {M : C} (hM : Indecomposable M) [IsLocalRing (End M)]
    (N : FiniteIndecomposableTargetNeighborhood M) :
    ∃ (E : C) (f : M ⟶ E), IsLeftAlmostSplit f := by
  classical
  let d (j : Fin N.n) :=
    Module.finrank k (radicalHomSubmodule k M (N.obj j))
  let b (j : Fin N.n) :=
    Module.finBasis k (radicalHomSubmodule k M (N.obj j))
  let B (j : Fin N.n) : C :=
    ⨁ fun _ : Fin (d j) ↦ N.obj j
  let component (j : Fin N.n) : M ⟶ B j :=
    biproduct.lift fun r ↦ (b j r).1
  let E : C := ⨁ B
  let f : M ⟶ E := biproduct.lift component
  have hcomponentRadical (j : Fin N.n) :
      IsRadicalMorphism (component j) := by
    dsimp only [component]
    rw [biproduct.lift_eq]
    apply isRadicalMorphism_finset_sum
    intro r _
    exact isRadicalMorphism_postcomp
      (biproduct.ι (fun _ : Fin (d j) ↦ N.obj j) r) (b j r).2
  have hfRadical : IsRadicalMorphism f := by
    dsimp only [f]
    rw [biproduct.lift_eq]
    apply isRadicalMorphism_finset_sum
    intro j _
    exact isRadicalMorphism_postcomp (biproduct.ι B j)
      (hcomponentRadical j)
  refine ⟨E, f, ?_⟩
  constructor
  · exact
      (isRadicalMorphism_iff_not_isSplitMono_of_local_end hM.1 f).1
        hfRadical
  · intro X g hg
    obtain ⟨q⟩ := decomposition X
    let a (j : Fin q.n) : M ⟶ q.summand j :=
      g ≫ q.isoBiproduct.hom ≫ biproduct.π q.summand j
    have haNotSplit (j : Fin q.n) : ¬ IsSplitMono (a j) := by
      intro hsplit
      obtain ⟨s⟩ := hsplit.exists_splitMono
      apply hg
      exact IsSplitMono.mk'
        { retraction :=
            q.isoBiproduct.hom ≫ biproduct.π q.summand j ≫ s.retraction
          id := by simpa only [a, Category.assoc] using s.id }
    have haRadical (j : Fin q.n) : IsRadicalMorphism (a j) :=
      (isRadicalMorphism_iff_not_isSplitMono_of_local_end hM.1 (a j)).2
        (haNotSplit j)
    have factorComponent (j : Fin q.n) :
        ∃ h : E ⟶ q.summand j, f ≫ h = a j := by
      by_cases haZero : a j = 0
      · exact ⟨0, by simp [haZero]⟩
      · obtain ⟨t, ⟨e⟩⟩ :=
          N.covers (q.indecomposable j) (a j) haZero
        let z : radicalHomSubmodule k M (N.obj t) :=
          ⟨a j ≫ e.inv,
            isRadicalMorphism_postcomp e.inv (haRadical j)⟩
        let coefficient (r : Fin (d t)) : k := (b t).repr z r
        let c : B t ⟶ q.summand j :=
          biproduct.desc fun r ↦ coefficient r • e.hom
        refine ⟨biproduct.π B t ≫ c, ?_⟩
        rw [← Category.assoc, biproduct.lift_π]
        dsimp only [component, c]
        rw [biproduct.lift_desc]
        have hsum :
            (∑ r : Fin (d t), coefficient r • (b t r).1) =
              a j ≫ e.inv := by
          calc
            (∑ r : Fin (d t), coefficient r • (b t r).1) =
                ((∑ r : Fin (d t), coefficient r • b t r :
                    radicalHomSubmodule k M (N.obj t)) : M ⟶ N.obj t) := by
                  symm
                  exact map_sum
                    (radicalHomSubmodule k M (N.obj t)).subtype
                    (fun r : Fin (d t) ↦ coefficient r • b t r)
                    Finset.univ
            _ = a j ≫ e.inv := by
              simpa only [coefficient, z] using
                congrArg Subtype.val ((b t).sum_repr z)
        calc
          (∑ r : Fin (d t),
              (b t r).1 ≫ (coefficient r • e.hom)) =
              (∑ r : Fin (d t), coefficient r • (b t r).1) ≫
                e.hom := by
                  rw [Preadditive.sum_comp]
                  simp
          _ = (a j ≫ e.inv) ≫ e.hom := by rw [hsum]
          _ = a j := by simp
    choose h hh using factorComponent
    refine ⟨biproduct.lift h ≫ q.isoBiproduct.inv, ?_⟩
    apply (cancel_mono q.isoBiproduct.hom).1
    simp only [Category.assoc, q.isoBiproduct.inv_hom_id,
      Category.comp_id]
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.lift_π, hh j]
    simp only [a, Category.assoc]

/-- Finite radical coevaluation over a source neighborhood gives a right
almost-split map to the chosen indecomposable target. -/
theorem exists_rightAlmostSplit_of_finiteIndecomposableSourceNeighborhood
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (decomposition : ∀ X : C,
      Nonempty (FiniteIndecomposableDecomposition X))
    {M : C} (hM : Indecomposable M) [IsLocalRing (End M)]
    (N : FiniteIndecomposableSourceNeighborhood M) :
    ∃ (E : C) (f : E ⟶ M), IsRightAlmostSplit f := by
  classical
  let V (j : Fin N.n) := radicalHomSubmodule k (N.obj j) M
  let d (j : Fin N.n) := Module.finrank k (V j)
  let b (j : Fin N.n) := Module.finBasis k (V j)
  let B (j : Fin N.n) : C :=
    ⨁ fun _ : Fin (d j) ↦ N.obj j
  let component (j : Fin N.n) : B j ⟶ M :=
    biproduct.desc fun r ↦ (b j r).1
  let E : C := ⨁ B
  let f : E ⟶ M := biproduct.desc component
  have hcomponentRadical (j : Fin N.n) :
      IsRadicalMorphism (component j) := by
    dsimp only [component]
    rw [biproduct.desc_eq]
    apply isRadicalMorphism_finset_sum
    intro r _
    exact isRadicalMorphism_precomp
      (biproduct.π (fun _ : Fin (d j) ↦ N.obj j) r) (b j r).2
  have hfRadical : IsRadicalMorphism f := by
    dsimp only [f]
    rw [biproduct.desc_eq]
    apply isRadicalMorphism_finset_sum
    intro j _
    exact isRadicalMorphism_precomp (biproduct.π B j)
      (hcomponentRadical j)
  refine ⟨E, f, ?_⟩
  constructor
  · exact
      (isRadicalMorphism_iff_not_isSplitEpi_of_local_end hM.1 f).1
        hfRadical
  · intro X g hg
    obtain ⟨q⟩ := decomposition X
    let inclusion (j : Fin q.n) : q.summand j ⟶ X :=
      biproduct.ι q.summand j ≫ q.isoBiproduct.inv
    let a (j : Fin q.n) : q.summand j ⟶ M := inclusion j ≫ g
    have haNotSplit (j : Fin q.n) : ¬ IsSplitEpi (a j) := by
      intro hsplit
      obtain ⟨s⟩ := hsplit.exists_splitEpi
      apply hg
      exact IsSplitEpi.mk'
        { section_ := s.section_ ≫ inclusion j
          id := by simpa only [a, Category.assoc] using s.id }
    have haRadical (j : Fin q.n) : IsRadicalMorphism (a j) :=
      (isRadicalMorphism_iff_not_isSplitEpi_of_local_end hM.1 (a j)).2
        (haNotSplit j)
    have factorComponent (j : Fin q.n) :
        ∃ h : q.summand j ⟶ E, h ≫ f = a j := by
      by_cases haZero : a j = 0
      · exact ⟨0, by simp [haZero]⟩
      · obtain ⟨t, ⟨e⟩⟩ :=
          N.covers (q.indecomposable j) (a j) haZero
        let z : radicalHomSubmodule k (N.obj t) M :=
          ⟨e.hom ≫ a j,
            isRadicalMorphism_precomp e.hom (haRadical j)⟩
        let coefficient (r : Fin (d t)) : k := (b t).repr z r
        let c : q.summand j ⟶ B t :=
          biproduct.lift fun r ↦ coefficient r • e.inv
        refine ⟨c ≫ biproduct.ι B t, ?_⟩
        rw [Category.assoc, biproduct.ι_desc]
        dsimp only [c, component]
        rw [biproduct.lift_desc]
        have hsum :
            (∑ r : Fin (d t), coefficient r • (b t r).1) =
              e.hom ≫ a j := by
          calc
            (∑ r : Fin (d t), coefficient r • (b t r).1) =
                ((∑ r : Fin (d t), coefficient r • b t r :
                    radicalHomSubmodule k (N.obj t) M) : N.obj t ⟶ M) := by
                  symm
                  exact map_sum
                    (radicalHomSubmodule k (N.obj t) M).subtype
                    (fun r : Fin (d t) ↦ coefficient r • b t r)
                    Finset.univ
            _ = e.hom ≫ a j := by
              simpa only [coefficient, z] using
                congrArg Subtype.val ((b t).sum_repr z)
        calc
          (∑ r : Fin (d t),
              (coefficient r • e.inv) ≫ (b t r).1) =
              e.inv ≫
                (∑ r : Fin (d t), coefficient r • (b t r).1) := by
                  rw [Preadditive.comp_sum]
                  apply Finset.sum_congr rfl
                  intro r _
                  simp
          _ = e.inv ≫ (e.hom ≫ a j) := by rw [hsum]
          _ = a j := by simp
    choose h hh using factorComponent
    refine ⟨q.isoBiproduct.hom ≫ biproduct.desc h, ?_⟩
    rw [← cancel_epi q.isoBiproduct.inv]
    apply biproduct.hom_ext'
    intro j
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, biproduct.ι_desc, hh]
    simp only [a, inclusion, Category.assoc]

end MagnitudeConjecture.CategoryTheory
