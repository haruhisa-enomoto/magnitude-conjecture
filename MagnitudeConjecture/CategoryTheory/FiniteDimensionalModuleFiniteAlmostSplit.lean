import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAlmostSplitMinimal
import MagnitudeConjecture.CategoryTheory.FiniteNeighborhoodAlmostSplit
import MagnitudeConjecture.CategoryTheory.RadicalMinimality

/-!
# Almost-split maps from a finite module skeleton

Finite radical evaluation over a complete indecomposable skeleton constructs
a right almost-split map at every label.  Minimalizing its finite-dimensional
source produces the chosen labelwise maps needed for downstream right-tau
data.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

namespace FiniteDimensionalModuleIndecomposableSkeleton

variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

/-- To prove a map into a chosen finite-module skeleton representative is
right almost split, it is enough to factor nonsplit maps from the chosen
indecomposable representatives. -/
theorem isRightAlmostSplit_of_factors_obj
    {z : Fin S.n}
    {E : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (f : E ⟶ S.obj z) (hnosplit : ¬ IsSplitEpi f)
    (hfac : ∀ (x : Fin S.n) (g : S.obj x ⟶ S.obj z),
      ¬ IsSplitEpi g → ∃ h : S.obj x ⟶ E, h ≫ f = g) :
    IsRightAlmostSplit f := by
  refine ⟨hnosplit, ?_⟩
  intro X g hg
  obtain ⟨n, label, ⟨e⟩⟩ := S.obj_decomposition X
  let F : Fin n →
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
    fun i ↦ S.obj (label i)
  let inc (i : Fin n) : F i ⟶ X := biproduct.ι F i ≫ e.inv
  let component (i : Fin n) : F i ⟶ S.obj z := inc i ≫ g
  have hcomponent (i : Fin n) : ¬ IsSplitEpi (component i) := by
    intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    apply hg
    exact IsSplitEpi.mk'
      { section_ := s.section_ ≫ inc i
        id := by
          simpa only [component, Category.assoc] using s.id }
  let factor (i : Fin n) : F i ⟶ E :=
    Classical.choose (hfac (label i) (component i) (hcomponent i))
  have factor_spec (i : Fin n) : factor i ≫ f = component i :=
    Classical.choose_spec (hfac (label i) (component i) (hcomponent i))
  let h : X ⟶ E := e.hom ≫ biproduct.desc factor
  refine ⟨h, ?_⟩
  rw [← cancel_epi e.inv]
  apply biproduct.hom_ext'
  intro i
  simp only [h, Category.assoc, Iso.inv_hom_id_assoc]
  change (biproduct.ι F i ≫ biproduct.desc factor) ≫ f = component i
  rw [biproduct.ι_desc, factor_spec]

/-- Finite radical evaluation over all skeleton labels gives a right
almost-split morphism ending at every chosen indecomposable. -/
theorem exists_rightAlmostSplit (y : Fin S.n) :
    ∃ (E : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      (f : E ⟶ S.obj y), IsRightAlmostSplit f := by
  classical
  letI : IsLocalRing (End (S.obj y)) := S.obj_end_local y
  let V (x : Fin S.n) :=
    MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
      k (S.obj x) (S.obj y)
  let d (x : Fin S.n) := Module.finrank k (V x)
  let b (x : Fin S.n) := Module.finBasis k (V x)
  let B (x : Fin S.n) :
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
    ⨁ fun _ : Fin (d x) ↦ S.obj x
  let component (x : Fin S.n) : B x ⟶ S.obj y :=
    biproduct.desc fun j ↦ (b x j).1
  let E : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
    ⨁ B
  let f : E ⟶ S.obj y := biproduct.desc component
  have hcomponentRadical (x : Fin S.n) :
      IsRadicalMorphism (component x) := by
    dsimp only [component]
    rw [biproduct.desc_eq]
    apply MagnitudeConjecture.CategoryTheory.isRadicalMorphism_finset_sum
    intro j _
    exact isRadicalMorphism_precomp
      (biproduct.π (fun _ : Fin (d x) ↦ S.obj x) j) (b x j).2
  have hfRadical : IsRadicalMorphism f := by
    dsimp only [f]
    rw [biproduct.desc_eq]
    apply MagnitudeConjecture.CategoryTheory.isRadicalMorphism_finset_sum
    intro x _
    exact isRadicalMorphism_precomp (biproduct.π B x)
      (hcomponentRadical x)
  have hfNotSplit : ¬ IsSplitEpi f :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
      (S.indecomposable y).1 f).1 hfRadical
  refine ⟨E, f, ⟨hfNotSplit, ?_⟩⟩
  intro X g hg
  obtain ⟨n, label, ⟨e⟩⟩ := S.obj_decomposition X
  let F : Fin n →
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
    fun i ↦ S.obj (label i)
  let inc (i : Fin n) : F i ⟶ X :=
    biproduct.ι F i ≫ e.inv
  let sourceComponent (i : Fin n) : F i ⟶ S.obj y :=
    inc i ≫ g
  have hsourceComponent (i : Fin n) :
      ¬ IsSplitEpi (sourceComponent i) := by
    intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    apply hg
    exact IsSplitEpi.mk'
      { section_ := s.section_ ≫ inc i
        id := by
          simpa only [sourceComponent, Category.assoc] using s.id }
  let u (i : Fin n) : V (label i) :=
    ⟨sourceComponent i,
      (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
        (S.indecomposable y).1 (sourceComponent i)).2
          (hsourceComponent i)⟩
  let q (i : Fin n) : F i ⟶ B (label i) :=
    biproduct.lift fun j ↦ (b (label i)).repr (u i) j • 𝟙 (F i)
  let factor (i : Fin n) : F i ⟶ E :=
    q i ≫ biproduct.ι B (label i)
  have hfactor (i : Fin n) : factor i ≫ f = sourceComponent i := by
    rw [Category.assoc, biproduct.ι_desc]
    dsimp only [q, component]
    rw [biproduct.lift_desc]
    change
      (∑ j : Fin (d (label i)),
          ((b (label i)).repr (u i) j • 𝟙 (F i)) ≫
            (b (label i) j).1) = sourceComponent i
    calc
      (∑ j : Fin (d (label i)),
          ((b (label i)).repr (u i) j • 𝟙 (F i)) ≫
            (b (label i) j).1) =
          ∑ j : Fin (d (label i)),
            (b (label i)).repr (u i) j • (b (label i) j).1 := by
              apply Finset.sum_congr rfl
              intro j _
              simp
      _ = ((∑ j : Fin (d (label i)),
            (b (label i)).repr (u i) j • b (label i) j :
              V (label i)) : F i ⟶ S.obj y) := by
          symm
          exact map_sum (V (label i)).subtype
            (fun j : Fin (d (label i)) ↦
              (b (label i)).repr (u i) j • b (label i) j) Finset.univ
      _ = (u i : F i ⟶ S.obj y) :=
        congrArg Subtype.val ((b (label i)).sum_repr (u i))
      _ = sourceComponent i := rfl
  let h : X ⟶ E := e.hom ≫ biproduct.desc factor
  refine ⟨h, ?_⟩
  rw [← cancel_epi e.inv]
  apply biproduct.hom_ext'
  intro i
  simp only [h, Category.assoc, Iso.inv_hom_id_assoc]
  change (biproduct.ι F i ≫ biproduct.desc factor) ≫ f =
    sourceComponent i
  rw [biproduct.ι_desc, hfactor]

/-- A chosen right-minimal right almost-split morphism ending at a skeleton
label. -/
structure MinimalRightAlmostSplitAt (y : Fin S.n) where
  source : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k
  map : source ⟶ S.obj y
  rightAlmostSplit : IsRightAlmostSplit map
  rightMinimal : IsRightMinimal map

/-- Choose a right-minimal right almost-split morphism at every skeleton
label. -/
noncomputable def minimalRightAlmostSplitAt (y : Fin S.n) :
    S.MinimalRightAlmostSplitAt y :=
  let h := S.exists_rightAlmostSplit y
  let f := Classical.choose (Classical.choose_spec h)
  let hf := Classical.choose_spec (Classical.choose_spec h)
  let hmin := finiteDimensionalModule_exists_rightMinimal_rightAlmostSplit f hf
  let E' := Classical.choose hmin
  let f' := Classical.choose (Classical.choose_spec hmin)
  { source := E'
    map := f'
    rightAlmostSplit := (Classical.choose_spec
      (Classical.choose_spec hmin)).1
    rightMinimal := (Classical.choose_spec
      (Classical.choose_spec hmin)).2 }

end FiniteDimensionalModuleIndecomposableSkeleton

end MagnitudeConjecture.CoveringHom
