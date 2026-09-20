import MagnitudeConjecture.CategoryTheory.GradedHomComponents
import MagnitudeConjecture.CategoryTheory.GradedHomInverse
import MagnitudeConjecture.CategoryTheory.FiniteOrbitRadicalComponents

/-!
# Homogeneous splitting of a finite identity decomposition

Taking degree zero in `∑ gⱼ fⱼ = 1` gives a finite sum of endomorphisms
of the graded source. In a local endomorphism ring, one summand is a unit.
The corresponding homogeneous map splits into one shifted target. If that
target also has local endomorphisms, the split map is an isomorphism.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w z

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

/-- The degree `d` component as a degree-zero map into the shift by `-d`. -/
def outPart (X Y : C) (d : ℤ) (f : X ⟶ Y) :
    (⟨X, 0⟩ : DegreeObject G) ⟶ (⟨Y, -d⟩ : DegreeObject G) :=
  ⟨G.part X Y d f, by simpa using G.part_mem d f⟩

/-- The opposite-degree component returning from that shifted target. -/
def inPart (X Y : C) (d : ℤ) (g : Y ⟶ X) :
    (⟨Y, -d⟩ : DegreeObject G) ⟶ (⟨X, 0⟩ : DegreeObject G) :=
  ⟨G.part Y X (-d) g, by simpa using G.part_mem (-d) g⟩

/-- The actual graded identity obtained by taking degree zero of an
ungraded finite identity decomposition. -/
theorem sum_part_composites_eq_id {ι : Type z} (s : Finset ι)
    (X : C) (Y : ι → C) (f : ∀ j, X ⟶ Y j) (g : ∀ j, Y j ⟶ X)
    (hsum : ∑ j ∈ s, f j ≫ g j = 𝟙 X) :
    ∑ j ∈ s, ∑ d ∈ (G.decomposeHom X (Y j) (f j)).support,
      G.outPart X (Y j) d (f j) ≫ G.inPart X (Y j) d (g j) =
      𝟙 (⟨X, 0⟩ : DegreeObject G) := by
  apply G.forget.map_injective
  simp only [Functor.map_sum, Functor.map_comp, Functor.map_id]
  change ∑ j ∈ s, ∑ d ∈ (G.decomposeHom X (Y j) (f j)).support,
      G.part X (Y j) d (f j) ≫ G.part (Y j) X (-d) (g j) = 𝟙 X
  calc
    _ = ∑ j ∈ s, G.part X X 0 (f j ≫ g j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (G.part_zero_comp (f j) (g j)).symm
    _ = G.part X X 0 (∑ j ∈ s, f j ≫ g j) := (map_sum _ _ _).symm
    _ = 𝟙 X := by rw [hsum, G.part_zero_id]

/-- One homogeneous component splits when the graded source endomorphism
ring is local. Neither a covering hypothesis nor an orbit-density theorem
is needed for this conclusion. -/
theorem exists_splitMono_part_of_identity {ι : Type z} (s : Finset ι)
    (X : C) (Y : ι → C) (f : ∀ j, X ⟶ Y j) (g : ∀ j, Y j ⟶ X)
    (hsum : ∑ j ∈ s, f j ≫ g j = 𝟙 X)
    (hlocal : IsLocalRing (End (⟨X, 0⟩ : DegreeObject G))) :
    ∃ j ∈ s, ∃ d : ℤ, IsSplitMono (G.outPart X (Y j) d (f j)) := by
  letI := hlocal
  let c (j : ι) (d : ℤ) : End (⟨X, 0⟩ : DegreeObject G) :=
    G.outPart X (Y j) d (f j) ≫ G.inPart X (Y j) d (g j)
  have hunit : IsUnit (∑ j ∈ s, ∑ d ∈ (G.decomposeHom X (Y j) (f j)).support,
      c j d) := by
    rw [show (∑ j ∈ s, ∑ d ∈ (G.decomposeHom X (Y j) (f j)).support,
      c j d) = 1 from G.sum_part_composites_eq_id s X Y f g hsum]
    exact isUnit_one
  obtain ⟨j, hj, hunitj⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  obtain ⟨d, _, hunitd⟩ := IsLocalRing.exists_of_isUnit_sum hunitj
  have hi : IsIso (c j d) := (isUnit_iff_isIso _).mp hunitd
  letI := hi
  refine ⟨j, hj, d, IsSplitMono.mk' ?_⟩
  exact
    { retraction := G.inPart X (Y j) d (g j) ≫ inv (c j d)
      id := by
        rw [← Category.assoc]
        exact IsIso.hom_inv_id (c j d) }

/-- With local target endomorphisms, the split component identifies the
graded source with one shift of a target in its ungraded decomposition. -/
theorem exists_iso_shift_of_identity {ι : Type z} (s : Finset ι)
    (X : C) (Y : ι → C) (f : ∀ j, X ⟶ Y j) (g : ∀ j, Y j ⟶ X)
    (hsum : ∑ j ∈ s, f j ≫ g j = 𝟙 X)
    (hlocal : IsLocalRing (End (⟨X, 0⟩ : DegreeObject G)))
    (htarget : ∀ j ∈ s, ∀ d : ℤ, IsLocalRing (End (⟨Y j, -d⟩ : DegreeObject G))) :
    ∃ j ∈ s, ∃ d : ℤ,
      Nonempty ((⟨X, 0⟩ : DegreeObject G) ≅ (⟨Y j, -d⟩ : DegreeObject G)) := by
  obtain ⟨j, hj, d, hd⟩ := G.exists_splitMono_part_of_identity s X Y f g hsum hlocal
  letI := hlocal
  letI := htarget j hj d
  letI := hd
  letI : IsIso (G.outPart X (Y j) d (f j)) :=
    MagnitudeConjecture.CoveringHom.isIso_of_isSplitMono_to_localEnd
      _ (MagnitudeConjecture.CoveringHom.not_isZero_of_end_isLocalRing _)
  exact ⟨j, hj, d, ⟨asIso (G.outPart X (Y j) d (f j))⟩⟩

/-- Ungraded target locality suffices: the homogeneous inverse theorem makes
each shifted target's degree-zero endomorphism ring local automatically. -/
theorem exists_iso_shift_of_identity_of_local_targets {ι : Type z} (s : Finset ι)
    (X : C) (Y : ι → C) (f : ∀ j, X ⟶ Y j) (g : ∀ j, Y j ⟶ X)
    (hsum : ∑ j ∈ s, f j ≫ g j = 𝟙 X)
    (hlocal : IsLocalRing (End (⟨X, 0⟩ : DegreeObject G)))
    (htarget : ∀ j ∈ s, IsLocalRing (End (Y j))) :
    ∃ j ∈ s, ∃ d : ℤ,
      Nonempty ((⟨X, 0⟩ : DegreeObject G) ≅ (⟨Y j, -d⟩ : DegreeObject G)) := by
  apply G.exists_iso_shift_of_identity s X Y f g hsum hlocal
  intro j hj d
  letI := htarget j hj
  exact G.localEnd_of_underlying_localEnd ⟨Y j, -d⟩

end MagnitudeConjecture.GradedCategory.HomGrading
