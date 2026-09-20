import MagnitudeConjecture.CategoryTheory.GradedHomComponents
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Homogeneous inverses and local graded endomorphisms

An invertible homogeneous map has a homogeneous inverse of the opposite
degree. In particular the degree-zero endomorphism ring is local whenever
the ungraded endomorphism ring is local. This supplies the target locality
in the homogeneous splitting argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

theorem inv_mem_opposite_degree {X Y : C} {d : ℤ} (f : X ⟶ Y)
    [IsIso f] (hf : f ∈ G.component X Y d) : inv f ∈ G.component Y X (-d) := by
  have hp := G.part_zero_comp_homogeneous f hf (inv f)
  rw [IsIso.hom_inv_id, G.part_zero_id] at hp
  have hi : G.part Y X (-d) (inv f) = inv f := by
    calc
      _ = inv f ≫ (f ≫ G.part Y X (-d) (inv f)) := by simp
      _ = inv f ≫ 𝟙 X := by rw [← hp]
      _ = inv f := Category.comp_id _
  rw [← hi]
  exact G.part_mem _ _

/-- Forgetting degrees reflects invertibility of homogeneous maps. -/
theorem isIso_of_underlying_isIso {X Y : DegreeObject G} (f : X ⟶ Y)
    [IsIso f.val] : IsIso f := by
  let g : Y ⟶ X := ⟨inv f.val, by
    have hi := G.inv_mem_opposite_degree f.val f.property
    have hd : -(X.degree - Y.degree) = Y.degree - X.degree := by omega
    exact hd ▸ hi⟩
  exact ⟨⟨g, Subtype.ext (IsIso.hom_inv_id f.val),
    Subtype.ext (IsIso.inv_hom_id f.val)⟩⟩

theorem isUnit_of_underlying_isUnit {X : DegreeObject G} (f : End X)
    (hf : IsUnit (show End X.obj from f.val)) : IsUnit f := by
  letI : IsIso f.val := (isUnit_iff_isIso _).mp hf
  letI : IsIso f := G.isIso_of_underlying_isIso f
  exact (isUnit_iff_isIso f).mpr inferInstance

/-- The degree-zero endomorphisms form a local ring if the ambient
endomorphism ring is local. -/
theorem localEnd_of_underlying_localEnd (X : DegreeObject G)
    [IsLocalRing (End X.obj)] : IsLocalRing (End X) := by
  letI : Nontrivial (End X) := ⟨⟨0, 1, by
    intro heq
    have heq' := congrArg (fun f : End X ↦ f.val) heq
    exact zero_ne_one (show (0 : End X.obj) = 1 from heq')⟩⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  let a : End X.obj := f.val
  have hsum : a + (1 - a) = 1 := by
    simp [← add_sub_assoc, add_comm]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with hf | hf
  · exact Or.inl (G.isUnit_of_underlying_isUnit f hf)
  · exact Or.inr (G.isUnit_of_underlying_isUnit (1 - f) hf)

end MagnitudeConjecture.GradedCategory.HomGrading
