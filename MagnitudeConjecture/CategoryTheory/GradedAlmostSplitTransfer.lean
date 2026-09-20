import MagnitudeConjecture.CategoryTheory.GradedHomInverse
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite
import QuotientSubmoduleEquidistribution.CategoryTheory.MinimalMorphism

/-! # Almost-split maps and minimality after taking homogeneous components -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

/-- If the last factor is homogeneous, one component of the first factor
computes any prescribed component of their composite. -/
theorem part_comp_right_homogeneous {X Y Z : C} {d : ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hg : g ∈ G.component Y Z d) (t : ℤ) :
    G.part X Z t (f ≫ g) = G.part X Y (t - d) f ≫ g := by
  letI := (G.internal X Y).chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component X Y)
    (motive := fun f ↦ G.part X Z t (f ≫ g) = G.part X Y (t - d) f ≫ g)
  · simp
  · intro e f
    by_cases he : e = t - d
    · subst e
      rw [G.part_of_mem f.property]
      apply G.part_of_mem
      have hc := G.comp_mem f.property hg
      simpa using hc
    · rw [G.part_of_mem_ne f.property he, Limits.zero_comp]
      exact G.part_of_mem_ne (G.comp_mem f.property hg) (by omega)
  · intro f f' hf hf'
    simp only [Preadditive.add_comp, map_add, hf, hf']

/-- A section of a homogeneous map can be replaced by its opposite-degree component. -/
theorem isSplitEpi_of_underlying_isSplitEpi {X Y : DegreeObject G} (f : X ⟶ Y)
    (hf : IsSplitEpi f.val) : IsSplitEpi f := by
  let s := hf.exists_splitEpi.some
  let a : Y ⟶ X := ⟨G.part Y.obj X.obj (Y.degree - X.degree) s.section_, G.part_mem _ _⟩
  refine IsSplitEpi.mk' { section_ := a, id := ?_ }
  apply Subtype.ext
  change G.part Y.obj X.obj (Y.degree - X.degree) s.section_ ≫ f.val = 𝟙 Y.obj
  have hc := G.part_comp_right_homogeneous s.section_ f.val f.property 0
  have hd : (0 : ℤ) - (X.degree - Y.degree) = Y.degree - X.degree := by omega
  rw [hd, s.id, G.part_zero_id] at hc
  exact hc.symm

/-- Forgetting degrees preserves and reflects whether a homogeneous map splits. -/
theorem isSplitEpi_iff_underlying {X Y : DegreeObject G} (f : X ⟶ Y) :
    IsSplitEpi f ↔ IsSplitEpi f.val := by
  constructor
  · intro hf
    let s := hf.exists_splitEpi.some
    exact IsSplitEpi.mk' { section_ := s.section_.val, id := congrArg Subtype.val s.id }
  · exact G.isSplitEpi_of_underlying_isSplitEpi f

/-- An ungraded almost-split map remains almost split in the degree category
when the given map is homogeneous. -/
theorem rightAlmostSplit_of_underlying {X Y : DegreeObject G} (f : X ⟶ Y)
    (hf : IsRightAlmostSplit f.val) : IsRightAlmostSplit f := by
  constructor
  · intro hs
    exact hf.not_isSplitEpi ((G.isSplitEpi_iff_underlying f).mp hs)
  · intro Z g hg
    have hgu : ¬ IsSplitEpi g.val := fun hs ↦ hg ((G.isSplitEpi_iff_underlying g).mpr hs)
    obtain ⟨a, ha⟩ := hf.factors g.val hgu
    refine ⟨⟨G.part Z.obj X.obj (Z.degree - X.degree) a, G.part_mem _ _⟩, ?_⟩
    apply Subtype.ext
    change G.part Z.obj X.obj (Z.degree - X.degree) a ≫ f.val = g.val
    have hc := G.part_comp_right_homogeneous a f.val f.property (Z.degree - Y.degree)
    have hd : Z.degree - Y.degree - (X.degree - Y.degree) = Z.degree - X.degree := by omega
    rw [hd, ha, G.part_of_mem g.property] at hc
    exact hc.symm

/-- Right minimality passes because a homogeneous invertible endomorphism
has a homogeneous inverse. -/
theorem rightMinimal_of_underlying {X Y : DegreeObject G} (f : X ⟶ Y)
    (hf : IsRightMinimal f.val) : IsRightMinimal f := by
  intro a ha
  letI : IsIso a.val := hf a.val (congrArg Subtype.val ha)
  exact G.isIso_of_underlying_isIso a

end MagnitudeConjecture.GradedCategory.HomGrading
