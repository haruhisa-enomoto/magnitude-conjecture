import MagnitudeConjecture.CategoryTheory.GradedHomComponents
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-! # Homogeneous Hom equivalences under fully faithful graded realization -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w u' v'
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable {D : Type v'} [Category.{u'} D] [Preadditive D] [Linear k D]
variable (G : HomGrading k C) (H : HomGrading k D)
variable (F : C ⥤ D) [F.Additive] [F.Linear k]
variable (hF : ∀ {X Y : C} {d : ℤ} {f : X ⟶ Y},
  f ∈ G.component X Y d → F.map f ∈ H.component (F.obj X) (F.obj Y) d)

include hF in
/-- A degree-preserving linear functor commutes with homogeneous projection. -/
theorem map_part {X Y : C} (d : ℤ) (f : X ⟶ Y) :
    F.map (G.part X Y d f) = H.part (F.obj X) (F.obj Y) d (F.map f) := by
  letI := (G.internal X Y).chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component X Y)
    (motive := fun f ↦ F.map (G.part X Y d f) = H.part (F.obj X) (F.obj Y) d (F.map f))
  · simp
  · intro e f
    by_cases he : e = d
    · subst e
      rw [G.part_of_mem f.property, H.part_of_mem (hF f.property)]
    · rw [G.part_of_mem_ne f.property he, H.part_of_mem_ne (hF f.property) he, F.map_zero]
  · intro f g hf hg
    simp only [map_add, F.map_add, hf, hg]

include hF in
/-- Faithfulness makes degree preservation an equivalence. -/
theorem map_mem_iff [F.Faithful] {X Y : C} {d : ℤ} {f : X ⟶ Y} :
    F.map f ∈ H.component (F.obj X) (F.obj Y) d ↔ f ∈ G.component X Y d := by
  constructor
  · intro hf
    have he : G.part X Y d f = f := F.map_injective (by
      rw [G.map_part H F hF, H.part_of_mem hf])
    rw [← he]
    exact G.part_mem d f
  · exact hF

/-- Full faithful degree-preserving realization identifies every homogeneous Hom space. -/
def componentEquiv [F.Full] [F.Faithful] (X Y : C) (d : ℤ) :
    G.component X Y d ≃ₗ[k] H.component (F.obj X) (F.obj Y) d where
  toFun f := ⟨F.map f, hF f.property⟩
  invFun g := ⟨F.preimage g, (G.map_mem_iff H F hF).1 (by simpa using g.property)⟩
  left_inv f := by apply Subtype.ext; exact F.preimage_map f.val
  right_inv g := by apply Subtype.ext; exact F.map_preimage g.val
  map_add' f g := by apply Subtype.ext; exact F.map_add
  map_smul' c f := by apply Subtype.ext; exact F.map_smul c f.val

/-- A degree-preserving realization acts on the categories of shifted objects. -/
def degreeFunctor : DegreeObject G ⥤ DegreeObject H where
  obj X := ⟨F.obj X.obj, X.degree⟩
  map f := ⟨F.map f.val, hF f.property⟩
  map_id X := by apply Subtype.ext; exact F.map_id X.obj
  map_comp f g := by apply Subtype.ext; exact F.map_comp f.val g.val

instance degreeFunctorFull [F.Full] [F.Faithful] : (G.degreeFunctor H F hF).Full where
  map_surjective f := ⟨(G.componentEquiv H F hF _ _ _).symm f,
    (G.componentEquiv H F hF _ _ _).apply_symm_apply f⟩

instance degreeFunctorFaithful [F.Faithful] : (G.degreeFunctor H F hF).Faithful where
  map_injective h := Subtype.ext (F.map_injective (congrArg Subtype.val h))

instance degreeFunctorAdditive : (G.degreeFunctor H F hF).Additive where
  map_add := by intros; apply Subtype.ext; exact F.map_add

instance degreeFunctorLinear : (G.degreeFunctor H F hF).Linear k where
  map_smul := by intros; apply Subtype.ext; exact F.map_smul _ _

/-- Scalar degree-zero endomorphisms remain scalar in a fully faithful graded realization. -/
theorem degreeFunctor_end_scalar [F.Full] [F.Faithful]
    (hzero : ∀ X : C, G.component X X 0 = k ∙ (𝟙 X))
    (X : DegreeObject G)
    (f : (G.degreeFunctor H F hF).obj X ⟶ (G.degreeFunctor H F hF).obj X) :
    ∃ c : k, f = c • 𝟙 ((G.degreeFunctor H F hF).obj X) := by
  let T := G.degreeFunctor H F hF
  let g := T.preimage f
  have hm : g.val ∈ k ∙ (𝟙 X.obj) := by
    have hg := g.property
    simpa only [sub_self, hzero] using hg
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hg : g = c • 𝟙 X := Subtype.ext hc.symm
  refine ⟨c, ?_⟩
  calc
    f = T.map g := (T.map_preimage f).symm
    _ = c • 𝟙 (T.obj X) := by rw [hg, T.map_smul, T.map_id]

end MagnitudeConjecture.GradedCategory.HomGrading
