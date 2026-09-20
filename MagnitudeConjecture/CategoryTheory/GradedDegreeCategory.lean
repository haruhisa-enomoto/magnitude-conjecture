import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.DirectSum.Decomposition
import Lean.Elab.Tactic.Omega
import MagnitudeConjecture.Graded.IntegerExtension

/-!
# The category of degree-labelled objects

For a linear category with graded Hom spaces, the objects `(X,s)` have
morphisms to `(Y,t)` given by the degree `s-t` part of `Hom(X,Y)`.
This is the shift convention of the graded interval proof. Restricting the
objects to projectives and a finite interval gives its finite category algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.GradedCategory

universe u v w

variable (k : Type u) [Field k]
variable (C : Type v) [Category.{w} C] [Preadditive C] [Linear k C]

/-- An internal grading of the Hom spaces, with composition adding degrees. -/
structure HomGrading where
  component : ∀ X Y : C, ℤ → Submodule k (X ⟶ Y)
  internal : ∀ X Y, DirectSum.IsInternal (component X Y)
  id_mem : ∀ X, 𝟙 X ∈ component X X 0
  comp_mem : ∀ {X Y Z : C} {i j : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ component X Y i → g ∈ component Y Z j → f ≫ g ∈ component X Z (i + j)

variable {k C}

/-- An object together with its integer shift. -/
structure DegreeObject (G : HomGrading k C) where
  obj : C
  degree : ℤ

namespace HomGrading

open MagnitudeConjecture.Graded

/-- Convert the natural path-length grading into an integer Hom grading. -/
def ofNat (A : ∀ X Y : C, ℕ → Submodule k (X ⟶ Y))
    (hinternal : ∀ X Y, DirectSum.IsInternal (A X Y))
    (hid : ∀ X, 𝟙 X ∈ A X X 0)
    (hcomp : ∀ {X Y Z : C} {i j : ℕ} {f : X ⟶ Y} {g : Y ⟶ Z},
      f ∈ A X Y i → g ∈ A Y Z j → f ≫ g ∈ A X Z (i + j)) :
    HomGrading k C where
  component X Y := integerComponent (A X Y)
  internal X Y := integerComponent_isInternal _ (hinternal X Y)
  id_mem X := by simpa [integerComponent] using hid X
  comp_mem := by
    intro X Y Z i j f g hf hg
    by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · have hij : 0 ≤ i + j := by omega
        simp only [integerComponent, if_pos hi] at hf
        simp only [integerComponent, if_pos hj] at hg
        simp only [integerComponent, if_pos hij]
        have hsum : (i + j).toNat = i.toNat + j.toNat := by omega
        rw [hsum]
        exact hcomp hf hg
      · have hg0 : g = 0 := by simpa [integerComponent, hj] using hg
        simp [hg0]
    · have hf0 : f = 0 := by simpa [integerComponent, hi] using hf
      simp [hf0]

variable (G : HomGrading k C)

instance : Category (DegreeObject G) where
  Hom X Y := G.component X.obj Y.obj (X.degree - Y.degree)
  id X := ⟨𝟙 X.obj, by simpa using G.id_mem X.obj⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by
    have hd : X.degree - Y.degree + (Y.degree - Z.degree) =
        X.degree - Z.degree := by omega
    exact hd ▸ G.comp_mem f.property g.property⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

instance : Preadditive (DegreeObject G) where
  homGroup X Y := inferInstanceAs (AddCommGroup
    (G.component X.obj Y.obj (X.degree - Y.degree)))
  add_comp _ _ _ f g h := Subtype.ext (Preadditive.add_comp _ _ _ f.val g.val h.val)
  comp_add _ _ _ f g h := Subtype.ext (Preadditive.comp_add _ _ _ f.val g.val h.val)

instance (X Y : DegreeObject G) : Module k (X ⟶ Y) :=
  inferInstanceAs (Module k (G.component X.obj Y.obj (X.degree - Y.degree)))

instance : Linear k (DegreeObject G) where
  smul_comp _ _ _ c f g := Subtype.ext (Linear.smul_comp _ _ _ c f.val g.val)
  comp_smul _ _ _ f c g := Subtype.ext (Linear.comp_smul _ _ _ f.val c g.val)

/-- Forget the shift and include the homogeneous component into its Hom space. -/
def forget : DegreeObject G ⥤ C where
  obj X := X.obj
  map f := f.val

instance : G.forget.Faithful where
  map_injective h := Subtype.ext h

instance : G.forget.Additive where
  map_add := by intros; rfl

instance : G.forget.Linear k where
  map_smul := by intros; rfl

/-- A nonzero homogeneous map cannot have degree outside the grading bound. -/
theorem degree_bounds_of_ne_zero
    (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    {X Y : DegreeObject G} (f : X ⟶ Y) (hf : f ≠ 0) :
    Y.degree ≤ X.degree ∧ X.degree ≤ Y.degree + h := by
  have hmem := f.property
  have hne : f.val ≠ 0 := by
    intro hzero
    exact hf (Subtype.ext hzero)
  have hd : ¬ (X.degree - Y.degree < 0 ∨ (h : ℤ) < X.degree - Y.degree) := by
    intro hd
    have hz : (f.val : X.obj ⟶ Y.obj) ∈ (⊥ : Submodule k (X.obj ⟶ Y.obj)) :=
      (hbound X.obj Y.obj _ hd) ▸ hmem
    exact hne (by simpa only [Submodule.mem_bot] using hz)
  omega

/-- For a skeletal degree-zero category, a nonzero map between distinct
degree-labelled objects strictly decreases their shift. -/
theorem degree_strict_of_ne_zero_of_ne
    (h : ℕ)
    (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)
    (hzero : ∀ X Y : C, X ≠ Y → G.component X Y 0 = ⊥)
    {X Y : DegreeObject G} (f : X ⟶ Y) (hf : f ≠ 0) (hXY : X ≠ Y) :
    Y.degree < X.degree := by
  have hb := G.degree_bounds_of_ne_zero h hbound f hf
  have hd : X.degree ≠ Y.degree := by
    intro hd
    have hobj : X.obj ≠ Y.obj := by
      intro ho
      apply hXY
      cases X
      cases Y
      dsimp at ho hd
      cases ho
      cases hd
      rfl
    have hcomp : G.component X.obj Y.obj (X.degree - Y.degree) = ⊥ := by
      rw [hd, sub_self]
      exact hzero _ _ hobj
    have hz : (f.val : X.obj ⟶ Y.obj) ∈ (⊥ : Submodule k (X.obj ⟶ Y.obj)) :=
      hcomp ▸ f.property
    apply hf
    apply Subtype.ext
    change f.val = 0
    simpa only [Submodule.mem_bot] using hz
  omega

end HomGrading

end MagnitudeConjecture.GradedCategory
