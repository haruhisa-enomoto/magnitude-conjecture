import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalCover

/-!
# Integer grading on the universal translation-quiver cover

Bongartz--Gabriel's universal-cover construction carries a canonical integer
grading.  Positive ordinary arrows have degree one, positive formal mesh edges
have degree two, and formal reverses have the opposite degrees.  The defining
walk homotopy preserves this degree, so it descends to universal-cover
vertices.  Consequently every lifted ordinary arrow raises vertex degree by
one and translation raises it by two.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

universe v w

variable {Q : Type v} [Quiver.{w} Q]

/-- Degree of a symmetric augmented arrow: ordinary arrows have absolute
degree one and formal mesh edges have absolute degree two. -/
def arrowDegree (T : RightMeshData Q) {x y : Q} :
    @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y → ℤ
  | Sum.inl (AugmentedArrow.old _) => 1
  | Sum.inl (AugmentedArrow.mesh _) => 2
  | Sum.inr (AugmentedArrow.old _) => -1
  | Sum.inr (AugmentedArrow.mesh _) => -2

@[simp]
theorem arrowDegree_oldArrow (T : RightMeshData Q) {x y : Q}
    (a : x ⟶ y) :
    arrowDegree T (oldArrow T a) = 1 :=
  rfl

@[simp]
theorem arrowDegree_meshArrow (T : RightMeshData Q)
    (x : {x : Q // x ∉ T.projective}) :
    arrowDegree T (meshArrow T x) = 2 :=
  rfl

@[simp]
theorem arrowDegree_reverse (T : RightMeshData Q) {x y : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    arrowDegree T (Quiver.reverse e) = -arrowDegree T e := by
  rcases e with e | e <;> cases e <;> rfl

/-- Signed degree of a walk in the symmetrified augmented quiver. -/
def walkDegree (T : RightMeshData Q) {x : Q} :
    {y : Q} → Walk T x y → ℤ
  | _, Quiver.Path.nil => 0
  | _, Quiver.Path.cons p e => walkDegree T p + arrowDegree T e

@[simp]
theorem walkDegree_nil (T : RightMeshData Q) (x : Q) :
    walkDegree T (Quiver.Path.nil : Walk T x x) = 0 :=
  rfl

@[simp]
theorem walkDegree_cons (T : RightMeshData Q) {x y z : Q}
    (p : Walk T x y)
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) y z) :
    walkDegree T (p.cons e) = walkDegree T p + arrowDegree T e :=
  rfl

@[simp]
theorem walkDegree_toPath (T : RightMeshData Q) {x y : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y) :
    walkDegree T e.toPath = arrowDegree T e := by
  simp [Quiver.Hom.toPath]

@[simp]
theorem walkDegree_comp (T : RightMeshData Q) {x y z : Q}
    (p : Walk T x y) (q : Walk T y z) :
    walkDegree T (p.comp q) = walkDegree T p + walkDegree T q := by
  induction q with
  | nil => exact (add_zero _).symm
  | cons q e ih =>
      change walkDegree T (p.comp q) + arrowDegree T e =
        walkDegree T p + (walkDegree T q + arrowDegree T e)
      rw [ih, add_assoc]

/-- Transporting the endpoints of an augmented walk does not change its
signed degree. -/
theorem walkDegree_cast (T : RightMeshData Q)
    {x y x' y' : Quiver.Symmetrify (AugmentedVertex T)}
    (p : @Quiver.Path (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) x y)
    (hx : x = x') (hy : y = y') :
    walkDegree T (p.cast hx hy) = walkDegree T p := by
  subst x'
  subst y'
  rfl

/-- Bongartz--Gabriel walk homotopy preserves signed degree. -/
theorem Homotopic.walkDegree_eq (T : RightMeshData Q) {x₀ y : Q}
    {p q : Walk T x₀ y} (h : Homotopic T x₀ p q) :
    walkDegree T p = walkDegree T q := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp _ r ih => simp only [walkDegree_comp, ih]
  | cancel p e =>
      simp only [walkDegree_comp, walkDegree_toPath, arrowDegree_reverse]
      abel
  | mesh s p a =>
      simp only [walkDegree_comp, meshArrowPath, oldArrowPath,
        walkDegree_toPath, arrowDegree_meshArrow, arrowDegree_oldArrow]
      abel

/-- Degree of one homotopy class of walks with a fixed endpoint. -/
def classDegree (T : RightMeshData Q) (x₀ : Q) {y : Q} :
    Quotient (homotopySetoid T x₀ y) → ℤ :=
  Quotient.lift (walkDegree T)
    (fun _ _ h ↦ Homotopic.walkDegree_eq T h)

@[simp]
theorem classDegree_mk (T : RightMeshData Q) (x₀ : Q) {y : Q}
    (p : Walk T x₀ y) :
    classDegree T x₀ (Quotient.mk (homotopySetoid T x₀ y) p) =
      walkDegree T p :=
  rfl

/-- Canonical integer degree of a universal-cover vertex. -/
def vertexDegree (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) : ℤ :=
  classDegree T x₀ W.2

/-- The universal-cover vertex represented by the empty walk at the base. -/
def baseVertex (T : RightMeshData Q) (x₀ : Q) : Vertex T x₀ :=
  ⟨x₀, Quotient.mk (homotopySetoid T x₀ x₀) Quiver.Path.nil⟩

@[simp]
theorem baseVertex_vertex (T : RightMeshData Q) (x₀ : Q) :
    (baseVertex T x₀).1 = x₀ :=
  rfl

@[simp]
theorem vertexDegree_baseVertex (T : RightMeshData Q) (x₀ : Q) :
    vertexDegree T x₀ (baseVertex T x₀) = 0 :=
  rfl

/-- Appending one symmetric augmented arrow adds its signed degree. -/
theorem vertexDegree_extend (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q}
    (e : @Quiver.Hom (Quiver.Symmetrify (AugmentedVertex T))
      (Quiver.symmetrifyQuiver (AugmentedVertex T)) W.1 z) :
    vertexDegree T x₀ (extend T x₀ W e) =
      vertexDegree T x₀ W + arrowDegree T e := by
  rcases W with ⟨y, W⟩
  induction W using Quotient.inductionOn with
  | _ p => simp [vertexDegree, classDegree, extend]

@[simp]
theorem vertexDegree_extendOld (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) {z : Q} (a : W.1 ⟶ z) :
    vertexDegree T x₀ (extendOld T x₀ W a) =
      vertexDegree T x₀ W + 1 := by
  simpa [extendOld] using vertexDegree_extend T x₀ W (oldArrow T a)

/-- Every arrow of the universal cover raises vertex degree by one. -/
theorem vertexDegree_arrow (T : RightMeshData Q) (x₀ : Q)
    {W Z : Vertex T x₀} (a : W ⟶ Z) :
    vertexDegree T x₀ Z = vertexDegree T x₀ W + 1 := by
  rw [← a.2]
  exact vertexDegree_extendOld T x₀ W a.1

/-- Translation in the universal cover raises vertex degree by two. -/
@[simp]
theorem vertexDegree_tau (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀}) :
    vertexDegree T x₀ (tau T x₀ W) =
      vertexDegree T x₀ W.1 + 2 := by
  rw [tau, vertexDegree_extend]
  rfl

/-- Bongartz--Gabriel height convention, opposite to the positive degree of
the reversed quiver used by this package. -/
def vertexHeight (T : RightMeshData Q) (x₀ : Q)
    (W : Vertex T x₀) : ℤ :=
  -vertexDegree T x₀ W

@[simp]
theorem vertexHeight_baseVertex (T : RightMeshData Q) (x₀ : Q) :
    vertexHeight T x₀ (baseVertex T x₀) = 0 := by
  simp [vertexHeight]

/-- In the package's reversed-quiver orientation, every quiver arrow lowers
Bongartz--Gabriel height by one.  The represented module morphism points in
the opposite direction and therefore raises height by one. -/
theorem vertexHeight_arrow (T : RightMeshData Q) (x₀ : Q)
    {W Z : Vertex T x₀} (a : W ⟶ Z) :
    vertexHeight T x₀ Z = vertexHeight T x₀ W - 1 := by
  rw [vertexHeight, vertexHeight, vertexDegree_arrow T x₀ a]
  abel

/-- Translation lowers Bongartz--Gabriel height by two in the reversed
quiver orientation. -/
@[simp]
theorem vertexHeight_tau (T : RightMeshData Q) (x₀ : Q)
    (W : {W : Vertex T x₀ // W ∉ projectiveSet T x₀}) :
    vertexHeight T x₀ (tau T x₀ W) =
      vertexHeight T x₀ W.1 - 2 := by
  rw [vertexHeight, vertexHeight, vertexDegree_tau]
  abel

/-- The two Bongartz--Gabriel inductions cover every represented arrow:
either its module-theoretic target has positive height, or its
module-theoretic source has nonpositive height. -/
theorem vertexHeight_arrow_positive_target_or_nonpositive_source
    (T : RightMeshData Q) (x₀ : Q)
    {W Z : Vertex T x₀} (a : W ⟶ Z) :
    0 < vertexHeight T x₀ W ∨ vertexHeight T x₀ Z ≤ 0 := by
  rw [vertexHeight_arrow T x₀ a]
  omega

end MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover
