import MagnitudeConjecture.CategoryTheory.MeshSectionalPath
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Repetition quivers of oriented trees

This file constructs the stable mesh datum on the repetition quiver `ℤB` of
an oriented tree `B`. Simple paths in `B` lift to mesh-sectional paths in
`ℤB`. Consequently, a uniform nilpotence bound for paths in the mesh category
forces a locally finite tree `B` to be finite.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RepetitionQuiver

universe u v

/-- An orientation of a simple tree. -/
structure OrientedTree (B : Type u) where
  Arrow : B → B → Prop
  irrefl : ∀ x, ¬ Arrow x x
  asymm : ∀ {x y}, Arrow x y → ¬ Arrow y x
  isTree : (SimpleGraph.fromRel Arrow).IsTree

namespace OrientedTree

variable {B : Type u} (O : OrientedTree B)

/-- The unoriented tree underlying an oriented tree. -/
abbrev graph : SimpleGraph B := SimpleGraph.fromRel O.Arrow

/-- Vertices of the repetition quiver `ℤB`. -/
structure Vertex (_O : OrientedTree B) where
  level : ℤ
  base : B

/-- Reversed repetition-quiver arrows.  A base arrow `a → b` supplies
`(n,b) → (n,a)` and `(n,a) → (n-1,b)`, in the convention used by the
free linear path category. -/
def RepetitionArrow (x y : O.Vertex) : Type :=
  (PLift (y.level = x.level) × PLift (O.Arrow y.base x.base)) ⊕
    (PLift (y.level = x.level - 1) × PLift (O.Arrow x.base y.base))

namespace RepetitionArrow

/-- The horizontal repetition arrow attached to a reversed base arrow. -/
def horizontal {n : ℤ} {a b : B} (h : O.Arrow b a) :
    O.RepetitionArrow ⟨n, a⟩ ⟨n, b⟩ :=
  Sum.inl ⟨PLift.up rfl, PLift.up h⟩

/-- The diagonal repetition arrow attached to a forward base arrow. -/
def diagonal {n : ℤ} {a b : B} (h : O.Arrow a b) :
    O.RepetitionArrow ⟨n, a⟩ ⟨n - 1, b⟩ :=
  Sum.inr ⟨PLift.up rfl, PLift.up h⟩

end RepetitionArrow

instance repetitionQuiver : Quiver O.Vertex where
  Hom := O.RepetitionArrow

instance repetitionArrowSubsingleton (x y : O.Vertex) :
    Subsingleton (x ⟶ y) := by
  constructor
  intro e e'
  rcases e with h | h <;> rcases e' with h' | h'
  · exact congrArg Sum.inl (Subsingleton.elim h h')
  · exact (O.asymm h.2.down h'.2.down).elim
  · exact (O.asymm h'.2.down h.2.down).elim
  · exact congrArg Sum.inr (Subsingleton.elim h h')

/-- Translation of the integer coordinate of a repetition vertex. -/
def levelShiftVertexEquiv (k : ℤ) : O.Vertex ≃ O.Vertex where
  toFun X := ⟨X.level + k, X.base⟩
  invFun X := ⟨X.level - k, X.base⟩
  left_inv := by
    rintro ⟨n, b⟩
    simp
  right_inv := by
    rintro ⟨n, b⟩
    simp

/-- Shifting both endpoints by the same integer preserves repetition arrows. -/
def levelShiftArrowEquiv (k : ℤ) (X Y : O.Vertex) :
    (X ⟶ Y) ≃
      (O.levelShiftVertexEquiv k X ⟶ O.levelShiftVertexEquiv k Y) where
  toFun e := by
    rcases X with ⟨n, x⟩
    rcases Y with ⟨m, y⟩
    rcases e with h | h
    · exact Sum.inl ⟨PLift.up (by
        have hlevel := h.1.down
        change m = n at hlevel
        change m + k = n + k
        omega), h.2⟩
    · exact Sum.inr ⟨PLift.up (by
        have hlevel := h.1.down
        change m = n - 1 at hlevel
        change m + k = (n + k) - 1
        omega), h.2⟩
  invFun e := by
    rcases X with ⟨n, x⟩
    rcases Y with ⟨m, y⟩
    rcases e with h | h
    · exact Sum.inl ⟨PLift.up (by
        have hlevel := h.1.down
        change m = n
        change m + k = n + k at hlevel
        omega), h.2⟩
    · exact Sum.inr ⟨PLift.up (by
        have hlevel := h.1.down
        change m = n - 1
        change m + k = (n + k) - 1 at hlevel
        omega), h.2⟩
  left_inv := fun _ ↦ Subsingleton.elim _ _
  right_inv := fun _ ↦ Subsingleton.elim _ _

/-- Integer-coordinate shift as an automorphism of the repetition quiver. -/
def levelShiftQuiverIso (k : ℤ) :
    CategoryTheory.Quiv.of O.Vertex ≅ CategoryTheory.Quiv.of O.Vertex :=
  CategoryTheory.Quiv.isoOfEquiv
    (O.levelShiftVertexEquiv k) (O.levelShiftArrowEquiv k)

@[simp]
theorem levelShiftQuiverIso_hom_obj (k : ℤ) (X : O.Vertex) :
    (O.levelShiftQuiverIso k).hom.obj X = ⟨X.level + k, X.base⟩ :=
  rfl

/-- Repetition translation. -/
def tauVertex (x : O.Vertex) : O.Vertex := ⟨x.level - 1, x.base⟩

private def pairArrow {x y : O.Vertex} :
    (x ⟶ y) → (y ⟶ O.tauVertex x) := by
  intro h
  rcases h with h | h
  · have hlevel := h.1.down
    exact Sum.inr ⟨PLift.up (by simp [tauVertex]; omega), h.2⟩
  · have hlevel := h.1.down
    exact Sum.inl ⟨PLift.up (by simp [tauVertex]; omega), h.2⟩

private def unpairArrow {x y : O.Vertex} :
    (y ⟶ O.tauVertex x) → (x ⟶ y) := by
  intro h
  rcases h with h | h
  · have hlevel := h.1.down
    exact Sum.inr ⟨PLift.up (by simp [tauVertex] at hlevel ⊢; omega), h.2⟩
  · have hlevel := h.1.down
    exact Sum.inl ⟨PLift.up (by simp [tauVertex] at hlevel ⊢; omega), h.2⟩

/-- The stable right mesh datum on the repetition quiver. -/
def rightMeshData : MagnitudeConjecture.MeshCategory.RightMeshData O.Vertex where
  projective := ∅
  tau s := O.tauVertex s.1
  arrowEquiv _ _ :=
    { toFun := O.pairArrow
      invFun := O.unpairArrow
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }

@[simp]
theorem rightMeshData_projective : O.rightMeshData.projective = ∅ := rfl

@[simp]
theorem rightMeshData_tau (s : {x : O.Vertex // x ∉ O.rightMeshData.projective}) :
    O.rightMeshData.tau s = O.tauVertex s.1 := rfl

/-- Repetition translation is bijective on vertices. -/
theorem tauVertex_bijective : Function.Bijective O.tauVertex := by
  constructor
  · rintro ⟨n, b⟩ ⟨m, c⟩ h
    change (⟨n - 1, b⟩ : O.Vertex) = ⟨m - 1, c⟩ at h
    have hn : n = m := by
      have hlevel := congrArg Vertex.level h
      change n - 1 = m - 1 at hlevel
      omega
    have hb : b = c := congrArg Vertex.base h
    cases hn
    cases hb
    rfl
  · rintro ⟨n, b⟩
    refine ⟨⟨n + 1, b⟩, ?_⟩
    change (⟨(n + 1) - 1, b⟩ : O.Vertex) = ⟨n, b⟩
    congr 1
    omega

/-- Every repetition arrow projects to an edge of the underlying tree. -/
theorem arrow_adj {x y : O.Vertex} (e : x ⟶ y) :
    O.graph.Adj x.base y.base := by
  cases e with
  | inl h =>
      exact ⟨fun hxy ↦ O.irrefl _ (by simpa [hxy] using h.2.down),
        Or.inr h.2.down⟩
  | inr h =>
      exact ⟨fun hxy ↦ O.irrefl _ (by simpa [hxy] using h.2.down),
        Or.inl h.2.down⟩

/-- An outgoing repetition arrow is determined by its target base vertex. -/
theorem starBase_injective (x : O.Vertex) :
    Function.Injective (fun e : Σ y, x ⟶ y ↦ e.1.base) := by
  rintro ⟨⟨m, b⟩, e⟩ ⟨⟨m', b'⟩, e'⟩ hbb
  simp only at hbb
  subst b'
  rcases x with ⟨n, a⟩
  have hmm : m = m' := by
    rcases e with h | h <;> rcases e' with h' | h'
    · exact h.1.down.trans h'.1.down.symm
    · exact (O.asymm h.2.down h'.2.down).elim
    · exact (O.asymm h'.2.down h.2.down).elim
    · exact h.1.down.trans h'.1.down.symm
  subst m'
  cases Subsingleton.elim e e'
  rfl

/-- Local finiteness of the base tree gives finite outgoing stars in the
repetition quiver. -/
noncomputable instance vertexStarFintype [O.graph.LocallyFinite]
    (x : O.Vertex) : Fintype (Σ y, x ⟶ y) :=
  Fintype.ofInjective
    (fun e : Σ y, x ⟶ y ↦
      (⟨e.1.base, O.arrow_adj e.2⟩ : O.graph.neighborSet x.base))
    (fun _ _ h ↦ O.starBase_injective x (congrArg Subtype.val h))

/-- Lift one unoriented tree edge from a chosen repetition vertex. -/
def liftAdj {a b : B} (n : ℤ) (h : O.graph.Adj a b) :
    Σ m : ℤ, (⟨n, a⟩ : O.Vertex) ⟶ ⟨m, b⟩ :=
  Classical.choice (show Nonempty
      (Σ m : ℤ, (⟨n, a⟩ : O.Vertex) ⟶ ⟨m, b⟩) by
    rcases h with ⟨hne, hab | hba⟩
    · exact ⟨⟨n - 1, RepetitionArrow.diagonal O hab⟩⟩
    · exact ⟨⟨n, RepetitionArrow.horizontal O hba⟩⟩)

/-- Lift an unoriented walk in the base tree to an oriented path in the
repetition quiver. -/
def liftWalk (O : OrientedTree B) (n : ℤ) {a b : B} :
    O.graph.Walk a b → Σ m : ℤ,
      Quiver.Path (⟨n, a⟩ : O.Vertex) ⟨m, b⟩
  | .nil => ⟨n, Quiver.Path.nil⟩
  | .cons h p =>
      let e := O.liftAdj n h
      let q := O.liftWalk e.1 p
      ⟨q.1, e.2.toPath.comp q.2⟩

@[simp]
theorem liftWalk_length (n : ℤ) {a b : B} (p : O.graph.Walk a b) :
    (O.liftWalk n p).2.length = p.length := by
  induction p generalizing n with
  | nil => simp [liftWalk]
  | @cons a c b h p ih =>
      simp only [liftWalk, Quiver.Path.length_comp, Quiver.Path.length_toPath,
        SimpleGraph.Walk.length_cons]
      rw [ih]
      omega

@[simp]
theorem liftWalk_baseVertices (n : ℤ) {a b : B} (p : O.graph.Walk a b) :
    (O.liftWalk n p).2.vertices.map (fun x ↦ x.base) = p.support := by
  induction p generalizing n with
  | nil => simp [liftWalk]
  | @cons a c b h p ih =>
      simp [liftWalk, Quiver.Path.vertices_comp, ih]

/-- A lifted simple tree path is mesh-sectional. -/
theorem liftWalk_pathIsMeshSectional
    (n : ℤ) {a b : B} (p : O.graph.Walk a b) (hp : p.IsPath) :
    O.rightMeshData.PathIsMeshSectional (O.liftWalk n p).2 := by
  apply O.rightMeshData.pathIsMeshSectional_of_map_vertices_nodup
    (fun x : O.Vertex ↦ x.base)
  · intro s
    rfl
  · rw [O.liftWalk_baseVertices n p]
    exact p.isPath_def.mp hp

/-- The finite set reached by walks of length strictly less than `n` from a
chosen root in a locally finite graph. -/
noncomputable def walkBall (O : OrientedTree B) [O.graph.LocallyFinite] : ℕ → B → Finset B
  | 0, _ => ∅
  | n + 1, a => by
      classical
      exact {a} ∪ (O.graph.neighborFinset a).biUnion (O.walkBall n)

theorem endpoint_mem_walkBall_of_length_lt [O.graph.LocallyFinite]
    {a b : B} (p : O.graph.Walk a b) {n : ℕ} (hp : p.length < n) :
    b ∈ O.walkBall n a := by
  induction n generalizing a b with
  | zero => omega
  | succ n ih =>
      cases p with
      | nil =>
          simp [walkBall]
      | @cons a c b h p =>
          have hp' : p.length < n := by
            simpa using hp
          have hm := ih p hp'
          classical
          simp only [walkBall, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion]
          right
          exact ⟨c, by simpa using h, hm⟩

/-- An infinite locally finite connected graph has simple paths of arbitrary
length. -/
theorem exists_path_length_ge_of_infinite
    [O.graph.LocallyFinite] [Infinite B] (N : ℕ) :
    ∃ (a b : B) (p : O.graph.Walk a b), p.IsPath ∧ N ≤ p.length := by
  classical
  letI : Nonempty B := O.isTree.connected.nonempty
  let a : B := Classical.choice (inferInstance : Nonempty B)
  by_contra hnone
  push Not at hnone
  let p (b : B) : O.graph.Walk a b :=
    Classical.choose (O.isTree.connected.preconnected.exists_isPath a b)
  have hpPath (b : B) : (p b).IsPath :=
    Classical.choose_spec (O.isTree.connected.preconnected.exists_isPath a b)
  have hpLength (b : B) : (p b).length < N :=
    hnone a b (p b) (hpPath b)
  let f : B → {b // b ∈ O.walkBall N a} := fun b ↦
    ⟨b, O.endpoint_mem_walkBall_of_length_lt (p b) (hpLength b)⟩
  letI : Finite B := Finite.of_injective f (fun _ _ h ↦ congrArg Subtype.val h)
  exact (inferInstance : Infinite B).false

/-- Uniform nilpotence of paths in the mesh category of `ℤB` forces the
locally finite tree `B` to be finite. -/
theorem finite_of_uniform_mesh_nilpotence
    {k : Type v} [Field k] [O.graph.LocallyFinite]
    (N : ℕ)
    (hnil : ∀ {x y : O.Vertex} (p : Quiver.Path x y),
      N ≤ p.length →
      (MagnitudeConjecture.MeshCategory.quotientFunctor
          (k := k) O.rightMeshData).map
        (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) p) = 0) :
    Finite B := by
  classical
  rcases finite_or_infinite B with hfinite | hinfinite
  · exact hfinite
  · letI : Infinite B := hinfinite
    exfalso
    obtain ⟨a, b, p, hp, hlength⟩ := O.exists_path_length_ge_of_infinite N
    let q := (O.liftWalk 0 p).2
    have hq : O.rightMeshData.PathIsMeshSectional q := by
      exact O.liftWalk_pathIsMeshSectional 0 p hp
    have hnonzero :=
      O.rightMeshData.quotient_map_pathHom_ne_zero_of_isMeshSectional
        (k := k) q hq
    exact hnonzero (hnil q (by simpa [q] using hlength))

end OrientedTree

end MagnitudeConjecture.RepetitionQuiver
