import MagnitudeConjecture.CategoryTheory.TranslationQuiverRepetition
import MagnitudeConjecture.Combinatorics.RootedParentTree

/-!
# Riedtmann's sectional-path tree

For a right mesh datum and a chosen root vertex, mesh-sectional paths from
the root form an oriented tree: the parent operation deletes the final arrow.
This is the tree `B` in Riedtmann's construction of the repetition-quiver
cover `ℤB`.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u v

variable {Q : Type u} [Quiver.{v} Q]
variable (T : RightMeshData Q)

/-- Removing the last arrow of a mesh-sectional path preserves
mesh-sectionality. -/
theorem pathIsMeshSectional_of_cons
    {x y z : Q} {p : Quiver.Path x y} {a : y ⟶ z}
    (h : T.PathIsMeshSectional (p.cons a)) :
    T.PathIsMeshSectional p := by
  intro hp
  apply h
  rcases hp with ⟨s, b, left, right, hfac⟩
  refine ⟨s, b, left, right.cons a, ?_⟩
  simpa only [Quiver.Path.comp_cons] using
    congrArg (fun q ↦ q.cons a) hfac

/-- The empty path is mesh-sectional. -/
theorem pathIsMeshSectional_nil (x : Q) :
    T.PathIsMeshSectional (Quiver.Path.nil : Quiver.Path x x) := by
  intro h
  rcases h with ⟨s, a, left, right, hfac⟩
  have hlength := congrArg Quiver.Path.length hfac
  simp at hlength
  omega

/-- Sectional paths beginning at a fixed vertex. -/
structure SectionalPath (x₀ : Q) where
  endpoint : Q
  path : Quiver.Path x₀ endpoint
  isSectional : T.PathIsMeshSectional path

namespace SectionalPath

variable {T} (x₀ : Q)

/-- The empty sectional path at the root. -/
def root : T.SectionalPath x₀ :=
  ⟨x₀, Quiver.Path.nil, T.pathIsMeshSectional_nil x₀⟩

/-- Append an ordinary arrow when the resulting path remains sectional. -/
def cons (p : T.SectionalPath x₀) {z : Q} (a : p.endpoint ⟶ z)
    (h : T.PathIsMeshSectional (p.path.cons a)) : T.SectionalPath x₀ :=
  ⟨z, p.path.cons a, h⟩

theorem cons_ne_root (p : T.SectionalPath x₀) {z : Q}
    (a : p.endpoint ⟶ z) (h : T.PathIsMeshSectional (p.path.cons a)) :
    cons x₀ p a h ≠ root x₀ := by
  intro heq
  have hlength := congrArg (fun q : T.SectionalPath x₀ ↦ q.path.length) heq
  simp [cons, root] at hlength

/-- Delete the final arrow of a sectional path, fixing the root. -/
def parent : T.SectionalPath x₀ → T.SectionalPath x₀
  | ⟨_, .nil, _⟩ => root x₀
  | ⟨_, .cons p _, hp⟩ =>
      ⟨_, p, T.pathIsMeshSectional_of_cons hp⟩

@[simp]
theorem parent_cons (p : T.SectionalPath x₀) {z : Q}
    (a : p.endpoint ⟶ z) (h : T.PathIsMeshSectional (p.path.cons a)) :
    parent x₀ (cons x₀ p a h) = p :=
  rfl

/-- Depth in the sectional prefix tree. -/
def rank (p : T.SectionalPath x₀) : ℕ := p.path.length

theorem parent_rank_add_one (p : T.SectionalPath x₀)
    (hp : p ≠ root x₀) :
    rank x₀ (parent x₀ p) + 1 = rank x₀ p := by
  rcases p with ⟨y, p, hsectional⟩
  cases p with
  | nil =>
      exfalso
      apply hp
      rfl
  | cons p a =>
      rfl

/-- The orientation from a nonempty path to the path obtained by deleting its
last arrow. -/
def Arrow (p q : T.SectionalPath x₀) : Prop :=
  p ≠ root x₀ ∧ parent x₀ p = q

/-- Every sectional one-arrow extension is a child of its prefix. -/
theorem arrow_cons_parent (p : T.SectionalPath x₀) {z : Q}
    (a : p.endpoint ⟶ z) (h : T.PathIsMeshSectional (p.path.cons a)) :
    Arrow x₀ (cons x₀ p a h) p :=
  ⟨cons_ne_root x₀ p a h, parent_cons x₀ p a h⟩

/-- Every nonroot sectional path is a child of its parent. -/
theorem arrow_parent (p : T.SectionalPath x₀) (hp : p ≠ root x₀) :
    Arrow x₀ p (parent x₀ p) :=
  ⟨hp, rfl⟩

theorem arrow_irrefl (p : T.SectionalPath x₀) :
    ¬ Arrow x₀ p p := by
  rintro ⟨hp, hparent⟩
  have hrank := parent_rank_add_one x₀ p hp
  rw [hparent] at hrank
  omega

theorem arrow_asymm {p q : T.SectionalPath x₀}
    (hpq : Arrow x₀ p q) :
    ¬ Arrow x₀ q p := by
  rintro hqp
  have hp := parent_rank_add_one x₀ p hpq.1
  have hq := parent_rank_add_one x₀ q hqp.1
  rw [hpq.2] at hp
  rw [hqp.2] at hq
  omega

/-- The final ordinary arrow of a nontrivial sectional path, viewed as an
arrow from its parent endpoint to its endpoint. -/
def extensionArrow {p q : T.SectionalPath x₀}
    (h : Arrow x₀ q p) : p.endpoint ⟶ q.endpoint := by
  rcases q with ⟨z, q, hq⟩
  cases q with
  | nil =>
      exact (h.1 rfl).elim
  | cons q a =>
      cases h.2
      exact a

@[simp]
theorem extensionArrow_arrow_cons_parent
    (p : T.SectionalPath x₀) {z : Q} (a : p.endpoint ⟶ z)
    (h : T.PathIsMeshSectional (p.path.cons a)) :
    extensionArrow x₀ (arrow_cons_parent x₀ p a h) = a :=
  rfl

/-- A sectional path is obtained from its parent by appending its final
ordinary arrow. -/
theorem path_eq_parent_path_cons {p q : T.SectionalPath x₀}
    (h : Arrow x₀ q p) :
    q.path = p.path.cons (extensionArrow x₀ h) := by
  rcases q with ⟨z, q, hq⟩
  cases q with
  | nil =>
      exact (h.1 rfl).elim
  | cons q a =>
      cases h.2
      rfl

/-- Appending the extracted final arrow to the parent is sectional. -/
theorem extension_isSectional {p q : T.SectionalPath x₀}
    (h : Arrow x₀ q p) :
    T.PathIsMeshSectional (p.path.cons (extensionArrow x₀ h)) := by
  rw [← path_eq_parent_path_cons x₀ h]
  exact q.isSectional

/-- Reattaching the final arrow recovers the original sectional path. -/
theorem cons_extensionArrow {p q : T.SectionalPath x₀}
    (h : Arrow x₀ q p) :
    cons x₀ p (extensionArrow x₀ h) (extension_isSectional x₀ h) = q := by
  rcases q with ⟨z, q, hq⟩
  cases q with
  | nil => exact (h.1 rfl).elim
  | cons q a =>
      cases h.2
      rfl

/-- Riedtmann's oriented tree of mesh-sectional paths from `x₀`. -/
def orientedTree : MagnitudeConjecture.RepetitionQuiver.OrientedTree
    (T.SectionalPath x₀) where
  Arrow := Arrow x₀
  irrefl := arrow_irrefl x₀
  asymm := arrow_asymm x₀
  isTree := MagnitudeConjecture.ParentTree.graph_isTree
    (root x₀) (parent x₀) (rank x₀) (parent_rank_add_one x₀)

/-- The canonical signed degree on the repetition of the sectional-prefix
tree.  Moving one level downward contributes two, while moving away from the
prefix root contributes one. -/
def repetitionDegree
    (X : (orientedTree (T := T) x₀).Vertex) : ℤ :=
  (rank x₀ X.base : ℤ) - 2 * X.level

/-- Every ordinary repetition arrow raises the canonical degree by one. -/
theorem repetitionDegree_arrow
    {X Y : (orientedTree (T := T) x₀).Vertex} (a : X ⟶ Y) :
    repetitionDegree (T := T) x₀ Y =
      repetitionDegree (T := T) x₀ X + 1 := by
  rcases X with ⟨n, p⟩
  rcases Y with ⟨m, q⟩
  rcases a with h | h
  · have hlevel := h.1.down
    change m = n at hlevel
    subst m
    have hparent := parent_rank_add_one x₀ q h.2.down.1
    rw [h.2.down.2] at hparent
    have hrank : (rank x₀ q : ℤ) = (rank x₀ p : ℤ) + 1 := by
      exact_mod_cast hparent.symm
    simp only [repetitionDegree]
    omega
  · have hlevel := h.1.down
    change m = n - 1 at hlevel
    subst m
    have hparent := parent_rank_add_one x₀ p h.2.down.1
    rw [h.2.down.2] at hparent
    have hrank : (rank x₀ p : ℤ) = (rank x₀ q : ℤ) + 1 := by
      exact_mod_cast hparent.symm
    simp only [repetitionDegree]
    omega

/-- Repetition translation raises the canonical degree by two. -/
@[simp]
theorem repetitionDegree_tau
    (X : (orientedTree (T := T) x₀).Vertex) :
    repetitionDegree (T := T) x₀
        ((orientedTree (T := T) x₀).tauVertex X) =
      repetitionDegree (T := T) x₀ X + 2 := by
  rcases X with ⟨n, p⟩
  simp only [repetitionDegree, RepetitionQuiver.OrientedTree.tauVertex]
  omega

/-- The degree change along a represented repetition path is its length. -/
theorem repetitionDegree_path
    {X Y : (orientedTree (T := T) x₀).Vertex}
    (p : Quiver.Path X Y) :
    repetitionDegree (T := T) x₀ Y =
      repetitionDegree (T := T) x₀ X + p.length := by
  induction p with
  | nil => simp
  | cons p a ih =>
      rw [repetitionDegree_arrow (T := T) x₀ a, ih]
      simp only [Quiver.Path.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- When the sectional tree is finite, every fixed-degree slice of its
repetition quiver is finite. -/
theorem repetitionDegree_fiber_finite
    [Finite (T.SectionalPath x₀)] (d : ℤ) :
    Finite {X : (orientedTree (T := T) x₀).Vertex //
      repetitionDegree (T := T) x₀ X = d} := by
  let f : {X : (orientedTree (T := T) x₀).Vertex //
      repetitionDegree (T := T) x₀ X = d} → T.SectionalPath x₀ :=
    fun X ↦ X.1.base
  apply Finite.of_injective f
  rintro ⟨⟨n, p⟩, hn⟩ ⟨⟨m, q⟩, hm⟩ hpq
  change p = q at hpq
  subst q
  have hnm : n = m := by
    simp only [repetitionDegree] at hn hm
    omega
  subst m
  rfl

/-- The two consecutive degree slices `0` and `1` form a canonical finite
fundamental window in the repetition. -/
abbrev DegreeWindow :=
  {X : (orientedTree (T := T) x₀).Vertex //
    repetitionDegree (T := T) x₀ X = 0 ∨
      repetitionDegree (T := T) x₀ X = 1}

/-- Put a sectional prefix into the unique level at which its repetition
degree is its rank modulo two. -/
def degreeWindowVertex (p : T.SectionalPath x₀) :
    (orientedTree (T := T) x₀).Vertex :=
  ⟨((rank x₀ p / 2 : ℕ) : ℤ), p⟩

@[simp]
theorem repetitionDegree_degreeWindowVertex (p : T.SectionalPath x₀) :
    repetitionDegree (T := T) x₀ (degreeWindowVertex x₀ p) =
      (rank x₀ p % 2 : ℕ) := by
  have hdiv := Nat.mod_add_div (rank x₀ p) 2
  have hdiv' : ((rank x₀ p % 2 : ℕ) : ℤ) +
      2 * ((rank x₀ p / 2 : ℕ) : ℤ) = (rank x₀ p : ℤ) := by
    exact_mod_cast hdiv
  simp only [repetitionDegree, degreeWindowVertex]
  omega

/-- The canonical fundamental-window vertex attached to a sectional prefix. -/
def toDegreeWindow (p : T.SectionalPath x₀) : DegreeWindow (T := T) x₀ :=
  ⟨degreeWindowVertex x₀ p, by
    rw [repetitionDegree_degreeWindowVertex]
    exact_mod_cast Nat.mod_two_eq_zero_or_one (rank x₀ p)⟩

/-- Every base-tree vertex occurs exactly once in the two consecutive degree
slices `0` and `1`. -/
def degreeWindowEquiv :
    T.SectionalPath x₀ ≃ DegreeWindow (T := T) x₀ where
  toFun := toDegreeWindow x₀
  invFun X := X.1.base
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨n, p⟩, hp⟩
    apply Subtype.ext
    change (⟨((rank x₀ p / 2 : ℕ) : ℤ), p⟩ :
      (orientedTree (T := T) x₀).Vertex) = ⟨n, p⟩
    have hdiv := Nat.mod_add_div (rank x₀ p) 2
    have hdiv' : ((rank x₀ p % 2 : ℕ) : ℤ) +
        2 * ((rank x₀ p / 2 : ℕ) : ℤ) = (rank x₀ p : ℤ) := by
      exact_mod_cast hdiv
    have hmod := Nat.mod_two_eq_zero_or_one (rank x₀ p)
    simp only [repetitionDegree] at hp
    congr 1
    rcases hp with hp | hp <;> rcases hmod with hmod | hmod <;>
      omega

/-- Finiteness of the sectional tree is equivalent to finiteness of its
two-degree repetition window. -/
noncomputable instance degreeWindowFintype [Finite (T.SectionalPath x₀)] :
    Fintype (DegreeWindow (T := T) x₀) := by
  letI : Fintype (T.SectionalPath x₀) := Fintype.ofFinite _
  exact Fintype.ofEquiv (T.SectionalPath x₀)
    (degreeWindowEquiv (T := T) x₀)

/-- Repetition arrows whose source has degree zero.  Their targets
automatically have degree one. -/
abbrev DegreeZeroArrow :=
  Σ X : {X : (orientedTree (T := T) x₀).Vertex //
      repetitionDegree (T := T) x₀ X = 0},
    Σ Y : (orientedTree (T := T) x₀).Vertex, X.1 ⟶ Y

/-- The underlying nonroot tree vertex of a degree-zero repetition arrow. -/
def degreeZeroArrowChild (A : DegreeZeroArrow (T := T) x₀) :
    {p : T.SectionalPath x₀ // p ≠ root x₀} := by
  rcases A with ⟨⟨X, hX⟩, Y, a⟩
  rcases X with ⟨n, p⟩
  rcases Y with ⟨m, q⟩
  rcases a with a | a
  · exact ⟨q, a.2.down.1⟩
  · exact ⟨p, a.2.down.1⟩

/-- The unique degree-zero repetition arrow carried by the parent edge of a
nonroot sectional prefix. -/
noncomputable def nonrootToDegreeZeroArrow
    (p : {p : T.SectionalPath x₀ // p ≠ root x₀}) :
    DegreeZeroArrow (T := T) x₀ := by
  classical
  let O := orientedTree (T := T) x₀
  let n : ℤ := ((rank x₀ p.1 / 2 : ℕ) : ℤ)
  let hp := arrow_parent x₀ p.1 p.2
  by_cases heven : rank x₀ p.1 % 2 = 0
  · let X : O.Vertex := ⟨n, p.1⟩
    let Y : O.Vertex := ⟨n - 1, parent x₀ p.1⟩
    let a : X ⟶ Y :=
      RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal (O := O) hp
    have hX : repetitionDegree (T := T) x₀ X = 0 := by
      simpa only [X, n, degreeWindowVertex] using
        (repetitionDegree_degreeWindowVertex (T := T) x₀ p.1).trans
          (by exact_mod_cast heven)
    have hY : repetitionDegree (T := T) x₀ Y = 1 := by
      have ha := repetitionDegree_arrow (T := T) x₀ a
      rw [hX] at ha
      omega
    exact ⟨⟨X, hX⟩, ⟨Y, a⟩⟩
  · have hodd : rank x₀ p.1 % 2 = 1 :=
      (Nat.mod_two_eq_zero_or_one (rank x₀ p.1)).resolve_left heven
    let X : O.Vertex := ⟨n, parent x₀ p.1⟩
    let Y : O.Vertex := ⟨n, p.1⟩
    let a : X ⟶ Y :=
      RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal O hp
    have hY : repetitionDegree (T := T) x₀ Y = 1 := by
      simpa only [Y, n, degreeWindowVertex] using
        (repetitionDegree_degreeWindowVertex (T := T) x₀ p.1).trans
          (by exact_mod_cast hodd)
    have hX : repetitionDegree (T := T) x₀ X = 0 := by
      have ha := repetitionDegree_arrow (T := T) x₀ a
      rw [hY] at ha
      omega
    exact ⟨⟨X, hX⟩, ⟨Y, a⟩⟩

@[simp]
theorem degreeZeroArrowChild_nonrootToDegreeZeroArrow
    (p : {p : T.SectionalPath x₀ // p ≠ root x₀}) :
    degreeZeroArrowChild x₀ (nonrootToDegreeZeroArrow x₀ p) = p := by
  classical
  simp only [nonrootToDegreeZeroArrow]
  split <;> rfl

/-- Degree-zero repetition arrows are in bijection with nonroot vertices of
the sectional-prefix tree. -/
noncomputable def degreeZeroArrowEquivNonroot :
    DegreeZeroArrow (T := T) x₀ ≃
      {p : T.SectionalPath x₀ // p ≠ root x₀} where
  toFun := degreeZeroArrowChild x₀
  invFun := nonrootToDegreeZeroArrow x₀
  left_inv := by
    rintro ⟨⟨⟨n, p⟩, hdegree⟩, ⟨m, q⟩, a⟩
    rcases a with a | a
    · have hlevel : m = n := a.1.down
      subst m
      have hrank := parent_rank_add_one x₀ q a.2.down.1
      rw [a.2.down.2] at hrank
      have hodd : rank x₀ q % 2 = 1 := by
        have hdiv := Nat.mod_add_div (rank x₀ q) 2
        have hdiv' : ((rank x₀ q % 2 : ℕ) : ℤ) +
            2 * ((rank x₀ q / 2 : ℕ) : ℤ) = (rank x₀ q : ℤ) := by
          exact_mod_cast hdiv
        have hrank' : (rank x₀ p : ℤ) + 1 = (rank x₀ q : ℤ) := by
          exact_mod_cast hrank
        have hmod := Nat.mod_two_eq_zero_or_one (rank x₀ q)
        simp only [repetitionDegree] at hdegree
        rcases hmod with hmod | hmod
        · exfalso
          have hmod' : ((rank x₀ q % 2 : ℕ) : ℤ) = 0 := by
            exact_mod_cast hmod
          omega
        · exact hmod
      have hn : ((rank x₀ q / 2 : ℕ) : ℤ) = n := by
        have hdiv := Nat.mod_add_div (rank x₀ q) 2
        have hdiv' : ((rank x₀ q % 2 : ℕ) : ℤ) +
            2 * ((rank x₀ q / 2 : ℕ) : ℤ) = (rank x₀ q : ℤ) := by
          exact_mod_cast hdiv
        have hodd' : ((rank x₀ q % 2 : ℕ) : ℤ) = 1 := by
          exact_mod_cast hodd
        have hrank' : (rank x₀ p : ℤ) + 1 = (rank x₀ q : ℤ) := by
          exact_mod_cast hrank
        simp only [repetitionDegree] at hdegree
        omega
      rw [show degreeZeroArrowChild x₀
          ⟨⟨⟨n, p⟩, hdegree⟩, ⟨⟨n, q⟩, Sum.inl a⟩⟩ =
          ⟨q, a.2.down.1⟩ from rfl]
      subst n
      have hpq : parent x₀ q = p := a.2.down.2
      subst p
      simp only [nonrootToDegreeZeroArrow, hodd]
      rw [dif_neg one_ne_zero]
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Sigma.ext rfl
      apply heq_of_eq
      exact Subsingleton.elim _ _
    · have hlevel : m = n - 1 := a.1.down
      subst m
      have heven : rank x₀ p % 2 = 0 := by
        have hdiv := Nat.mod_add_div (rank x₀ p) 2
        have hdiv' : ((rank x₀ p % 2 : ℕ) : ℤ) +
            2 * ((rank x₀ p / 2 : ℕ) : ℤ) = (rank x₀ p : ℤ) := by
          exact_mod_cast hdiv
        have hmod := Nat.mod_two_eq_zero_or_one (rank x₀ p)
        simp only [repetitionDegree] at hdegree
        rcases hmod with hmod | hmod
        · exact hmod
        · exfalso
          have hmod' : ((rank x₀ p % 2 : ℕ) : ℤ) = 1 := by
            exact_mod_cast hmod
          omega
      have hn : ((rank x₀ p / 2 : ℕ) : ℤ) = n := by
        have hdiv := Nat.mod_add_div (rank x₀ p) 2
        have hdiv' : ((rank x₀ p % 2 : ℕ) : ℤ) +
            2 * ((rank x₀ p / 2 : ℕ) : ℤ) = (rank x₀ p : ℤ) := by
          exact_mod_cast hdiv
        have heven' : ((rank x₀ p % 2 : ℕ) : ℤ) = 0 := by
          exact_mod_cast heven
        simp only [repetitionDegree] at hdegree
        omega
      rw [show degreeZeroArrowChild x₀
          ⟨⟨⟨n, p⟩, hdegree⟩, ⟨⟨n - 1, q⟩, Sum.inr a⟩⟩ =
          ⟨p, a.2.down.1⟩ from rfl]
      subst n
      have hpq : parent x₀ p = q := a.2.down.2
      subst q
      simp only [nonrootToDegreeZeroArrow, heven]
      rw [dif_pos trivial]
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Sigma.ext rfl
      apply heq_of_eq
      exact Subsingleton.elim _ _
  right_inv := degreeZeroArrowChild_nonrootToDegreeZeroArrow (T := T) x₀

/-- For a finite sectional tree, the degree-zero repetition arrows form a
finite type with one element for every nonroot tree vertex. -/
noncomputable instance degreeZeroArrowFintype
    [Finite (T.SectionalPath x₀)] :
    Fintype (DegreeZeroArrow (T := T) x₀) := by
  letI : Fintype {p : T.SectionalPath x₀ // p ≠ root x₀} :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv {p : T.SectionalPath x₀ // p ≠ root x₀}
    (degreeZeroArrowEquivNonroot (T := T) x₀).symm

/-- Endpoint data for an arrow from degree zero to degree one.  Using
nonemptiness rather than a chosen arrow makes group actions on this finite
edge window proof-irrelevant. -/
abbrev DegreeZeroOneEdge :=
  {P :
      {X : (orientedTree (T := T) x₀).Vertex //
          repetitionDegree (T := T) x₀ X = 0} ×
        {Y : (orientedTree (T := T) x₀).Vertex //
          repetitionDegree (T := T) x₀ Y = 1} //
    Nonempty (P.1.1 ⟶ P.2.1)}

/-- A chosen degree-zero arrow and its degree-zero/degree-one endpoints carry
the same finite information. -/
noncomputable def degreeZeroArrowEquivDegreeZeroOneEdge :
    DegreeZeroArrow (T := T) x₀ ≃ DegreeZeroOneEdge (T := T) x₀ where
  toFun A :=
    ⟨⟨A.1, ⟨A.2.1, by
      have h := repetitionDegree_arrow (T := T) x₀ A.2.2
      rw [A.1.2] at h
      omega⟩⟩, ⟨A.2.2⟩⟩
  invFun E := ⟨E.1.1, E.1.2.1, Classical.choice E.2⟩
  left_inv := by
    rintro ⟨X, Y, a⟩
    change (⟨X, ⟨Y, Classical.choice
      (show Nonempty (X.1 ⟶ Y) from ⟨a⟩)⟩⟩ :
        DegreeZeroArrow (T := T) x₀) = ⟨X, ⟨Y, a⟩⟩
    have ha : Classical.choice
        (show Nonempty (X.1 ⟶ Y) from ⟨a⟩) = a :=
      Subsingleton.elim _ _
    exact congrArg
      (fun b : X.1 ⟶ Y ↦
        (⟨X, ⟨Y, b⟩⟩ : DegreeZeroArrow (T := T) x₀)) ha
  right_inv E := by
    apply Subtype.ext
    rfl

/-- The endpoint edge window is finite whenever the sectional tree is. -/
noncomputable instance degreeZeroOneEdgeFintype
    [Finite (T.SectionalPath x₀)] :
    Fintype (DegreeZeroOneEdge (T := T) x₀) :=
  Fintype.ofEquiv (DegreeZeroArrow (T := T) x₀)
    (degreeZeroArrowEquivDegreeZeroOneEdge (T := T) x₀)

/-- The finite two-degree window has one edge for every nonroot tree vertex,
so its edge count plus one is the tree-vertex count. -/
theorem card_degreeZeroOneEdge_add_one
    [Finite (T.SectionalPath x₀)] :
    Fintype.card (DegreeZeroOneEdge (T := T) x₀) + 1 =
      Nat.card (T.SectionalPath x₀) := by
  letI : Fintype (T.SectionalPath x₀) := Fintype.ofFinite _
  letI : Fintype {p : T.SectionalPath x₀ // p ≠ root x₀} :=
    Fintype.ofFinite _
  have hedge : Fintype.card (DegreeZeroOneEdge (T := T) x₀) =
      Fintype.card {p : T.SectionalPath x₀ // p ≠ root x₀} := by
    calc
      _ = Fintype.card (DegreeZeroArrow (T := T) x₀) :=
        Fintype.card_congr
          (degreeZeroArrowEquivDegreeZeroOneEdge (T := T) x₀).symm
      _ = _ := Fintype.card_congr
        (degreeZeroArrowEquivNonroot (T := T) x₀)
  rw [hedge, Nat.card_eq_fintype_card]
  have hcomplement :
      Fintype.card {p : T.SectionalPath x₀ // p ≠ root x₀} =
        Fintype.card (T.SectionalPath x₀) - 1 := by
    simpa using Fintype.card_subtype_compl
      (fun p : T.SectionalPath x₀ ↦ p = root x₀)
  rw [hcomplement]
  have hpositive : 0 < Fintype.card (T.SectionalPath x₀) :=
    Fintype.card_pos_iff.mpr ⟨root x₀⟩
  omega

/-- The canonical all-horizontal repetition path from the root prefix to a
sectional prefix at a fixed level. -/
def horizontalPrefixPath (n : ℤ) :
    (p : T.SectionalPath x₀) →
      Quiver.Path
        (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex)
        ⟨n, p⟩
  | ⟨_, .nil, _⟩ => Quiver.Path.nil
  | ⟨z, .cons p a, h⟩ => by
      let q : T.SectionalPath x₀ :=
        ⟨_, p, T.pathIsMeshSectional_of_cons h⟩
      let e :
          @Quiver.Hom (orientedTree (T := T) x₀).Vertex
            (RepetitionQuiver.OrientedTree.repetitionQuiver
              (orientedTree (T := T) x₀))
            ⟨n, q⟩
            ⟨n, cons x₀ q a h⟩ :=
        RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
          (orientedTree (T := T) x₀)
          (arrow_cons_parent x₀ q a h)
      exact (horizontalPrefixPath n q).cons e

@[simp]
theorem horizontalPrefixPath_root (n : ℤ) :
    horizontalPrefixPath (T := T) x₀ n (root x₀) = Quiver.Path.nil :=
  by simp [root, horizontalPrefixPath]

/-- Extending a sectional prefix extends its canonical horizontal path by
the corresponding horizontal repetition arrow. -/
theorem horizontalPrefixPath_cons
    (n : ℤ) (p : T.SectionalPath x₀) {z : Q}
    (a : p.endpoint ⟶ z)
    (h : T.PathIsMeshSectional (p.path.cons a)) :
    horizontalPrefixPath (T := T) x₀ n (cons x₀ p a h) =
      (horizontalPrefixPath (T := T) x₀ n p).cons
        (RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
          (orientedTree (T := T) x₀)
          (arrow_cons_parent x₀ p a h)) := by
  rcases p with ⟨y, p, hp⟩
  simp [cons, horizontalPrefixPath]

@[simp]
theorem horizontalPrefixPath_length
    (n : ℤ) (p : T.SectionalPath x₀) :
    (horizontalPrefixPath (T := T) x₀ n p).length = p.path.length := by
  rcases p with ⟨y, p, hp⟩
  induction p with
  | nil =>
      simp only [horizontalPrefixPath]
      rfl
  | cons p a ih =>
      simp only [horizontalPrefixPath, Quiver.Path.length_cons]
      exact congrArg (fun k ↦ k + 1)
        (ih (T.pathIsMeshSectional_of_cons hp))

variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

/-- A neighbor of a sectional prefix is either its unique parent or a child,
and a child is encoded by its final ambient arrow. -/
noncomputable def neighborCode
    (p : T.SectionalPath x₀)
    (q : (orientedTree (T := T) x₀).graph.neighborSet p) :
    Unit ⊕ (Σ y : Q, p.endpoint ⟶ y) := by
  classical
  by_cases hpq : Arrow x₀ p q.1
  · exact Sum.inl ()
  · have hqp : Arrow x₀ q.1 p :=
      ((SimpleGraph.fromRel_adj (Arrow x₀) p q.1).1 q.2).2.resolve_left hpq
    exact Sum.inr ⟨q.1.endpoint, extensionArrow x₀ hqp⟩

omit [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)] in
/-- The parent/last-arrow encoding of neighbors is injective. -/
theorem neighborCode_injective
    (p : T.SectionalPath x₀) :
    Function.Injective (neighborCode (T := T) x₀ p) := by
  classical
  intro q r hcode
  apply Subtype.ext
  by_cases hpq : Arrow x₀ p q.1
  · by_cases hpr : Arrow x₀ p r.1
    · exact hpq.2.symm.trans hpr.2
    · simp [neighborCode, hpq, hpr] at hcode
  · have hqp : Arrow x₀ q.1 p :=
      ((SimpleGraph.fromRel_adj (Arrow x₀) p q.1).1 q.2).2.resolve_left hpq
    by_cases hpr : Arrow x₀ p r.1
    · simp [neighborCode, hpq, hpr] at hcode
    · have hrp : Arrow x₀ r.1 p :=
        ((SimpleGraph.fromRel_adj (Arrow x₀) p r.1).1 r.2).2.resolve_left hpr
      have hsigma :
          (⟨q.1.endpoint, extensionArrow x₀ hqp⟩ :
              Σ y : Q, p.endpoint ⟶ y) =
            ⟨r.1.endpoint, extensionArrow x₀ hrp⟩ := by
        have hinr :
            (Sum.inr ⟨q.1.endpoint, extensionArrow x₀ hqp⟩ :
                Unit ⊕ (Σ y : Q, p.endpoint ⟶ y)) =
              Sum.inr ⟨r.1.endpoint, extensionArrow x₀ hrp⟩ := by
          simpa [neighborCode, hpq, hpr] using hcode
        exact Sum.inr.inj hinr
      have hcons :
          cons x₀ p (extensionArrow x₀ hqp)
              (extension_isSectional x₀ hqp) =
            cons x₀ p (extensionArrow x₀ hrp)
              (extension_isSectional x₀ hrp) := by
        let sq :
            { a : Σ y : Q, p.endpoint ⟶ y //
              T.PathIsMeshSectional (p.path.cons a.2) } :=
          ⟨⟨q.1.endpoint, extensionArrow x₀ hqp⟩,
            extension_isSectional x₀ hqp⟩
        let sr :
            { a : Σ y : Q, p.endpoint ⟶ y //
              T.PathIsMeshSectional (p.path.cons a.2) } :=
          ⟨⟨r.1.endpoint, extensionArrow x₀ hrp⟩,
            extension_isSectional x₀ hrp⟩
        have hsr : sq = sr := Subtype.ext hsigma
        exact congrArg (fun s ↦ cons x₀ p s.1.2 s.2) hsr
      exact (cons_extensionArrow x₀ hqp).symm.trans
        (hcons.trans (cons_extensionArrow x₀ hrp))

/-- Local finiteness of the ambient outgoing stars makes the sectional
prefix tree locally finite. -/
noncomputable instance orientedTree_graphLocallyFinite :
    (orientedTree (T := T) x₀).graph.LocallyFinite :=
  fun p ↦ Fintype.ofInjective (neighborCode (T := T) x₀ p)
    (neighborCode_injective (T := T) x₀ p)

end SectionalPath

end MagnitudeConjecture.MeshCategory.RightMeshData
