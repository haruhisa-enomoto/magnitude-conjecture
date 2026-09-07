import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyGroupoidPresentation
import MagnitudeConjecture.CategoryTheory.TranslationQuiverSectionalPathTree

/-!
# Contracting the sectional-prefix tree in a repetition quiver

The canonical horizontal prefix paths identify every copy of the finite
sectional-prefix tree with its root line.  The key relation is the commuting
square obtained from the two mesh relations adjacent to a tree edge.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RepetitionLine

/-- The oriented integer line, with one generator from `n` to `n - 1`. -/
def Arrow (n m : ℤ) := PLift (m = n - 1)

instance : Quiver ℤ where
  Hom := Arrow

/-- The downward generator of the oriented integer line. -/
def down (n : ℤ) : n ⟶ n - 1 :=
  PLift.up rfl

end MagnitudeConjecture.RepetitionLine

namespace MagnitudeConjecture.RepetitionQuiver.OrientedTree

universe u

open MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

variable {B : Type u} (O : OrientedTree B)

/-- A repetition vertex regarded as nonprojective in the stable repetition
mesh datum. -/
def nonprojectiveVertex (X : O.Vertex) :
    {X : O.Vertex // X ∉ O.rightMeshData.projective} :=
  ⟨X, by simp⟩

/-- The formal mesh edge at a repetition vertex, as a morphism in the
mesh-homotopy groupoid. -/
def meshMorphism (X : O.Vertex) :
    (show HomotopyGroupoid O.rightMeshData from X) ⟶
      (show HomotopyGroupoid O.rightMeshData from O.tauVertex X) :=
  (HomotopyGroupoid.of O.rightMeshData).map
    (AugmentedArrow.mesh (O.nonprojectiveVertex X))

/-- Collapse the augmented repetition quiver to the integer root line:
horizontal arrows become identities, while diagonal and mesh arrows become
the unique downward line generator. -/
def collapseLabelling :
    AugmentedVertex O.rightMeshData ⥤q
      Quiver.FreeGroupoid ℤ where
  obj X := (Quiver.FreeGroupoid.of ℤ).obj
    (show O.Vertex from X).level
  map {X Y} e := by
    cases e with
    | old a =>
        rcases X with ⟨n, x⟩
        rcases Y with ⟨m, y⟩
        rcases a with h | h
        · have hm := h.1.down
          change m = n at hm
          subst m
          exact 𝟙 _
        · have hm := h.1.down
          change m = n - 1 at hm
          subst m
          exact (Quiver.FreeGroupoid.of ℤ).map
            (MagnitudeConjecture.RepetitionLine.down n)
    | mesh s =>
        exact (Quiver.FreeGroupoid.of ℤ).map
          (MagnitudeConjecture.RepetitionLine.down s.1.level)

/-- The line collapse respects every polarized mesh relation. -/
theorem collapseLabelling_meshCompatible :
    HomotopyGroupoid.MeshCompatible O.rightMeshData
      O.collapseLabelling := by
  rintro ⟨⟨n, x⟩, hs⟩ ⟨⟨m, y⟩, a⟩
  rcases a with h | h
  · have hm := h.1.down
    change m = n at hm
    subst m
    change (Quiver.FreeGroupoid.of ℤ).map
        (MagnitudeConjecture.RepetitionLine.down n) =
      𝟙 _ ≫ (Quiver.FreeGroupoid.of ℤ).map
        (MagnitudeConjecture.RepetitionLine.down n)
    rw [Category.id_comp]
  · have hm := h.1.down
    change m = n - 1 at hm
    subst m
    change (Quiver.FreeGroupoid.of ℤ).map
        (MagnitudeConjecture.RepetitionLine.down n) =
      (Quiver.FreeGroupoid.of ℤ).map
          (MagnitudeConjecture.RepetitionLine.down n) ≫ 𝟙 _
    rw [Category.comp_id]

/-- The functor collapsing the mesh-homotopy groupoid of a repetition quiver
to the free groupoid on the integer line. -/
def collapseFunctor :
    HomotopyGroupoid O.rightMeshData ⥤ Quiver.FreeGroupoid ℤ :=
  HomotopyGroupoid.lift O.rightMeshData O.collapseLabelling
    O.collapseLabelling_meshCompatible

/-- Include the integer line as the root line of a repetition quiver, sending
its generator to the formal mesh edge. -/
def rootLineLabelling (b₀ : B) :
    ℤ ⥤q HomotopyGroupoid O.rightMeshData where
  obj n := show HomotopyGroupoid O.rightMeshData from
    (⟨n, b₀⟩ : O.Vertex)
  map {n m} e := by
    rcases e with ⟨hm⟩
    subst m
    exact O.meshMorphism (⟨n, b₀⟩ : O.Vertex)

/-- Extend the root-line inclusion from generators to the free groupoid. -/
def rootLineFunctor (b₀ : B) :
    Quiver.FreeGroupoid ℤ ⥤ HomotopyGroupoid O.rightMeshData :=
  Quiver.FreeGroupoid.lift (O.rootLineLabelling b₀)

@[simp]
theorem collapseFunctor_obj (X : O.Vertex) :
    O.collapseFunctor.obj (show HomotopyGroupoid O.rightMeshData from X) =
      (Quiver.FreeGroupoid.of ℤ).obj X.level :=
  rfl

@[simp]
theorem collapseFunctor_map_meshMorphism (X : O.Vertex) :
    O.collapseFunctor.map (O.meshMorphism X) =
      (Quiver.FreeGroupoid.of ℤ).map
        (MagnitudeConjecture.RepetitionLine.down X.level) := by
  exact HomotopyGroupoid.lift_map_of O.rightMeshData
    O.collapseLabelling O.collapseLabelling_meshCompatible
    (AugmentedArrow.mesh (O.nonprojectiveVertex X))

@[simp]
theorem collapseFunctor_map_old_horizontal
    {a b : B} (h : O.Arrow b a) (n : ℤ) :
    O.collapseFunctor.map
        ((HomotopyGroupoid.of O.rightMeshData).map
          (AugmentedArrow.old
            (RepetitionArrow.horizontal O h :
              (⟨n, a⟩ : O.Vertex) ⟶ ⟨n, b⟩))) =
      𝟙 ((Quiver.FreeGroupoid.of ℤ).obj n) := by
  exact HomotopyGroupoid.lift_map_of O.rightMeshData
    O.collapseLabelling O.collapseLabelling_meshCompatible _

@[simp]
theorem collapseFunctor_map_old_diagonal
    {a b : B} (h : O.Arrow a b) (n : ℤ) :
    O.collapseFunctor.map
        ((HomotopyGroupoid.of O.rightMeshData).map
          (AugmentedArrow.old
            (RepetitionArrow.diagonal O h :
              (⟨n, a⟩ : O.Vertex) ⟶ ⟨n - 1, b⟩))) =
      (Quiver.FreeGroupoid.of ℤ).map
        (MagnitudeConjecture.RepetitionLine.down n) := by
  exact HomotopyGroupoid.lift_map_of O.rightMeshData
    O.collapseLabelling O.collapseLabelling_meshCompatible _

@[simp]
theorem rootLineFunctor_map_down (b₀ : B) (n : ℤ) :
    (O.rootLineFunctor b₀).map
        ((Quiver.FreeGroupoid.of ℤ).map
          (MagnitudeConjecture.RepetitionLine.down n)) =
      O.meshMorphism (⟨n, b₀⟩ : O.Vertex) := by
  rfl

/-- Collapsing after including the root line is the identity functor. -/
theorem rootLineFunctor_comp_collapseFunctor (b₀ : B) :
    O.rootLineFunctor b₀ ⋙ O.collapseFunctor =
      𝟭 (Quiver.FreeGroupoid ℤ) := by
  let F := O.rootLineFunctor b₀ ⋙ O.collapseFunctor
  have hF : Quiver.FreeGroupoid.of ℤ ⋙q F.toPrefunctor =
      Quiver.FreeGroupoid.of ℤ := by
    fapply Prefunctor.ext
    · intro n
      rfl
    · intro n m e
      rcases e with ⟨hm⟩
      subst m
      change O.collapseFunctor.map
          (O.meshMorphism (⟨n, b₀⟩ : O.Vertex)) =
        (Quiver.FreeGroupoid.of ℤ).map
          (MagnitudeConjecture.RepetitionLine.down n)
      exact O.collapseFunctor_map_meshMorphism (⟨n, b₀⟩ : O.Vertex)
  have hFlift := Quiver.FreeGroupoid.lift_unique
    (Quiver.FreeGroupoid.of ℤ) F hF
  have hidlift := Quiver.FreeGroupoid.lift_unique
    (Quiver.FreeGroupoid.of ℤ) (𝟭 (Quiver.FreeGroupoid ℤ)) (by rfl)
  exact hFlift.trans hidlift.symm

/-- Across one oriented tree edge, the horizontal repetition arrow commutes
with the formal mesh edge. -/
theorem horizontal_comp_meshMorphism
    {a b : B} (h : O.Arrow b a) (n : ℤ) :
    (HomotopyGroupoid.of O.rightMeshData).map
        (AugmentedArrow.old (RepetitionArrow.horizontal O h :
          (⟨n, a⟩ : O.Vertex) ⟶ ⟨n, b⟩)) ≫
      O.meshMorphism (⟨n, b⟩ : O.Vertex) =
    O.meshMorphism (⟨n, a⟩ : O.Vertex) ≫
      (HomotopyGroupoid.of O.rightMeshData).map
        (AugmentedArrow.old (RepetitionArrow.horizontal O h :
          (⟨n - 1, a⟩ : O.Vertex) ⟶ ⟨n - 1, b⟩)) := by
  let A : O.Vertex := ⟨n, a⟩
  let Bv : O.Vertex := ⟨n, b⟩
  let tA : O.Vertex := ⟨n - 1, a⟩
  let tB : O.Vertex := ⟨n - 1, b⟩
  let H : A ⟶ Bv := RepetitionArrow.horizontal O h
  let D : Bv ⟶ tA := RepetitionArrow.diagonal O h
  let H' : tA ⟶ tB := RepetitionArrow.horizontal O h
  let sA := O.nonprojectiveVertex A
  let sB := O.nonprojectiveVertex Bv
  let eA : O.rightMeshData.MeshArrow sA := ⟨Bv, H⟩
  let eB : O.rightMeshData.MeshArrow sB := ⟨tA, D⟩
  have hpairA :
      (O.rightMeshData.arrowEquiv sA Bv) H = D :=
    Subsingleton.elim _ _
  have hpairB :
      (O.rightMeshData.arrowEquiv sB tA) D = H' :=
    Subsingleton.elim _ _
  have hmeshA :=
    HomotopyGroupoid.of_mesh_eq_old_comp_old O.rightMeshData sA eA
  have hmeshB :=
    HomotopyGroupoid.of_mesh_eq_old_comp_old O.rightMeshData sB eB
  change (HomotopyGroupoid.of O.rightMeshData).map
      (AugmentedArrow.old H) ≫ O.meshMorphism Bv =
    O.meshMorphism A ≫ (HomotopyGroupoid.of O.rightMeshData).map
      (AugmentedArrow.old H')
  rw [show O.meshMorphism Bv = _ from hmeshB,
    show O.meshMorphism A = _ from hmeshA, hpairA, hpairB]
  simp only [eA, eB]
  exact (Category.assoc _ _ _).symm

end MagnitudeConjecture.RepetitionQuiver.OrientedTree

namespace MagnitudeConjecture.MeshCategory.RightMeshData.SectionalPath

universe u v

open MagnitudeConjecture.MeshCategory.RightMeshData.UniversalCover

variable {Q : Type u} [Quiver.{v} Q]
variable {T : RightMeshData Q} (x₀ : Q)

/-- The canonical horizontal prefix path, evaluated in the mesh-homotopy
groupoid of the sectional repetition. -/
def horizontalPrefixMorphism (n : ℤ) (p : T.SectionalPath x₀) :
    (show HomotopyGroupoid (orientedTree (T := T) x₀).rightMeshData from
      (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex)) ⟶
    (show HomotopyGroupoid (orientedTree (T := T) x₀).rightMeshData from
      (⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex)) :=
  HomotopyGroupoid.ofOldPath (orientedTree (T := T) x₀).rightMeshData
    (horizontalPrefixPath (T := T) x₀ n p)

@[simp]
theorem horizontalPrefixMorphism_root (n : ℤ) :
    horizontalPrefixMorphism (T := T) x₀ n (root x₀) = 𝟙 _ := by
  simp [horizontalPrefixMorphism]

/-- Extending a prefix appends the corresponding horizontal generator to its
canonical morphism. -/
theorem horizontalPrefixMorphism_cons
    (n : ℤ) (p : T.SectionalPath x₀) {z : Q}
    (a : p.endpoint ⟶ z)
    (h : T.PathIsMeshSectional (p.path.cons a)) :
    horizontalPrefixMorphism (T := T) x₀ n (cons x₀ p a h) =
      horizontalPrefixMorphism (T := T) x₀ n p ≫
        (HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map
          (AugmentedArrow.old
            (MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
              (orientedTree (T := T) x₀)
              (arrow_cons_parent x₀ p a h))) := by
  simp [horizontalPrefixMorphism, horizontalPrefixPath_cons]

set_option backward.isDefEq.respectTransparency false in
/-- A horizontal generator appends precisely the final edge of a sectional
prefix. -/
theorem horizontalPrefixMorphism_of_arrow
    (n : ℤ) {p q : T.SectionalPath x₀} (h : Arrow x₀ q p) :
    horizontalPrefixMorphism (T := T) x₀ n q =
      horizontalPrefixMorphism (T := T) x₀ n p ≫
        (HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map
          (AugmentedArrow.old
            (MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
              (orientedTree (T := T) x₀) h)) := by
  rcases q with ⟨z, q, hq⟩
  cases q with
  | nil => exact (h.1 rfl).elim
  | cons q a =>
      let p' : T.SectionalPath x₀ :=
        ⟨_, q, T.pathIsMeshSectional_of_cons hq⟩
      have hp : p = p' := h.2.symm
      subst p
      change horizontalPrefixMorphism (T := T) x₀ n (cons x₀ p' a hq) = _
      exact horizontalPrefixMorphism_cons (T := T) x₀ n p' a hq

set_option backward.isDefEq.respectTransparency false in
/-- The canonical horizontal path from the root line to any sectional prefix
commutes with translation represented by the formal mesh edge. -/
theorem horizontalPrefixMorphism_comp_meshMorphism
    (n : ℤ) (p : T.SectionalPath x₀) :
    horizontalPrefixMorphism (T := T) x₀ n p ≫
        (orientedTree (T := T) x₀).meshMorphism
          (⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex) =
      (orientedTree (T := T) x₀).meshMorphism
          (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex) ≫
        horizontalPrefixMorphism (T := T) x₀ (n - 1) p := by
  rcases p with ⟨y, p, hp⟩
  induction p with
  | nil =>
      change horizontalPrefixMorphism (T := T) x₀ n (root x₀) ≫
          (orientedTree (T := T) x₀).meshMorphism
            (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex) =
        (orientedTree (T := T) x₀).meshMorphism
            (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex) ≫
          horizontalPrefixMorphism (T := T) x₀ (n - 1) (root x₀)
      rw [horizontalPrefixMorphism_root, horizontalPrefixMorphism_root,
        Category.id_comp]
      exact (Category.comp_id _).symm
  | @cons z y p a ih =>
      let q : T.SectionalPath x₀ :=
        ⟨z, p, T.pathIsMeshSectional_of_cons hp⟩
      let e := arrow_cons_parent x₀ q a hp
      have ihq := ih (T.pathIsMeshSectional_of_cons hp)
      change horizontalPrefixMorphism (T := T) x₀ n (cons x₀ q a hp) ≫
          (orientedTree (T := T) x₀).meshMorphism
            (⟨n, cons x₀ q a hp⟩ :
              (orientedTree (T := T) x₀).Vertex) =
        (orientedTree (T := T) x₀).meshMorphism
            (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex) ≫
          horizontalPrefixMorphism (T := T) x₀ (n - 1)
            (cons x₀ q a hp)
      rw [horizontalPrefixMorphism_cons (T := T) x₀ n q a hp,
        horizontalPrefixMorphism_cons (T := T) x₀ (n - 1) q a hp]
      rw [Category.assoc]
      rw [(orientedTree (T := T) x₀).horizontal_comp_meshMorphism e n]
      rw [← Category.assoc, ihq, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal generator is the local mesh edge after removing its horizontal
half, hence has the root-line normal form. -/
theorem horizontalPrefixMorphism_comp_diagonal
    (n : ℤ) {p q : T.SectionalPath x₀} (h : Arrow x₀ q p) :
    horizontalPrefixMorphism (T := T) x₀ n q ≫
        (HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map
          (AugmentedArrow.old
            (MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
              (orientedTree (T := T) x₀) h)) =
      (orientedTree (T := T) x₀).meshMorphism
          (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex) ≫
        horizontalPrefixMorphism (T := T) x₀ (n - 1) p := by
  let O := orientedTree (T := T) x₀
  let X : O.Vertex := ⟨n, p⟩
  let Y : O.Vertex := ⟨n, q⟩
  let tX : O.Vertex := ⟨n - 1, p⟩
  let H : X ⟶ Y :=
    MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal O h
  let D : Y ⟶ tX :=
    MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal O h
  let sX := O.nonprojectiveVertex X
  let eX : O.rightMeshData.MeshArrow sX := ⟨Y, H⟩
  have hpair : (O.rightMeshData.arrowEquiv sX Y) H = D :=
    Subsingleton.elim _ _
  have hmesh :=
    HomotopyGroupoid.of_mesh_eq_old_comp_old O.rightMeshData sX eX
  have hprefix :=
    horizontalPrefixMorphism_comp_meshMorphism (T := T) x₀ n p
  rw [show O.meshMorphism X = _ from hmesh, hpair] at hprefix
  rw [horizontalPrefixMorphism_of_arrow (T := T) x₀ n h]
  apply (Category.assoc _ _ _).trans
  simpa only [eX] using hprefix

/-- Collapse to the integer level and include the root line again. -/
def rootRetractionFunctor :
    HomotopyGroupoid (orientedTree (T := T) x₀).rightMeshData ⥤
      HomotopyGroupoid (orientedTree (T := T) x₀).rightMeshData :=
  (orientedTree (T := T) x₀).collapseFunctor ⋙
    (orientedTree (T := T) x₀).rootLineFunctor (root x₀)

@[simp]
theorem rootRetractionFunctor_map_old_horizontal
    {p q : T.SectionalPath x₀} (h : Arrow x₀ q p) (n : ℤ) :
    (rootRetractionFunctor (T := T) x₀).map
        ((HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map
          (AugmentedArrow.old
            (MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
              (orientedTree (T := T) x₀) h :
              (⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex) ⟶
                ⟨n, q⟩))) = 𝟙 _ := by
  dsimp only [rootRetractionFunctor, Functor.comp_map]
  rw [(orientedTree (T := T) x₀).collapseFunctor_map_old_horizontal]
  exact ((orientedTree (T := T) x₀).rootLineFunctor (root x₀)).map_id _

@[simp]
theorem rootRetractionFunctor_map_old_diagonal
    {p q : T.SectionalPath x₀} (h : Arrow x₀ p q) (n : ℤ) :
    (rootRetractionFunctor (T := T) x₀).map
        ((HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map
          (AugmentedArrow.old
            (MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
              (orientedTree (T := T) x₀) h :
              (⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex) ⟶
                ⟨n - 1, q⟩))) =
      (orientedTree (T := T) x₀).meshMorphism
        (⟨n, root x₀⟩ : (orientedTree (T := T) x₀).Vertex) := by
  dsimp only [rootRetractionFunctor, Functor.comp_map]
  rw [(orientedTree (T := T) x₀).collapseFunctor_map_old_diagonal]
  exact (orientedTree (T := T) x₀).rootLineFunctor_map_down (root x₀) n

@[simp]
theorem rootRetractionFunctor_map_meshMorphism
    (X : (orientedTree (T := T) x₀).Vertex) :
    (rootRetractionFunctor (T := T) x₀).map
        ((orientedTree (T := T) x₀).meshMorphism X) =
      (orientedTree (T := T) x₀).meshMorphism
        (⟨X.level, root x₀⟩ :
          (orientedTree (T := T) x₀).Vertex) := by
  dsimp only [rootRetractionFunctor, Functor.comp_map]
  rw [(orientedTree (T := T) x₀).collapseFunctor_map_meshMorphism]
  exact (orientedTree (T := T) x₀).rootLineFunctor_map_down
    (root x₀) X.level

@[simp]
theorem rootRetractionFunctor_map_of_mesh
    (s : {X : (orientedTree (T := T) x₀).Vertex //
      X ∉ (orientedTree (T := T) x₀).rightMeshData.projective}) :
    (rootRetractionFunctor (T := T) x₀).map
        ((HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map
          (AugmentedArrow.mesh s)) =
      (orientedTree (T := T) x₀).meshMorphism
        (⟨s.1.level, root x₀⟩ :
          (orientedTree (T := T) x₀).Vertex) := by
  dsimp only [rootRetractionFunctor, Functor.comp_map,
    MagnitudeConjecture.RepetitionQuiver.OrientedTree.collapseFunctor]
  rw [HomotopyGroupoid.lift_map_of]
  exact (orientedTree (T := T) x₀).rootLineFunctor_map_down
    (root x₀) s.1.level

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the root-line contraction on every augmented-quiver
generator. -/
theorem rootRetraction_naturality_of
    {X Y : (orientedTree (T := T) x₀).Vertex}
    (e : @Quiver.Hom
      (AugmentedVertex (orientedTree (T := T) x₀).rightMeshData)
      (augmentedQuiver (orientedTree (T := T) x₀).rightMeshData)
      X Y) :
    (rootRetractionFunctor (T := T) x₀).map
        ((HomotopyGroupoid.of
          (orientedTree (T := T) x₀).rightMeshData).map e) ≫
      horizontalPrefixMorphism (T := T) x₀ Y.level Y.base =
    horizontalPrefixMorphism (T := T) x₀ X.level X.base ≫
      (HomotopyGroupoid.of
        (orientedTree (T := T) x₀).rightMeshData).map e := by
  cases e with
  | old a =>
      rcases X with ⟨n, p⟩
      rcases Y with ⟨m, q⟩
      rcases a with h | h
      · have hm := h.1.down
        change m = n at hm
        subst m
        have ha :
            (Sum.inl h :
              (⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex) ⟶
                ⟨n, q⟩) =
              MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
                (orientedTree (T := T) x₀) h.2.down :=
          @Subsingleton.elim _
            ((orientedTree (T := T) x₀).repetitionArrowSubsingleton _ _) _ _
        rw [ha]
        rw [rootRetractionFunctor_map_old_horizontal,
          Category.id_comp]
        exact horizontalPrefixMorphism_of_arrow (T := T) x₀ n h.2.down
      · have hm := h.1.down
        change m = n - 1 at hm
        subst m
        have ha :
            (Sum.inr h :
              (⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex) ⟶
                ⟨n - 1, q⟩) =
              MagnitudeConjecture.RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
                (orientedTree (T := T) x₀) h.2.down :=
          @Subsingleton.elim _
            ((orientedTree (T := T) x₀).repetitionArrowSubsingleton _ _) _ _
        rw [ha]
        rw [rootRetractionFunctor_map_old_diagonal]
        exact (horizontalPrefixMorphism_comp_diagonal
          (T := T) x₀ n h.2.down).symm
  | mesh s =>
      rcases s with ⟨⟨n, p⟩, hs⟩
      have hsEq :
          (⟨(⟨n, p⟩ : (orientedTree (T := T) x₀).Vertex), hs⟩ :
            {X // X ∉ (orientedTree (T := T) x₀).rightMeshData.projective}) =
            (orientedTree (T := T) x₀).nonprojectiveVertex ⟨n, p⟩ :=
        Subtype.ext rfl
      rw [hsEq]
      rw [rootRetractionFunctor_map_of_mesh]
      exact (horizontalPrefixMorphism_comp_meshMorphism
        (T := T) x₀ n p).symm

/-- The horizontal prefix morphisms form the counit of the root-line
contraction on the whole mesh-homotopy groupoid. -/
def rootRetractionNatTrans :
    rootRetractionFunctor (T := T) x₀ ⟶
      𝟭 (HomotopyGroupoid
        (orientedTree (T := T) x₀).rightMeshData) :=
  HomotopyGroupoid.natTransOfGenerator
    (orientedTree (T := T) x₀).rightMeshData
    (rootRetractionFunctor (T := T) x₀)
    (𝟭 (HomotopyGroupoid
      (orientedTree (T := T) x₀).rightMeshData))
    (fun X ↦ horizontalPrefixMorphism (T := T) x₀
      (show (orientedTree (T := T) x₀).Vertex from X).level
      (show (orientedTree (T := T) x₀).Vertex from X).base)
    (by
      intro X Y e
      exact rootRetraction_naturality_of (T := T) x₀ e)

/-- The root-line retraction is naturally isomorphic to the identity. -/
def rootRetractionIso :
    rootRetractionFunctor (T := T) x₀ ≅
      𝟭 (HomotopyGroupoid
        (orientedTree (T := T) x₀).rightMeshData) :=
  NatIso.ofComponents
    (fun X ↦ asIso (horizontalPrefixMorphism (T := T) x₀
      (show (orientedTree (T := T) x₀).Vertex from X).level
      (show (orientedTree (T := T) x₀).Vertex from X).base))
    (fun f ↦ (rootRetractionNatTrans (T := T) x₀).naturality f)

/-- The mesh-homotopy groupoid of the sectional-path repetition contracts to
the free groupoid on the oriented integer root line. -/
def repetitionHomotopyEquivalence :
    HomotopyGroupoid (orientedTree (T := T) x₀).rightMeshData ≌
      Quiver.FreeGroupoid ℤ :=
  CategoryTheory.Equivalence.mk
    (orientedTree (T := T) x₀).collapseFunctor
    ((orientedTree (T := T) x₀).rootLineFunctor (root x₀))
    (rootRetractionIso (T := T) x₀).symm
    (eqToIso
      (MagnitudeConjecture.RepetitionQuiver.OrientedTree.rootLineFunctor_comp_collapseFunctor
        (orientedTree (T := T) x₀) (root x₀)))

end MagnitudeConjecture.MeshCategory.RightMeshData.SectionalPath
