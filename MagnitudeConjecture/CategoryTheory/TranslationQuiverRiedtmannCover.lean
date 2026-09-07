import MagnitudeConjecture.CategoryTheory.TranslationQuiverSectionalPathTree
import MagnitudeConjecture.CategoryTheory.TranslationQuiverStable

/-!
# The canonical Riedtmann repetition-quiver map

For a stable polarized right translation quiver with bijective translation,
this file extends endpoint evaluation on the sectional-path tree to the
canonical map from its repetition quiver and packages that map as a covering
of polarized translation quivers.  The fundamental local calculation is the
star bijection at level zero: appending an arrow either creates a new
sectional child or is the polarized mesh partner leading to the translated
parent.  Integer-shift equivariance transports it to all stars, while stable
polarization supplies the costars and mesh compatibility.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u v
variable {Q : Type u} [Quiver.{v} Q]
variable (T : RightMeshData Q)
variable (hstable : T.projective = ∅)
variable (hbijective : Function.Bijective (T.stableTau hstable))

namespace RiedtmannCover

/-- The image of a repetition vertex: level `n` acts by `τ⁻ⁿ` on the
endpoint of its sectional path. -/
def shiftedVertex (n : ℤ) (x : Q) : Q :=
  (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.obj x)

theorem shiftedVertex_sub_one (n : ℤ) (x : Q) :
    shiftedVertex T hstable hbijective n (T.stableTau hstable x) =
      shiftedVertex T hstable hbijective (n - 1) x := by
  change
    (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.obj
      ((T.stableTauQuiverAut hstable hbijective).hom.obj x)) =
    (((T.stableTauQuiverAut hstable hbijective) ^ (-(n - 1))).hom.obj x)
  rw [show -(n - 1) = -n + 1 by omega]
  rw [zpow_add]
  rfl

@[simp]
theorem shiftedVertex_zero (x : Q) :
    shiftedVertex T hstable hbijective 0 x = x := by
  unfold shiftedVertex
  rw [show -(0 : ℤ) = 0 by omega, zpow_zero]
  rfl

@[simp]
theorem shiftedArrow_zero {x y : Q} (a : x ⟶ y) :
    ((T.stableTauQuiverAut hstable hbijective) ^ (0 : ℤ)).hom.map a = a := by
  change (Prefunctor.id Q).map a = a
  rfl

@[simp]
theorem shiftedArrow_neg_zero {x y : Q} (a : x ⟶ y) :
    ((T.stableTauQuiverAut hstable hbijective) ^ (-(0 : ℤ))).hom.map a = a := by
  change (Prefunctor.id Q).map a = a
  rfl

private theorem prefunctor_ext_of_map_heq
    {U : Type*} {V : Type*} [Quiver U] [Quiver V]
    {F G : Prefunctor U V}
    (hobj : ∀ x, F.obj x = G.obj x)
    (hmap : ∀ (x y : U) (a : x ⟶ y), F.map a ≍ G.map a) :
    F = G := by
  rcases F with ⟨Fobj, Fmap⟩
  rcases G with ⟨Gobj, Gmap⟩
  have hobj' : Fobj = Gobj := funext hobj
  subst Gobj
  congr
  funext x y a
  exact eq_of_heq (hmap x y a)

private theorem prefunctor_map_cast_heq
    {U : Type*} {V : Type*} [Quiver U] [Quiver V]
    (F : Prefunctor U V) {x y x' y' : U}
    (hx : x = x') (hy : y = y') (a : x ⟶ y) :
    F.map (Quiver.Hom.cast hx hy a) ≍ F.map a := by
  cases hx
  cases hy
  rfl

private def quiverIsoStarEquiv
    (E : CategoryTheory.Quiv.of Q ≅ CategoryTheory.Quiv.of Q)
    (x : Q) : Quiver.Star x ≃ Quiver.Star (E.hom.obj x) :=
  Equiv.sigmaCongr (CategoryTheory.Quiv.equivOfIso E)
    (fun _ ↦ CategoryTheory.Quiv.homEquivOfIso E)

/-- Riedtmann's sectional tree at the chosen base vertex. -/
abbrev Tree (x₀ : Q) :=
  RightMeshData.SectionalPath.orientedTree (T := T) x₀

/-- The canonical quiver map from the repetition of the sectional-path tree.
Horizontal arrows are translated final arrows; diagonal arrows are translated
polarized partners. -/
def projection (x₀ : Q) : (Tree T x₀).Vertex ⥤q Q where
  obj X := shiftedVertex T hstable hbijective X.level X.base.endpoint
  map {X Y} a := by
    rcases X with ⟨n, p⟩
    rcases Y with ⟨m, q⟩
    rcases a with h | h
    · have hm := h.1.down
      have hqp := h.2.down
      change m = n at hm
      change RightMeshData.SectionalPath.Arrow x₀ q p at hqp
      subst m
      exact
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
          (RightMeshData.SectionalPath.extensionArrow x₀ hqp))
    · have hm := h.1.down
      have hpq := h.2.down
      change m = n - 1 at hm
      change RightMeshData.SectionalPath.Arrow x₀ p q at hpq
      subst m
      let b := (T.arrowEquiv (T.stableNonprojective hstable q.endpoint)
        p.endpoint) (RightMeshData.SectionalPath.extensionArrow x₀ hpq)
      exact Quiver.Hom.cast rfl
        (shiftedVertex_sub_one T hstable hbijective n q.endpoint)
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map b)

@[simp]
theorem projection_map_horizontal (x₀ : Q) (n : ℤ)
    {p q : T.SectionalPath x₀}
    (h : RightMeshData.SectionalPath.Arrow x₀ q p) :
    (projection T hstable hbijective x₀).map
        (RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
          (Tree T x₀) h) =
      (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
        (RightMeshData.SectionalPath.extensionArrow x₀ h)) :=
  rfl

@[simp]
theorem projection_map_diagonal (x₀ : Q) (n : ℤ)
    {p q : T.SectionalPath x₀}
    (h : RightMeshData.SectionalPath.Arrow x₀ p q) :
    (projection T hstable hbijective x₀).map
        (RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
          (O := Tree T x₀) (n := n) h) =
      Quiver.Hom.cast rfl
        (shiftedVertex_sub_one T hstable hbijective n q.endpoint)
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
          ((T.arrowEquiv (T.stableNonprojective hstable q.endpoint)
            p.endpoint)
            (RightMeshData.SectionalPath.extensionArrow x₀ h))) :=
  rfl

theorem ne_root_of_not_sectional_cons (x₀ : Q)
    (p : T.SectionalPath x₀) {z : Q} (a : p.endpoint ⟶ z)
    (h : ¬ T.PathIsMeshSectional (p.path.cons a)) :
    p ≠ RightMeshData.SectionalPath.root x₀ := by
  intro hp
  subst p
  rcases T.terminalMeshHook_of_not_sectional_cons
      (Quiver.Path.nil : Quiver.Path x₀ x₀)
      (T.pathIsMeshSectional_nil x₀) a h with
    ⟨s, b, left, hy, hz, hpath, ha⟩
  have hlength := congrArg Quiver.Path.length hpath
  cases hy
  simp at hlength

/-- Explicit inverse to the level-zero star map. -/
noncomputable def zeroStarLift (x₀ : Q) (p : T.SectionalPath x₀) :
    Quiver.Star p.endpoint →
      Quiver.Star (⟨0, p⟩ : (Tree T x₀).Vertex) := by
  classical
  exact fun A ↦
    if h : T.PathIsMeshSectional (p.path.cons A.2) then
      ⟨⟨0, RightMeshData.SectionalPath.cons x₀ p A.2 h⟩,
        RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal (Tree T x₀)
          (RightMeshData.SectionalPath.arrow_cons_parent x₀ p A.2 h)⟩
    else
      ⟨⟨-1, RightMeshData.SectionalPath.parent x₀ p⟩,
        RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal (Tree T x₀)
          (RightMeshData.SectionalPath.arrow_parent x₀ p
            (ne_root_of_not_sectional_cons T x₀ p A.2 h))⟩

theorem projection_star_zeroStarLift (x₀ : Q)
    (p : T.SectionalPath x₀) (A : Quiver.Star p.endpoint) :
    (projection T hstable hbijective x₀).star ⟨0, p⟩
        (zeroStarLift T x₀ p A) = A := by
  classical
  by_cases h : T.PathIsMeshSectional (p.path.cons A.2)
  · rw [show zeroStarLift T x₀ p A =
        ⟨⟨0, RightMeshData.SectionalPath.cons x₀ p A.2 h⟩,
          RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
            (Tree T x₀)
              (RightMeshData.SectionalPath.arrow_cons_parent
                x₀ p A.2 h)⟩ by simp [zeroStarLift, h]]
    simp only [Prefunctor.star_apply, projection_map_horizontal]
    apply Sigma.ext
    · exact shiftedVertex_zero T hstable hbijective A.1
    · exact heq_of_eq (shiftedArrow_zero T hstable hbijective A.2)
  · have hne := ne_root_of_not_sectional_cons T x₀ p A.2 h
    rcases p with ⟨y, p, hp⟩
    cases p with
    | nil =>
        exact (hne rfl).elim
    | cons p c =>
        rename_i w
        let s := T.stableNonprojective hstable w
        obtain ⟨hz, ha⟩ := T.paired_eq_of_sectional_cons_not_sectional
          s p c hp A.2 h
        let d := RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
          (O := Tree T x₀) (n := 0)
            (RightMeshData.SectionalPath.arrow_parent x₀
              ⟨y, p.cons c, hp⟩ hne)
        rw [show zeroStarLift T x₀
            ⟨y, p.cons c, hp⟩ A =
          ⟨⟨0 - 1, RightMeshData.SectionalPath.parent x₀
              ⟨y, p.cons c, hp⟩⟩,
            d⟩ by
              simp only [zeroStarLift, dif_neg h]
              congr 1]
        let htarget : shiftedVertex T hstable hbijective (0 - 1) w = A.1 :=
          (shiftedVertex_sub_one T hstable hbijective 0 w).symm.trans hz.symm
        have hmap : HEq
            ((projection T hstable hbijective x₀).map d) A.2 := by
          dsimp only [d]
          rw [projection_map_diagonal]
          simp only [RightMeshData.SectionalPath.parent,
            RightMeshData.SectionalPath.extensionArrow]
          rw [shiftedArrow_neg_zero]
          have hcast := Quiver.Hom.cast_heq rfl
            (shiftedVertex_sub_one T hstable hbijective 0 w)
            ((T.arrowEquiv s y) c)
          have hA : A.2 ≍ (T.arrowEquiv s y) c :=
            (Quiver.Hom.cast_eq_iff_heq rfl hz A.2
              ((T.arrowEquiv s y) c)).1 ha
          exact hcast.trans hA.symm
        exact Sigma.ext htarget hmap

theorem zeroStarLift_projection_star (x₀ : Q)
    (p : T.SectionalPath x₀)
    (E : Quiver.Star (⟨0, p⟩ : (Tree T x₀).Vertex)) :
    zeroStarLift T x₀ p
        ((projection T hstable hbijective x₀).star ⟨0, p⟩ E) = E := by
  classical
  rcases E with ⟨⟨m, q⟩, e⟩
  rcases e with e | e
  · have hm := e.1.down
    have hqp := e.2.down
    change m = 0 at hm
    change RightMeshData.SectionalPath.Arrow x₀ q p at hqp
    subst m
    have hepair : e = ⟨PLift.up rfl, PLift.up hqp⟩ :=
      Subsingleton.elim _ _
    have heq : (Sum.inl e :
        (Tree T x₀).RepetitionArrow ⟨0, p⟩ ⟨0, q⟩) =
        RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
          (Tree T x₀) hqp := congrArg Sum.inl hepair
    rw [heq]
    let a := RightMeshData.SectionalPath.extensionArrow x₀ hqp
    have hstar :
        (projection T hstable hbijective x₀).star ⟨0, p⟩
            ⟨⟨0, q⟩,
              RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
                (Tree T x₀) hqp⟩ =
          (⟨q.endpoint, a⟩ : Quiver.Star p.endpoint) := by
      apply Sigma.ext
      · exact shiftedVertex_zero T hstable hbijective q.endpoint
      · exact heq_of_eq (shiftedArrow_neg_zero T hstable hbijective a)
    rw [hstar]
    have hsec := RightMeshData.SectionalPath.extension_isSectional x₀ hqp
    unfold zeroStarLift
    rw [dif_pos hsec]
    let child := RightMeshData.SectionalPath.cons x₀ p a hsec
    have hchild : child = q :=
      RightMeshData.SectionalPath.cons_extensionArrow x₀ hqp
    have hvertex : (⟨0, child⟩ : (Tree T x₀).Vertex) = ⟨0, q⟩ := by
      rw [hchild]
    refine Sigma.ext hvertex ?_
    exact (Quiver.Hom.cast_heq rfl hvertex _).symm.trans
      (heq_of_eq (Subsingleton.elim _ _))
  · have hm := e.1.down
    have hpq := e.2.down
    change m = 0 - 1 at hm
    change RightMeshData.SectionalPath.Arrow x₀ p q at hpq
    subst m
    have hepair : e = ⟨PLift.up rfl, PLift.up hpq⟩ :=
      Subsingleton.elim _ _
    have heq : (Sum.inr e :
        (Tree T x₀).RepetitionArrow ⟨0, p⟩ ⟨0 - 1, q⟩) =
        RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
          (O := Tree T x₀) (n := 0) hpq := congrArg Sum.inr hepair
    rw [heq]
    let c := RightMeshData.SectionalPath.extensionArrow x₀ hpq
    let s := T.stableNonprojective hstable q.endpoint
    let paired := (T.arrowEquiv s p.endpoint) c
    let hsub := shiftedVertex_sub_one T hstable hbijective 0 q.endpoint
    change T.tau s = shiftedVertex T hstable hbijective (0 - 1) q.endpoint at hsub
    have hnot : ¬ T.PathIsMeshSectional
        (p.path.cons (paired.cast rfl hsub)) := by
      intro hsectional
      have hcast : T.PathIsMeshSectional
          ((p.path.cons paired).cast rfl hsub) := by
        rw [Quiver.Path.cast_cons, Quiver.Path.cast_rfl_rfl]
        exact hsectional
      have hliteral := (T.pathIsMeshSectional_cast
        (p.path.cons paired) rfl hsub).1 hcast
      apply T.cons_paired_not_sectional s q.path c
      dsimp only [s, c, paired] at hliteral ⊢
      rw [RightMeshData.SectionalPath.path_eq_parent_path_cons x₀ hpq] at hliteral
      exact hliteral
    have hstar :
        (projection T hstable hbijective x₀).star ⟨0, p⟩
            ⟨⟨0 - 1, q⟩,
              RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
                (O := Tree T x₀) (n := 0) hpq⟩ =
          (⟨shiftedVertex T hstable hbijective (0 - 1) q.endpoint,
            paired.cast rfl hsub⟩ : Quiver.Star p.endpoint) := by
      apply Sigma.ext rfl
      exact HEq.rfl
    rw [hstar]
    unfold zeroStarLift
    rw [dif_neg hnot]
    have hvertex :
        (⟨-1, RightMeshData.SectionalPath.parent x₀ p⟩ :
          (Tree T x₀).Vertex) = ⟨0 - 1, q⟩ := by
      rw [← hpq.2]
      congr 1
    refine Sigma.ext hvertex ?_
    exact (Quiver.Hom.cast_heq rfl hvertex _).symm.trans
      (heq_of_eq (Subsingleton.elim _ _))

/-- The canonical Riedtmann map is bijective on outgoing stars at level zero. -/
theorem projection_star_zero_bijective (x₀ : Q)
    (p : T.SectionalPath x₀) :
    Function.Bijective
      ((projection T hstable hbijective x₀).star ⟨0, p⟩) :=
  ⟨Function.LeftInverse.injective
      (zeroStarLift_projection_star T hstable hbijective x₀ p),
    Function.RightInverse.surjective
      (projection_star_zeroStarLift T hstable hbijective x₀ p)⟩

/-- Level shift upstairs corresponds to the same inverse translation power
downstairs on objects. -/
theorem projection_levelShift_obj (x₀ : Q) (n : ℤ)
    (X : (Tree T x₀).Vertex) :
    (projection T hstable hbijective x₀).obj
        (((Tree T x₀).levelShiftQuiverIso n).hom.obj X) =
      ((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.obj
        ((projection T hstable hbijective x₀).obj X) := by
  rcases X with ⟨m, p⟩
  change
    (((T.stableTauQuiverAut hstable hbijective) ^ (-(m + n))).hom.obj
      p.endpoint) =
    (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.obj
      (((T.stableTauQuiverAut hstable hbijective) ^ (-m)).hom.obj
        p.endpoint))
  rw [show -(m + n) = -n + -m by omega, zpow_add]
  rfl

/-- The canonical projection intertwines integer-coordinate shifts with
inverse powers of stable translation. -/
theorem projection_levelShift (x₀ : Q) (n : ℤ) :
    ((Tree T x₀).levelShiftQuiverIso n).hom ⋙q
        projection T hstable hbijective x₀ =
      projection T hstable hbijective x₀ ⋙q
        ((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom := by
  apply prefunctor_ext_of_map_heq
  · exact projection_levelShift_obj T hstable hbijective x₀ n
  · intro X Y e
    rcases X with ⟨m, p⟩
    rcases Y with ⟨l, q⟩
    rcases e with e | e
    · have hl := e.1.down
      change l = m at hl
      subst l
      let a := RightMeshData.SectionalPath.extensionArrow x₀ e.2.down
      change
        (((T.stableTauQuiverAut hstable hbijective) ^ (-(m + n))).hom.map a) ≍
          (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
            (((T.stableTauQuiverAut hstable hbijective) ^ (-m)).hom.map a))
      rw [show -(m + n) = -n + -m by omega, zpow_add]
      rfl
    · have hl := e.1.down
      change l = m - 1 at hl
      subst l
      let b := (T.arrowEquiv (T.stableNonprojective hstable q.endpoint)
        p.endpoint) (RightMeshData.SectionalPath.extensionArrow x₀ e.2.down)
      let d := RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
        (O := Tree T x₀) (n := m + n) e.2.down
      have hX : ((Tree T x₀).levelShiftQuiverIso n).hom.obj
          (⟨m, p⟩ : (Tree T x₀).Vertex) = ⟨m + n, p⟩ := rfl
      have hY : ((Tree T x₀).levelShiftQuiverIso n).hom.obj
          (⟨m - 1, q⟩ : (Tree T x₀).Vertex) = ⟨m + n - 1, q⟩ := by
        change (⟨(m - 1) + n, q⟩ : (Tree T x₀).Vertex) =
          ⟨m + n - 1, q⟩
        congr 1
        omega
      have hshift : Quiver.Hom.cast hX hY
          (((Tree T x₀).levelShiftQuiverIso n).hom.map (Sum.inr e)) = d := by
        exact (RepetitionQuiver.OrientedTree.repetitionArrowSubsingleton
          (Tree T x₀) _ _).elim _ _
      have hleft :
          (projection T hstable hbijective x₀).map
              (((Tree T x₀).levelShiftQuiverIso n).hom.map (Sum.inr e)) ≍
            (projection T hstable hbijective x₀).map d := by
        have hmap := congrArg
          (fun c ↦ (projection T hstable hbijective x₀).map c) hshift
        exact (prefunctor_map_cast_heq
          (projection T hstable hbijective x₀) hX hY _).symm.trans
            (heq_of_eq hmap)
      refine hleft.trans ?_
      let d₀ := RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
        (O := Tree T x₀) (n := m) e.2.down
      have he₀ : (Sum.inr e :
          (Tree T x₀).RepetitionArrow ⟨m, p⟩ ⟨m - 1, q⟩) = d₀ :=
        (RepetitionQuiver.OrientedTree.repetitionArrowSubsingleton
          (Tree T x₀) _ _).elim _ _
      rw [he₀]
      dsimp only [d, d₀]
      rw [projection_map_diagonal]
      change _ ≍
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
          ((projection T hstable hbijective x₀).map
            (RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
              (O := Tree T x₀) (n := m) e.2.down)))
      rw [projection_map_diagonal]
      change
        (Quiver.Hom.cast _ _
          (((T.stableTauQuiverAut hstable hbijective) ^ (-(m + n))).hom.map b)) ≍
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
          (Quiver.Hom.cast _ _
            (((T.stableTauQuiverAut hstable hbijective) ^ (-m)).hom.map b)))
      refine (Quiver.Hom.cast_heq _ _ _).trans ?_
      refine (show
          (((T.stableTauQuiverAut hstable hbijective) ^ (-(m + n))).hom.map b) ≍
            (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
              (((T.stableTauQuiverAut hstable hbijective) ^ (-m)).hom.map b)) by
        rw [show -(m + n) = -n + -m by omega, zpow_add]
        rfl).trans ?_
      exact (prefunctor_map_cast_heq
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom) _ _ _).symm

/-- The canonical Riedtmann map is bijective on every outgoing star. -/
theorem projection_star_bijective (x₀ : Q)
    (X : (Tree T x₀).Vertex) :
    Function.Bijective ((projection T hstable hbijective x₀).star X) := by
  rcases X with ⟨n, p⟩
  let S := (Tree T x₀).levelShiftQuiverIso n
  let A := (T.stableTauQuiverAut hstable hbijective) ^ (-n)
  let X₀ : (Tree T x₀).Vertex := ⟨0, p⟩
  have hS : Function.Bijective (S.hom.star X₀) :=
    (quiverIsoStarEquiv S X₀).bijective
  have hA : Function.Bijective
      (A.hom.star ((projection T hstable hbijective x₀).obj X₀)) :=
    (quiverIsoStarEquiv A
      ((projection T hstable hbijective x₀).obj X₀)).bijective
  have hzero : Function.Bijective
      ((projection T hstable hbijective x₀).star X₀) :=
    projection_star_zero_bijective T hstable hbijective x₀ p
  have hright : Function.Bijective
      ((projection T hstable hbijective x₀ ⋙q A.hom).star X₀) := by
    change Function.Bijective
      (A.hom.star ((projection T hstable hbijective x₀).obj X₀) ∘
        (projection T hstable hbijective x₀).star X₀)
    exact hA.comp hzero
  have hleft : Function.Bijective
      ((S.hom ⋙q projection T hstable hbijective x₀).star X₀) := by
    rw [projection_levelShift T hstable hbijective x₀ n]
    exact hright
  have hprojected : Function.Bijective
      ((projection T hstable hbijective x₀).star (S.hom.obj X₀)) := by
    apply (Function.Bijective.of_comp_iff _ hS).mp
    exact hleft
  have hSX₀ : S.hom.obj X₀ = (⟨n, p⟩ : (Tree T x₀).Vertex) := by
    change (⟨0 + n, p⟩ : (Tree T x₀).Vertex) = ⟨n, p⟩
    rw [zero_add]
  rw [hSX₀] at hprojected
  exact hprojected

theorem stableTau_shiftedVertex (n : ℤ) (x : Q) :
    T.stableTau hstable (shiftedVertex T hstable hbijective n x) =
      shiftedVertex T hstable hbijective (n - 1) x := by
  change
    (T.stableTauQuiverAut hstable hbijective).hom.obj
      (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.obj x) =
    (((T.stableTauQuiverAut hstable hbijective) ^ (-(n - 1))).hom.obj x)
  rw [show -(n - 1) = 1 + -n by omega, zpow_add]
  rfl

/-- Projective-boundary compatibility is automatic for the stable source and
target. -/
theorem projection_map_projective_iff (x₀ : Q)
    (X : (Tree T x₀).Vertex) :
    X ∈ (Tree T x₀).rightMeshData.projective ↔
      (projection T hstable hbijective x₀).obj X ∈ T.projective := by
  simp [hstable]

/-- The canonical projection preserves stable translation. -/
theorem projection_map_tau (x₀ : Q)
    (X : {X : (Tree T x₀).Vertex //
      X ∉ (Tree T x₀).rightMeshData.projective}) :
    (projection T hstable hbijective x₀).obj
        ((Tree T x₀).rightMeshData.tau X) =
      T.tau (mappedNonprojective (Tree T x₀).rightMeshData T
        (projection T hstable hbijective x₀)
        (projection_map_projective_iff T hstable hbijective x₀) X) := by
  rcases X with ⟨⟨n, p⟩, hX⟩
  change shiftedVertex T hstable hbijective (n - 1) p.endpoint =
    T.stableTau hstable (shiftedVertex T hstable hbijective n p.endpoint)
  exact (stableTau_shiftedVertex T hstable hbijective n p.endpoint).symm

private theorem totalArrow_arrow_heq_of_eq
    {A B : TotalArrow Q} (h : A = B) : A.2.2 ≍ B.2.2 := by
  cases h
  rfl

/-- The canonical projection preserves the chosen mesh polarization. -/
theorem projection_map_arrowEquiv (x₀ : Q)
    (X : {X : (Tree T x₀).Vertex //
      X ∉ (Tree T x₀).rightMeshData.projective})
    (Y : (Tree T x₀).Vertex) (a : X.1 ⟶ Y) :
    ((projection T hstable hbijective x₀).map
      (((Tree T x₀).rightMeshData.arrowEquiv X Y) a)).cast rfl
        (projection_map_tau T hstable hbijective x₀ X) =
      (T.arrowEquiv
        (mappedNonprojective (Tree T x₀).rightMeshData T
          (projection T hstable hbijective x₀)
          (projection_map_projective_iff T hstable hbijective x₀) X)
        ((projection T hstable hbijective x₀).obj Y))
        ((projection T hstable hbijective x₀).map a) := by
  rcases X with ⟨⟨n, p⟩, hX⟩
  rcases Y with ⟨m, q⟩
  rcases a with a | a
  · have hm := a.1.down
    change m = n at hm
    subst m
    let h := a.2.down
    have ha : (Sum.inl a :
        (Tree T x₀).RepetitionArrow ⟨n, p⟩ ⟨n, q⟩) =
        RepetitionQuiver.OrientedTree.RepetitionArrow.horizontal
          (Tree T x₀) h :=
      (RepetitionQuiver.OrientedTree.repetitionArrowSubsingleton
        (Tree T x₀) _ _).elim _ _
    rw [ha]
    let c := RightMeshData.SectionalPath.extensionArrow x₀ h
    change
      (Quiver.Hom.cast _ _
        (Quiver.Hom.cast rfl
          (shiftedVertex_sub_one T hstable hbijective n p.endpoint)
          (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map
            ((T.arrowEquiv (T.stableNonprojective hstable p.endpoint)
              q.endpoint) c)))) =
        (T.arrowEquiv
          (T.stableNonprojective hstable
            (shiftedVertex T hstable hbijective n p.endpoint))
          (shiftedVertex T hstable hbijective n q.endpoint))
          (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map c)
    rw [Quiver.Hom.cast_eq_iff_heq]
    refine (Quiver.Hom.cast_heq _ _ _).trans ?_
    exact (Quiver.Hom.cast_eq_iff_heq _ _ _ _).1
      (T.stableTau_zpow_map_arrowEquiv hstable hbijective (-n) c)
  · have hm := a.1.down
    change m = n - 1 at hm
    subst m
    let h := a.2.down
    have ha : (Sum.inr a :
        (Tree T x₀).RepetitionArrow ⟨n, p⟩ ⟨n - 1, q⟩) =
        RepetitionQuiver.OrientedTree.RepetitionArrow.diagonal
          (O := Tree T x₀) (n := n) h :=
      (RepetitionQuiver.OrientedTree.repetitionArrowSubsingleton
        (Tree T x₀) _ _).elim _ _
    rw [ha]
    let c := RightMeshData.SectionalPath.extensionArrow x₀ h
    let paired := (T.arrowEquiv
      (T.stableNonprojective hstable q.endpoint) p.endpoint) c
    let inner := Quiver.Hom.cast rfl
      (shiftedVertex_sub_one T hstable hbijective n q.endpoint)
      (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map paired)
    change
      (Quiver.Hom.cast _ _
        (((T.stableTauQuiverAut hstable hbijective) ^ (-(n - 1))).hom.map c)) =
      (T.arrowEquiv
        (T.stableNonprojective hstable
          (shiftedVertex T hstable hbijective n p.endpoint))
        (shiftedVertex T hstable hbijective (n - 1) q.endpoint)) inner
    rw [Quiver.Hom.cast_eq_iff_heq]
    let E := (T.stableTauQuiverAut hstable hbijective) ^ (-n)
    let A₀ : TotalArrow Q := ⟨q.endpoint, p.endpoint, c⟩
    let Lcast : TotalArrow Q :=
      ⟨shiftedVertex T hstable hbijective n p.endpoint,
        shiftedVertex T hstable hbijective (n - 1) q.endpoint, inner⟩
    have hcast : quiverAutTotalArrowAction (Q := Q) E
        (T.stablePolarizationTotal hstable A₀) = Lcast := by
      rw [quiverAutTotalArrowAction_apply]
      dsimp only [E, A₀, Lcast, stablePolarizationTotal, paired, inner]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Sigma.ext
        · exact shiftedVertex_sub_one T hstable hbijective n q.endpoint
        · exact (Quiver.Hom.cast_heq rfl
            (shiftedVertex_sub_one T hstable hbijective n q.endpoint) _).symm
    have hcomm := T.stableTau_zpow_totalArrow_commute
      hstable hbijective (-n) A₀
    have hcombined :
        T.stablePolarizationTotal hstable Lcast =
          T.stablePolarizationTotal hstable
            (T.stablePolarizationTotal hstable
              (quiverAutTotalArrowAction (Q := Q) E A₀)) :=
      (congrArg (T.stablePolarizationTotal hstable) hcast).symm.trans
        (congrArg (T.stablePolarizationTotal hstable) hcomm)
    have hrhs := totalArrow_arrow_heq_of_eq hcombined
    dsimp only [Lcast, A₀, E, stablePolarizationTotal] at hrhs
    change
      (T.arrowEquiv
        (T.stableNonprojective hstable
          (shiftedVertex T hstable hbijective n p.endpoint))
        (shiftedVertex T hstable hbijective (n - 1) q.endpoint)) inner ≍
      (T.stableTauQuiverAut hstable hbijective).hom.map
        (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map c) at hrhs
    refine (show
        (((T.stableTauQuiverAut hstable hbijective) ^ (-(n - 1))).hom.map c) ≍
          (T.stableTauQuiverAut hstable hbijective).hom.map
            (((T.stableTauQuiverAut hstable hbijective) ^ (-n)).hom.map c) by
      rw [show -(n - 1) = 1 + -n by omega, zpow_add]
      rfl).trans hrhs.symm

private theorem source_stableTau_bijective (x₀ : Q) :
    Function.Bijective
      ((Tree T x₀).rightMeshData.stableTau
        (Tree T x₀).rightMeshData_projective) := by
  change Function.Bijective (Tree T x₀).tauVertex
  exact (Tree T x₀).tauVertex_bijective

/-- Polarization turns the costar square for the canonical projection into
its already proved star square. -/
theorem projection_costar_star_comm (x₀ : Q)
    (Y : (Tree T x₀).Vertex) :
    (projection T hstable hbijective x₀).star Y ∘
        (Tree T x₀).rightMeshData.stableCostarStarEquiv
          (Tree T x₀).rightMeshData_projective
          (source_stableTau_bijective T x₀) Y =
      T.stableCostarStarEquiv hstable hbijective
          ((projection T hstable hbijective x₀).obj Y) ∘
        (projection T hstable hbijective x₀).costar Y := by
  funext A
  rcases A with ⟨X, a⟩
  apply Sigma.ext
  · exact projection_map_tau T hstable hbijective x₀
      ⟨X, by simp⟩
  · exact (Quiver.Hom.cast_heq rfl
      (projection_map_tau T hstable hbijective x₀ ⟨X, by simp⟩) _).symm.trans
        (heq_of_eq
          (projection_map_arrowEquiv T hstable hbijective x₀
            ⟨X, by simp⟩ Y a))

/-- The canonical Riedtmann map is bijective on every incoming costar. -/
theorem projection_costar_bijective (x₀ : Q)
    (Y : (Tree T x₀).Vertex) :
    Function.Bijective ((projection T hstable hbijective x₀).costar Y) := by
  let sourceEquiv :=
    (Tree T x₀).rightMeshData.stableCostarStarEquiv
      (Tree T x₀).rightMeshData_projective
      (source_stableTau_bijective T x₀) Y
  let targetEquiv := T.stableCostarStarEquiv hstable hbijective
    ((projection T hstable hbijective x₀).obj Y)
  have hleft : Function.Bijective
      ((projection T hstable hbijective x₀).star Y ∘ sourceEquiv) :=
    (projection_star_bijective T hstable hbijective x₀ Y).comp
      sourceEquiv.bijective
  have hright : Function.Bijective
      (targetEquiv ∘ (projection T hstable hbijective x₀).costar Y) := by
    rw [← projection_costar_star_comm T hstable hbijective x₀ Y]
    exact hleft
  exact (Function.Bijective.of_comp_iff' targetEquiv.bijective _).mp hright

/-- Riedtmann's canonical projection, packaged as a covering of polarized
stable translation quivers. -/
def cover (x₀ : Q) :
    RightMeshData.Cover (Tree T x₀).rightMeshData T where
  toPrefunctor := projection T hstable hbijective x₀
  isCovering :=
    { star_bijective := projection_star_bijective T hstable hbijective x₀
      costar_bijective := projection_costar_bijective T hstable hbijective x₀ }
  map_projective_iff := projection_map_projective_iff T hstable hbijective x₀
  map_tau := projection_map_tau T hstable hbijective x₀
  map_arrowEquiv := projection_map_arrowEquiv T hstable hbijective x₀

end RiedtmannCover
end MagnitudeConjecture.MeshCategory.RightMeshData
