import MagnitudeConjecture.Algebra.StringBoundarySquare

/-!
# Mixed cohook-hook boundary squares

The peak/non-peak cases of Butler--Ringel's canonical sequences combine a
cohook deletion at one endpoint with a hook at the other.  In the right-module
convention this is a commuting square with horizontal monomorphisms and
vertical epimorphisms.  Its associated short complex has the upper-right word
as source, the lower-left and upper-right-corner words as middle terms, and
the cohook-extended word as target.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A commuting boundary square with a negative extension on the left and a
positive extension on the right. -/
structure MixedBoundarySquare (D : Word R) where
  rightResult : Word R
  right : PositiveBoundaryExtension D rightResult
  left : LeftNegativeBoundaryExtension D
  cornerLeft : LeftNegativeBoundaryExtension rightResult
  cornerRight : PositiveBoundaryExtension left.result cornerLeft.result
  steps_eq : cornerLeft.steps = left.steps
  position_commutes : ∀ {x : Q} (i : D.PositionAt x),
    cornerRight.toRightExtension.position (left.position i) =
      cornerLeft.position (right.toRightExtension.position i)
  position_intersection : ∀ {x : Q}
      (q : left.result.PositionAt x)
      (p : rightResult.PositionAt x),
    cornerRight.toRightExtension.position q = cornerLeft.position p →
      ∃ i : D.PositionAt x,
        left.position i = q ∧ right.toRightExtension.position i = p

namespace MixedBoundarySquare

/-- Equal left-extension lengths force the position coherence required by a
mixed boundary square. -/
def ofExtensions {D rightResult : Word R}
    (right : PositiveBoundaryExtension D rightResult)
    (left : LeftNegativeBoundaryExtension D)
    (cornerLeft : LeftNegativeBoundaryExtension rightResult)
    (cornerRight : PositiveBoundaryExtension left.result cornerLeft.result)
    (hsteps : cornerLeft.steps = left.steps) :
    MixedBoundarySquare D where
  rightResult := rightResult
  right := right
  left := left
  cornerLeft := cornerLeft
  cornerRight := cornerRight
  steps_eq := hsteps
  position_commutes := by
    intro x i
    apply PositionAt.ext_index
    simp only [RightExtension.position_index,
      LeftNegativeBoundaryExtension.position_index, hsteps]
  position_intersection := by
    intro x q p hqp
    have hindex := congrArg PositionAt.index hqp
    simp only [RightExtension.position_index,
      LeftNegativeBoundaryExtension.position_index] at hindex
    have hqBound : left.steps ≤ q.index := by
      rw [← hsteps]
      omega
    rcases left.exists_eq_position_of_steps_le q hqBound with ⟨i, hi⟩
    refine ⟨i, hi, ?_⟩
    apply cornerLeft.position_injective
    calc
      cornerLeft.position (right.toRightExtension.position i) =
          cornerRight.toRightExtension.position (left.position i) := by
        apply PositionAt.ext_index
        simp only [RightExtension.position_index,
          LeftNegativeBoundaryExtension.position_index, hsteps]
      _ = cornerRight.toRightExtension.position q := by rw [hi]
      _ = cornerLeft.position p := hqp

/-- The common corner word. -/
abbrev corner {D : Word R} (square : MixedBoundarySquare D) : Word R :=
  square.cornerLeft.result

/-- Projection from the right-hook result back to the shortened word. -/
def rightToBaseMap {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    square.rightResult.rightModule hmono ⟶ D.rightModule hmono :=
  square.right.rightModuleProjection hmono

/-- Inclusion from the right-hook result into the common corner. -/
def rightToCornerMap {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    square.rightResult.rightModule hmono ⟶ square.corner.rightModule hmono :=
  square.cornerLeft.moduleMap hmono

/-- Inclusion from the shortened word into the cohook-extended word. -/
def baseToLeftMap {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ square.left.result.rightModule hmono :=
  square.left.moduleMap hmono

/-- Projection from the common corner onto the cohook-extended word. -/
def cornerToLeftMap {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    square.corner.rightModule hmono ⟶ square.left.result.rightModule hmono :=
  square.cornerRight.rightModuleProjection hmono

/-- The coordinate square commutes on every vertex space. -/
theorem space_map_commutes {D : Word R} (square : MixedBoundarySquare D)
    {x : Q} (v : square.rightResult.Space x) :
    square.left.spaceInclusion x
        (square.right.toRightExtension.spaceProjection x v) =
      square.cornerRight.toRightExtension.spaceProjection x
        (square.cornerLeft.spaceInclusion x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p c =>
      classical
      by_cases hp : ∃ i : D.PositionAt x,
          square.right.toRightExtension.position i = p
      · rcases hp with ⟨i, rfl⟩
        rw [RightExtension.spaceProjection_single_position,
          LeftNegativeBoundaryExtension.spaceInclusion_single,
          LeftNegativeBoundaryExtension.spaceInclusion_single,
          ← square.position_commutes i,
          RightExtension.spaceProjection_single_position]
      · rw [square.right.toRightExtension.spaceProjection_single_of_not_exists
            p c hp, map_zero,
          LeftNegativeBoundaryExtension.spaceInclusion_single]
        rw [square.cornerRight.toRightExtension.spaceProjection_single_of_not_exists]
        rintro ⟨q, hq⟩
        rcases square.position_intersection q p hq with ⟨i, _, hi⟩
        exact hp ⟨i, hi⟩

/-- The two module maps around the mixed square commute. -/
theorem map_commutes {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    square.rightToBaseMap hmono ≫ square.baseToLeftMap hmono =
      square.rightToCornerMap hmono ≫ square.cornerToLeftMap hmono := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact square.space_map_commutes v

/-- Projecting through the two sides of the square gives the same base-word
coordinates. -/
theorem base_projection_commutes {D : Word R}
    (square : MixedBoundarySquare D) {x : Q}
    (v : square.corner.Space x) :
    square.left.spaceProjection x
        (square.cornerRight.toRightExtension.spaceProjection x v) =
      square.right.toRightExtension.spaceProjection x
        (square.cornerLeft.spaceProjection x v) := by
  apply Finsupp.ext
  intro i
  rw [LeftNegativeBoundaryExtension.spaceProjection_apply_position,
    RightExtension.spaceProjection_apply_position,
    RightExtension.spaceProjection_apply_position,
    LeftNegativeBoundaryExtension.spaceProjection_apply_position,
    square.position_commutes i]

/-- A vector in the common corner whose projection cancels an included base
vector has no coordinates outside the upper-right word. -/
theorem cornerLeft_inclusion_projection_eq_of_kernel
    {D : Word R} (square : MixedBoundarySquare D) {x : Q}
    (d : D.Space x) (c : square.corner.Space x)
    (hkernel : square.left.spaceInclusion x d +
      square.cornerRight.toRightExtension.spaceProjection x c = 0) :
    square.cornerLeft.spaceInclusion x
        (square.cornerLeft.spaceProjection x c) = c := by
  classical
  apply Finsupp.ext
  intro j
  by_cases hj : ∃ p : square.rightResult.PositionAt x,
      square.cornerLeft.position p = j
  · rcases hj with ⟨p, rfl⟩
    rw [LeftNegativeBoundaryExtension.spaceInclusion_apply_position,
      LeftNegativeBoundaryExtension.spaceProjection_apply_position]
  · rw [square.cornerLeft.spaceInclusion_apply_of_not_exists _ j hj]
    have hjIndex : j.index < square.cornerLeft.steps := by
      by_contra hnot
      have hle : square.cornerLeft.steps ≤ j.index := Nat.le_of_not_gt hnot
      rcases square.cornerLeft.exists_eq_position_of_steps_le j hle with
        ⟨p, hp⟩
      exact hj ⟨p, hp⟩
    have hjBound : j.index ≤ square.left.result.length := by
      rw [square.left.result_length]
      rw [square.steps_eq] at hjIndex
      omega
    rcases square.cornerRight.toRightExtension.exists_eq_position_of_index_le
        j hjBound with ⟨q, hq⟩
    have hqNotLeft : ¬ ∃ i : D.PositionAt x,
        square.left.position i = q := by
      rintro ⟨i, hi⟩
      apply hj
      refine ⟨square.right.toRightExtension.position i, ?_⟩
      calc
        square.cornerLeft.position
            (square.right.toRightExtension.position i) =
            square.cornerRight.toRightExtension.position
              (square.left.position i) := (square.position_commutes i).symm
        _ = square.cornerRight.toRightExtension.position q := by rw [hi]
        _ = j := hq
    have hcoeff := congrArg (fun w : square.left.result.Space x ↦ w q)
      hkernel
    rw [Finsupp.add_apply,
      square.left.spaceInclusion_apply_of_not_exists d q hqNotLeft,
      RightExtension.spaceProjection_apply_position,
      hq, Finsupp.zero_apply, zero_add] at hcoeff
    exact hcoeff.symm

/-- The mixed square maps written on the product of the two middle vertex
spaces. -/
def toPairSpaceMap {D : Word R} (square : MixedBoundarySquare D)
    (x : Q) : square.rightResult.Space x →ₗ[k]
      D.Space x × square.corner.Space x :=
  LinearMap.prod
    (square.right.toRightExtension.spaceProjection x)
    (-square.cornerLeft.spaceInclusion x)

/-- The middle-to-target map written on the product of vertex spaces. -/
def fromPairSpaceMap {D : Word R} (square : MixedBoundarySquare D)
    (x : Q) : D.Space x × square.corner.Space x →ₗ[k]
      square.left.result.Space x :=
  (square.left.spaceInclusion x).comp (LinearMap.fst k _ _) +
    (square.cornerRight.toRightExtension.spaceProjection x).comp
      (LinearMap.snd k _ _)

/-- The explicit mixed-square product maps are exact. -/
theorem pairSpaceMap_exact {D : Word R}
    (square : MixedBoundarySquare D) (x : Q) :
    Function.Exact (square.toPairSpaceMap x) (square.fromPairSpaceMap x) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, toPairSpaceMap,
      fromPairSpaceMap, LinearMap.add_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.neg_apply, map_neg]
    rw [← sub_eq_add_neg]
    exact sub_eq_zero.mpr (square.space_map_commutes v)
  · intro v hv
    let r : square.rightResult.Space x :=
      -square.cornerLeft.spaceProjection x v.2
    refine ⟨r, ?_⟩
    apply Prod.ext
    · change square.right.toRightExtension.spaceProjection x r = v.1
      dsimp only [r]
      rw [map_neg, ← square.base_projection_commutes]
      have hbase := congrArg (square.left.spaceProjection x) hv
      change square.left.spaceProjection x
          (square.left.spaceInclusion x v.1 +
            square.cornerRight.toRightExtension.spaceProjection x v.2) = 0
        at hbase
      rw [map_add,
        LeftNegativeBoundaryExtension.spaceProjection_inclusion] at hbase
      symm
      exact eq_neg_of_add_eq_zero_left hbase
    · change -square.cornerLeft.spaceInclusion x r = v.2
      dsimp only [r]
      rw [map_neg, neg_neg]
      exact cornerLeft_inclusion_projection_eq_of_kernel square v.1 v.2 hv

/-- The signed source-to-middle map of the mixed canonical complex. -/
def toMiddleMap {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    square.rightResult.rightModule hmono ⟶
      D.rightModule hmono ⊞ square.corner.rightModule hmono :=
  biprod.lift (square.rightToBaseMap hmono) (-square.rightToCornerMap hmono)

/-- The sum of the inclusion and projection from the two middle terms to the
cohook-extended target. -/
def fromMiddleMap {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⊞ square.corner.rightModule hmono ⟶
      square.left.result.rightModule hmono :=
  biprod.desc (square.baseToLeftMap hmono) (square.cornerToLeftMap hmono)

@[reassoc]
theorem toMiddleMap_fromMiddleMap {D : Word R}
    (square : MixedBoundarySquare D) (hmono : IsMonomial R) :
    square.toMiddleMap hmono ≫ square.fromMiddleMap hmono = 0 := by
  rw [toMiddleMap, fromMiddleMap, biprod.lift_desc, Preadditive.neg_comp,
    square.map_commutes]
  exact add_neg_cancel _

/-- The mixed cohook-hook boundary short complex. -/
def shortComplex {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) :=
  ShortComplex.mk (square.toMiddleMap hmono)
    (square.fromMiddleMap hmono) (square.toMiddleMap_fromMiddleMap hmono)

/-- Every coherent mixed boundary square gives an exact canonical short
complex of right string modules. -/
theorem shortComplex_exact {D : Word R}
    (square : MixedBoundarySquare D) (hmono : IsMonomial R) :
    (square.shortComplex hmono).Exact := by
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  let x : Q := LinearPathCategory.vertex X.unop.as
  let e := functorBiprodAppLinearEquiv
    (D.rightModule hmono) (square.corner.rightModule hmono) X
  have hTo : e.toLinearMap ∘ₗ
        ((square.toMiddleMap hmono).app X).hom =
      square.toPairSpaceMap x := by
    apply LinearMap.ext
    intro w
    have hfst : square.toMiddleMap hmono ≫
        (biprod.fst :
          D.rightModule hmono ⊞ square.corner.rightModule hmono ⟶
            D.rightModule hmono) = square.rightToBaseMap hmono := by
      rw [toMiddleMap, biprod.lift_fst]
    have hsnd : square.toMiddleMap hmono ≫
        (biprod.snd :
          D.rightModule hmono ⊞ square.corner.rightModule hmono ⟶
            square.corner.rightModule hmono) =
          -square.rightToCornerMap hmono := by
      rw [toMiddleMap, biprod.lift_snd]
    apply Prod.ext
    · have h := congrArg
        (fun q : square.rightResult.rightModule hmono ⟶
            D.rightModule hmono ↦ (q.app X).hom w) hfst
      change
        ((biprod.fst :
          D.rightModule hmono ⊞ square.corner.rightModule hmono ⟶
            D.rightModule hmono).app X).hom
              (((square.toMiddleMap hmono).app X).hom w) =
          square.right.toRightExtension.spaceProjection x w at h
      exact h
    · have h := congrArg
        (fun q : square.rightResult.rightModule hmono ⟶
            square.corner.rightModule hmono ↦ (q.app X).hom w) hsnd
      change
        ((biprod.snd :
          D.rightModule hmono ⊞ square.corner.rightModule hmono ⟶
            square.corner.rightModule hmono).app X).hom
              (((square.toMiddleMap hmono).app X).hom w) =
          -square.cornerLeft.spaceInclusion x w at h
      exact h
  have hFrom : ((square.fromMiddleMap hmono).app X).hom ∘ₗ
        e.symm.toLinearMap = square.fromPairSpaceMap x := by
    apply LinearMap.ext
    intro v
    have hinl :
        (biprod.inl : D.rightModule hmono ⟶
          D.rightModule hmono ⊞ square.corner.rightModule hmono) ≫
            square.fromMiddleMap hmono = square.baseToLeftMap hmono := by
      rw [fromMiddleMap, biprod.inl_desc]
    have hinr :
        (biprod.inr : square.corner.rightModule hmono ⟶
          D.rightModule hmono ⊞ square.corner.rightModule hmono) ≫
            square.fromMiddleMap hmono = square.cornerToLeftMap hmono := by
      rw [fromMiddleMap, biprod.inr_desc]
    have h₁ := congrArg
      (fun q : D.rightModule hmono ⟶ square.left.result.rightModule hmono ↦
        (q.app X).hom v.1) hinl
    have h₂ := congrArg
      (fun q : square.corner.rightModule hmono ⟶
          square.left.result.rightModule hmono ↦ (q.app X).hom v.2) hinr
    change ((square.fromMiddleMap hmono).app X).hom
        (((biprod.inl : D.rightModule hmono ⟶
          D.rightModule hmono ⊞ square.corner.rightModule hmono).app X).hom v.1 +
        ((biprod.inr : square.corner.rightModule hmono ⟶
          D.rightModule hmono ⊞ square.corner.rightModule hmono).app X).hom v.2) = _
    rw [map_add]
    change
      ((square.fromMiddleMap hmono).app X).hom
          (((biprod.inl : D.rightModule hmono ⟶
            D.rightModule hmono ⊞ square.corner.rightModule hmono).app X).hom
              v.1) = square.left.spaceInclusion x v.1 at h₁
    change
      ((square.fromMiddleMap hmono).app X).hom
          (((biprod.inr : square.corner.rightModule hmono ⟶
            D.rightModule hmono ⊞ square.corner.rightModule hmono).app X).hom
              v.2) =
        square.cornerRight.toRightExtension.spaceProjection x v.2 at h₂
    rw [h₁, h₂]
    rfl
  have hexact : Function.Exact
      (e.toLinearMap ∘ₗ ((square.toMiddleMap hmono).app X).hom)
      (((square.fromMiddleMap hmono).app X).hom ∘ₗ
        e.symm.toLinearMap) := by
    rw [hTo, hFrom]
    exact square.pairSpaceMap_exact x
  have hOriginal : Function.Exact
      ((square.toMiddleMap hmono).app X).hom
      ((square.fromMiddleMap hmono).app X).hom :=
    (LinearEquiv.conj_exact_iff_exact _ _ e).mp hexact
  exact (LinearMap.exact_iff.mp hOriginal).symm

end MixedBoundarySquare

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
