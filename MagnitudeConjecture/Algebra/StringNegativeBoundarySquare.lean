import MagnitudeConjecture.Algebra.StringBoundarySquare

/-!
# Two-ended negative boundary squares for string modules

The double-peak Butler--Ringel sequence is obtained by attaching a negative
boundary at both ends of a shorter string.  The right-module maps are
inclusions.  This file proves that any coherent common-corner square of those
inclusions gives the canonical exact complex from the base to the two
one-ended extensions and then to the common corner.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A common corner for negative boundary extensions at both ends of `D`. -/
structure NegativeBoundarySquare (D : Word R) where
  rightResult : Word R
  right : NegativeBoundaryExtension D rightResult
  left : LeftNegativeBoundaryExtension D
  cornerLeft : LeftNegativeBoundaryExtension rightResult
  cornerRight : NegativeBoundaryExtension left.result cornerLeft.result
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

namespace NegativeBoundarySquare

/-- Equal left-extension lengths force the position coherence required by a
negative boundary square. -/
def ofExtensions {D rightResult : Word R}
    (right : NegativeBoundaryExtension D rightResult)
    (left : LeftNegativeBoundaryExtension D)
    (cornerLeft : LeftNegativeBoundaryExtension rightResult)
    (cornerRight : NegativeBoundaryExtension left.result cornerLeft.result)
    (hsteps : cornerLeft.steps = left.steps) :
    NegativeBoundarySquare D where
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

/-- The common two-ended negative extension. -/
abbrev corner {D : Word R} (square : NegativeBoundarySquare D) : Word R :=
  square.cornerLeft.result

/-- Inclusion from the base into its left negative-boundary extension. -/
def baseToLeftMap {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ square.left.result.rightModule hmono :=
  square.left.moduleMap hmono

/-- Inclusion from the base into its right negative-boundary extension. -/
def baseToRightMap {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶ square.rightResult.rightModule hmono :=
  square.right.rightModuleInclusion hmono

/-- Inclusion from the left-extended word into the common corner. -/
def leftToCornerMap {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    square.left.result.rightModule hmono ⟶ square.corner.rightModule hmono :=
  square.cornerRight.rightModuleInclusion hmono

/-- Inclusion from the right-extended word into the common corner. -/
def rightToCornerMap {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    square.rightResult.rightModule hmono ⟶ square.corner.rightModule hmono :=
  square.cornerLeft.moduleMap hmono

/-- The two coordinate inclusions around a negative boundary square agree. -/
theorem space_map_commutes {D : Word R} (square : NegativeBoundarySquare D)
    {x : Q} (v : D.Space x) :
    square.cornerRight.toRightExtension.spaceInclusion x
        (square.left.spaceInclusion x v) =
      square.cornerLeft.spaceInclusion x
        (square.right.toRightExtension.spaceInclusion x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      rw [LeftNegativeBoundaryExtension.spaceInclusion_single,
        RightExtension.spaceInclusion_single,
        RightExtension.spaceInclusion_single,
        LeftNegativeBoundaryExtension.spaceInclusion_single,
        square.position_commutes i]

/-- The two module inclusions around a negative boundary square commute. -/
theorem map_commutes {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    square.baseToLeftMap hmono ≫ square.leftToCornerMap hmono =
      square.baseToRightMap hmono ≫ square.rightToCornerMap hmono := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact square.space_map_commutes v

/-- Equality in the corner forces a left-result vector to be supported on
positions inherited from the base. -/
theorem left_inclusion_projection_eq_of_corner_eq
    {D : Word R} (square : NegativeBoundarySquare D) {x : Q}
    (l : square.left.result.Space x)
    (r : square.rightResult.Space x)
    (hcorner : square.cornerRight.toRightExtension.spaceInclusion x l =
      square.cornerLeft.spaceInclusion x r) :
    square.left.spaceInclusion x (square.left.spaceProjection x l) = l := by
  classical
  apply Finsupp.ext
  intro q
  by_cases hq : ∃ i : D.PositionAt x, square.left.position i = q
  · rcases hq with ⟨i, rfl⟩
    rw [LeftNegativeBoundaryExtension.spaceInclusion_apply_position,
      LeftNegativeBoundaryExtension.spaceProjection_apply_position]
  · rw [square.left.spaceInclusion_apply_of_not_exists _ q hq]
    have hnotRight : ¬ ∃ p : square.rightResult.PositionAt x,
        square.cornerLeft.position p =
          square.cornerRight.toRightExtension.position q := by
      rintro ⟨p, hp⟩
      rcases square.position_intersection q p hp.symm with ⟨i, hi, _⟩
      exact hq ⟨i, hi⟩
    have hcoeff := congrArg
      (fun w : square.corner.Space x ↦
        w (square.cornerRight.toRightExtension.position q)) hcorner
    rw [RightExtension.spaceInclusion_apply_position,
      square.cornerLeft.spaceInclusion_apply_of_not_exists _ _ hnotRight]
      at hcoeff
    exact hcoeff.symm

/-- Equality in the corner forces a right-result vector to be supported on
positions inherited from the base. -/
theorem right_inclusion_projection_eq_of_corner_eq
    {D : Word R} (square : NegativeBoundarySquare D) {x : Q}
    (l : square.left.result.Space x)
    (r : square.rightResult.Space x)
    (hcorner : square.cornerRight.toRightExtension.spaceInclusion x l =
      square.cornerLeft.spaceInclusion x r) :
    square.right.toRightExtension.spaceInclusion x
        (square.right.toRightExtension.spaceProjection x r) = r := by
  classical
  apply Finsupp.ext
  intro p
  by_cases hp : ∃ i : D.PositionAt x,
      square.right.toRightExtension.position i = p
  · rcases hp with ⟨i, rfl⟩
    rw [RightExtension.spaceInclusion_apply_position,
      RightExtension.spaceProjection_apply_position]
  · rw [square.right.toRightExtension.spaceInclusion_apply_of_not_exists
      _ p hp]
    have hnotLeft : ¬ ∃ q : square.left.result.PositionAt x,
        square.cornerRight.toRightExtension.position q =
          square.cornerLeft.position p := by
      rintro ⟨q, hq⟩
      rcases square.position_intersection q p hq with ⟨i, _, hi⟩
      exact hp ⟨i, hi⟩
    have hcoeff := congrArg
      (fun w : square.corner.Space x ↦ w (square.cornerLeft.position p))
      hcorner
    rw [square.cornerRight.toRightExtension.spaceInclusion_apply_of_not_exists
        _ _ hnotLeft,
      LeftNegativeBoundaryExtension.spaceInclusion_apply_position] at hcoeff
    exact hcoeff

/-- Equal corner inclusions have equal base-coordinate projections. -/
theorem base_projection_eq_of_corner_eq
    {D : Word R} (square : NegativeBoundarySquare D) {x : Q}
    (l : square.left.result.Space x)
    (r : square.rightResult.Space x)
    (hcorner : square.cornerRight.toRightExtension.spaceInclusion x l =
      square.cornerLeft.spaceInclusion x r) :
    square.left.spaceProjection x l =
      square.right.toRightExtension.spaceProjection x r := by
  apply Finsupp.ext
  intro i
  rw [LeftNegativeBoundaryExtension.spaceProjection_apply_position,
    RightExtension.spaceProjection_apply_position]
  have hcoeff := congrArg
    (fun w : square.corner.Space x ↦
      w (square.cornerRight.toRightExtension.position
        (square.left.position i))) hcorner
  rw [RightExtension.spaceInclusion_apply_position,
    square.position_commutes i,
    LeftNegativeBoundaryExtension.spaceInclusion_apply_position] at hcoeff
  exact hcoeff

/-- The base-to-middle map on explicit vertex-space products. -/
def toPairSpaceMap {D : Word R} (square : NegativeBoundarySquare D)
    (x : Q) : D.Space x →ₗ[k]
      square.left.result.Space x × square.rightResult.Space x :=
  LinearMap.prod (square.left.spaceInclusion x)
    (square.right.toRightExtension.spaceInclusion x)

/-- The signed middle-to-corner map on explicit vertex-space products. -/
def fromPairSpaceMap {D : Word R} (square : NegativeBoundarySquare D)
    (x : Q) : square.left.result.Space x × square.rightResult.Space x →ₗ[k]
      square.corner.Space x :=
  (square.cornerRight.toRightExtension.spaceInclusion x).comp
      (LinearMap.fst k _ _) -
    (square.cornerLeft.spaceInclusion x).comp (LinearMap.snd k _ _)

/-- The explicit double-inclusion product maps are exact. -/
theorem pairSpaceMap_exact {D : Word R}
    (square : NegativeBoundarySquare D) (x : Q) :
    Function.Exact (square.toPairSpaceMap x) (square.fromPairSpaceMap x) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, toPairSpaceMap,
      fromPairSpaceMap, LinearMap.sub_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    exact sub_eq_zero.mpr (square.space_map_commutes v)
  · intro v hv
    have hcorner :
        square.cornerRight.toRightExtension.spaceInclusion x v.1 =
          square.cornerLeft.spaceInclusion x v.2 := sub_eq_zero.mp hv
    let b : D.Space x := square.left.spaceProjection x v.1
    refine ⟨b, ?_⟩
    apply Prod.ext
    · exact square.left_inclusion_projection_eq_of_corner_eq v.1 v.2 hcorner
    · change square.right.toRightExtension.spaceInclusion x b = v.2
      dsimp only [b]
      rw [square.base_projection_eq_of_corner_eq v.1 v.2 hcorner]
      exact square.right_inclusion_projection_eq_of_corner_eq v.1 v.2 hcorner

/-- The base-to-middle map of the double-cohook canonical complex. -/
def toMiddleMap {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    D.rightModule hmono ⟶
      square.left.result.rightModule hmono ⊞
        square.rightResult.rightModule hmono :=
  biprod.lift (square.baseToLeftMap hmono) (square.baseToRightMap hmono)

/-- The signed middle-to-corner map of the double-cohook canonical complex. -/
def fromMiddleMap {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :
    square.left.result.rightModule hmono ⊞
        square.rightResult.rightModule hmono ⟶ square.corner.rightModule hmono :=
  biprod.desc (square.leftToCornerMap hmono) (-square.rightToCornerMap hmono)

@[reassoc]
theorem toMiddleMap_fromMiddleMap {D : Word R}
    (square : NegativeBoundarySquare D) (hmono : IsMonomial R) :
    square.toMiddleMap hmono ≫ square.fromMiddleMap hmono = 0 := by
  rw [toMiddleMap, fromMiddleMap, biprod.lift_desc,
    Preadditive.comp_neg, square.map_commutes]
  exact add_neg_cancel _

/-- The double-negative-boundary short complex. -/
def shortComplex {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) :=
  ShortComplex.mk (square.toMiddleMap hmono)
    (square.fromMiddleMap hmono) (square.toMiddleMap_fromMiddleMap hmono)

/-- Every coherent negative boundary square gives an exact canonical short
complex of right string modules. -/
theorem shortComplex_exact {D : Word R}
    (square : NegativeBoundarySquare D) (hmono : IsMonomial R) :
    (square.shortComplex hmono).Exact := by
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  let x : Q := LinearPathCategory.vertex X.unop.as
  let e := functorBiprodAppLinearEquiv
    (square.left.result.rightModule hmono)
    (square.rightResult.rightModule hmono) X
  have hTo : e.toLinearMap ∘ₗ
        ((square.toMiddleMap hmono).app X).hom =
      square.toPairSpaceMap x := by
    apply LinearMap.ext
    intro w
    have hfst : square.toMiddleMap hmono ≫
        (biprod.fst :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.left.result.rightModule hmono) =
          square.baseToLeftMap hmono := by
      rw [toMiddleMap, biprod.lift_fst]
    have hsnd : square.toMiddleMap hmono ≫
        (biprod.snd :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.rightResult.rightModule hmono) =
          square.baseToRightMap hmono := by
      rw [toMiddleMap, biprod.lift_snd]
    apply Prod.ext
    · have h := congrArg
        (fun q : D.rightModule hmono ⟶ square.left.result.rightModule hmono ↦
          (q.app X).hom w) hfst
      change
        ((biprod.fst :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.left.result.rightModule hmono).app X).hom
              (((square.toMiddleMap hmono).app X).hom w) =
          square.left.spaceInclusion x w at h
      exact h
    · have h := congrArg
        (fun q : D.rightModule hmono ⟶ square.rightResult.rightModule hmono ↦
          (q.app X).hom w) hsnd
      change
        ((biprod.snd :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.rightResult.rightModule hmono).app X).hom
              (((square.toMiddleMap hmono).app X).hom w) =
          square.right.toRightExtension.spaceInclusion x w at h
      exact h
  have hFrom : ((square.fromMiddleMap hmono).app X).hom ∘ₗ
        e.symm.toLinearMap = square.fromPairSpaceMap x := by
    apply LinearMap.ext
    intro v
    have hinl :
        (biprod.inl : square.left.result.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono) ≫
            square.fromMiddleMap hmono = square.leftToCornerMap hmono := by
      rw [fromMiddleMap, biprod.inl_desc]
    have hinr :
        (biprod.inr : square.rightResult.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono) ≫
            square.fromMiddleMap hmono = -square.rightToCornerMap hmono := by
      rw [fromMiddleMap, biprod.inr_desc]
    have h₁ := congrArg
      (fun q : square.left.result.rightModule hmono ⟶
          square.corner.rightModule hmono ↦ (q.app X).hom v.1) hinl
    have h₂ := congrArg
      (fun q : square.rightResult.rightModule hmono ⟶
          square.corner.rightModule hmono ↦ (q.app X).hom v.2) hinr
    change ((square.fromMiddleMap hmono).app X).hom
        (((biprod.inl : square.left.result.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono).app X).hom v.1 +
        ((biprod.inr : square.rightResult.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono).app X).hom v.2) = _
    rw [map_add]
    change ((square.fromMiddleMap hmono).app X).hom
        (((biprod.inl : square.left.result.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono).app X).hom v.1) =
      square.cornerRight.toRightExtension.spaceInclusion x v.1 at h₁
    change ((square.fromMiddleMap hmono).app X).hom
        (((biprod.inr : square.rightResult.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono).app X).hom v.2) =
      -square.cornerLeft.spaceInclusion x v.2 at h₂
    rw [h₁, h₂]
    change
      square.cornerRight.toRightExtension.spaceInclusion x v.1 +
          -square.cornerLeft.spaceInclusion x v.2 =
        square.cornerRight.toRightExtension.spaceInclusion x v.1 -
          square.cornerLeft.spaceInclusion x v.2
    rw [sub_eq_add_neg]
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

end NegativeBoundarySquare

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
