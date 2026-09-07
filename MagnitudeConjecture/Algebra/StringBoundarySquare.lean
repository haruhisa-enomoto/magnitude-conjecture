import MagnitudeConjecture.Algebra.StringLeftBoundaryExtension
import MagnitudeConjecture.CategoryTheory.ModuleFunctorExact

/-!
# Commuting two-ended boundary squares for string modules

A positive boundary extension at each end of a string gives two quotient
maps.  When the two extensions have a common corner and their inherited
position embeddings agree, the resulting square of string-module quotient
maps commutes.  This is the coordinate core of the two-hook canonical exact
sequence; construction of the common maximal-hook corner is a separate word
combinatorics step.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

/-- Evaluation of a functor-category biproduct is linearly equivalent to the
ordinary product of the two evaluated modules.  The definition uses the
actual chosen biproduct projections and inclusions, so it does not depend on
definitional choices for pointwise limits. -/
def functorBiprodAppLinearEquiv
    {D : Type u} [CategoryTheory.Category.{u} D]
    (F G : D ⥤ ModuleCat.{u} k) (X : D) :
    (F ⊞ G).obj X ≃ₗ[k] F.obj X × G.obj X where
  toFun v :=
    (((biprod.fst : F ⊞ G ⟶ F).app X).hom v,
      ((biprod.snd : F ⊞ G ⟶ G).app X).hom v)
  invFun v :=
    ((biprod.inl : F ⟶ F ⊞ G).app X).hom v.1 +
      ((biprod.inr : G ⟶ F ⊞ G).app X).hom v.2
  map_add' v w := by simp
  map_smul' c v := by simp
  left_inv v := by
    have htotal :
        (biprod.fst : F ⊞ G ⟶ F) ≫ biprod.inl +
          (biprod.snd : F ⊞ G ⟶ G) ≫ biprod.inr = 𝟙 (F ⊞ G) :=
      biprod.total
    have h := congrArg
      (fun q : (F ⊞ G) ⟶ (F ⊞ G) ↦ (q.app X).hom v) htotal
    change
      ((biprod.inl : F ⟶ F ⊞ G).app X).hom
          (((biprod.fst : F ⊞ G ⟶ F).app X).hom v) +
        ((biprod.inr : G ⟶ F ⊞ G).app X).hom
          (((biprod.snd : F ⊞ G ⟶ G).app X).hom v) = v at h
    exact h
  right_inv v := by
    have hinlFst :
        (biprod.inl : F ⟶ F ⊞ G) ≫ biprod.fst = 𝟙 F :=
      biprod.inl_fst
    have hinrFst :
        (biprod.inr : G ⟶ F ⊞ G) ≫ biprod.fst = 0 :=
      biprod.inr_fst
    have hinlSnd :
        (biprod.inl : F ⟶ F ⊞ G) ≫ biprod.snd = 0 :=
      biprod.inl_snd
    have hinrSnd :
        (biprod.inr : G ⟶ F ⊞ G) ≫ biprod.snd = 𝟙 G :=
      biprod.inr_snd
    apply Prod.ext
    · change
        ((biprod.fst : F ⊞ G ⟶ F).app X).hom
          (((biprod.inl : F ⟶ F ⊞ G).app X).hom v.1 +
            ((biprod.inr : G ⟶ F ⊞ G).app X).hom v.2) = v.1
      rw [map_add]
      have h₁ := congrArg (fun q : F ⟶ F ↦ (q.app X).hom v.1) hinlFst
      have h₂ := congrArg (fun q : G ⟶ F ↦ (q.app X).hom v.2) hinrFst
      change
        ((biprod.fst : F ⊞ G ⟶ F).app X).hom
            (((biprod.inl : F ⟶ F ⊞ G).app X).hom v.1) = v.1 at h₁
      change
        ((biprod.fst : F ⊞ G ⟶ F).app X).hom
            (((biprod.inr : G ⟶ F ⊞ G).app X).hom v.2) = 0 at h₂
      rw [h₁, h₂, add_zero]
    · change
        ((biprod.snd : F ⊞ G ⟶ G).app X).hom
          (((biprod.inl : F ⟶ F ⊞ G).app X).hom v.1 +
            ((biprod.inr : G ⟶ F ⊞ G).app X).hom v.2) = v.2
      rw [map_add]
      have h₁ := congrArg (fun q : F ⟶ G ↦ (q.app X).hom v.1) hinlSnd
      have h₂ := congrArg (fun q : G ⟶ G ↦ (q.app X).hom v.2) hinrSnd
      change
        ((biprod.snd : F ⊞ G ⟶ G).app X).hom
            (((biprod.inl : F ⟶ F ⊞ G).app X).hom v.1) = 0 at h₁
      change
        ((biprod.snd : F ⊞ G ⟶ G).app X).hom
            (((biprod.inr : G ⟶ F ⊞ G).app X).hom v.2) = v.2 at h₂
      rw [h₁, h₂, zero_add]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A common corner for positive boundary extensions at both ends of `C`.
The coherence field says that the two ways of embedding every old word
position into the corner are literally equal. -/
structure PositiveBoundarySquare (C : Word R) where
  rightResult : Word R
  right : PositiveBoundaryExtension C rightResult
  left : LeftPositiveBoundaryExtension C
  cornerLeft : LeftPositiveBoundaryExtension rightResult
  cornerRight : PositiveBoundaryExtension left.result cornerLeft.result
  position_commutes : ∀ {x : Q} (i : C.PositionAt x),
    cornerRight.toRightExtension.position (left.position i) =
      cornerLeft.position (right.toRightExtension.position i)
  position_intersection : ∀ {x : Q}
      (q : left.result.PositionAt x)
      (p : rightResult.PositionAt x),
    cornerRight.toRightExtension.position q = cornerLeft.position p →
      ∃ i : C.PositionAt x,
        left.position i = q ∧ right.toRightExtension.position i = p

namespace PositiveBoundarySquare

/-- Assemble a positive-boundary square from two compatible constructions of
the same corner.  Equality of the numbers of letters added on the left is
enough to force both position commutativity and the required intersection
property. -/
def ofExtensions {C rightResult : Word R}
    (right : PositiveBoundaryExtension C rightResult)
    (left : LeftPositiveBoundaryExtension C)
    (cornerLeft : LeftPositiveBoundaryExtension rightResult)
    (cornerRight : PositiveBoundaryExtension left.result cornerLeft.result)
    (hsteps : cornerLeft.steps = left.steps) :
    PositiveBoundarySquare C where
  rightResult := rightResult
  right := right
  left := left
  cornerLeft := cornerLeft
  cornerRight := cornerRight
  position_commutes := by
    intro x i
    apply PositionAt.ext_index
    simp only [RightExtension.position_index,
      LeftPositiveBoundaryExtension.position_index, hsteps]
  position_intersection := by
    intro x q p hqp
    have hindex := congrArg PositionAt.index hqp
    simp only [RightExtension.position_index,
      LeftPositiveBoundaryExtension.position_index] at hindex
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
          LeftPositiveBoundaryExtension.position_index, hsteps]
      _ = cornerRight.toRightExtension.position q := by rw [hi]
      _ = cornerLeft.position p := hqp

/-- The common two-ended extension. -/
abbrev corner {C : Word R} (square : PositiveBoundarySquare C) : Word R :=
  square.cornerLeft.result

/-- Projection from the corner after forgetting the right extension. -/
def toLeftMap {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.corner.rightModule hmono ⟶ square.left.result.rightModule hmono :=
  square.cornerRight.rightModuleProjection hmono

/-- Projection from the corner after forgetting the left extension. -/
def toRightMap {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.corner.rightModule hmono ⟶ square.rightResult.rightModule hmono :=
  square.cornerLeft.moduleMap hmono

/-- Projection from the left-extended word back to the original word. -/
def leftToBaseMap {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.left.result.rightModule hmono ⟶ C.rightModule hmono :=
  square.left.moduleMap hmono

/-- Projection from the right-extended word back to the original word. -/
def rightToBaseMap {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.rightResult.rightModule hmono ⟶ C.rightModule hmono :=
  square.right.rightModuleProjection hmono

/-- The two composites around a coherent positive-boundary square agree. -/
theorem map_commutes {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.toLeftMap hmono ≫ square.leftToBaseMap hmono =
      square.toRightMap hmono ≫ square.rightToBaseMap hmono := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  let x : Q := LinearPathCategory.vertex X.unop.as
  change square.left.spaceProjection x
      (square.cornerRight.toRightExtension.spaceProjection x v) =
    square.right.toRightExtension.spaceProjection x
      (square.cornerLeft.spaceProjection x v)
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single j c =>
      classical
      by_cases hcornerRight : ∃ q : square.left.result.PositionAt x,
          square.cornerRight.toRightExtension.position q = j
      · rcases hcornerRight with ⟨q, rfl⟩
        rw [RightExtension.spaceProjection_single_position]
        by_cases hleft : ∃ i : C.PositionAt x,
            square.left.position i = q
        · rcases hleft with ⟨i, rfl⟩
          rw [LeftPositiveBoundaryExtension.spaceProjection_single_position]
          rw [square.position_commutes i]
          rw [LeftPositiveBoundaryExtension.spaceProjection_single_position,
            RightExtension.spaceProjection_single_position]
        · rw [square.left.spaceProjection_single_of_not_exists _ _ hleft]
          by_cases hcornerLeft :
              ∃ p : square.rightResult.PositionAt x,
                square.cornerLeft.position p =
                  square.cornerRight.toRightExtension.position q
          · rcases hcornerLeft with ⟨p, hp⟩
            rw [← hp,
              LeftPositiveBoundaryExtension.spaceProjection_single_position]
            rw [RightExtension.spaceProjection_single_of_not_exists]
            rintro ⟨i, hi⟩
            apply hleft
            refine ⟨i,
              square.cornerRight.toRightExtension.position_injective ?_⟩
            calc
              square.cornerRight.toRightExtension.position
                  (square.left.position i) =
                  square.cornerLeft.position
                    (square.right.toRightExtension.position i) :=
                square.position_commutes i
              _ = square.cornerLeft.position p := by rw [hi]
              _ = square.cornerRight.toRightExtension.position q := hp
          · rw [square.cornerLeft.spaceProjection_single_of_not_exists
                _ _ hcornerLeft,
              map_zero]
      · rw [RightExtension.spaceProjection_single_of_not_exists
            _ _ _ hcornerRight,
          map_zero]
        by_cases hcornerLeft :
            ∃ p : square.rightResult.PositionAt x,
              square.cornerLeft.position p = j
        · rcases hcornerLeft with ⟨p, rfl⟩
          rw [LeftPositiveBoundaryExtension.spaceProjection_single_position]
          rw [RightExtension.spaceProjection_single_of_not_exists]
          rintro ⟨i, hi⟩
          apply hcornerRight
          refine ⟨square.left.position i, ?_⟩
          calc
            square.cornerRight.toRightExtension.position
                (square.left.position i) =
                square.cornerLeft.position
                  (square.right.toRightExtension.position i) :=
              square.position_commutes i
            _ = square.cornerLeft.position p := by rw [hi]
        · rw [square.cornerLeft.spaceProjection_single_of_not_exists
              _ _ hcornerLeft,
            map_zero]

/-- Projecting a right-result vector through the corner onto the left result
retains exactly its coordinates inherited from the base word. -/
theorem cornerRight_projection_cornerLeft_inclusion
    {C : Word R} (square : PositiveBoundarySquare C) {x : Q}
    (v : square.rightResult.Space x) :
    square.cornerRight.toRightExtension.spaceProjection x
        (square.cornerLeft.spaceInclusion x v) =
      square.left.spaceInclusion x
        (square.right.toRightExtension.spaceProjection x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single p c =>
      classical
      by_cases hp : ∃ i : C.PositionAt x,
          square.right.toRightExtension.position i = p
      · rcases hp with ⟨i, rfl⟩
        rw [LeftPositiveBoundaryExtension.spaceInclusion_single,
          ← square.position_commutes i,
          RightExtension.spaceProjection_single_position,
          RightExtension.spaceProjection_single_position,
          LeftPositiveBoundaryExtension.spaceInclusion_single]
      · have hcorner : ¬ ∃ q : square.left.result.PositionAt x,
            square.cornerRight.toRightExtension.position q =
              square.cornerLeft.position p := by
          rintro ⟨q, hq⟩
          rcases square.position_intersection q p hq with ⟨i, _, hi⟩
          exact hp ⟨i, hi⟩
        rw [LeftPositiveBoundaryExtension.spaceInclusion_single,
          RightExtension.spaceProjection_single_of_not_exists _ _ _ hcorner,
          RightExtension.spaceProjection_single_of_not_exists _ _ _ hp,
          map_zero]

/-- The symmetric cross projection formula: projecting a left-result vector
through the corner onto the right result retains exactly its base-word
coordinates. -/
theorem cornerLeft_projection_cornerRight_inclusion
    {C : Word R} (square : PositiveBoundarySquare C) {x : Q}
    (v : square.left.result.Space x) :
    square.cornerLeft.spaceProjection x
        (square.cornerRight.toRightExtension.spaceInclusion x v) =
      square.right.toRightExtension.spaceInclusion x
        (square.left.spaceProjection x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single q c =>
      classical
      by_cases hq : ∃ i : C.PositionAt x, square.left.position i = q
      · rcases hq with ⟨i, rfl⟩
        rw [RightExtension.spaceInclusion_single,
          square.position_commutes i,
          LeftPositiveBoundaryExtension.spaceProjection_single_position,
          LeftPositiveBoundaryExtension.spaceProjection_single_position,
          RightExtension.spaceInclusion_single]
      · have hcorner : ¬ ∃ p : square.rightResult.PositionAt x,
            square.cornerLeft.position p =
              square.cornerRight.toRightExtension.position q := by
          rintro ⟨p, hp⟩
          rcases square.position_intersection q p hp.symm with ⟨i, hi, _⟩
          exact hq ⟨i, hi⟩
        rw [RightExtension.spaceInclusion_single,
          square.cornerLeft.spaceProjection_single_of_not_exists
            _ _ hcorner,
          square.left.spaceProjection_single_of_not_exists _ _ hq,
          map_zero]

/-- Coordinate inclusion of the base word into the common corner, using the
left result and then the right extension to the corner. -/
def baseToCornerSpaceInclusion {C : Word R}
    (square : PositiveBoundarySquare C) (x : Q) :
    C.Space x →ₗ[k] square.corner.Space x :=
  square.cornerRight.toRightExtension.spaceInclusion x |>.comp
    (square.left.spaceInclusion x)

@[simp]
theorem cornerRight_projection_baseToCorner_inclusion
    {C : Word R} (square : PositiveBoundarySquare C) (x : Q)
    (v : C.Space x) :
    square.cornerRight.toRightExtension.spaceProjection x
        (square.baseToCornerSpaceInclusion x v) =
      square.left.spaceInclusion x v := by
  exact square.cornerRight.toRightExtension.spaceProjection_inclusion
    x (square.left.spaceInclusion x v)

@[simp]
theorem cornerLeft_projection_baseToCorner_inclusion
    {C : Word R} (square : PositiveBoundarySquare C) (x : Q)
    (v : C.Space x) :
    square.cornerLeft.spaceProjection x
        (square.baseToCornerSpaceInclusion x v) =
      square.right.toRightExtension.spaceInclusion x v := by
  rw [baseToCornerSpaceInclusion, LinearMap.comp_apply,
    square.cornerLeft_projection_cornerRight_inclusion]
  simp

/-- Lift a pair of one-ended coordinate vectors to the corner.  The last
term corrects the overlap along the old word. -/
def kernelPairLift {C : Word R} (square : PositiveBoundarySquare C)
    (x : Q) :
    square.left.result.Space x × square.rightResult.Space x →ₗ[k]
      square.corner.Space x :=
  (square.cornerRight.toRightExtension.spaceInclusion x).comp
      (LinearMap.fst k _ _) -
    (square.cornerLeft.spaceInclusion x).comp (LinearMap.snd k _ _) +
    (square.baseToCornerSpaceInclusion x).comp
      ((square.right.toRightExtension.spaceProjection x).comp
        (LinearMap.snd k _ _))

/-- The left corner projection of the corrected lift is the first component. -/
@[simp]
theorem cornerRight_projection_kernelPairLift
    {C : Word R} (square : PositiveBoundarySquare C) (x : Q)
    (v : square.left.result.Space x × square.rightResult.Space x) :
    square.cornerRight.toRightExtension.spaceProjection x
        (square.kernelPairLift x v) = v.1 := by
  rw [kernelPairLift]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_add, map_sub,
    square.cornerRight_projection_cornerLeft_inclusion,
    square.cornerRight_projection_baseToCorner_inclusion]
  rw [square.cornerRight.toRightExtension.spaceProjection_inclusion]
  abel

/-- On a pair killed by the sum of the two base projections, the right
corner projection of the corrected lift is the negative second component. -/
theorem cornerLeft_projection_kernelPairLift
    {C : Word R} (square : PositiveBoundarySquare C) (x : Q)
    (v : square.left.result.Space x × square.rightResult.Space x)
    (hv : square.left.spaceProjection x v.1 +
      square.right.toRightExtension.spaceProjection x v.2 = 0) :
    square.cornerLeft.spaceProjection x
        (square.kernelPairLift x v) = -v.2 := by
  rw [kernelPairLift]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, map_add, map_sub,
    square.cornerLeft_projection_cornerRight_inclusion,
    LeftPositiveBoundaryExtension.spaceProjection_inclusion,
    square.cornerLeft_projection_baseToCorner_inclusion]
  have hsum :
      square.right.toRightExtension.spaceInclusion x
          (square.left.spaceProjection x v.1) +
        square.right.toRightExtension.spaceInclusion x
          (square.right.toRightExtension.spaceProjection x v.2) = 0 := by
    rw [← map_add, hv, map_zero]
  calc
    square.right.toRightExtension.spaceInclusion x
          (square.left.spaceProjection x v.1) - v.2 +
        square.right.toRightExtension.spaceInclusion x
          (square.right.toRightExtension.spaceProjection x v.2) =
        (square.right.toRightExtension.spaceInclusion x
            (square.left.spaceProjection x v.1) +
          square.right.toRightExtension.spaceInclusion x
            (square.right.toRightExtension.spaceProjection x v.2)) - v.2 := by
          abel
    _ = -v.2 := by rw [hsum, zero_sub]

/-- The corner map written on the explicit product of the two one-ended
vertex spaces. -/
def toPairSpaceMap {C : Word R} (square : PositiveBoundarySquare C)
    (x : Q) : square.corner.Space x →ₗ[k]
      square.left.result.Space x × square.rightResult.Space x :=
  LinearMap.prod
    (square.cornerRight.toRightExtension.spaceProjection x)
    (-square.cornerLeft.spaceProjection x)

/-- The middle-to-base map written on the explicit product of vertex
spaces. -/
def fromPairSpaceMap {C : Word R} (square : PositiveBoundarySquare C)
    (x : Q) :
    square.left.result.Space x × square.rightResult.Space x →ₗ[k]
      C.Space x :=
  (square.left.spaceProjection x).comp (LinearMap.fst k _ _) +
    (square.right.toRightExtension.spaceProjection x).comp
      (LinearMap.snd k _ _)

/-- The explicit product-space maps are exact.  Surjectivity onto the kernel
is witnessed by `kernelPairLift`. -/
theorem pairSpaceMap_exact {C : Word R}
    (square : PositiveBoundarySquare C) (hmono : IsMonomial R) (x : Q) :
    Function.Exact (square.toPairSpaceMap x) (square.fromPairSpaceMap x) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, toPairSpaceMap,
      fromPairSpaceMap, LinearMap.add_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.neg_apply, map_neg]
    rw [← sub_eq_add_neg]
    apply sub_eq_zero.mpr
    have hmaps := congrArg
      (fun f ↦ (f.app (Opposite.op (obj R x))).hom w)
      (square.map_commutes hmono)
    exact hmaps
  · intro v hv
    have hv' : square.left.spaceProjection x v.1 +
        square.right.toRightExtension.spaceProjection x v.2 = 0 := by
      exact hv
    refine ⟨square.kernelPairLift x v, ?_⟩
    apply Prod.ext
    · exact square.cornerRight_projection_kernelPairLift x v
    · change -square.cornerLeft.spaceProjection x
          (square.kernelPairLift x v) = v.2
      rw [square.cornerLeft_projection_kernelPairLift x v hv', neg_neg]

/-- The signed map from the common corner to the direct sum of the two
one-ended extensions. -/
def toMiddleMap {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.corner.rightModule hmono ⟶
      square.left.result.rightModule hmono ⊞
        square.rightResult.rightModule hmono :=
  biprod.lift (square.toLeftMap hmono) (-square.toRightMap hmono)

/-- The sum of the two canonical projections from the one-ended extensions
back to the original string module. -/
def fromMiddleMap {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :
    square.left.result.rightModule hmono ⊞
        square.rightResult.rightModule hmono ⟶ C.rightModule hmono :=
  biprod.desc (square.leftToBaseMap hmono) (square.rightToBaseMap hmono)

/-- Commutativity of the boundary square gives the complex relation after
putting the conventional minus sign on the right component. -/
@[reassoc]
theorem toMiddleMap_fromMiddleMap {C : Word R}
    (square : PositiveBoundarySquare C) (hmono : IsMonomial R) :
    square.toMiddleMap hmono ≫ square.fromMiddleMap hmono = 0 := by
  rw [toMiddleMap, fromMiddleMap, biprod.lift_desc]
  rw [Preadditive.neg_comp]
  rw [square.map_commutes hmono]
  exact add_neg_cancel _

/-- The canonical two-ended boundary short complex. -/
def shortComplex {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) :=
  ShortComplex.mk (square.toMiddleMap hmono)
    (square.fromMiddleMap hmono) (square.toMiddleMap_fromMiddleMap hmono)

/-- A coherent two-ended boundary square with no extra overlap gives an
exact canonical sequence. -/
theorem shortComplex_exact {C : Word R}
    (square : PositiveBoundarySquare C) (hmono : IsMonomial R) :
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
          square.toLeftMap hmono := by
      rw [toMiddleMap, biprod.lift_fst]
    have hsnd : square.toMiddleMap hmono ≫
        (biprod.snd :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.rightResult.rightModule hmono) =
          -square.toRightMap hmono := by
      rw [toMiddleMap, biprod.lift_snd]
    apply Prod.ext
    · have h := congrArg
        (fun q : square.corner.rightModule hmono ⟶
            square.left.result.rightModule hmono ↦ (q.app X).hom w) hfst
      change
        ((biprod.fst :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.left.result.rightModule hmono).app X).hom
            (((square.toMiddleMap hmono).app X).hom w) =
          ((square.toLeftMap hmono).app X).hom w at h
      change
        ((biprod.fst :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.left.result.rightModule hmono).app X).hom
            (((square.toMiddleMap hmono).app X).hom w) =
          square.cornerRight.toRightExtension.spaceProjection x w
      change
        ((biprod.fst :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.left.result.rightModule hmono).app X).hom
            (((square.toMiddleMap hmono).app X).hom w) =
          square.cornerRight.toRightExtension.spaceProjection x w at h
      exact h
    · have h := congrArg
        (fun q : square.corner.rightModule hmono ⟶
            square.rightResult.rightModule hmono ↦ (q.app X).hom w) hsnd
      change
        ((biprod.snd :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.rightResult.rightModule hmono).app X).hom
            (((square.toMiddleMap hmono).app X).hom w) =
          ((-square.toRightMap hmono).app X).hom w at h
      change
        ((biprod.snd :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.rightResult.rightModule hmono).app X).hom
            (((square.toMiddleMap hmono).app X).hom w) =
          -square.cornerLeft.spaceProjection x w
      change
        ((biprod.snd :
          square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono ⟶
            square.rightResult.rightModule hmono).app X).hom
            (((square.toMiddleMap hmono).app X).hom w) =
          -square.cornerLeft.spaceProjection x w at h
      exact h
  have hFrom : ((square.fromMiddleMap hmono).app X).hom ∘ₗ
        e.symm.toLinearMap = square.fromPairSpaceMap x := by
    apply LinearMap.ext
    intro v
    have hinl :
        (biprod.inl : square.left.result.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono) ≫
            square.fromMiddleMap hmono = square.leftToBaseMap hmono := by
      rw [fromMiddleMap, biprod.inl_desc]
    have hinr :
        (biprod.inr : square.rightResult.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono) ≫
            square.fromMiddleMap hmono = square.rightToBaseMap hmono := by
      rw [fromMiddleMap, biprod.inr_desc]
    have h₁ := congrArg
      (fun q : square.left.result.rightModule hmono ⟶
          C.rightModule hmono ↦ (q.app X).hom v.1) hinl
    have h₂ := congrArg
      (fun q : square.rightResult.rightModule hmono ⟶
          C.rightModule hmono ↦ (q.app X).hom v.2) hinr
    change ((square.fromMiddleMap hmono).app X).hom
        (((biprod.inl : square.left.result.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono).app X).hom v.1 +
        ((biprod.inr : square.rightResult.rightModule hmono ⟶
          square.left.result.rightModule hmono ⊞
            square.rightResult.rightModule hmono).app X).hom v.2) = _
    rw [map_add]
    change
      ((square.fromMiddleMap hmono).app X).hom
          (((biprod.inl : square.left.result.rightModule hmono ⟶
            square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono).app X).hom v.1) =
        ((square.leftToBaseMap hmono).app X).hom v.1 at h₁
    change
      ((square.fromMiddleMap hmono).app X).hom
          (((biprod.inr : square.rightResult.rightModule hmono ⟶
            square.left.result.rightModule hmono ⊞
              square.rightResult.rightModule hmono).app X).hom v.2) =
        ((square.rightToBaseMap hmono).app X).hom v.2 at h₂
    rw [h₁, h₂]
    rfl
  have hexact : Function.Exact
      (e.toLinearMap ∘ₗ ((square.toMiddleMap hmono).app X).hom)
      (((square.fromMiddleMap hmono).app X).hom ∘ₗ
        e.symm.toLinearMap) := by
    rw [hTo, hFrom]
    exact square.pairSpaceMap_exact hmono x
  have hOriginal : Function.Exact
      ((square.toMiddleMap hmono).app X).hom
      ((square.fromMiddleMap hmono).app X).hom :=
    (LinearEquiv.conj_exact_iff_exact _ _ e).mp hexact
  exact (LinearMap.exact_iff.mp hOriginal).symm

end PositiveBoundarySquare

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
