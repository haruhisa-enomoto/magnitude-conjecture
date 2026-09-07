import MagnitudeConjecture.Algebra.StringArrowRightIdealBasis
import MagnitudeConjecture.Algebra.UniserialModule
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# The path action on a string-arrow right ideal

Longer surviving continuations factor through shorter ones.  This file
realizes the intervening path as a matrix coordinate in the finite category
algebra and computes its action on the global continuation basis.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The representable transformation induced by an arbitrary displayed
path. -/
def pathRepresentableMap
    (P : StringPresentation k A Q) {z x : Q}
    (p : Quiver.Path z x) :
    P.quotientRepresentable (obj P.toPresentation.relations z) ⟶
      P.quotientRepresentable (obj P.toPresentation.relations x) :=
  (CoveringHom.finiteDimensionalLinearCoyonedaFunctor
      (finiteRepresentablesOfAdmissible P.toPresentation.admissible)).map
    (pathMap P.toPresentation.relations p).op

@[simp]
theorem pathRepresentableMap_app_apply
    (P : StringPresentation k A Q) {z x : Q}
    (p : Quiver.Path z x) (w : Q)
    (f : obj P.toPresentation.relations z ⟶
      obj P.toPresentation.relations w) :
    ((P.pathRepresentableMap p).hom.hom.app
        (obj P.toPresentation.relations w)).hom f =
      pathMap P.toPresentation.relations p ≫ f :=
  rfl

/-- Concatenation of displayed paths becomes composition of the induced
representable transformations. -/
theorem pathRepresentableMap_comp
    (P : StringPresentation k A Q) {w z x : Q}
    (r : Quiver.Path w z) (p : Quiver.Path z x) :
    P.pathRepresentableMap r ≫ P.pathRepresentableMap p =
      P.pathRepresentableMap (r.comp p) := by
  unfold pathRepresentableMap
  rw [← Functor.map_comp, ← op_comp, pathMap_comp]

/-- A killed path after the displayed arrow induces the zero composite of
representable transformations. -/
theorem pathRepresentableMap_comp_arrowRepresentableMap_eq_zero
    (P : StringPresentation k A Q) {w x y : Q}
    (a : x ⟶ y) (p : Quiver.Path w x)
    (hzero : arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations p = 0) :
    P.pathRepresentableMap p ≫ P.arrowRepresentableMap a = 0 := by
  unfold pathRepresentableMap arrowRepresentableMap
  rw [← Functor.map_comp, ← op_comp, hzero, op_zero, Functor.map_zero]

/-- The matrix coordinate of an arbitrary displayed path in the finite
category algebra. -/
def pathAlgebraCoordinate
    (P : StringPresentation k A Q) {z x : Q}
    (p : Quiver.Path z x) : P.quotientCategoryAlgebra :=
  biproduct.π P.quotientRepresentable
      (obj P.toPresentation.relations z) ≫
    P.pathRepresentableMap p ≫
    biproduct.ι P.quotientRepresentable
      (obj P.toPresentation.relations x)

/-- The algebra-linear represented range has the same continuation basis as
its coefficient-field-linear realization. -/
def representedArrowModuleBasis
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module.Basis
      (P.toSpecialBiserialPresentation.LeftContinuationPath a) k
      (LinearMap.range (P.representedArrowLinearMap a)) :=
  (P.representedArrowRangeBasis a).map
  (P.representedArrowRangeKLinearEquiv a).symm

/-- The explicit represented-range element belonging to one surviving left
continuation. -/
def representedContinuationElement
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    LinearMap.range (P.representedArrowLinearMap a) :=
  ⟨biproduct.π P.quotientRepresentable
        (obj P.toPresentation.relations p.1.1) ≫
      P.pathRepresentableMap p.1.2 ≫ P.arrowRepresentableMap a,
    ⟨biproduct.π P.quotientRepresentable
        (obj P.toPresentation.relations p.1.1) ≫
      P.pathRepresentableMap p.1.2, rfl⟩⟩

/-- The explicit continuation element has its path vector at its starting
vertex. -/
theorem representedContinuationElement_coordinate_self
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    P.representedArrowRangeCoordinateLinearEquiv a
        (P.representedArrowRangeKLinearEquiv a
          (P.representedContinuationElement a p))
            (obj P.toPresentation.relations p.1.1) =
      P.leftArrowCoordinateBasis a p.1.1 ⟨p.1.2, p.2⟩ := by
  apply Subtype.ext
  rw [P.leftArrowCoordinateBasis_apply]
  let g : P.representedVertexHom y :=
    (P.representedContinuationElement a p).1
  have hrestrict :
      biproduct.ι P.quotientRepresentable
          (obj P.toPresentation.relations p.1.1) ≫
        g =
          P.pathRepresentableMap p.1.2 ≫
            P.arrowRepresentableMap a := by
    simp [g, representedContinuationElement]
  change
    P.representedVertexCoordinateLinearEquiv y
        g
          (obj P.toPresentation.relations p.1.1) =
      arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations p.1.2
  rw [P.representedVertexCoordinateLinearEquiv_apply]
  rw [hrestrict]
  change
    P.leftArrowCompositionLinearMap a p.1.1
        (pathMap P.toPresentation.relations p.1.2) =
      arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations p.1.2
  rfl

/-- The explicit continuation element vanishes in every other starting
vertex coordinate. -/
theorem representedContinuationElement_coordinate_ne
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (z : Q) (hz : z ≠ p.1.1) :
    P.representedArrowRangeCoordinateLinearEquiv a
        (P.representedArrowRangeKLinearEquiv a
          (P.representedContinuationElement a p))
            (obj P.toPresentation.relations z) = 0 := by
  apply Subtype.ext
  change
    (biproduct.ι P.quotientRepresentable
        (obj P.toPresentation.relations z) ≫
      (P.representedContinuationElement a p).1).hom.hom.app
        (obj P.toPresentation.relations z) (𝟙 _) = 0
  have hobj :
      obj P.toPresentation.relations z ≠
        obj P.toPresentation.relations p.1.1 := by
    intro h
    apply hz
    simpa using congrArg P.quotientObjectEquiv h
  have hzero :
      biproduct.ι P.quotientRepresentable
          (obj P.toPresentation.relations z) ≫
        (P.representedContinuationElement a p).1 = 0 := by
    simp [representedContinuationElement, hobj]
  rw [hzero]
  rfl

/-- The transported global basis vector is the explicit matrix-supported
continuation element. -/
theorem representedArrowModuleBasis_apply
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    P.representedArrowModuleBasis a p =
      P.representedContinuationElement a p := by
  apply (P.representedArrowRangeKLinearEquiv a).injective
  apply (P.representedArrowRangeCoordinateLinearEquiv a).injective
  funext X
  let z := P.quotientObjectEquiv X
  have hX : X = obj P.toPresentation.relations z := by
    apply P.quotientObjectEquiv.injective
    simp [z]
  rw [hX]
  by_cases hz : z = p.1.1
  · rw [hz]
    have hb := P.representedArrowRangeBasis_coordinate_self a p
    have he := P.representedContinuationElement_coordinate_self a p
    simpa [representedArrowModuleBasis] using hb.trans he.symm
  · have hb := P.representedArrowRangeBasis_coordinate_ne a p z hz
    have he := P.representedContinuationElement_coordinate_ne a p z hz
    simpa [representedArrowModuleBasis] using hb.trans he.symm

@[simp]
theorem representedArrowRange_smul_val
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (c : P.quotientCategoryAlgebraᵐᵒᵖ)
    (g : LinearMap.range (P.representedArrowLinearMap a)) :
    (c • g).1 = c.unop ≫ g.1 :=
  rfl

/-- The matrix coordinate of the factor between two continuations sends the
shorter explicit continuation element to the longer one. -/
theorem pathAlgebraCoordinate_smul_representedContinuationElement
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p q : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (r : Quiver.Path q.1.1 p.1.1)
    (hr : q.1.2 = r.comp p.1.2) :
    MulOpposite.op (P.pathAlgebraCoordinate r) •
        P.representedContinuationElement a p =
      P.representedContinuationElement a q := by
  apply Subtype.ext
  rw [P.representedArrowRange_smul_val]
  change
    P.pathAlgebraCoordinate r ≫
        (biproduct.π P.quotientRepresentable
            (obj P.toPresentation.relations p.1.1) ≫
          P.pathRepresentableMap p.1.2 ≫ P.arrowRepresentableMap a) =
      biproduct.π P.quotientRepresentable
          (obj P.toPresentation.relations q.1.1) ≫
        P.pathRepresentableMap q.1.2 ≫ P.arrowRepresentableMap a
  simp only [pathAlgebraCoordinate, Category.assoc,
    bicone_ι_π_self_assoc, hr]
  rw [← P.pathRepresentableMap_comp]
  simp only [Category.assoc]

/-- The same path-coordinate action, stated on the transported global basis.
-/
theorem pathAlgebraCoordinate_smul_representedArrowModuleBasis
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p q : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (r : Quiver.Path q.1.1 p.1.1)
    (hr : q.1.2 = r.comp p.1.2) :
    MulOpposite.op (P.pathAlgebraCoordinate r) •
        P.representedArrowModuleBasis a p =
      P.representedArrowModuleBasis a q := by
  rw [P.representedArrowModuleBasis_apply,
    P.representedArrowModuleBasis_apply,
    P.pathAlgebraCoordinate_smul_representedContinuationElement a p q r hr]

/-- Every longer continuation-basis vector is an algebra multiple of every
shorter one. -/
theorem representedArrowModuleBasis_smul_of_length_le
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p q : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (h : p.1.2.length ≤ q.1.2.length) :
    ∃ c : P.quotientCategoryAlgebraᵐᵒᵖ,
      c • P.representedArrowModuleBasis a p =
        P.representedArrowModuleBasis a q := by
  obtain ⟨r, hr⟩ :=
    P.toSpecialBiserialPresentation.leftContinuationPath_factor_of_length_le
      a p q h
  exact ⟨MulOpposite.op (P.pathAlgebraCoordinate r),
    P.pathAlgebraCoordinate_smul_representedArrowModuleBasis a p q r hr⟩

/-- A path coordinate whose target does not match the starting vertex of a
continuation kills its basis vector. -/
theorem pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_of_ne
    (P : StringPresentation k A Q) {x y w z : Q} (a : x ⟶ y)
    (r : Quiver.Path w z)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (hz : z ≠ p.1.1) :
    MulOpposite.op (P.pathAlgebraCoordinate r) •
        P.representedArrowModuleBasis a p = 0 := by
  rw [P.representedArrowModuleBasis_apply]
  apply Subtype.ext
  rw [P.representedArrowRange_smul_val]
  have hobj :
      obj P.toPresentation.relations z ≠
        obj P.toPresentation.relations p.1.1 := by
    intro h
    apply hz
    simpa using congrArg P.quotientObjectEquiv h
  change
    P.pathAlgebraCoordinate r ≫
        (biproduct.π P.quotientRepresentable
            (obj P.toPresentation.relations p.1.1) ≫
          P.pathRepresentableMap p.1.2 ≫ P.arrowRepresentableMap a) = 0
  simp [pathAlgebraCoordinate, Category.assoc, hobj]

/-- When the concatenated path is killed after the arrow, the matching path
coordinate kills the continuation basis vector. -/
theorem pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_of_comp
    (P : StringPresentation k A Q) {x y w : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (r : Quiver.Path w p.1.1)
    (hzero : arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations (r.comp p.1.2) = 0) :
    MulOpposite.op (P.pathAlgebraCoordinate r) •
        P.representedArrowModuleBasis a p = 0 := by
  rw [P.representedArrowModuleBasis_apply]
  apply Subtype.ext
  rw [P.representedArrowRange_smul_val]
  have hmapzero :=
    P.pathRepresentableMap_comp_arrowRepresentableMap_eq_zero
      a (r.comp p.1.2) hzero
  change
    P.pathAlgebraCoordinate r ≫
        (biproduct.π P.quotientRepresentable
            (obj P.toPresentation.relations p.1.1) ≫
          P.pathRepresentableMap p.1.2 ≫ P.arrowRepresentableMap a) = 0
  simp only [pathAlgebraCoordinate, Category.assoc,
    bicone_ι_π_self_assoc]
  rw [← P.pathRepresentableMap_comp] at hmapzero
  simp only [Category.assoc] at hmapzero
  rw [hmapzero]
  simp

/-- A path coordinate acts on any continuation basis vector either by zero or
by the basis vector of the surviving concatenation. -/
theorem pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_or
    (P : StringPresentation k A Q) {x y w : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (r : Quiver.Path w p.1.1) :
    MulOpposite.op (P.pathAlgebraCoordinate r) •
          P.representedArrowModuleBasis a p = 0 ∨
      ∃ q : P.toSpecialBiserialPresentation.LeftContinuationPath a,
        q.1.2.length = r.length + p.1.2.length ∧
        MulOpposite.op (P.pathAlgebraCoordinate r) •
            P.representedArrowModuleBasis a p =
          P.representedArrowModuleBasis a q := by
  by_cases hzero : arrowMap P.toPresentation.relations a ≫
      pathMap P.toPresentation.relations (r.comp p.1.2) = 0
  · exact Or.inl
      (P.pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_of_comp
        a p r hzero)
  · let q : P.toSpecialBiserialPresentation.LeftContinuationPath a :=
      ⟨⟨w, r.comp p.1.2⟩, hzero⟩
    exact Or.inr ⟨q, by simp [q],
      P.pathAlgebraCoordinate_smul_representedArrowModuleBasis a p q r rfl⟩

/-- An arbitrary path coordinate acts on a continuation basis vector either
by zero or by a basis vector whose length increases by the path length. -/
theorem pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_or_any
    (P : StringPresentation k A Q) {x y w z : Q} (a : x ⟶ y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (r : Quiver.Path w z) :
    MulOpposite.op (P.pathAlgebraCoordinate r) •
          P.representedArrowModuleBasis a p = 0 ∨
      ∃ q : P.toSpecialBiserialPresentation.LeftContinuationPath a,
        q.1.2.length = r.length + p.1.2.length ∧
        MulOpposite.op (P.pathAlgebraCoordinate r) •
            P.representedArrowModuleBasis a p =
          P.representedArrowModuleBasis a q := by
  by_cases hz : z = p.1.1
  · subst z
    exact
      P.pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_or
        a p r
  · exact Or.inl
      (P.pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_of_ne
        a r p hz)

/-- The subspace spanned by continuation-basis vectors of length at least
`m`. -/
def representedArrowLengthTail
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) (m : ℕ) :
    Submodule k (LinearMap.range (P.representedArrowLinearMap a)) :=
  Submodule.span k
    (P.representedArrowModuleBasis a ''
      {p | m ≤ p.1.2.length})

/-- A continuation-basis vector belongs to every length tail below its
length. -/
theorem representedArrowModuleBasis_mem_lengthTail
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) (m : ℕ)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (hp : m ≤ p.1.2.length) :
    P.representedArrowModuleBasis a p ∈
      P.representedArrowLengthTail a m := by
  apply Submodule.subset_span
  exact ⟨p, hp, rfl⟩

/-- Requiring a larger minimum length gives a smaller tail. -/
theorem representedArrowLengthTail_antitone
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {m n : ℕ} (hmn : m ≤ n) :
    P.representedArrowLengthTail a n ≤
      P.representedArrowLengthTail a m := by
  apply Submodule.span_mono
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, hmn.trans hp, rfl⟩

/-- A length tail beyond every surviving continuation is zero. -/
theorem representedArrowLengthTail_eq_bot_of_forall_lt
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) (n : ℕ)
    (hn : ∀ p : P.toSpecialBiserialPresentation.LeftContinuationPath a,
      p.1.2.length < n) :
    P.representedArrowLengthTail a n = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.2
  rintro _ ⟨p, hp, rfl⟩
  exact False.elim (Nat.not_le_of_lt (hn p) hp)

/-- Admissibility makes one sufficiently deep continuation-length tail
zero. -/
theorem exists_representedArrowLengthTail_eq_bot
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    ∃ n : ℕ, P.representedArrowLengthTail a n = ⊥ := by
  obtain ⟨n, _, hlong⟩ := P.toPresentation.admissible.long_paths_mem
  refine ⟨n, P.representedArrowLengthTail_eq_bot_of_forall_lt a n ?_⟩
  intro p
  apply Nat.lt_of_not_ge
  intro hp
  have hmem := hlong (p.1.2.comp a.toPath) (by
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega)
  have hzero :
      pathMap P.toPresentation.relations (p.1.2.comp a.toPath) = 0 :=
    (pathMap_eq_zero_iff_mem_relationIdeal
      P.toPresentation.relations (p.1.2.comp a.toPath)).2 hmem
  rw [← pathMap_comp] at hzero
  exact p.2 (by simpa only [arrowMap] using hzero)

set_option maxHeartbeats 800000 in
/-- Acting by a path coordinate raises the length tail by the length of the
path. -/
theorem pathAlgebraCoordinate_smul_mem_lengthTail
    (P : StringPresentation k A Q) {x y w z : Q} (a : x ⟶ y)
    (r : Quiver.Path w z) (m : ℕ)
    (g : LinearMap.range (P.representedArrowLinearMap a))
    (hg : g ∈ P.representedArrowLengthTail a m) :
    MulOpposite.op (P.pathAlgebraCoordinate r) • g ∈
      P.representedArrowLengthTail a (m + r.length) := by
  let s : P.quotientCategoryAlgebraᵐᵒᵖ :=
    MulOpposite.op (P.pathAlgebraCoordinate r)
  let T := P.representedArrowLengthTail a (m + r.length)
  change s • g ∈ T
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨p, hp, rfl⟩ := hg
      change MulOpposite.op (P.pathAlgebraCoordinate r) •
          P.representedArrowModuleBasis a p ∈
        P.representedArrowLengthTail a (m + r.length)
      rcases
          P.pathAlgebraCoordinate_smul_representedArrowModuleBasis_eq_zero_or_any
            a p r with hzero | ⟨q, hlength, hq⟩
      · rw [hzero]
        exact Submodule.zero_mem _
      · rw [hq]
        apply P.representedArrowModuleBasis_mem_lengthTail
        rw [hlength]
        simpa [Nat.add_comm] using Nat.add_le_add_left hp r.length
  | zero =>
      have hzero :
          s • (0 : LinearMap.range (P.representedArrowLinearMap a)) = 0 :=
        smul_zero s
      exact hzero.symm ▸ T.zero_mem
  | add f g _ _ hf hg =>
      have hadd : s • (f + g) = s • f + s • g := smul_add s f g
      exact hadd.symm ▸ T.add_mem hf hg
  | smul c g _ hg =>
      have hcomm : s • (c • g) = c • (s • g) := smul_comm s c g
      exact hcomm.symm ▸ T.smul_mem c hg

/-- A category-algebra scalar is positive on an arrow module when it raises
every continuation-length tail by one. -/
def RaisesRepresentedArrowLengthTail
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (c : P.quotientCategoryAlgebraᵐᵒᵖ) : Prop :=
  ∀ (m : ℕ) (g : LinearMap.range (P.representedArrowLinearMap a)),
    g ∈ P.representedArrowLengthTail a m →
      c • g ∈ P.representedArrowLengthTail a (m + 1)

/-- A positive-length path coordinate raises every length tail. -/
theorem raisesRepresentedArrowLengthTail_pathAlgebraCoordinate
    (P : StringPresentation k A Q) {x y w z : Q} (a : x ⟶ y)
    (r : Quiver.Path w z) (hr : r.length ≠ 0) :
    P.RaisesRepresentedArrowLengthTail a
      (MulOpposite.op (P.pathAlgebraCoordinate r)) := by
  intro m g hg
  apply P.representedArrowLengthTail_antitone a
      (show m + 1 ≤ m + r.length by omega)
  exact P.pathAlgebraCoordinate_smul_mem_lengthTail a r m g hg

/-- Zero raises every length tail. -/
theorem raisesRepresentedArrowLengthTail_zero
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.RaisesRepresentedArrowLengthTail a 0 := by
  intro m g _
  rw [zero_smul]
  exact Submodule.zero_mem _

/-- Sums of tail-raising scalars still raise tails. -/
theorem RaisesRepresentedArrowLengthTail.add
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {c d : P.quotientCategoryAlgebraᵐᵒᵖ}
    (hc : P.RaisesRepresentedArrowLengthTail a c)
    (hd : P.RaisesRepresentedArrowLengthTail a d) :
    P.RaisesRepresentedArrowLengthTail a (c + d) := by
  intro m g hg
  rw [add_smul]
  exact Submodule.add_mem _ (hc m g hg) (hd m g hg)

/-- A finite sum of tail-raising scalars raises tails. -/
theorem raisesRepresentedArrowLengthTail_finset_sum
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {I : Type*} (s : Finset I)
    (f : I → P.quotientCategoryAlgebraᵐᵒᵖ)
    (hf : ∀ i ∈ s, P.RaisesRepresentedArrowLengthTail a (f i)) :
    P.RaisesRepresentedArrowLengthTail a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using P.raisesRepresentedArrowLengthTail_zero a
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add P a
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- Multiplying a tail-raising scalar by a field scalar preserves the
tail-raising property. -/
theorem RaisesRepresentedArrowLengthTail.algebraMap_mul
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {d : P.quotientCategoryAlgebraᵐᵒᵖ}
    (hd : P.RaisesRepresentedArrowLengthTail a d) (c : k) :
    P.RaisesRepresentedArrowLengthTail a
      (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ c * d) := by
  intro m g hg
  rw [mul_smul]
  change c • (d • g) ∈ P.representedArrowLengthTail a (m + 1)
  exact Submodule.smul_mem _ c (hd m g hg)

/-- A strictly longer continuation is obtained from a shorter one by a
tail-raising scalar. -/
theorem exists_raisesRepresentedArrowLengthTail_smul_basis_of_length_lt
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (p q : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (hpq : p.1.2.length < q.1.2.length) :
    ∃ c : P.quotientCategoryAlgebraᵐᵒᵖ,
      P.RaisesRepresentedArrowLengthTail a c ∧
        c • P.representedArrowModuleBasis a p =
          P.representedArrowModuleBasis a q := by
  obtain ⟨r, hr, hrpos⟩ :=
    P.toSpecialBiserialPresentation.leftContinuationPath_factor_of_length_lt
      a p q hpq
  exact ⟨MulOpposite.op (P.pathAlgebraCoordinate r),
    P.raisesRepresentedArrowLengthTail_pathAlgebraCoordinate a r hrpos,
    P.pathAlgebraCoordinate_smul_representedArrowModuleBasis a p q r hr⟩

set_option maxHeartbeats 800000 in
/-- The `n`th power of a tail-raising scalar raises length by `n`. -/
theorem RaisesRepresentedArrowLengthTail.pow_smul_mem
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {c : P.quotientCategoryAlgebraᵐᵒᵖ}
    (hc : P.RaisesRepresentedArrowLengthTail a c)
    (n m : ℕ) (g : LinearMap.range (P.representedArrowLinearMap a))
    (hg : g ∈ P.representedArrowLengthTail a m) :
    c ^ n • g ∈ P.representedArrowLengthTail a (m + n) := by
  induction n generalizing m g with
  | zero =>
      simpa only [pow_zero, one_smul, Nat.add_zero] using hg
  | succ n ih =>
      rw [pow_succ, mul_smul]
      have hcg := hc m g hg
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (m + 1) (c • g) hcg

set_option maxHeartbeats 800000 in
/-- A tail-raising scalar acts locally nilpotently on each continuation-basis
vector. -/
theorem RaisesRepresentedArrowLengthTail.exists_pow_smul_basis_eq_zero
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    {c : P.quotientCategoryAlgebraᵐᵒᵖ}
    (hc : P.RaisesRepresentedArrowLengthTail a c)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
    ∃ n : ℕ, c ^ n • P.representedArrowModuleBasis a p = 0 := by
  obtain ⟨n, hn⟩ := P.exists_representedArrowLengthTail_eq_bot a
  refine ⟨n, ?_⟩
  have hmem := hc.pow_smul_mem P a n 0
    (P.representedArrowModuleBasis a p)
    (P.representedArrowModuleBasis_mem_lengthTail a 0 p (Nat.zero_le _))
  rw [Nat.zero_add, hn] at hmem
  exact hmem

set_option maxHeartbeats 1200000 in
/-- After selecting a nonzero shortest coordinate of a vector, all remaining
coordinates are produced from that basis vector by one tail-raising scalar.
-/
theorem exists_raisesRepresentedArrowLengthTail_smul_basis_eq_sub
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (g : LinearMap.range (P.representedArrowLinearMap a))
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (hp : (P.representedArrowModuleBasis a).repr g p ≠ 0)
    (hmin : ∀ q : P.toSpecialBiserialPresentation.LeftContinuationPath a,
      (P.representedArrowModuleBasis a).repr g q ≠ 0 →
        p.1.2.length ≤ q.1.2.length) :
    ∃ n : P.quotientCategoryAlgebraᵐᵒᵖ,
      P.RaisesRepresentedArrowLengthTail a n ∧
        n • P.representedArrowModuleBasis a p =
          g - (P.representedArrowModuleBasis a).repr g p •
            P.representedArrowModuleBasis a p := by
  classical
  let b := P.representedArrowModuleBasis a
  let S := (b.repr g).support.erase p
  have hpSupport : p ∈ (b.repr g).support :=
    Finsupp.mem_support_iff.mpr hp
  have hlt : ∀ q ∈ S, p.1.2.length < q.1.2.length := by
    intro q hq
    have hqData := Finset.mem_erase.mp hq
    have hle := hmin q (Finsupp.mem_support_iff.mp hqData.2)
    apply lt_of_le_of_ne hle
    intro heq
    apply hqData.1
    exact
      (P.toSpecialBiserialPresentation.leftContinuationLengthEmbedding a).injective
        heq.symm
  let c (q : P.toSpecialBiserialPresentation.LeftContinuationPath a) :
      P.quotientCategoryAlgebraᵐᵒᵖ :=
    if hq : q ∈ S then
      Classical.choose
        (P.exists_raisesRepresentedArrowLengthTail_smul_basis_of_length_lt
          a p q (hlt q hq))
    else 0
  have hcRaises : ∀ q ∈ S,
      P.RaisesRepresentedArrowLengthTail a (c q) := by
    intro q hq
    rw [show c q = Classical.choose
        (P.exists_raisesRepresentedArrowLengthTail_smul_basis_of_length_lt
          a p q (hlt q hq)) by simp [c, hq]]
    exact (Classical.choose_spec
      (P.exists_raisesRepresentedArrowLengthTail_smul_basis_of_length_lt
        a p q (hlt q hq))).1
  have hcSmul : ∀ q ∈ S,
      c q • b p = b q := by
    intro q hq
    rw [show c q = Classical.choose
        (P.exists_raisesRepresentedArrowLengthTail_smul_basis_of_length_lt
          a p q (hlt q hq)) by simp [c, hq]]
    exact (Classical.choose_spec
      (P.exists_raisesRepresentedArrowLengthTail_smul_basis_of_length_lt
        a p q (hlt q hq))).2
  let n : P.quotientCategoryAlgebraᵐᵒᵖ :=
    ∑ q ∈ S, algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ (b.repr g q) * c q
  refine ⟨n, ?_, ?_⟩
  · apply P.raisesRepresentedArrowLengthTail_finset_sum a S
    intro q hq
    exact (hcRaises q hq).algebraMap_mul P a (b.repr g q)
  · have hnSmul : n • b p = ∑ q ∈ S, b.repr g q • b q := by
      dsimp [n]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro q hq
      rw [mul_smul, hcSmul q hq]
      rfl
    have hdecomp :
        g = b.repr g p • b p + ∑ q ∈ S, b.repr g q • b q := by
      simpa only [S] using basis_sum_repr_support_erase b g p hpSupport
    calc
      n • b p = ∑ q ∈ S, b.repr g q • b q := hnSmul
      _ = (b.repr g p • b p + ∑ q ∈ S, b.repr g q • b q) -
          b.repr g p • b p := by abel
      _ = g - b.repr g p • b p :=
        (congrArg (fun z ↦ z - b.repr g p • b p) hdecomp).symm

set_option maxHeartbeats 4000000 in
/-- A nonzero shortest basis coordinate and its vector generate one another
under the category-algebra action. -/
theorem exists_mutually_smul_basis_of_minimal_repr
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (g : LinearMap.range (P.representedArrowLinearMap a))
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a)
    (hp : (P.representedArrowModuleBasis a).repr g p ≠ 0)
    (hmin : ∀ q : P.toSpecialBiserialPresentation.LeftContinuationPath a,
      (P.representedArrowModuleBasis a).repr g q ≠ 0 →
        p.1.2.length ≤ q.1.2.length) :
    ∃ c d : P.quotientCategoryAlgebraᵐᵒᵖ,
      c • P.representedArrowModuleBasis a p = g ∧
        d • g = P.representedArrowModuleBasis a p := by
  let b := P.representedArrowModuleBasis a
  let α := b.repr g p
  obtain ⟨n, hnRaises, hnSmul⟩ :=
    P.exists_raisesRepresentedArrowLengthTail_smul_basis_eq_sub
      a g p hp hmin
  let u : P.quotientCategoryAlgebraᵐᵒᵖ :=
    algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α⁻¹ * n
  have huRaises : P.RaisesRepresentedArrowLengthTail a u :=
    hnRaises.algebraMap_mul P a α⁻¹
  have hgDecomp : g = α • b p + n • b p := by
    rw [hnSmul]
    abel
  have huSmul : u • b p = α⁻¹ • (n • b p) := by
    dsimp [u]
    rw [mul_smul]
    rfl
  have hinvLeading : α⁻¹ • (α • b p) = b p := by
    rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
  have hscaledDecomp :
      α⁻¹ • g = b p + α⁻¹ • (n • b p) := by
    calc
      α⁻¹ • g = α⁻¹ • (α • b p + n • b p) :=
        congrArg (fun z ↦ α⁻¹ • z) hgDecomp
      _ = α⁻¹ • (α • b p) + α⁻¹ • (n • b p) :=
        smul_add α⁻¹ (α • b p) (n • b p)
      _ = b p + α⁻¹ • (n • b p) :=
        congrArg (fun z ↦ z + α⁻¹ • (n • b p)) hinvLeading
  have hnormalized :
      algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α⁻¹ • g =
        (1 + u) • b p := by
    rw [add_smul, one_smul, huSmul]
    change α⁻¹ • g = b p + α⁻¹ • (n • b p)
    exact hscaledDecomp
  obtain ⟨N, hN⟩ := huRaises.exists_pow_smul_basis_eq_zero P a p
  obtain ⟨e, he⟩ :=
    exists_smul_one_add_eq_of_pow_smul_eq_zero u (b p) N hN
  let leading : P.quotientCategoryAlgebraᵐᵒᵖ :=
    algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α
  have hforward : (leading * (1 + u)) • b p = g := by
    calc
      (leading * (1 + u)) • b p = leading • ((1 + u) • b p) :=
        mul_smul leading (1 + u) (b p)
      _ = leading •
          (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α⁻¹ • g) :=
        congrArg (fun z ↦ leading • z) hnormalized.symm
      _ = g := by
        change α • (α⁻¹ • g) = g
        rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
  refine ⟨leading * (1 + u),
    e * algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α⁻¹,
    hforward, ?_⟩
  calc
    (e * algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α⁻¹) • g =
        e • (algebraMap k P.quotientCategoryAlgebraᵐᵒᵖ α⁻¹ • g) :=
      mul_smul e _ g
    _ = e • ((1 + u) • b p) :=
      congrArg (fun z ↦ e • z) hnormalized
    _ = b p := he

set_option maxHeartbeats 2000000 in
/-- Every nonzero represented arrow-module vector is mutually cyclic with
its shortest continuation-basis vector. -/
theorem exists_mutually_smul_basis_of_ne_zero
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (g : LinearMap.range (P.representedArrowLinearMap a)) (hg : g ≠ 0) :
    ∃ p : P.toSpecialBiserialPresentation.LeftContinuationPath a,
      ∃ c d : P.quotientCategoryAlgebraᵐᵒᵖ,
        c • P.representedArrowModuleBasis a p = g ∧
          d • g = P.representedArrowModuleBasis a p := by
  classical
  let b := P.representedArrowModuleBasis a
  have hrepr : b.repr g ≠ 0 := by
    intro hzero
    apply hg
    exact b.repr.injective (hzero.trans b.repr.map_zero.symm)
  have hsupport : (b.repr g).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr hrepr
  obtain ⟨p, hpSupport, hmin⟩ :=
    Finset.exists_min_image (b.repr g).support
      (fun q ↦ q.1.2.length) hsupport
  refine ⟨p, ?_⟩
  apply P.exists_mutually_smul_basis_of_minimal_repr a g p
  · exact Finsupp.mem_support_iff.mp hpSupport
  · intro q hq
    exact hmin q (Finsupp.mem_support_iff.mpr hq)

set_option maxHeartbeats 2000000 in
/-- The represented range of a string arrow is a uniserial module over the
opposite finite category algebra. -/
theorem representedArrowLinearRange_isUniserial
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (LinearMap.range (P.representedArrowLinearMap a)) := by
  apply IsUniserialModule.of_smul_comparable
  intro g h
  by_cases hg : g = 0
  · right
    exact ⟨0, by simp [hg]⟩
  by_cases hh : h = 0
  · left
    exact ⟨0, by simp [hh]⟩
  obtain ⟨p, cg, dg, hcg, hdg⟩ :=
    P.exists_mutually_smul_basis_of_ne_zero a g hg
  obtain ⟨q, ch, dh, hch, hdh⟩ :=
    P.exists_mutually_smul_basis_of_ne_zero a h hh
  by_cases hpq : p.1.2.length ≤ q.1.2.length
  · obtain ⟨r, hr⟩ := P.representedArrowModuleBasis_smul_of_length_le a p q hpq
    left
    refine ⟨ch * r * dg, ?_⟩
    rw [mul_smul, mul_smul, hdg, hr, hch]
  · have hqp : q.1.2.length ≤ p.1.2.length := Nat.le_of_not_ge hpq
    obtain ⟨r, hr⟩ := P.representedArrowModuleBasis_smul_of_length_le a q p hqp
    right
    refine ⟨cg * r * dh, ?_⟩
    rw [mul_smul, mul_smul, hdh, hr, hcg]

/-- The literal principal right ideal generated by a string arrow is
uniserial. -/
theorem arrowRightIdeal_isUniserial
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (RightModule.rightIdeal (P.arrowAlgebraCoordinate a)) :=
  IsUniserialModule.congr
    (P.arrowRightIdealRepresentedRangeLinearEquiv a).symm
    (P.representedArrowLinearRange_isUniserial a)

end StringPresentation

end MagnitudeConjecture.BoundQuiver
