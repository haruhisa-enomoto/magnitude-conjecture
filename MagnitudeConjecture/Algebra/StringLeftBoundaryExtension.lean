import MagnitudeConjecture.Algebra.StringBoundaryExtension
import MagnitudeConjecture.Algebra.StringReverse

/-!
# Boundary extensions at the left endpoint of a string

Reversal turns a left extension into an ordinary right extension.  This file
packages that transport before imposing the maximal-tail conditions defining
hooks and cohooks.  It also exposes the resulting maps on the original
position basis, so left- and right-endpoint maps can be combined in the same
coordinate argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- A nonempty left extension whose boundary letter becomes positive after
reversing the source word. -/
structure LeftPositiveBoundaryExtension (C : Word R) where
  reverseResult : Word R
  extension : PositiveBoundaryExtension C.reverse reverseResult

namespace LeftPositiveBoundaryExtension

/-- The extended word in the original orientation. -/
def result {C : Word R} (extension : LeftPositiveBoundaryExtension C) :
    Word R :=
  extension.reverseResult.reverse

/-- Number of letters added at the left endpoint. -/
def steps {C : Word R} (extension : LeftPositiveBoundaryExtension C) : ℕ :=
  extension.extension.toRightExtension.steps

/-- A left extension increases the word length by its number of added
letters. -/
@[simp]
theorem result_length {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) :
    extension.result.length = C.length + extension.steps := by
  rw [result, reverse_length,
    extension.extension.toRightExtension.result_length, reverse_length]
  rfl

/-- The canonical left-boundary quotient map, transported through word
reversal. -/
def moduleMap {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) :
    extension.result.rightModule hmono ⟶ C.rightModule hmono :=
  (reverseRightModuleIso extension.reverseResult hmono).inv ≫
    extension.extension.rightModuleProjection hmono ≫
    (reverseRightModuleIso C hmono).inv

instance moduleMap_epi {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) : Epi (extension.moduleMap hmono) := by
  dsimp only [moduleMap]
  infer_instance

/-- Embed an occurrence of the original word into the left-extended result.
In reversed orientation this is the usual prefix-position embedding. -/
def position {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) : extension.result.PositionAt x :=
  reversePosition extension.reverseResult
    (extension.extension.toRightExtension.position (reversePosition C i))

/-- Embedding an old position into a left extension shifts its index by the
number of letters added on the left. -/
@[simp]
theorem position_index {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) :
    (extension.position i).index = extension.steps + i.index := by
  change (reversePosition extension.reverseResult
      (extension.extension.toRightExtension.position
        (reversePosition C i))).index = extension.steps + i.index
  rw [reversePosition_index,
    extension.extension.toRightExtension.position_index,
    reversePosition_index,
    extension.extension.toRightExtension.result_length, reverse_length]
  have hi := i.index_le
  simp only [steps]
  omega

/-- Every position at or to the right of the first inherited index in a
left extension comes from the original word. -/
theorem exists_eq_position_of_steps_le {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) {x : Q}
    (j : extension.result.PositionAt x)
    (hj : extension.steps ≤ j.index) :
    ∃ i : C.PositionAt x, extension.position i = j := by
  have hreverseResultLength :
      extension.reverseResult.length = C.length + extension.steps := by
    rw [extension.extension.toRightExtension.result_length, reverse_length]
    rfl
  let q : extension.reverseResult.PositionAt x :=
    unreversePosition extension.reverseResult j
  have hqIndex : q.index = extension.reverseResult.length - j.index :=
    unreversePosition_index extension.reverseResult j
  have hqBound : q.index ≤ C.reverse.length := by
    rw [hqIndex, hreverseResultLength, reverse_length]
    have hjUpper := j.index_le
    rw [extension.result_length] at hjUpper
    omega
  rcases extension.extension.toRightExtension.exists_eq_position_of_index_le
      q hqBound with ⟨iReverse, hiReverse⟩
  let i : C.PositionAt x := unreversePosition C iReverse
  refine ⟨i, ?_⟩
  apply PositionAt.ext_index
  rw [extension.position_index]
  have hiReverseIndex := congrArg PositionAt.index hiReverse
  rw [extension.extension.toRightExtension.position_index] at hiReverseIndex
  have hiIndex : i.index = C.length - iReverse.index :=
    unreversePosition_index C iReverse
  rw [hiIndex, hiReverseIndex, hqIndex]
  rw [hreverseResultLength]
  have hjUpper := j.index_le
  rw [extension.result_length] at hjUpper
  omega

/-- Coordinate projection from a left-extended word onto its inherited
positions, expressed by reversal and the ordinary right-extension
projection. -/
def spaceProjection {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) (x : Q) :
    extension.result.Space x →ₗ[k] C.Space x :=
  (reverseSpaceEquiv C x).symm.toLinearMap.comp
    (extension.extension.toRightExtension.spaceProjection x |>.comp
      (reverseSpaceEquiv extension.reverseResult x).symm.toLinearMap)

/-- Coordinate inclusion of the inherited positions into a left positive
boundary extension.  This is a linear splitting of the canonical
projection, although it is not generally a module morphism. -/
def spaceInclusion {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) (x : Q) :
    C.Space x →ₗ[k] extension.result.Space x :=
  Finsupp.lmapDomain k k extension.position

@[simp]
theorem moduleMap_app_obj {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) (x : Q) :
    (extension.moduleMap hmono).app (Opposite.op (obj R x)) =
      ModuleCat.ofHom (extension.spaceProjection x) :=
  rfl

/-- The inherited-position embedding of a left positive extension is
injective. -/
theorem position_injective {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) {x : Q} :
    Function.Injective
      (extension.position : C.PositionAt x → extension.result.PositionAt x) := by
  intro i j hij
  apply (reversePositionEquiv C x).injective
  apply extension.extension.toRightExtension.position_injective
  apply (reversePositionEquiv extension.reverseResult x).injective
  exact hij

/-- The coordinate projection is the identity on inherited basis positions. -/
@[simp]
theorem spaceProjection_single_position {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) (c : k) :
    extension.spaceProjection x
        (Finsupp.single (extension.position i) c) =
      Finsupp.single i c := by
  change (reverseSpaceEquiv C x).symm
    (extension.extension.toRightExtension.spaceProjection x
      ((reverseSpaceEquiv extension.reverseResult x).symm
        (Finsupp.single (extension.position i) c))) = _
  rw [position, reverseSpaceEquiv_symm_single]
  have hleft : unreversePosition extension.reverseResult
      (reversePosition extension.reverseResult
        (extension.extension.toRightExtension.position
          (reversePosition C i))) =
      extension.extension.toRightExtension.position (reversePosition C i) :=
    (reversePositionEquiv extension.reverseResult x).left_inv _
  rw [hleft,
    RightExtension.spaceProjection_single_position
      extension.extension.toRightExtension (reversePosition C i) c,
    reverseSpaceEquiv_symm_single]
  have hright : unreversePosition C (reversePosition C i) = i :=
    (reversePositionEquiv C x).left_inv i
  rw [hright]

/-- The coordinate inclusion sends a basis vector to its inherited
position. -/
@[simp]
theorem spaceInclusion_single {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) (c : k) :
    extension.spaceInclusion x (Finsupp.single i c) =
      Finsupp.single (extension.position i) c := by
  exact Finsupp.mapDomain_single

/-- The left-boundary projection is a left inverse to its coordinate
inclusion. -/
@[simp]
theorem spaceProjection_inclusion {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    (x : Q) (v : C.Space x) :
    extension.spaceProjection x (extension.spaceInclusion x v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i c => simp

/-- A left positive-boundary module projection is the identity on inherited
basis positions. -/
@[simp]
theorem moduleMap_app_single_position {C : Word R}
    (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) (c : k) :
    (extension.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single (extension.position i) c) =
      Finsupp.single i c := by
  change extension.spaceProjection x
      (Finsupp.single (extension.position i) c) = _
  exact extension.spaceProjection_single_position i c

/-- The left coordinate projection kills every basis position not inherited
from the original word. -/
theorem spaceProjection_single_of_not_exists {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) {x : Q}
    (j : extension.result.PositionAt x) (c : k)
    (hj : ¬ ∃ i : C.PositionAt x, extension.position i = j) :
    extension.spaceProjection x (Finsupp.single j c) = 0 := by
  change (reverseSpaceEquiv C x).symm
    (extension.extension.toRightExtension.spaceProjection x
      ((reverseSpaceEquiv extension.reverseResult x).symm
        (Finsupp.single j c))) = 0
  rw [reverseSpaceEquiv_symm_single]
  rw [RightExtension.spaceProjection_single_of_not_exists]
  · simp
  · rintro ⟨q, hq⟩
    apply hj
    let i : C.PositionAt x := unreversePosition C q
    refine ⟨i, ?_⟩
    change reversePosition extension.reverseResult
        (extension.extension.toRightExtension.position
          (reversePosition C i)) = j
    rw [← (reversePositionEquiv extension.reverseResult x).right_inv j]
    change reversePosition extension.reverseResult
        (extension.extension.toRightExtension.position
          (reversePosition C i)) =
      reversePosition extension.reverseResult
        (unreversePosition extension.reverseResult j)
    apply congrArg (reversePosition extension.reverseResult)
    have hi : reversePosition C i = q :=
      (reversePositionEquiv C x).right_inv q
    rw [hi, hq]

/-- Projection reads the coefficient at the corresponding inherited
position. -/
@[simp]
theorem spaceProjection_apply_position {C : Word R}
    (extension : LeftPositiveBoundaryExtension C) {x : Q}
    (v : extension.result.Space x) (i : C.PositionAt x) :
    extension.spaceProjection x v i = v (extension.position i) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single j c =>
      classical
      by_cases hj : ∃ q : C.PositionAt x, extension.position q = j
      · rcases hj with ⟨q, rfl⟩
        rw [spaceProjection_single_position]
        simp only [Finsupp.single_apply]
        rw [extension.position_injective.eq_iff]
      · rw [extension.spaceProjection_single_of_not_exists j c hj]
        simp only [Finsupp.zero_apply, Finsupp.single_apply]
        exact (if_neg (fun hji : j = extension.position i ↦
          hj ⟨i, hji.symm⟩)).symm

end LeftPositiveBoundaryExtension

/-- A nonempty left extension whose boundary letter becomes negative after
reversing the source word. -/
structure LeftNegativeBoundaryExtension (C : Word R) where
  reverseResult : Word R
  extension : NegativeBoundaryExtension C.reverse reverseResult

namespace LeftNegativeBoundaryExtension

/-- The extended word in the original orientation. -/
def result {C : Word R} (extension : LeftNegativeBoundaryExtension C) :
    Word R :=
  extension.reverseResult.reverse

/-- Number of letters added at the left endpoint. -/
def steps {C : Word R} (extension : LeftNegativeBoundaryExtension C) : ℕ :=
  extension.extension.toRightExtension.steps

/-- A negative left extension increases the word length by its number of
added letters. -/
@[simp]
theorem result_length {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) :
    extension.result.length = C.length + extension.steps := by
  rw [result, reverse_length,
    extension.extension.toRightExtension.result_length, reverse_length]
  rfl

/-- The canonical left-boundary inclusion, transported through word
reversal. -/
def moduleMap {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) :
    C.rightModule hmono ⟶ extension.result.rightModule hmono :=
  (reverseRightModuleIso C hmono).hom ≫
    extension.extension.rightModuleInclusion hmono ≫
    (reverseRightModuleIso extension.reverseResult hmono).hom

instance moduleMap_mono {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) : Mono (extension.moduleMap hmono) := by
  dsimp only [moduleMap]
  infer_instance

/-- Embed an occurrence of the original word into the left-extended result. -/
def position {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) : extension.result.PositionAt x :=
  reversePosition extension.reverseResult
    (extension.extension.toRightExtension.position (reversePosition C i))

/-- The signed prefix added before the original word, written in the original
orientation. -/
def prefixPath {C : Word R} (extension : LeftNegativeBoundaryExtension C) :
    SignedPath extension.result.source C.source :=
  extension.extension.toRightExtension.suffixPath.reverse

/-- After casting the preserved endpoint, a negative left extension is its
added prefix followed by the original word. -/
theorem path_cast_eq_prefixPath_comp {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q)
      extension.result.source extension.result.target
      extension.result.source C.target rfl
      extension.extension.toRightExtension.source_eq extension.result.path) =
      extension.prefixPath.comp C.path := by
  have hfactor :=
    extension.extension.toRightExtension.path_cast_comp_suffixPath
  have hreverse := congrArg Quiver.Path.reverse hfactor
  rw [path_reverse_cast] at hreverse
  simp only [reverse_path, Quiver.Path.reverse_comp] at hreverse
  have hreverseReverse : C.path.reverse.reverse = C.path :=
    @Quiver.Path.reverse_reverse (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) _ _ _ C.path
  have hpath :
      extension.extension.toRightExtension.suffixPath.reverse.comp
          C.path.reverse.reverse =
        extension.extension.toRightExtension.suffixPath.reverse.comp C.path :=
    congrArg
      (fun p : SignedPath C.source C.target ↦
        extension.extension.toRightExtension.suffixPath.reverse.comp p)
      hreverseReverse
  exact hreverse.trans hpath

/-- The same factorization with the original word cast to the actual right
endpoint of the left extension. -/
theorem path_eq_prefixPath_comp_cast {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) :
    extension.result.path = extension.prefixPath.comp
      (@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        C.source C.target C.source extension.result.target rfl
        extension.extension.toRightExtension.source_eq.symm C.path) := by
  let htarget : extension.result.target = C.target :=
    extension.extension.toRightExtension.source_eq
  apply (path_cast_target_injective
    (V := Quiver.Symmetrify Q) (a := extension.result.source) htarget)
  calc
    _ = extension.prefixPath.comp C.path :=
      extension.path_cast_eq_prefixPath_comp
    _ = (@Quiver.Path.cast (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q)
          extension.result.source extension.result.target
          extension.result.source C.target rfl htarget
          (extension.prefixPath.comp
            (@Quiver.Path.cast (Quiver.Symmetrify Q)
              (Quiver.symmetrifyQuiver Q)
              C.source C.target C.source extension.result.target rfl
              htarget.symm C.path))) := by
      rw [path_cast_comp_target, Quiver.Path.cast_cast]
      exact congrArg
        (fun p : SignedPath C.source C.target ↦ extension.prefixPath.comp p)
        (eq_of_heq
          (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q) C.source C.target
            C.source C.target rfl (htarget.symm.trans htarget) C.path)).symm

/-- Embedding an old position into a negative left extension shifts its
index by the number of letters added on the left. -/
@[simp]
theorem position_index {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) :
    (extension.position i).index = extension.steps + i.index := by
  change (reversePosition extension.reverseResult
      (extension.extension.toRightExtension.position
        (reversePosition C i))).index = extension.steps + i.index
  rw [reversePosition_index,
    extension.extension.toRightExtension.position_index,
    reversePosition_index,
    extension.extension.toRightExtension.result_length, reverse_length]
  have hi := i.index_le
  simp only [steps]
  omega

/-- Every position at or to the right of the first inherited index in a
negative left extension comes from the original word. -/
theorem exists_eq_position_of_steps_le {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) {x : Q}
    (j : extension.result.PositionAt x)
    (hj : extension.steps ≤ j.index) :
    ∃ i : C.PositionAt x, extension.position i = j := by
  have hreverseResultLength :
      extension.reverseResult.length = C.length + extension.steps := by
    rw [extension.extension.toRightExtension.result_length, reverse_length]
    rfl
  let q : extension.reverseResult.PositionAt x :=
    unreversePosition extension.reverseResult j
  have hqIndex : q.index = extension.reverseResult.length - j.index :=
    unreversePosition_index extension.reverseResult j
  have hqBound : q.index ≤ C.reverse.length := by
    rw [hqIndex, hreverseResultLength, reverse_length]
    have hjUpper := j.index_le
    rw [extension.result_length] at hjUpper
    omega
  rcases extension.extension.toRightExtension.exists_eq_position_of_index_le
      q hqBound with ⟨iReverse, hiReverse⟩
  let i : C.PositionAt x := unreversePosition C iReverse
  refine ⟨i, ?_⟩
  apply PositionAt.ext_index
  rw [extension.position_index]
  have hiReverseIndex := congrArg PositionAt.index hiReverse
  rw [extension.extension.toRightExtension.position_index] at hiReverseIndex
  have hiIndex : i.index = C.length - iReverse.index :=
    unreversePosition_index C iReverse
  rw [hiIndex, hiReverseIndex, hqIndex]
  rw [hreverseResultLength]
  have hjUpper := j.index_le
  rw [extension.result_length] at hjUpper
  omega

/-- Coordinate inclusion for a negative left boundary, expressed by
reversal. -/
def spaceInclusion {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) (x : Q) :
    C.Space x →ₗ[k] extension.result.Space x :=
  (reverseSpaceEquiv extension.reverseResult x).toLinearMap.comp
    (extension.extension.toRightExtension.spaceInclusion x |>.comp
      (reverseSpaceEquiv C x).toLinearMap)

/-- Coordinate projection onto the inherited positions of a negative left
extension.  It is a linear retraction of `spaceInclusion`; unlike the latter,
it is not generally a module morphism. -/
def spaceProjection {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) (x : Q) :
    extension.result.Space x →ₗ[k] C.Space x :=
  (reverseSpaceEquiv C x).symm.toLinearMap.comp
    (extension.extension.toRightExtension.spaceProjection x |>.comp
      (reverseSpaceEquiv extension.reverseResult x).symm.toLinearMap)

@[simp]
theorem moduleMap_app_obj {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) (x : Q) :
    (extension.moduleMap hmono).app (Opposite.op (obj R x)) =
      ModuleCat.ofHom (extension.spaceInclusion x) :=
  rfl

/-- The left negative-boundary inclusion carries a basis vector to its
inherited position. -/
@[simp]
theorem moduleMap_app_single {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) (c : k) :
    (extension.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single i c) =
      Finsupp.single (extension.position i) c := by
  change reverseSpaceEquiv extension.reverseResult x
    (extension.extension.toRightExtension.spaceInclusion x
      (reverseSpaceEquiv C x (Finsupp.single i c))) = _
  rw [reverseSpaceEquiv_single, RightExtension.spaceInclusion_single,
    reverseSpaceEquiv_single]
  rfl

/-- The inherited-position embedding of a negative left extension is
injective. -/
theorem position_injective {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) {x : Q} :
    Function.Injective
      (extension.position : C.PositionAt x → extension.result.PositionAt x) := by
  intro i j hij
  apply (reversePositionEquiv C x).injective
  apply extension.extension.toRightExtension.position_injective
  apply (reversePositionEquiv extension.reverseResult x).injective
  exact hij

/-- The coordinate projection is the identity on inherited basis
positions. -/
@[simp]
theorem spaceProjection_single_position {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) (c : k) :
    extension.spaceProjection x
        (Finsupp.single (extension.position i) c) =
      Finsupp.single i c := by
  change (reverseSpaceEquiv C x).symm
    (extension.extension.toRightExtension.spaceProjection x
      ((reverseSpaceEquiv extension.reverseResult x).symm
        (Finsupp.single (extension.position i) c))) = _
  rw [position, reverseSpaceEquiv_symm_single]
  have hleft : unreversePosition extension.reverseResult
      (reversePosition extension.reverseResult
        (extension.extension.toRightExtension.position
          (reversePosition C i))) =
      extension.extension.toRightExtension.position (reversePosition C i) :=
    (reversePositionEquiv extension.reverseResult x).left_inv _
  rw [hleft,
    RightExtension.spaceProjection_single_position
      extension.extension.toRightExtension (reversePosition C i) c,
    reverseSpaceEquiv_symm_single]
  have hright : unreversePosition C (reversePosition C i) = i :=
    (reversePositionEquiv C x).left_inv i
  rw [hright]

/-- The negative left coordinate inclusion sends a basis vector to its
inherited position. -/
@[simp]
theorem spaceInclusion_single {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) (c : k) :
    extension.spaceInclusion x (Finsupp.single i c) =
      Finsupp.single (extension.position i) c := by
  change reverseSpaceEquiv extension.reverseResult x
    (extension.extension.toRightExtension.spaceInclusion x
      (reverseSpaceEquiv C x (Finsupp.single i c))) = _
  rw [reverseSpaceEquiv_single, RightExtension.spaceInclusion_single,
    reverseSpaceEquiv_single]
  rfl

/-- The negative left coordinate projection retracts its inclusion. -/
@[simp]
theorem spaceProjection_inclusion {C : Word R}
    (extension : LeftNegativeBoundaryExtension C)
    (x : Q) (v : C.Space x) :
    extension.spaceProjection x (extension.spaceInclusion x v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i c => simp

/-- Inclusion preserves the coefficient at every inherited position. -/
@[simp]
theorem spaceInclusion_apply_position {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) {x : Q}
    (v : C.Space x) (i : C.PositionAt x) :
    extension.spaceInclusion x v (extension.position i) = v i := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single j c =>
      rw [extension.spaceInclusion_single]
      simp only [Finsupp.single_apply]
      rw [extension.position_injective.eq_iff]

/-- Inclusion has zero coefficient at every non-inherited position. -/
theorem spaceInclusion_apply_of_not_exists {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) {x : Q}
    (v : C.Space x) (j : extension.result.PositionAt x)
    (hj : ¬ ∃ i : C.PositionAt x, extension.position i = j) :
    extension.spaceInclusion x v j = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single i c =>
      rw [extension.spaceInclusion_single, Finsupp.single_apply]
      exact if_neg (fun h ↦ hj ⟨i, h⟩)

/-- The negative left coordinate projection kills basis positions which do
not come from the shorter word. -/
theorem spaceProjection_single_of_not_exists {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) {x : Q}
    (j : extension.result.PositionAt x) (c : k)
    (hj : ¬ ∃ i : C.PositionAt x, extension.position i = j) :
    extension.spaceProjection x (Finsupp.single j c) = 0 := by
  change (reverseSpaceEquiv C x).symm
    (extension.extension.toRightExtension.spaceProjection x
      ((reverseSpaceEquiv extension.reverseResult x).symm
        (Finsupp.single j c))) = 0
  rw [reverseSpaceEquiv_symm_single]
  rw [RightExtension.spaceProjection_single_of_not_exists]
  · simp
  · rintro ⟨q, hq⟩
    apply hj
    let i : C.PositionAt x := unreversePosition C q
    refine ⟨i, ?_⟩
    change reversePosition extension.reverseResult
        (extension.extension.toRightExtension.position
          (reversePosition C i)) = j
    rw [← (reversePositionEquiv extension.reverseResult x).right_inv j]
    change reversePosition extension.reverseResult
        (extension.extension.toRightExtension.position
          (reversePosition C i)) =
      reversePosition extension.reverseResult
        (unreversePosition extension.reverseResult j)
    apply congrArg (reversePosition extension.reverseResult)
    have hi : reversePosition C i = q :=
      (reversePositionEquiv C x).right_inv q
    rw [hi, hq]

/-- Projection reads the coefficient at the corresponding inherited
position. -/
@[simp]
theorem spaceProjection_apply_position {C : Word R}
    (extension : LeftNegativeBoundaryExtension C) {x : Q}
    (v : extension.result.Space x) (i : C.PositionAt x) :
    extension.spaceProjection x v i = v (extension.position i) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single j c =>
      classical
      by_cases hj : ∃ q : C.PositionAt x, extension.position q = j
      · rcases hj with ⟨q, rfl⟩
        rw [spaceProjection_single_position]
        simp only [Finsupp.single_apply]
        rw [extension.position_injective.eq_iff]
      · rw [extension.spaceProjection_single_of_not_exists j c hj]
        simp only [Finsupp.zero_apply, Finsupp.single_apply]
        exact (if_neg (fun hji : j = extension.position i ↦
          hj ⟨i, hji.symm⟩)).symm

end LeftNegativeBoundaryExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
