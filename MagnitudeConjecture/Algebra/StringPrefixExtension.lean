import MagnitudeConjecture.Algebra.StringExtensionArm

/-!
# Prefix extensions of string words

A right prefix extension records an arbitrary finite sequence of letters
appended to a string word.  It retains the canonical embedding of old word
positions and the split coordinate inclusion/projection on every displayed
vertex space.  The first appended letter is recorded separately when its
sign controls whether the old coordinates form a subrepresentation or a
quotient representation.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- Bundle an already certified string path as a word. -/
def ofStringPath {source target : Q}
    (path : SignedPath source target) (h : IsString R path) : Word R where
  source := source
  target := target
  path := path
  isString := h

@[simp]
theorem ofStringPath_word_path (C : Word R) :
    ofStringPath C.path C.isString = C := by
  apply Word.ext <;> simp [ofStringPath]

/-- An arbitrary finite sequence of letters appended at the right endpoint
of `C`. -/
inductive RightExtension (C : Word R) : Word R → Type u
  | base : RightExtension C C
  | step {D : Word R} (extension : RightExtension C D) {z : Q}
      (e : SignedArrow D.target z)
      (h : IsString R (D.path.comp e.toPath)) :
      RightExtension C (append R D e h)

namespace RightExtension

/-- Number of appended letters. -/
def steps {C D : Word R} : RightExtension C D → ℕ
  | .base => 0
  | .step extension _ _ => extension.steps + 1

/-- The signed suffix appended by a right extension. -/
def suffixPath {C D : Word R} :
    RightExtension C D → SignedPath C.target D.target
  | .base => Quiver.Path.nil
  | .step extension e _ => extension.suffixPath.comp e.toPath

/-- A right extension does not change the source vertex. -/
theorem source_eq {C D : Word R} (extension : RightExtension C D) :
    D.source = C.source := by
  induction extension with
  | base => rfl
  | step extension e h ih => exact ih

/-- The final path is the original path followed by the recorded suffix.
The source cast is necessary because source preservation is propositional for
an indexed extension record. -/
theorem path_cast_comp_suffixPath {C D : Word R}
    (extension : RightExtension C D) :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) D.source D.target C.source D.target
      extension.source_eq rfl D.path) =
      C.path.comp extension.suffixPath := by
  induction extension with
  | base => rfl
  | @step D extension z e h ih =>
      simp only [append_path, suffixPath,
        Quiver.Path.comp_toPath_eq_cons]
      have hcastCons :
          (@Quiver.Path.cast (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q) _ _ _ _
            extension.source_eq rfl (D.path.cons e)) =
          (@Quiver.Path.cast (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q) _ _ _ _
            extension.source_eq rfl D.path).cons e := by
        exact Quiver.Path.cast_cons D.path e
          extension.source_eq rfl
      calc
        _ = (@Quiver.Path.cast (Quiver.Symmetrify Q)
              (Quiver.symmetrifyQuiver Q) _ _ _ _
              extension.source_eq rfl D.path).cons e := hcastCons
        _ = (C.path.comp extension.suffixPath).cons e := by rw [ih]
        _ = C.path.comp (extension.suffixPath.comp e.toPath) := by rfl

/-- The explicit original-path-plus-suffix factorization is itself a string. -/
theorem comp_suffixPath_isString {C D : Word R}
    (extension : RightExtension C D) :
    IsString R (C.path.comp extension.suffixPath) := by
  rw [← extension.path_cast_comp_suffixPath]
  exact (isString_cast R extension.source_eq rfl D.path).2 D.isString

/-- Replaying an extension suffix after a different path with the same final
vertex. -/
structure RebaseResult {C D : Word R}
    (extension : RightExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : RightExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp extension.suffixPath

/-- Replay a right extension after a different certified prefix.  It is
enough to know that the path with the complete replayed suffix is a string;
all intermediate validity proofs follow by contiguous-subpath heredity. -/
def rebase {C D : Word R}
    (extension : RightExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R (basePath.comp extension.suffixPath)) :
    RebaseResult extension basePath hbase := by
  induction extension with
  | base =>
      exact {
        result := ofStringPath basePath hbase
        rebased := .base
        source_eq := rfl
        target_eq := rfl
        path_cast_eq := rfl }
  | @step D extension z e h ih =>
      have hprefix : IsString R
          (basePath.comp extension.suffixPath) := by
        apply IsString.of_contiguousSubpath R hfull
        refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
        simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc,
          suffixPath]
      let previous := ih hprefix
      let castArrow : SignedArrow previous.result.target z :=
        @Quiver.Hom.cast (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) D.target z
          previous.result.target z previous.target_eq.symm rfl e
      have hcastValid : IsString R
          ((@Quiver.Path.cast (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q)
            previous.result.source previous.result.target source D.target
            previous.source_eq previous.target_eq previous.result.path).comp
            e.toPath) := by
        rw [previous.path_cast_eq]
        simpa only [Quiver.Path.comp_assoc, suffixPath,
          append_target] using hfull
      have hvalid : IsString R
          (previous.result.path.comp castArrow.toPath) :=
        isString_comp_cast_toPath R previous.result.path e
          previous.source_eq previous.target_eq hcastValid
      exact {
        result := append R previous.result castArrow hvalid
        rebased := .step previous.rebased castArrow hvalid
        source_eq := previous.source_eq
        target_eq := rfl
        path_cast_eq := by
          change
            (@Quiver.Path.cast (Quiver.Symmetrify Q)
              (Quiver.symmetrifyQuiver Q)
              previous.result.source z source z
              previous.source_eq rfl
              (previous.result.path.comp castArrow.toPath)) =
              basePath.comp (extension.suffixPath.comp e.toPath)
          rw [path_cast_comp_cast_toPath previous.result.path e
            previous.source_eq previous.target_eq,
            previous.path_cast_eq, Quiver.Path.comp_assoc] }

@[simp]
theorem rebase_steps {C D : Word R}
    (extension : RightExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R (basePath.comp extension.suffixPath)) :
    (extension.rebase basePath hbase hfull).rebased.steps =
      extension.steps := by
  induction extension with
  | base => rfl
  | step extension e h ih =>
      simp only [rebase, steps]
      exact congrArg (fun n ↦ n + 1) (ih _)

@[simp]
theorem suffixPath_length {C D : Word R}
    (extension : RightExtension C D) :
    extension.suffixPath.length = extension.steps := by
  induction extension with
  | base => rfl
  | step extension e h ih =>
      simp [suffixPath, steps, ih]

/-- The final word is longer by exactly the number of appended letters. -/
@[simp]
theorem result_length {C D : Word R} (extension : RightExtension C D) :
    D.length = C.length + extension.steps := by
  induction extension with
  | base => rfl
  | step extension e h ih => simp [steps, ih, Nat.add_assoc]

/-- Concatenate two right extensions. -/
def trans {C D E : Word R}
    (first : RightExtension C D) (second : RightExtension D E) :
    RightExtension C E :=
  match second with
  | .base => first
  | .step extension e h => .step (first.trans extension) e h

@[simp]
theorem base_trans {C D : Word R} (extension : RightExtension C D) :
    (RightExtension.base : RightExtension C C).trans extension = extension := by
  induction extension with
  | base => rfl
  | step extension e h ih => simp only [trans, ih]

@[simp]
theorem trans_base {C D : Word R} (extension : RightExtension C D) :
    extension.trans RightExtension.base = extension :=
  rfl

@[simp]
theorem steps_trans {C D E : Word R}
    (first : RightExtension C D) (second : RightExtension D E) :
    (first.trans second).steps = first.steps + second.steps := by
  induction second with
  | base => simp [trans, steps]
  | step extension e h ih => simp [trans, steps, ih, Nat.add_assoc]

@[simp]
theorem suffixPath_trans {C D E : Word R}
    (first : RightExtension C D) (second : RightExtension D E) :
    (first.trans second).suffixPath =
      first.suffixPath.comp second.suffixPath := by
  induction second with
  | base => simp [trans, suffixPath]
  | step second e h ih => simp [trans, suffixPath, ih]

/-- Concatenation of right extensions is associative as dependent extension
data. -/
theorem trans_assoc {B C D E : Word R}
    (first : RightExtension B C) (second : RightExtension C D)
    (third : RightExtension D E) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  induction third with
  | base => rfl
  | step third e h ih => simp only [trans, ih]

/-- Embed every old prefix position into the extended word. -/
def position {C D : Word R} (extension : RightExtension C D) {x : Q}
    (i : C.PositionAt x) : D.PositionAt x := by
  induction extension with
  | base => exact i
  | step extension e h ih =>
      exact appendPosition _ e h ih

@[simp]
theorem position_index {C D : Word R} (extension : RightExtension C D)
    {x : Q} (i : C.PositionAt x) :
    (extension.position i).index = i.index := by
  induction extension with
  | base => rfl
  | step extension e h ih =>
      exact (appendPosition_index _ e h _).trans ih

@[simp]
theorem position_trans {C D E : Word R}
    (first : RightExtension C D) (second : RightExtension D E)
    {x : Q} (i : C.PositionAt x) :
    (first.trans second).position i =
      second.position (first.position i) := by
  induction second with
  | base => rfl
  | step extension e h ih =>
      change appendPosition _ e h
          ((first.trans extension).position i) =
        appendPosition _ e h (extension.position (first.position i))
      rw [ih]

/-- The old-position embedding is injective. -/
theorem position_injective {C D : Word R}
    (extension : RightExtension C D) {x : Q} :
    Function.Injective (extension.position : C.PositionAt x → D.PositionAt x) := by
  intro i j hij
  apply PositionAt.ext_index
  simpa only [position_index] using congrArg PositionAt.index hij

/-- Transporting the source word of an extension does not change its number
of appended letters. -/
theorem steps_transport_source {C C' D : Word R}
    (h : C = C') (extension : RightExtension C D) :
    (Eq.mp (congrArg (fun W : Word R ↦ RightExtension W D) h)
      extension).steps = extension.steps := by
  cases h
  rfl

/-- Every arrow step between old positions remains an arrow step after an
arbitrary right extension. -/
theorem arrowStep_position {C D : Word R}
    (extension : RightExtension C D) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    D.ArrowStep a (extension.position i) (extension.position j) := by
  induction extension with
  | base => exact hij
  | step extension e h ih =>
      exact arrowStep_appendPosition _ e h a _ _ ih

/-- Appending further letters neither creates nor removes an arrow step
between two inherited positions. -/
theorem arrowStep_position_iff {C D : Word R}
    (extension : RightExtension C D) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y) :
    D.ArrowStep a (extension.position i) (extension.position j) ↔
      C.ArrowStep a i j := by
  induction extension with
  | base => rfl
  | step extension e h ih => exact ih

/-- Every position in the extended word at or before the old final index is
the image of a unique old position. -/
theorem exists_eq_position_of_index_le {C D : Word R}
    (extension : RightExtension C D) {x : Q} (j : D.PositionAt x)
    (hj : j.index ≤ C.length) :
    ∃ i : C.PositionAt x, extension.position i = j := by
  induction extension with
  | base => exact ⟨j, rfl⟩
  | @step D extension z e h ih =>
      have hCD : C.length ≤ D.length := by
        rw [extension.result_length]
        omega
      rcases exists_eq_appendPosition_of_index_le D e h j
          (hj.trans hCD) with ⟨jD, hjD⟩
      have hjDle : jD.index ≤ C.length := by
        rw [← appendPosition_index D e h jD, hjD]
        exact hj
      rcases ih jD hjDle with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      change appendPosition D e h (extension.position i) = j
      rw [hi, hjD]

/-- Coordinate inclusion of the old position basis into an arbitrary right
extension. -/
def spaceInclusion {C D : Word R} (extension : RightExtension C D)
    (x : Q) : C.Space x →ₗ[k] D.Space x :=
  Finsupp.lmapDomain k k extension.position

/-- Coordinate projection from an arbitrary extension onto its old position
basis. -/
def spaceProjection {C D : Word R} (extension : RightExtension C D)
    (x : Q) : D.Space x →ₗ[k] C.Space x :=
  Finsupp.linearCombination k fun j ↦ by
    classical
    exact if hex : ∃ i : C.PositionAt x, extension.position i = j then
        Finsupp.single (Classical.choose hex) 1
      else
        0

@[simp]
theorem spaceInclusion_single {C D : Word R}
    (extension : RightExtension C D) {x : Q}
    (i : C.PositionAt x) (c : k) :
    extension.spaceInclusion x (Finsupp.single i c) =
      Finsupp.single (extension.position i) c := by
  exact Finsupp.mapDomain_single

@[simp]
theorem spaceProjection_single_position {C D : Word R}
    (extension : RightExtension C D) {x : Q}
    (i : C.PositionAt x) (c : k) :
    extension.spaceProjection x
        (Finsupp.single (extension.position i) c) =
      Finsupp.single i c := by
  classical
  rw [spaceProjection, Finsupp.linearCombination_single]
  let hex : ∃ j : C.PositionAt x,
      extension.position j = extension.position i := ⟨i, rfl⟩
  rw [dif_pos hex]
  have hchosen : Classical.choose hex = i := by
    apply extension.position_injective
    exact Classical.choose_spec hex
  rw [hchosen]
  exact Finsupp.smul_single_one i c

/-- Coordinate projection kills a basis position not inherited from the old
word. -/
theorem spaceProjection_single_of_not_exists {C D : Word R}
    (extension : RightExtension C D) {x : Q} (j : D.PositionAt x)
    (c : k) (hj : ¬ ∃ i : C.PositionAt x, extension.position i = j) :
    extension.spaceProjection x (Finsupp.single j c) = 0 := by
  rw [spaceProjection, Finsupp.linearCombination_single, dif_neg hj,
    smul_zero]

/-- Projection is a left inverse to inclusion on every vertex space. -/
theorem spaceProjection_inclusion {C D : Word R}
    (extension : RightExtension C D) (x : Q) (v : C.Space x) :
    extension.spaceProjection x (extension.spaceInclusion x v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c => rw [spaceInclusion_single, spaceProjection_single_position]

/-- Projection reads the coefficient at the corresponding inherited
position. -/
@[simp]
theorem spaceProjection_apply_position {C D : Word R}
    (extension : RightExtension C D) {x : Q}
    (v : D.Space x) (i : C.PositionAt x) :
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

/-- Inclusion preserves the coefficient at every inherited position. -/
@[simp]
theorem spaceInclusion_apply_position {C D : Word R}
    (extension : RightExtension C D) {x : Q}
    (v : C.Space x) (i : C.PositionAt x) :
    extension.spaceInclusion x v (extension.position i) = v i := by
  change Finsupp.mapDomain extension.position v (extension.position i) = v i
  rw [Finsupp.mapDomain_apply extension.position_injective]

/-- Inclusion has zero coefficient at every non-inherited position. -/
theorem spaceInclusion_apply_of_not_exists {C D : Word R}
    (extension : RightExtension C D) {x : Q}
    (v : C.Space x) (j : D.PositionAt x)
    (hj : ¬ ∃ i : C.PositionAt x, extension.position i = j) :
    extension.spaceInclusion x v j = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single i c =>
      rw [spaceInclusion_single]
      have hne : extension.position i ≠ j := fun h ↦ hj ⟨i, h⟩
      rw [Finsupp.single_apply]
      exact if_neg hne

/-- Coordinate inclusion along a right extension is injective. -/
theorem spaceInclusion_injective {C D : Word R}
    (extension : RightExtension C D) (x : Q) :
    Function.Injective (extension.spaceInclusion x) :=
  Function.LeftInverse.injective
    (fun v ↦ extension.spaceProjection_inclusion x v)

/-- Coordinate projection along a right extension is surjective. -/
theorem spaceProjection_surjective {C D : Word R}
    (extension : RightExtension C D) (x : Q) :
    Function.Surjective (extension.spaceProjection x) :=
  Function.LeftInverse.surjective
    (fun v ↦ extension.spaceProjection_inclusion x v)

/-- Coordinate inclusions compose when right extensions are concatenated. -/
theorem spaceInclusion_trans_apply {C D E : Word R}
    (first : RightExtension C D) (second : RightExtension D E)
    (x : Q) (v : C.Space x) :
    (first.trans second).spaceInclusion x v =
      second.spaceInclusion x (first.spaceInclusion x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      rw [spaceInclusion_single, spaceInclusion_single,
        spaceInclusion_single, position_trans]

/-- Coordinate projections compose in the reverse order when right
extensions are concatenated. -/
theorem spaceProjection_trans_apply {C D E : Word R}
    (first : RightExtension C D) (second : RightExtension D E)
    (x : Q) (v : E.Space x) :
    (first.trans second).spaceProjection x v =
      first.spaceProjection x (second.spaceProjection x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single j c =>
      classical
      by_cases hsecond : ∃ q : D.PositionAt x, second.position q = j
      · rcases hsecond with ⟨q, rfl⟩
        rw [second.spaceProjection_single_position]
        by_cases hfirst : ∃ i : C.PositionAt x, first.position i = q
        · rcases hfirst with ⟨i, rfl⟩
          rw [← position_trans first second i,
            (first.trans second).spaceProjection_single_position,
            first.spaceProjection_single_position]
        · rw [first.spaceProjection_single_of_not_exists _ _ hfirst,
            (first.trans second).spaceProjection_single_of_not_exists]
          rintro ⟨i, hi⟩
          apply hfirst
          refine ⟨i, second.position_injective ?_⟩
          simpa only [position_trans] using hi
      · rw [second.spaceProjection_single_of_not_exists _ _ hsecond,
          map_zero,
          (first.trans second).spaceProjection_single_of_not_exists]
        rintro ⟨i, hi⟩
        apply hsecond
        exact ⟨first.position i, by simpa only [position_trans] using hi⟩

end RightExtension

namespace NegativeExtension

/-- Forget that every letter of a negative arm has the same sign. -/
def toRightExtension {C D : Word R}
    (arm : NegativeExtension C D) : RightExtension C D :=
  match arm with
  | .base => .base
  | .step arm a h => .step arm.toRightExtension (negativeArrow a) h

@[simp]
theorem toRightExtension_steps {C D : Word R}
    (arm : NegativeExtension C D) :
    arm.toRightExtension.steps = arm.steps := by
  induction arm with
  | base => rfl
  | step arm a h ih => simp [toRightExtension, RightExtension.steps, steps, ih]

end NegativeExtension

namespace PositiveExtension

/-- Forget that every letter of a positive arm has the same sign. -/
def toRightExtension {C D : Word R}
    (arm : PositiveExtension C D) : RightExtension C D :=
  match arm with
  | .base => .base
  | .step arm a h => .step arm.toRightExtension (positiveArrow a) h

@[simp]
theorem toRightExtension_steps {C D : Word R}
    (arm : PositiveExtension C D) :
    arm.toRightExtension.steps = arm.steps := by
  induction arm with
  | base => rfl
  | step arm a h ih => simp [toRightExtension, RightExtension.steps, steps, ih]

/-- Forgetting positivity retains exactly the positive signed path associated
to the ordinary displayed-quiver arm. -/
theorem toRightExtension_suffixPath_eq_positivePath {C D : Word R}
    (arm : PositiveExtension C D) :
    arm.toRightExtension.suffixPath = positivePath arm.ordinaryPath := by
  induction arm with
  | base => rfl
  | step arm a h ih =>
      simp only [toRightExtension, RightExtension.suffixPath,
        ordinaryPath, positivePath_comp, ih]
      exact congrArg (fun p ↦ (positivePath arm.ordinaryPath).comp p)
        (positivePath_toPath (Q := Q) a).symm

end PositiveExtension

/-- A nonempty right extension whose first appended letter is negative.  Its
remaining tail may contain arbitrary signs. -/
structure NegativeBoundaryExtension (C D : Word R) where
  vertex : Q
  arrow : vertex ⟶ C.target
  valid : IsString R (C.path.comp (negativeArrow arrow).toPath)
  tail : RightExtension (append R C (negativeArrow arrow) valid) D

namespace NegativeBoundaryExtension

/-- Forget the marked first negative letter. -/
def toRightExtension {C D : Word R}
    (extension : NegativeBoundaryExtension C D) : RightExtension C D :=
  (RightExtension.step RightExtension.base
      (negativeArrow extension.arrow) extension.valid).trans extension.tail

@[simp]
theorem toRightExtension_position {C D : Word R}
    (extension : NegativeBoundaryExtension C D) {x : Q}
    (i : C.PositionAt x) :
    extension.toRightExtension.position i =
      extension.tail.position
        (appendPosition C (negativeArrow extension.arrow)
          extension.valid i) := by
  rw [toRightExtension, RightExtension.position_trans]
  rfl

/-- The first position created by a negative-boundary extension, retained
through its arbitrary tail. -/
def firstNewPosition {C D : Word R}
    (extension : NegativeBoundaryExtension C D) :
    D.PositionAt extension.vertex :=
  extension.tail.position
    (appendEndPosition C (negativeArrow extension.arrow) extension.valid)

@[simp]
theorem firstNewPosition_index {C D : Word R}
    (extension : NegativeBoundaryExtension C D) :
    extension.firstNewPosition.index = C.length + 1 := by
  rw [firstNewPosition, RightExtension.position_index,
    appendEndPosition_index]

/-- The first negative boundary letter is an ordinary arrow from the new
position into the inherited old endpoint. -/
theorem arrowStep_firstNewPosition {C D : Word R}
    (extension : NegativeBoundaryExtension C D) :
    D.ArrowStep extension.arrow extension.firstNewPosition
      (extension.toRightExtension.position C.targetPosition) := by
  rw [extension.toRightExtension_position]
  apply extension.tail.arrowStep_position
  exact Or.inr rfl

@[simp]
theorem toRightExtension_steps {C D : Word R}
    (extension : NegativeBoundaryExtension C D) :
    extension.toRightExtension.steps = extension.tail.steps + 1 := by
  simp [toRightExtension, RightExtension.steps, Nat.add_comm]

/-- Transporting the source word of a negative-boundary extension preserves
its total step count. -/
theorem toRightExtension_steps_transport_source {C C' D : Word R}
    (h : C = C') (extension : NegativeBoundaryExtension C D) :
    (Eq.mp
      (congrArg (fun W : Word R ↦ NegativeBoundaryExtension W D) h)
      extension).toRightExtension.steps =
      extension.toRightExtension.steps := by
  cases h
  rfl

@[simp]
theorem toRightExtension_suffixPath {C D : Word R}
    (extension : NegativeBoundaryExtension C D) :
    extension.toRightExtension.suffixPath =
      (negativeArrow extension.arrow).toPath.comp
        extension.tail.suffixPath := by
  simp [toRightExtension, RightExtension.suffixPath]
  rfl

@[simp]
theorem result_length {C D : Word R}
    (extension : NegativeBoundaryExtension C D) :
    D.length = C.length + extension.tail.steps + 1 := by
  rw [extension.toRightExtension.result_length,
    extension.toRightExtension_steps, Nat.add_assoc, Nat.add_comm _ 1,
    ← Nat.add_assoc]

/-- Appending any further right extension preserves the marked negative
boundary letter. -/
def transRightExtension {C D E : Word R}
    (extension : NegativeBoundaryExtension C D)
    (further : RightExtension D E) : NegativeBoundaryExtension C E where
  vertex := extension.vertex
  arrow := extension.arrow
  valid := extension.valid
  tail := extension.tail.trans further

@[simp]
theorem toRightExtension_transRightExtension {C D E : Word R}
    (extension : NegativeBoundaryExtension C D)
    (further : RightExtension D E) :
    (extension.transRightExtension further).toRightExtension =
      extension.toRightExtension.trans further := by
  exact (RightExtension.trans_assoc _ _ _).symm

/-- Replaying a negative-boundary extension after another certified base
path, while retaining its distinguished first negative arrow. -/
structure RebaseResult {C D : Word R}
    (extension : NegativeBoundaryExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : NegativeBoundaryExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp extension.toRightExtension.suffixPath

/-- Construct the negative-boundary replay. -/
def rebase {C D : Word R}
    (extension : NegativeBoundaryExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp extension.toRightExtension.suffixPath)) :
    RebaseResult extension basePath hbase := by
  have hvalid : IsString R
      (basePath.comp (negativeArrow extension.arrow).toPath) := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil, extension.tail.suffixPath, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc,
      toRightExtension_suffixPath]
  let baseWord : Word R := ofStringPath basePath hbase
  let firstWord : Word R :=
    append R baseWord (negativeArrow extension.arrow) hvalid
  have htailFull : IsString R
      (firstWord.path.comp extension.tail.suffixPath) := by
    change IsString R
      ((basePath.comp (negativeArrow extension.arrow).toPath).comp
        extension.tail.suffixPath)
    simpa only [Quiver.Path.comp_assoc, toRightExtension_suffixPath] using hfull
  let tailReplay := extension.tail.rebase
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : RightExtension firstWord tailReplay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ RightExtension W tailReplay.result)
        hreplayBase)
      tailReplay.rebased
  let rebased : NegativeBoundaryExtension baseWord tailReplay.result := {
    vertex := extension.vertex
    arrow := extension.arrow
    valid := hvalid
    tail := replayTail }
  exact {
    result := tailReplay.result
    rebased := rebased
    source_eq := tailReplay.source_eq
    target_eq := tailReplay.target_eq
    path_cast_eq := by
      calc
        _ = firstWord.path.comp extension.tail.suffixPath :=
          tailReplay.path_cast_eq
        _ = (basePath.comp (negativeArrow extension.arrow).toPath).comp
            extension.tail.suffixPath := rfl
        _ = basePath.comp extension.toRightExtension.suffixPath := by
          simp only [toRightExtension_suffixPath, Quiver.Path.comp_assoc] }

/-- Replaying a negative-boundary extension preserves its total number of
letters. -/
@[simp]
theorem rebase_steps {C D : Word R}
    (extension : NegativeBoundaryExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp extension.toRightExtension.suffixPath)) :
    (extension.rebase basePath hbase hfull).rebased.toRightExtension.steps =
      extension.toRightExtension.steps := by
  let replay := extension.rebase basePath hbase hfull
  change replay.rebased.toRightExtension.steps =
    extension.toRightExtension.steps
  have hresult := replay.rebased.toRightExtension.result_length
  have hpath := congrArg Quiver.Path.length replay.path_cast_eq
  have hsuffix := extension.toRightExtension.suffixPath_length
  change replay.result.length =
      basePath.length + replay.rebased.toRightExtension.steps at hresult
  simp only [path_cast_length, Quiver.Path.length_comp] at hpath
  change replay.result.length =
      basePath.length + extension.toRightExtension.suffixPath.length at hpath
  rw [hsuffix] at hpath
  omega

end NegativeBoundaryExtension

/-- A nonempty right extension whose first appended letter is positive.  Its
remaining tail may contain arbitrary signs. -/
structure PositiveBoundaryExtension (C D : Word R) where
  vertex : Q
  arrow : C.target ⟶ vertex
  valid : IsString R (C.path.comp (positiveArrow arrow).toPath)
  tail : RightExtension (append R C (positiveArrow arrow) valid) D

namespace PositiveBoundaryExtension

/-- Forget the marked first positive letter. -/
def toRightExtension {C D : Word R}
    (extension : PositiveBoundaryExtension C D) : RightExtension C D :=
  (RightExtension.step RightExtension.base
      (positiveArrow extension.arrow) extension.valid).trans extension.tail

@[simp]
theorem toRightExtension_position {C D : Word R}
    (extension : PositiveBoundaryExtension C D) {x : Q}
    (i : C.PositionAt x) :
    extension.toRightExtension.position i =
      extension.tail.position
        (appendPosition C (positiveArrow extension.arrow)
          extension.valid i) := by
  rw [toRightExtension, RightExtension.position_trans]
  rfl

/-- The first position created by a positive-boundary extension, retained
through its arbitrary tail. -/
def firstNewPosition {C D : Word R}
    (extension : PositiveBoundaryExtension C D) :
    D.PositionAt extension.vertex :=
  extension.tail.position
    (appendEndPosition C (positiveArrow extension.arrow) extension.valid)

@[simp]
theorem firstNewPosition_index {C D : Word R}
    (extension : PositiveBoundaryExtension C D) :
    extension.firstNewPosition.index = C.length + 1 := by
  rw [firstNewPosition, RightExtension.position_index,
    appendEndPosition_index]

/-- The first positive boundary letter is an ordinary arrow from the
inherited old endpoint to the new position. -/
theorem arrowStep_firstNewPosition {C D : Word R}
    (extension : PositiveBoundaryExtension C D) :
    D.ArrowStep extension.arrow
      (extension.toRightExtension.position C.targetPosition)
      extension.firstNewPosition := by
  rw [extension.toRightExtension_position]
  apply extension.tail.arrowStep_position
  exact Or.inl rfl

@[simp]
theorem toRightExtension_steps {C D : Word R}
    (extension : PositiveBoundaryExtension C D) :
    extension.toRightExtension.steps = extension.tail.steps + 1 := by
  simp [toRightExtension, RightExtension.steps, Nat.add_comm]

/-- Transporting the source word of a positive-boundary extension preserves
its total step count. -/
theorem toRightExtension_steps_transport_source {C C' D : Word R}
    (h : C = C') (extension : PositiveBoundaryExtension C D) :
    (Eq.mp
      (congrArg (fun W : Word R ↦ PositiveBoundaryExtension W D) h)
      extension).toRightExtension.steps =
      extension.toRightExtension.steps := by
  cases h
  rfl

@[simp]
theorem toRightExtension_suffixPath {C D : Word R}
    (extension : PositiveBoundaryExtension C D) :
    extension.toRightExtension.suffixPath =
      (positiveArrow extension.arrow).toPath.comp
        extension.tail.suffixPath := by
  simp [toRightExtension, RightExtension.suffixPath]
  rfl

@[simp]
theorem result_length {C D : Word R}
    (extension : PositiveBoundaryExtension C D) :
    D.length = C.length + extension.tail.steps + 1 := by
  rw [extension.toRightExtension.result_length,
    extension.toRightExtension_steps, Nat.add_assoc, Nat.add_comm _ 1,
    ← Nat.add_assoc]

/-- Appending any further right extension preserves the marked positive
boundary letter. -/
def transRightExtension {C D E : Word R}
    (extension : PositiveBoundaryExtension C D)
    (further : RightExtension D E) : PositiveBoundaryExtension C E where
  vertex := extension.vertex
  arrow := extension.arrow
  valid := extension.valid
  tail := extension.tail.trans further

@[simp]
theorem toRightExtension_transRightExtension {C D E : Word R}
    (extension : PositiveBoundaryExtension C D)
    (further : RightExtension D E) :
    (extension.transRightExtension further).toRightExtension =
      extension.toRightExtension.trans further := by
  exact (RightExtension.trans_assoc _ _ _).symm

/-- Replaying a positive-boundary extension after another certified base
path, while retaining its distinguished first positive arrow. -/
structure RebaseResult {C D : Word R}
    (extension : PositiveBoundaryExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : PositiveBoundaryExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp extension.toRightExtension.suffixPath

/-- Construct the positive-boundary replay.  Validity of the complete
replayed path supplies validity of the first arrow and every later tail
prefix by contiguous-subpath heredity. -/
def rebase {C D : Word R}
    (extension : PositiveBoundaryExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp extension.toRightExtension.suffixPath)) :
    RebaseResult extension basePath hbase := by
  have hvalid : IsString R
      (basePath.comp (positiveArrow extension.arrow).toPath) := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil, extension.tail.suffixPath, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc,
      toRightExtension_suffixPath]
  let baseWord : Word R := ofStringPath basePath hbase
  let firstWord : Word R :=
    append R baseWord (positiveArrow extension.arrow) hvalid
  have htailFull : IsString R
      (firstWord.path.comp extension.tail.suffixPath) := by
    change IsString R
      ((basePath.comp (positiveArrow extension.arrow).toPath).comp
        extension.tail.suffixPath)
    simpa only [Quiver.Path.comp_assoc, toRightExtension_suffixPath] using hfull
  let tailReplay := extension.tail.rebase
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : RightExtension firstWord tailReplay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ RightExtension W tailReplay.result)
        hreplayBase)
      tailReplay.rebased
  let rebased : PositiveBoundaryExtension baseWord tailReplay.result := {
    vertex := extension.vertex
    arrow := extension.arrow
    valid := hvalid
    tail := replayTail }
  exact {
    result := tailReplay.result
    rebased := rebased
    source_eq := tailReplay.source_eq
    target_eq := tailReplay.target_eq
    path_cast_eq := by
      calc
        _ = firstWord.path.comp extension.tail.suffixPath :=
          tailReplay.path_cast_eq
        _ = (basePath.comp (positiveArrow extension.arrow).toPath).comp
            extension.tail.suffixPath := rfl
        _ = basePath.comp extension.toRightExtension.suffixPath := by
          simp only [toRightExtension_suffixPath, Quiver.Path.comp_assoc] }

/-- Replaying a positive-boundary extension preserves its total number of
letters. -/
@[simp]
theorem rebase_steps {C D : Word R}
    (extension : PositiveBoundaryExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp extension.toRightExtension.suffixPath)) :
    (extension.rebase basePath hbase hfull).rebased.toRightExtension.steps =
      extension.toRightExtension.steps := by
  let replay := extension.rebase basePath hbase hfull
  change replay.rebased.toRightExtension.steps =
    extension.toRightExtension.steps
  have hresult := replay.rebased.toRightExtension.result_length
  have hpath := congrArg Quiver.Path.length replay.path_cast_eq
  have hsuffix := extension.toRightExtension.suffixPath_length
  change replay.result.length =
      basePath.length + replay.rebased.toRightExtension.steps at hresult
  simp only [path_cast_length, Quiver.Path.length_comp] at hpath
  change replay.result.length =
      basePath.length + extension.toRightExtension.suffixPath.length at hpath
  rw [hsuffix] at hpath
  omega

end PositiveBoundaryExtension

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
