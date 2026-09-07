import MagnitudeConjecture.Algebra.StringEndpointDeterminism
import MagnitudeConjecture.Algebra.StringHookCohookReplay
import MagnitudeConjecture.Algebra.StringPositivePath

/-!
# The canonical kernel word of a displayed hook arrow

The negative tail after a positive hook boundary is independent of the word
before that boundary.  More precisely, its positive reversal is determined
by the displayed central arrow.  The proof splits a nonempty tail at the
arrow adjacent to the center: the degree-two condition determines that
arrow, and special-biserial continuation uniqueness determines the remaining
path at each fixed length.  Replaying a hook onto the trivial source word
shows that maximal tails have the same length.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {R : RelationFamily k Q}

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
@[simp]
theorem NegativeExtension.suffixPath_reverse_eq_positivePath_ordinaryPath
    {C D : Word R} (arm : NegativeExtension C D) :
    arm.toRightExtension.suffixPath.reverse =
      positivePath arm.ordinaryPath := by
  induction arm with
  | base => rfl
  | step arm a h ih =>
      change
        (arm.toRightExtension.suffixPath.comp
          (negativeArrow a).toPath).reverse =
        positivePath (a.toPath.comp arm.ordinaryPath)
      rw [Quiver.Path.reverse_comp, ih, positivePath_comp]
      change
        (positiveArrow a).toPath.comp
            (positivePath arm.ordinaryPath) =
          (positivePath a.toPath).comp (positivePath arm.ordinaryPath)
      rw [positivePath_toPath (Q := Q)]

/-- The first arrow adjacent to the base of a nonempty negative extension,
together with the path before it. -/
structure NegativeExtension.FirstArrowData
    {C D : Word R} (arm : NegativeExtension C D) where
  vertex : Q
  arrow : vertex ⟶ C.target
  initialPath : Quiver.Path D.target vertex
  path_eq : arm.ordinaryPath = initialPath.comp arrow.toPath
  initialPath_length : initialPath.length + 1 = arm.steps
  first_valid : IsString R
    (C.path.comp (negativeArrow arrow).toPath)

/-- Extract the boundary-adjacent arrow of a nonempty negative extension. -/
def NegativeExtension.firstArrowData
    {C D : Word R} (arm : NegativeExtension C D)
    (hpos : 0 < arm.steps) : arm.FirstArrowData := by
  induction arm with
  | base => simp [NegativeExtension.steps] at hpos
  | @step E arm z a h ih =>
      cases arm with
      | base =>
        exact {
          vertex := z
          arrow := a
          initialPath := Quiver.Path.nil
          path_eq := rfl
          initialPath_length := by simp [NegativeExtension.steps]
          first_valid := h }
      | @step F inner w b hb =>
        let first := ih (by simp [NegativeExtension.steps])
        exact {
          vertex := first.vertex
          arrow := first.arrow
          initialPath := a.toPath.comp first.initialPath
          path_eq := by
            change a.toPath.comp (inner.step b hb).ordinaryPath = _
            rw [first.path_eq]
            exact (Quiver.Path.comp_assoc _ _ _).symm
          initialPath_length := by
            have hlen : (a.toPath.comp first.initialPath).length =
                1 + first.initialPath.length := by simp
            calc
              (a.toPath.comp first.initialPath).length + 1 =
                  (1 + first.initialPath.length) + 1 :=
                congrArg (fun n ↦ n + 1) hlen
              _ = (inner.step b hb).steps + 1 := by
                rw [← first.initialPath_length]
                omega
              _ = ((inner.step b hb).step a h).steps := rfl
          first_valid := first.first_valid }

/-- Read the ordinary path of a negative extension as a positive string
word. -/
def NegativeExtension.positiveWord
    (hR : IsAdmissible R) {C D : Word R}
    (arm : NegativeExtension C D) : Word R :=
  ofStringPath (positivePath arm.ordinaryPath)
    (isString_positivePath_of_pathMap_ne_zero hR arm.ordinaryPath
      arm.pathMap_ordinaryPath_ne_zero)

/-- Two equal-length negative tails after the same displayed positive arrow
have the same positive word, even when the preceding base word differs.  It
is enough here to compare an arbitrary base with the trivial base used for
the canonical hook. -/
theorem NegativeExtension.positiveWord_eq_of_vertexBoundary_steps_eq
    (P : SpecialBiserialPresentation k A Q)
    (C : Word P.toPresentation.relations)
    {z : Q} (a : C.target ⟶ z)
    (ha : IsString P.toPresentation.relations
      (C.path.comp (positiveArrow a).toPath))
    (haVertex : IsString P.toPresentation.relations
      ((Word.vertex P.toPresentation.relations
          P.toPresentation.admissible C.target).path.comp
        (positiveArrow a).toPath))
    {D₁ D₂ : Word P.toPresentation.relations}
    (tail₁ : NegativeExtension
      (append P.toPresentation.relations C (positiveArrow a) ha) D₁)
    (tail₂ : NegativeExtension
      (append P.toPresentation.relations
        (Word.vertex P.toPresentation.relations
          P.toPresentation.admissible C.target)
        (positiveArrow a) haVertex) D₂)
    (hsteps : tail₁.steps = tail₂.steps) :
    tail₁.positiveWord P.toPresentation.admissible =
      tail₂.positiveWord P.toPresentation.admissible := by
  by_cases hzero : tail₁.steps = 0
  · have hzero₂ : tail₂.steps = 0 := hsteps.symm ▸ hzero
    have hlength₁ : tail₁.ordinaryPath.length = 0 := by
      rw [tail₁.ordinaryPath_length]
      exact hzero
    have hlength₂ : tail₂.ordinaryPath.length = 0 := by
      rw [tail₂.ordinaryPath_length]
      exact hzero₂
    have hsource₁ : D₁.target = z :=
      tail₁.ordinaryPath.eq_of_length_zero hlength₁
    have hsource₂ : D₂.target = z :=
      tail₂.ordinaryPath.eq_of_length_zero hlength₂
    have hpcast₁ :
        (@Quiver.Path.cast Q _ D₁.target z z z hsource₁ rfl
          tail₁.ordinaryPath) = Quiver.Path.nil :=
      Quiver.Path.eq_nil_of_length_zero _ (by simpa using hlength₁)
    have hpcast₂ :
        (@Quiver.Path.cast Q _ D₂.target z z z hsource₂ rfl
          tail₂.ordinaryPath) = Quiver.Path.nil :=
      Quiver.Path.eq_nil_of_length_zero _ (by simpa using hlength₂)
    have hsigma₁ :
        (⟨D₁.target, tail₁.ordinaryPath⟩ :
            Σ w : Q, Quiver.Path w z) =
          ⟨z, Quiver.Path.nil⟩ := by
      apply Sigma.ext hsource₁
      exact (Quiver.Path.cast_heq hsource₁ rfl
        tail₁.ordinaryPath).symm.trans (heq_of_eq hpcast₁)
    have hsigma₂ :
        (⟨D₂.target, tail₂.ordinaryPath⟩ :
            Σ w : Q, Quiver.Path w z) =
          ⟨z, Quiver.Path.nil⟩ := by
      apply Sigma.ext hsource₂
      exact (Quiver.Path.cast_heq hsource₂ rfl
        tail₂.ordinaryPath).symm.trans (heq_of_eq hpcast₂)
    have hpaths := hsigma₁.trans hsigma₂.symm
    apply Word.ext
    · exact congrArg Sigma.fst hpaths
    · rfl
    · have hsigned :
          (⟨D₁.target, positivePath tail₁.ordinaryPath⟩ :
              Σ w : Q, SignedPath w z) =
            ⟨D₂.target, positivePath tail₂.ordinaryPath⟩ :=
        congrArg
          (fun p : Σ w : Q, Quiver.Path w z ↦
            (⟨p.1, positivePath p.2⟩ : Σ w : Q, SignedPath w z)) hpaths
      exact (Sigma.ext_iff.mp hsigned).2
  · have hpos₁ : 0 < tail₁.steps := Nat.pos_of_ne_zero hzero
    have hpos₂ : 0 < tail₂.steps := by omega
    let first₁ := tail₁.firstArrowData hpos₁
    let first₂ := tail₂.firstArrowData hpos₂
    rcases first₁ with ⟨v₁, b₁, p₁, hpath₁, hlength₁, hvalid₁⟩
    rcases first₂ with ⟨v₂, b₂, p₂, hpath₂, hlength₂, hvalid₂⟩
    have hfirst₁ : IsString P.toPresentation.relations
        ((C.path.comp (positiveArrow a).toPath).comp
          (negativeArrow b₁).toPath) := by
      change IsString P.toPresentation.relations
        ((C.path.comp (positiveArrow a).toPath).comp
          (negativeArrow b₁).toPath) at hvalid₁
      exact hvalid₁
    have hfirst₂ : IsString P.toPresentation.relations
        (((Word.vertex P.toPresentation.relations
            P.toPresentation.admissible C.target).path.comp
          (positiveArrow a).toPath).comp
          (negativeArrow b₂).toPath) := by
      change IsString P.toPresentation.relations
        (((Word.vertex P.toPresentation.relations
            P.toPresentation.admissible C.target).path.comp
          (positiveArrow a).toPath).comp
          (negativeArrow b₂).toPath) at hvalid₂
      exact hvalid₂
    have hb : (⟨v₁, b₁⟩ : Quiver.Costar z) = ⟨v₂, b₂⟩ := by
      apply eq_of_ne_of_ne_of_natCard_le_two
        (⟨C.target, a⟩ : Quiver.Costar z)
      · exact negativeTail_costar_ne_boundary C a b₁ hfirst₁
      · exact negativeTail_costar_ne_boundary
          (Word.vertex P.toPresentation.relations
            P.toPresentation.admissible C.target)
          a b₂ hfirst₂
      · exact P.arrows_ending_le_two z
    cases hb
    have hnonzero₁ :
        arrowMap P.toPresentation.relations b₁ ≫
          pathMap P.toPresentation.relations p₁ ≠ 0 := by
      have h := tail₁.pathMap_ordinaryPath_ne_zero
      rw [hpath₁, ← pathMap_comp] at h
      exact h
    have hnonzero₂ :
        arrowMap P.toPresentation.relations b₁ ≫
          pathMap P.toPresentation.relations p₂ ≠ 0 := by
      have h := tail₂.pathMap_ordinaryPath_ne_zero
      rw [hpath₂, ← pathMap_comp] at h
      exact h
    have hp₁Length : p₁.length = tail₁.steps - 1 := by omega
    have hp₂Length : p₂.length = tail₁.steps - 1 := by omega
    let q₁ : P.LeftContinuationPathAtLength b₁
        (tail₁.steps - 1) :=
      ⟨⟨D₁.target, p₁⟩, hp₁Length, hnonzero₁⟩
    let q₂ : P.LeftContinuationPathAtLength b₁
        (tail₁.steps - 1) :=
      ⟨⟨D₂.target, p₂⟩, hp₂Length, hnonzero₂⟩
    have hp : q₁ = q₂ :=
      @Subsingleton.elim _
        (P.leftContinuationPathAtLength_subsingleton
          (tail₁.steps - 1) b₁) q₁ q₂
    have hpaths :
        (⟨D₁.target, p₁⟩ : Σ w : Q, Quiver.Path w v₁) =
          ⟨D₂.target, p₂⟩ :=
      congrArg (fun p ↦ p.1) hp
    apply Word.ext
    · exact congrArg Sigma.fst hpaths
    · rfl
    · have hfull :
          (⟨D₁.target, tail₁.ordinaryPath⟩ :
              Σ w : Q, Quiver.Path w z) =
            ⟨D₂.target, tail₂.ordinaryPath⟩ := by
        rw [hpath₁, hpath₂]
        exact congrArg
          (fun p : Σ w : Q, Quiver.Path w v₁ ↦
            (⟨p.1, p.2.comp b₁.toPath⟩ :
              Σ w : Q, Quiver.Path w z)) hpaths
      have hsigned :
          (⟨D₁.target, positivePath tail₁.ordinaryPath⟩ :
              Σ w : Q, SignedPath w z) =
            ⟨D₂.target, positivePath tail₂.ordinaryPath⟩ :=
        congrArg
          (fun p : Σ w : Q, Quiver.Path w z ↦
            (⟨p.1, positivePath p.2⟩ : Σ w : Q, SignedPath w z)) hfull
      exact (Sigma.ext_iff.mp hsigned).2

/-- A canonical maximal hook based at the trivial word of a displayed
arrow's source. -/
structure HookExtension.CanonicalAtArrow
    (P : SpecialBiserialPresentation k A Q)
    (a : Σ y : Q, Σ x : Q, x ⟶ y) where
  result : Word P.toPresentation.relations
  hook : HookExtension
    (Word.vertex P.toPresentation.relations
      P.toPresentation.admissible a.2.1) result
  boundary :
    (⟨hook.vertex, hook.arrow⟩ : Quiver.Star a.2.1) =
      ⟨a.1, a.2.2⟩

/-- Choose the canonical-base maximal hook belonging to a displayed arrow. -/
noncomputable def HookExtension.canonicalAtArrow
    (P : SpecialBiserialPresentation k A Q)
    (a : Σ y : Q, Σ x : Q, x ⟶ y) :
    HookExtension.CanonicalAtArrow P a := by
  let V := Word.vertex P.toPresentation.relations
    P.toPresentation.admissible a.2.1
  have ha : IsString P.toPresentation.relations
      (V.path.comp (positiveArrow a.2.2).toPath) := by
    apply isString_of_length_lt_two P.toPresentation.relations
      P.toPresentation.admissible
    simp [V, Word.vertex]
  have hexists := HookExtension.exists_of_append_positive
    P.toPresentation.admissible V a.2.2 ha
  let D := Classical.choose hexists
  let hook := Classical.choose (Classical.choose_spec hexists)
  have hboundary := Classical.choose_spec
    (Classical.choose_spec hexists)
  exact ⟨D, hook, hboundary⟩

/-- The positive tail word canonically determined by a displayed arrow. -/
noncomputable def HookExtension.canonicalKernelWord
    (P : SpecialBiserialPresentation k A Q)
    (a : Σ y : Q, Σ x : Q, x ⟶ y) :
    Word P.toPresentation.relations :=
  (HookExtension.canonicalAtArrow P a).hook.tail.positiveWord
    P.toPresentation.admissible

/-- The tail word of any maximal hook is the canonical word of its displayed
boundary arrow. -/
theorem HookExtension.tail_positiveWord_eq_canonicalKernelWord
    (P : SpecialBiserialPresentation k A Q)
    {C D : Word P.toPresentation.relations}
    (hook : HookExtension C D) :
    hook.tail.positiveWord P.toPresentation.admissible =
      HookExtension.canonicalKernelWord P
        ⟨hook.vertex, C.target, hook.arrow⟩ := by
  let V := Word.vertex P.toPresentation.relations
    P.toPresentation.admissible C.target
  let extension := hook.toPositiveBoundaryExtension.toRightExtension
  have hsuffix : IsString P.toPresentation.relations extension.suffixPath := by
    apply IsString.of_contiguousSubpath P.toPresentation.relations
      extension.comp_suffixPath_isString
    refine ⟨C.path, Quiver.Path.nil, ?_⟩
    simp only [Quiver.Path.comp_nil]
  have hfull : IsString P.toPresentation.relations
      (V.path.comp extension.suffixPath) := by
    simpa [V, Word.vertex] using hsuffix
  let replay := hook.rebase V.path V.isString hfull
  have hbase : ofStringPath V.path V.isString = V :=
    ofStringPath_word_path V
  let normalized : HookExtension V replay.result :=
    Eq.mp (congrArg (fun W : Word P.toPresentation.relations ↦
      HookExtension W replay.result) hbase) replay.rebased
  let canonical := HookExtension.canonicalAtArrow P
    ⟨hook.vertex, C.target, hook.arrow⟩
  change hook.tail.positiveWord P.toPresentation.admissible =
    canonical.hook.tail.positiveWord P.toPresentation.admissible
  rcases canonical with ⟨E, canonHook, hcanonBoundary⟩
  rcases canonHook with ⟨canonVertex, canonArrow, canonValid,
    canonTail, canonMaximal⟩
  dsimp only at hcanonBoundary
  cases hcanonBoundary
  let canonicalHook : HookExtension V E := {
    vertex := hook.vertex
    arrow := hook.arrow
    valid := canonValid
    tail := canonTail
    maximal := canonMaximal }
  have hnormalizedBoundary :
      (⟨normalized.vertex, normalized.arrow⟩ : Quiver.Star V.target) =
        ⟨hook.vertex, hook.arrow⟩ := by
    dsimp only [normalized]
    cases hbase
    rfl
  have hpairs := HookExtension.eq_of_boundary_eq P normalized canonicalHook
    hnormalizedBoundary
  have hnormalizedSteps : normalized.steps = canonicalHook.steps := by
    exact congrArg (fun H : Σ E, HookExtension V E ↦ H.2.steps) hpairs
  have htransportSteps : normalized.steps = replay.rebased.steps := by
    exact HookExtension.steps_transport_source hbase replay.rebased
  have hreplaySteps : replay.rebased.steps = hook.steps := by
    exact hook.rebase_steps V.path V.isString hfull
  have hhookSteps : hook.steps = canonicalHook.steps :=
    hreplaySteps.symm.trans (htransportSteps.symm.trans hnormalizedSteps)
  have htailSteps : hook.tail.steps = canonTail.steps := by
    dsimp only [HookExtension.steps, canonicalHook] at hhookSteps
    omega
  have hvalidV : IsString P.toPresentation.relations
      (V.path.comp (positiveArrow hook.arrow).toPath) := canonValid
  exact hook.tail.positiveWord_eq_of_vertexBoundary_steps_eq
    P C hook.arrow hook.valid hvalidV canonTail htailSteps

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- Transporting the source word of a hook does not alter its displayed
arrow. -/
theorem HookExtension.displayedArrow_transport_source
    {C C' D : Word R} (h : C = C') (hook : HookExtension C D) :
    let transported := Eq.mp
      (congrArg (fun W : Word R ↦ HookExtension W D) h) hook
    (⟨transported.vertex, C'.target, transported.arrow⟩ :
        Σ y : Q, Σ x : Q, x ⟶ y) =
      ⟨hook.vertex, C.target, hook.arrow⟩ := by
  cases h
  rfl

end MagnitudeConjecture.BoundQuiver.StringWord.Word
