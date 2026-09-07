import MagnitudeConjecture.Algebra.StringDoubleCohookSquare
import MagnitudeConjecture.Algebra.StringHookCohookReplay
import MagnitudeConjecture.Algebra.StringPureEndpoint

/-!
# Nesting nonoverlapping cohook deletions

If maximal cohooks can be deleted from both ends of a string and their total
length does not exceed the string length, then the deletions are independent:
after deleting the right cohook, the original left cohook can still be deleted.
The proof identifies the remaining middle substring and replays the left
cohook on it.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

private def signedPathCast {a b a' b' : Q}
    (p : SignedPath a b) (ha : a = a') (hb : b = b') :
    SignedPath a' b' :=
  @Quiver.Path.cast (Quiver.Symmetrify Q)
    (Quiver.symmetrifyQuiver Q) a b a' b' ha hb p

private theorem signedPathCast_then_target
    {a b a' b' b'' : Q} (p : SignedPath a b)
    (ha : a = a') (hb : b = b') (hb' : b' = b'') :
    signedPathCast (signedPathCast p ha hb) rfl hb' =
      signedPathCast p ha (hb.trans hb') := by
  subst a'
  subst b'
  subst b''
  rfl

private theorem signedPathCast_then
    {a b a' b' a'' b'' : Q} (p : SignedPath a b)
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'') :
    signedPathCast (signedPathCast p ha hb) ha' hb' =
      signedPathCast p (ha.trans ha') (hb.trans hb') := by
  subst a'
  subst b'
  subst a''
  subst b''
  rfl

private theorem signedPathCast_comp
    {a b c a' c' : Q} (p : SignedPath a b) (q : SignedPath b c)
    (ha : a = a') (hc : c = c') :
    signedPathCast (p.comp q) ha hc =
      (signedPathCast p ha rfl).comp (signedPathCast q rfl hc) := by
  subst a'
  subst c'
  rfl

private theorem signedPathCast_source_injective
    {a b a' : Q} (ha : a = a') :
    Function.Injective
      (fun p : SignedPath a b ↦ signedPathCast p ha rfl) := by
  subst a'
  exact Function.injective_id

private theorem positivePathCast
    {a b a' b' : Q} (p : Quiver.Path a b)
    (ha : a = a') (hb : b = b') :
    positivePath (@Quiver.Path.cast Q _ a b a' b' ha hb p) =
      signedPathCast (positivePath p) ha hb := by
  subst a'
  subst b'
  rfl

private theorem signedPathCast_comp_target
    {a b c c' : Q} (p : SignedPath a b) (q : SignedPath b c)
    (h : c = c') :
    signedPathCast (p.comp q) rfl h =
      p.comp (signedPathCast q rfl h) := by
  subst c'
  rfl

private theorem signedPathCast_reverse
    {a b a' b' : Q} (p : SignedPath a b)
    (ha : a = a') (hb : b = b') :
    (signedPathCast p ha hb).reverse =
      signedPathCast p.reverse hb ha := by
  subst a'
  subst b'
  rfl

private theorem signedPathCast_heq
    {a b a' b' : Q} (p : SignedPath a b)
    (ha : a = a') (hb : b = b') :
    signedPathCast p ha hb ≍ p := by
  subst a'
  subst b'
  rfl

@[simp]
private theorem signedPathCast_length
    {a b a' b' : Q} (p : SignedPath a b)
    (ha : a = a') (hb : b = b') :
    (signedPathCast p ha hb).length = p.length := by
  subst a'
  subst b'
  rfl

private theorem signedPathCast_factor_target
    {a b c a' c' : Q} (r : SignedPath a c)
    (p : SignedPath a' b) (q : SignedPath b c)
    (ha : a = a') (hc : c = c')
    (hfactor : signedPathCast r ha rfl = p.comp q) :
    signedPathCast r ha hc =
      p.comp (signedPathCast q rfl hc) := by
  subst a'
  subst c'
  exact hfactor

private theorem signedPathCast_factor_source
    {a b c a' c' : Q} (r : SignedPath a c)
    (p : SignedPath a b) (q : SignedPath b c')
    (ha : a = a') (hc : c = c')
    (hfactor : signedPathCast r rfl hc = p.comp q) :
    signedPathCast r ha hc =
      (signedPathCast p ha rfl).comp q := by
  subst a'
  subst c'
  exact hfactor

private theorem signedPathCast_reverse_factor
    {a b c a' : Q} (r : SignedPath a c)
    (p : SignedPath a' b) (q : SignedPath b c)
    (ha : a = a')
    (hfactor : signedPathCast r ha rfl = p.comp q) :
    signedPathCast r.reverse rfl ha = q.reverse.comp p.reverse := by
  calc
    signedPathCast r.reverse rfl ha =
        (signedPathCast r ha rfl).reverse :=
      (signedPathCast_reverse r ha rfl).symm
    _ = (p.comp q).reverse := congrArg Quiver.Path.reverse hfactor
    _ = q.reverse.comp p.reverse := Quiver.Path.reverse_comp _ _

/-- If cohooks at the two ends occupy no more than the whole source word,
deleting the right cohook leaves a word from which the left cohook can still
be deleted. -/
theorem exists_leftCohookDeletion_after_right_of_steps_add_le
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hnonoverlap :
      leftDeletion.steps + rightDeletion.steps ≤ C.length) :
    ∃ E : Word R, Nonempty (LeftCohookDeletion L E) := by
  let leftExtension :=
    leftDeletion.cohook.toNegativeBoundaryExtension.toRightExtension
  let rightExtension :=
    rightDeletion.cohook.toNegativeBoundaryExtension.toRightExtension
  have htarget : C.target = D.target := leftExtension.source_eq
  have hsource : C.source = L.source := rightExtension.source_eq
  have hrightLeD : rightDeletion.steps ≤ D.reverse.length := by
    rw [reverse_length]
    have hlength := leftDeletion.source_length
    omega
  obtain ⟨position, hposition⟩ :=
    D.reverse.exists_position_index_eq rightDeletion.steps hrightLeD
  let basePath := position.2.suffix
  have hbase : IsString R basePath := by
    apply IsString.of_contiguousSubpath R D.reverse.isString
    refine ⟨position.2.1, Quiver.Path.nil, ?_⟩
    rw [Quiver.Path.comp_nil]
    exact position.2.prefix_comp_suffix
  let suffix :=
    leftDeletion.cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath
  let ambientPath : SignedPath D.reverse.source L.reverse.target :=
    signedPathCast C.reverse.path htarget hsource
  have hfull : IsString R (basePath.comp suffix) := by
    let sourceCastPath : SignedPath D.reverse.source C.reverse.target :=
      signedPathCast C.reverse.path htarget rfl
    have hsourceAmbient : IsString R sourceCastPath := by
      exact (isString_cast R htarget rfl C.reverse.path).2
        C.reverse.isString
    apply IsString.of_contiguousSubpath R hsourceAmbient
    refine ⟨position.2.1, Quiver.Path.nil, ?_⟩
    rw [Quiver.Path.comp_nil, ← Quiver.Path.comp_assoc]
    rw [← position.2.prefix_comp_suffix]
    exact leftExtension.path_cast_comp_suffixPath
  let replay := leftDeletion.cohook.rebase basePath hbase hfull
  have hreplay : replay.result = L.reverse := by
    let rightSuffix := rightExtension.suffixPath
    let leftTail : SignedPath D.reverse.target L.reverse.target :=
      signedPathCast suffix rfl hsource
    let rightPrefix : SignedPath D.reverse.source L.reverse.source :=
      signedPathCast rightSuffix.reverse htarget rfl
    have hleftFactorSource :
        signedPathCast C.reverse.path htarget rfl =
          D.reverse.path.comp suffix :=
      leftExtension.path_cast_comp_suffixPath
    have hleftFactor : ambientPath =
        D.reverse.path.comp leftTail := by
      exact signedPathCast_factor_target C.reverse.path D.reverse.path
        suffix htarget hsource hleftFactorSource
    have hrightFactorBase : signedPathCast C.path hsource rfl =
        L.path.comp rightSuffix :=
      rightExtension.path_cast_comp_suffixPath
    have hrightFactorTarget : signedPathCast C.reverse.path rfl hsource =
        rightSuffix.reverse.comp L.reverse.path := by
      change signedPathCast C.path.reverse rfl hsource =
        rightSuffix.reverse.comp L.path.reverse
      exact signedPathCast_reverse_factor C.path L.path rightSuffix
        hsource hrightFactorBase
    have hrightFactor : ambientPath =
        rightPrefix.comp L.reverse.path := by
      exact signedPathCast_factor_source C.reverse.path rightSuffix.reverse
        L.reverse.path htarget hsource hrightFactorTarget
    have hleftDecomposition : ambientPath =
        position.2.1.comp (basePath.comp leftTail) := by
      calc
        ambientPath = D.reverse.path.comp leftTail := hleftFactor
        _ = (position.2.1.comp basePath).comp leftTail :=
          congrArg (fun p ↦ p.comp leftTail)
            position.2.prefix_comp_suffix
        _ = position.2.1.comp (basePath.comp leftTail) :=
          Quiver.Path.comp_assoc _ _ _
    have hprefixLength : position.2.1.length =
        rightPrefix.length := by
      have hpindex : position.2.1.length = rightDeletion.steps := by
        simpa only [Position.index, PositionAt.index] using hposition
      rw [hpindex]
      have hsuffix := rightExtension.suffixPath_length
      have hsteps : rightExtension.steps = rightDeletion.steps := by
        simp only [rightExtension, CohookDeletion.steps,
          CohookExtension.toNegativeBoundaryExtension,
          NegativeBoundaryExtension.toRightExtension_steps,
          PositiveExtension.toRightExtension_steps, CohookExtension.steps]
      change rightDeletion.steps =
        (signedPathCast rightSuffix.reverse htarget rfl).length
      rw [signedPathCast_length, length_reverse]
      exact hsteps.symm.trans hsuffix.symm
    have hcomp : position.2.1.comp (basePath.comp leftTail) =
        rightPrefix.comp L.reverse.path :=
      hleftDecomposition.symm.trans hrightFactor
    obtain ⟨hvertex, _, hsuffixEq⟩ :=
      path_comp_decomposition_unique hcomp hprefixLength
    apply Word.ext
    · exact replay.source_eq.trans hvertex
    · exact replay.target_eq.trans hsource
    · exact HEq.trans
        (signedPathCast_heq replay.result.path replay.source_eq
          (replay.target_eq.trans hsource)).symm
        (HEq.trans (heq_of_eq (by
          calc
            signedPathCast replay.result.path replay.source_eq
                (replay.target_eq.trans hsource) =
                signedPathCast
                  (signedPathCast replay.result.path replay.source_eq
                    replay.target_eq) rfl hsource :=
              (signedPathCast_then_target replay.result.path
                replay.source_eq replay.target_eq hsource).symm
            _ = signedPathCast (basePath.comp suffix) rfl hsource :=
              congrArg (fun p ↦ signedPathCast p rfl hsource)
                replay.path_cast_eq
            _ = basePath.comp leftTail :=
              signedPathCast_comp_target _ _ _))
          hsuffixEq)
  let baseWord := ofStringPath basePath hbase
  let deletion : LeftCohookDeletion L baseWord.reverse := {
    cohook := Eq.mp
      (congrArg₂ (fun X Y : Word R ↦ CohookExtension X Y)
        (reverse_reverse R baseWord).symm hreplay)
      replay.rebased }
  exact ⟨baseWord.reverse, ⟨deletion⟩⟩

private theorem signedPathSigns_length'
    {x y : Quiver.Symmetrify Q}
    (p : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y) :
    (signedPathSigns p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      cases e <;> simp [signedPathSigns, ih]

/-- The signs of a cohook result consist of its positive tail, its initial
negative boundary letter, and the signs of the base word, in the reverse
order used by `signedPathSigns`. -/
theorem CohookExtension.signedPathSigns_eq {C D : Word R}
    (cohook : CohookExtension C D) :
    signedPathSigns D.path =
      List.replicate cohook.tail.steps false ++
        true :: signedPathSigns C.path := by
  rw [cohook.tail.signedPathSigns_eq]
  rfl

/-- A left cohook deletion gives the complementary suffix description of
the original word's sign list. -/
theorem LeftCohookDeletion.signedPathSigns_eq {C D : Word R}
    (deletion : LeftCohookDeletion C D) :
    signedPathSigns C.path =
      (signedPathSigns D.reverse.path).reverse.map (!·) ++
        false :: List.replicate deletion.cohook.tail.steps true := by
  have hreverse := deletion.cohook.signedPathSigns_eq
  calc
    signedPathSigns C.path = signedPathSigns C.reverse.path.reverse := by
      change signedPathSigns C.path = signedPathSigns C.path.reverse.reverse
      exact congrArg signedPathSigns
        (Quiver.Path.reverse_reverse C.path).symm
    _ = (signedPathSigns C.reverse.path).reverse.map (!·) :=
      signedPathSigns_reverse C.reverse.path
    _ = (List.replicate deletion.cohook.tail.steps false ++
          true :: signedPathSigns D.reverse.path).reverse.map (!·) := by
      rw [hreverse]
    _ = (signedPathSigns D.reverse.path).reverse.map (!·) ++
          false :: List.replicate deletion.cohook.tail.steps true := by
      simp

/-- In the original orientation, a left cohook deletion displays the signs
of the shortened word followed by its negative boundary letter and positive
tail. -/
theorem LeftCohookDeletion.signedPathSigns_eq_base {C D : Word R}
    (deletion : LeftCohookDeletion C D) :
    signedPathSigns C.path = signedPathSigns D.path ++
      false :: List.replicate deletion.cohook.tail.steps true := by
  have hcollapse :
      (signedPathSigns D.reverse.path).reverse.map (!·) =
        signedPathSigns D.path := by
    change (signedPathSigns D.path.reverse).reverse.map (!·) = _
    rw [signedPathSigns_reverse]
    simp [List.map_reverse, Function.comp_def]
  simpa only [hcollapse] using deletion.signedPathSigns_eq

private theorem cohookOverlap_list
    {rt lt : ℕ} {u v : List Bool}
    (h : List.replicate rt false ++ true :: u =
      v ++ false :: List.replicate lt true)
    (hover : (lt + 1) + (rt + 1) >
      (List.replicate rt false ++ true :: u).length) :
    rt = v.length + 1 ∧ lt = u.length + 1 ∧
      List.replicate rt false ++ true :: u =
        List.replicate rt false ++ List.replicate lt true := by
  have hlength := congrArg List.length h
  simp only [List.length_append, List.length_replicate, List.length_cons]
    at hlength hover
  have hrt : v.length ≤ rt := by omega
  have hdrop := congrArg (List.drop v.length) h
  simp at hdrop
  have hne : rt ≠ v.length := by
    intro heq
    subst rt
    simp at hdrop
  have hlt : v.length < rt := lt_of_le_of_ne hrt (Ne.symm hne)
  have hupper : rt ≤ v.length + 1 := by
    by_contra hnot
    have htwo : v.length + 2 ≤ rt := by omega
    have hdrop' := congrArg (List.drop (v.length + 1)) h
    simp at hdrop'
    rw [List.drop_append_of_le_length (by simp; omega)] at hdrop'
    have hltpos : 0 < lt := by omega
    have hremain : 0 < rt - (v.length + 1) := by omega
    cases hdiff : rt - (v.length + 1) with
    | zero => omega
    | succ n =>
        rw [List.drop_replicate, hdiff] at hdrop'
        cases lt with
        | zero => omega
        | succ m => simp [List.replicate_succ] at hdrop'
  have hrtEq : rt = v.length + 1 := by omega
  have hltEq : lt = u.length + 1 := by omega
  have hsuffix := congrArg (List.drop rt) h
  rw [hrtEq] at hsuffix
  simp at hsuffix
  exact ⟨hrtEq, hltEq, by rw [hsuffix]⟩

/-- If two endpoint cohook deletions overlap, each positive cohook tail runs
one letter past the opposite shortened word, and the source has exactly one
negative-to-positive sign change. -/
theorem overlappingCohookDeletion_rigidity
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hoverlap :
      C.length < leftDeletion.steps + rightDeletion.steps) :
    rightDeletion.cohook.tail.steps = D.length + 1 ∧
      leftDeletion.cohook.tail.steps = L.length + 1 ∧
      signedPathSigns C.path =
        List.replicate rightDeletion.cohook.tail.steps false ++
          List.replicate leftDeletion.cohook.tail.steps true := by
  have hright := rightDeletion.cohook.signedPathSigns_eq
  have hleft := leftDeletion.signedPathSigns_eq
  have hdecompositions :
      List.replicate rightDeletion.cohook.tail.steps false ++
          true :: signedPathSigns L.path =
        (signedPathSigns D.reverse.path).reverse.map (!·) ++
          false :: List.replicate leftDeletion.cohook.tail.steps true :=
    hright.symm.trans hleft
  have hoverlap' :
      (leftDeletion.cohook.tail.steps + 1) +
          (rightDeletion.cohook.tail.steps + 1) >
        (List.replicate rightDeletion.cohook.tail.steps false ++
          true :: signedPathSigns L.path).length := by
    rw [← hright]
    rw [signedPathSigns_length']
    simpa only [Word.length, LeftCohookDeletion.steps,
      CohookDeletion.steps, CohookExtension.steps] using hoverlap
  obtain ⟨hrightLength, hleftLength, hsigns⟩ :=
    cohookOverlap_list hdecompositions hoverlap'
  have hrightLength' :
      rightDeletion.cohook.tail.steps = D.length + 1 := by
    rw [List.length_map, List.length_reverse,
      signedPathSigns_length'] at hrightLength
    change rightDeletion.cohook.tail.steps = D.reverse.length + 1 at hrightLength
    rw [reverse_length] at hrightLength
    exact hrightLength
  have hleftLength' :
      leftDeletion.cohook.tail.steps = L.length + 1 := by
    rw [signedPathSigns_length'] at hleftLength
    exact hleftLength
  exact ⟨hrightLength', hleftLength', hright.trans hsigns⟩

/-- In the overlap case, the right-shortened word is entirely negative and
the left-shortened word is entirely positive. -/
theorem overlappingCohookDeletion_residual_signs
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hoverlap :
      C.length < leftDeletion.steps + rightDeletion.steps) :
    signedPathSigns L.path = List.replicate L.length true ∧
      signedPathSigns D.path = List.replicate D.length false := by
  obtain ⟨hrightLength, hleftLength, hrigid⟩ :=
    overlappingCohookDeletion_rigidity
      leftDeletion rightDeletion hoverlap
  have hright := rightDeletion.cohook.signedPathSigns_eq
  have hleft := leftDeletion.signedPathSigns_eq_base
  have hL : true :: signedPathSigns L.path =
      List.replicate leftDeletion.cohook.tail.steps true := by
    exact List.append_right_injective _
      (hright.symm.trans hrigid)
  have hD : signedPathSigns D.path ++
      false :: List.replicate leftDeletion.cohook.tail.steps true =
      List.replicate rightDeletion.cohook.tail.steps false ++
        List.replicate leftDeletion.cohook.tail.steps true :=
    hleft.symm.trans hrigid
  constructor
  · rw [hleftLength, List.replicate_succ] at hL
    exact (List.cons.inj hL).2
  · rw [hrightLength, List.replicate_add, List.replicate_one,
      List.append_assoc] at hD
    exact List.append_left_injective _ hD

/-- The rigid overlap word is a literal two-arm wedge.  Both arms are
ordinary surviving paths starting at one common displayed vertex; traversing
the left arm backwards and then the right arm forwards recovers the source
word.  Their lengths are exactly the two positive cohook tails. -/
theorem exists_peak_path_decomposition_of_overlappingCohookDeletions
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hoverlap :
      C.length < leftDeletion.steps + rightDeletion.steps) :
    ∃ (u : Q) (leftArm : Quiver.Path u C.source)
        (rightArm : Quiver.Path u C.target),
      C.path = (positivePath leftArm).reverse.comp
        (positivePath rightArm) ∧
      leftArm.length = leftDeletion.cohook.tail.steps ∧
      rightArm.length = rightDeletion.cohook.tail.steps := by
  let leftBase := append R D.reverse
    (negativeArrow leftDeletion.cohook.arrow) leftDeletion.cohook.valid
  let rightBase := append R L
    (negativeArrow rightDeletion.cohook.arrow) rightDeletion.cohook.valid
  let leftTail := leftDeletion.cohook.tail.toRightExtension
  let rightTail := rightDeletion.cohook.tail.toRightExtension
  have hleftFactorBase :
      signedPathCast C.reverse.path leftTail.source_eq rfl =
        leftBase.path.comp leftTail.suffixPath := by
    exact leftTail.path_cast_comp_suffixPath
  have hleftFactor :
      signedPathCast C.path rfl leftTail.source_eq =
        leftTail.suffixPath.reverse.comp leftBase.path.reverse := by
    calc
      signedPathCast C.path rfl leftTail.source_eq =
          signedPathCast C.reverse.path.reverse rfl
            leftTail.source_eq := by
        exact congrArg
          (fun p ↦ signedPathCast p rfl leftTail.source_eq)
          (Quiver.Path.reverse_reverse C.path).symm
      _ = leftTail.suffixPath.reverse.comp leftBase.path.reverse :=
        signedPathCast_reverse_factor C.reverse.path leftBase.path
          leftTail.suffixPath leftTail.source_eq hleftFactorBase
  have hrightFactorBase :
      signedPathCast C.path rightTail.source_eq rfl =
        rightBase.path.comp rightTail.suffixPath := by
    exact rightTail.path_cast_comp_suffixPath
  have hrightFactor :
      signedPathCast C.path rightTail.source_eq leftTail.source_eq =
        rightBase.path.comp
          (signedPathCast rightTail.suffixPath rfl
            leftTail.source_eq) :=
    signedPathCast_factor_target C.path rightBase.path
      rightTail.suffixPath rightTail.source_eq leftTail.source_eq
      hrightFactorBase
  have hleftFactor' :
      signedPathCast C.path rightTail.source_eq leftTail.source_eq =
        (signedPathCast leftTail.suffixPath.reverse
          rightTail.source_eq rfl).comp leftBase.path.reverse :=
    signedPathCast_factor_source C.path leftTail.suffixPath.reverse
      leftBase.path.reverse rightTail.source_eq leftTail.source_eq
      hleftFactor
  have hcomp :
      rightBase.path.comp
          (signedPathCast rightTail.suffixPath rfl leftTail.source_eq) =
        (signedPathCast leftTail.suffixPath.reverse
          rightTail.source_eq rfl).comp leftBase.path.reverse :=
    hrightFactor.symm.trans hleftFactor'
  obtain ⟨_, hleftLength, _⟩ :=
    overlappingCohookDeletion_rigidity
      leftDeletion rightDeletion hoverlap
  have hprefLength : rightBase.path.length =
      (signedPathCast leftTail.suffixPath.reverse
        rightTail.source_eq rfl).length := by
    rw [signedPathCast_length, length_reverse,
      leftTail.suffixPath_length]
    change rightBase.length = _
    simp only [rightBase, append_length]
    rw [PositiveExtension.toRightExtension_steps]
    exact hleftLength.symm
  obtain ⟨hcenter, hpref, _⟩ :=
    path_comp_decomposition_unique hcomp hprefLength
  let leftArm : Quiver.Path rightBase.target C.source :=
    @Quiver.Path.cast Q _ leftBase.target C.source
      rightBase.target C.source hcenter.symm rfl
      leftDeletion.cohook.tail.ordinaryPath
  let rightArm : Quiver.Path rightBase.target C.target :=
    rightDeletion.cohook.tail.ordinaryPath
  refine ⟨rightBase.target, leftArm, rightArm, ?_, ?_, ?_⟩
  · have hprefCast : rightBase.path =
        signedPathCast leftTail.suffixPath.reverse
          rightTail.source_eq hcenter.symm := by
      apply eq_of_heq
      exact HEq.trans hpref
        (HEq.trans
          (signedPathCast_heq leftTail.suffixPath.reverse
            rightTail.source_eq rfl)
          (signedPathCast_heq leftTail.suffixPath.reverse
            rightTail.source_eq hcenter.symm).symm)
    have hleftArmPositive : positivePath leftArm =
        signedPathCast leftTail.suffixPath hcenter.symm rfl := by
      calc
        positivePath leftArm =
            signedPathCast
              (positivePath leftDeletion.cohook.tail.ordinaryPath)
              hcenter.symm rfl :=
          positivePathCast _ _ _
        _ = signedPathCast leftTail.suffixPath hcenter.symm rfl := by
          rw [PositiveExtension.toRightExtension_suffixPath_eq_positivePath]
    have hleftReverse : (positivePath leftArm).reverse =
        signedPathCast leftTail.suffixPath.reverse rfl
          hcenter.symm := by
      rw [hleftArmPositive]
      exact signedPathCast_reverse leftTail.suffixPath hcenter.symm rfl
    have hleftCasted :
        signedPathCast (positivePath leftArm).reverse
            rightTail.source_eq rfl =
          signedPathCast leftTail.suffixPath.reverse
            rightTail.source_eq hcenter.symm := by
      rw [hleftReverse]
      exact signedPathCast_then leftTail.suffixPath.reverse rfl
        hcenter.symm rightTail.source_eq rfl
    apply signedPathCast_source_injective rightTail.source_eq
    calc
      signedPathCast C.path rightTail.source_eq rfl =
          rightBase.path.comp rightTail.suffixPath := hrightFactorBase
      _ = (signedPathCast leftTail.suffixPath.reverse
          rightTail.source_eq hcenter.symm).comp
            rightTail.suffixPath := by rw [hprefCast]
      _ = (signedPathCast (positivePath leftArm).reverse
          rightTail.source_eq rfl).comp
            (positivePath rightArm) := by
        rw [hleftCasted,
          rightDeletion.cohook.tail.toRightExtension_suffixPath_eq_positivePath]
      _ = signedPathCast ((positivePath leftArm).reverse.comp
          (positivePath rightArm)) rightTail.source_eq rfl :=
        (signedPathCast_comp (Q := Q) (positivePath leftArm).reverse
          (positivePath rightArm) rightTail.source_eq rfl).symm
  · calc
      leftArm.length =
          leftDeletion.cohook.tail.ordinaryPath.length :=
        path_cast_length _ _ _
      _ = leftDeletion.cohook.tail.steps :=
        leftDeletion.cohook.tail.ordinaryPath_length
  · exact rightDeletion.cohook.tail.ordinaryPath_length

/-- Overlapping left and right cohooks share exactly their two boundary
letters: their deletion lengths exceed the word length by precisely two. -/
theorem cohookDeletion_steps_add_eq_length_add_two_of_overlap
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hoverlap :
      C.length < leftDeletion.steps + rightDeletion.steps) :
    leftDeletion.steps + rightDeletion.steps = C.length + 2 := by
  obtain ⟨hright, _, _⟩ :=
    overlappingCohookDeletion_rigidity
      leftDeletion rightDeletion hoverlap
  have hsource := leftDeletion.source_length
  simp only [LeftCohookDeletion.steps, CohookDeletion.steps,
    CohookExtension.steps] at hsource ⊢
  omega

/-- The strict overlap inequality is equivalent to the exact two-letter
overlap formula. -/
theorem cohookDeletion_overlap_iff_steps_add_eq_length_add_two
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L) :
    C.length < leftDeletion.steps + rightDeletion.steps ↔
      leftDeletion.steps + rightDeletion.steps = C.length + 2 := by
  constructor
  · exact cohookDeletion_steps_add_eq_length_add_two_of_overlap
      leftDeletion rightDeletion
  · omega

/-- Two endpoint cohook deletions either nest to give successive deletions,
or have the rigid two-letter overlap and one-change sign pattern. -/
theorem cohookDeletion_nesting_or_overlap
    {C L D : Word R}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L) :
    (∃ E : Word R, Nonempty (LeftCohookDeletion L E)) ∨
      (leftDeletion.steps + rightDeletion.steps = C.length + 2 ∧
        signedPathSigns C.path =
          List.replicate rightDeletion.cohook.tail.steps false ++
            List.replicate leftDeletion.cohook.tail.steps true) := by
  by_cases hnonoverlap :
      leftDeletion.steps + rightDeletion.steps ≤ C.length
  · exact Or.inl
      (exists_leftCohookDeletion_after_right_of_steps_add_le
        leftDeletion rightDeletion hnonoverlap)
  · have hoverlap :
        C.length < leftDeletion.steps + rightDeletion.steps := by omega
    exact Or.inr ⟨
      cohookDeletion_steps_add_eq_length_add_two_of_overlap
        leftDeletion rightDeletion hoverlap,
      (overlappingCohookDeletion_rigidity
        leftDeletion rightDeletion hoverlap).2.2⟩

end MagnitudeConjecture.BoundQuiver.StringWord.Word
