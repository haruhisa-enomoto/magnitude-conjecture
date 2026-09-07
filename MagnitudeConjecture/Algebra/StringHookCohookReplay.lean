import MagnitudeConjecture.Algebra.StringHookCohook

/-!
# Sign-preserving replay of hook and cohook arms

The boundary-square constructions replay endpoint suffixes after replacing
the prefix word.  The generic right-extension replay forgets that a hook tail
is entirely negative or that a cohook tail is entirely positive.  This file
retains those signs; the resulting data can therefore be repackaged as
literal maximal hooks and cohooks.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Casting the target of an ordinary arrow and then taking its negative
signed copy agrees with casting the source of its negative copy. -/
private theorem cast_negativeArrow_target
    {x y y' : Q} (a : x ⟶ y') (h : y = y') :
    (@Quiver.Hom.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) y' x y x h.symm rfl
      (negativeArrow a)) =
      negativeArrow
        (@Quiver.Hom.cast Q _ x y' x y rfl h.symm a) := by
  subst y'
  rfl

/-- Casting the source of an ordinary arrow and then taking its positive
signed copy agrees with casting the source of its positive copy. -/
private theorem cast_positiveArrow_source
    {x x' y : Q} (a : x' ⟶ y) (h : x = x') :
    (@Quiver.Hom.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x' y x y h.symm rfl
      (positiveArrow a)) =
      positiveArrow
        (@Quiver.Hom.cast Q _ x' y x y h.symm rfl a) := by
  subst x'
  rfl

namespace NegativeExtension

/-- Replay a negative arm after a different certified prefix while retaining
the fact that every replayed letter is negative. -/
structure RebaseNegativeResult {C D : Word R}
    (arm : NegativeExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : NegativeExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp arm.toRightExtension.suffixPath

/-- Construct the sign-preserving replay of a negative arm. -/
def rebaseNegative {C D : Word R}
    (arm : NegativeExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp arm.toRightExtension.suffixPath)) :
    RebaseNegativeResult arm basePath hbase := by
  induction arm with
  | base =>
      exact {
        result := ofStringPath basePath hbase
        rebased := .base
        source_eq := rfl
        target_eq := rfl
        path_cast_eq := rfl }
  | @step D arm z a h ih =>
      have hprefix : IsString R
          (basePath.comp arm.toRightExtension.suffixPath) := by
        apply IsString.of_contiguousSubpath R hfull
        refine ⟨Quiver.Path.nil, (negativeArrow a).toPath, ?_⟩
        simp only [Quiver.Path.nil_comp, NegativeExtension.toRightExtension,
          RightExtension.suffixPath, Quiver.Path.comp_assoc]
      let previous := ih hprefix
      let castArrow : z ⟶ previous.result.target :=
        @Quiver.Hom.cast Q _ z D.target z previous.result.target
          rfl previous.target_eq.symm a
      let signedArrow : @Quiver.Hom (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) D.target z := negativeArrow a
      have hcastValid : IsString R
          ((@Quiver.Path.cast (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q)
            previous.result.source previous.result.target source D.target
            previous.source_eq previous.target_eq previous.result.path).comp
            signedArrow.toPath) := by
        rw [previous.path_cast_eq]
        simpa only [NegativeExtension.toRightExtension,
          RightExtension.suffixPath, Quiver.Path.comp_assoc,
          append_target, signedArrow] using hfull
      have hvalid : IsString R
          (previous.result.path.comp (negativeArrow castArrow).toPath) := by
        have hcast := isString_comp_cast_toPath (Q := Q) R previous.result.path
          signedArrow previous.source_eq previous.target_eq hcastValid
        simpa only [castArrow,
          signedArrow, cast_negativeArrow_target a previous.target_eq] using hcast
      exact {
        result := append R previous.result (negativeArrow castArrow) hvalid
        rebased := .step previous.rebased castArrow hvalid
        source_eq := previous.source_eq
        target_eq := rfl
        path_cast_eq := by
          change
            (@Quiver.Path.cast (Quiver.Symmetrify Q)
              (Quiver.symmetrifyQuiver Q)
              previous.result.source z source z previous.source_eq rfl
              (previous.result.path.comp
                (negativeArrow castArrow).toPath)) =
              basePath.comp
                (arm.toRightExtension.suffixPath.comp
                  (negativeArrow a).toPath)
          rw [← cast_negativeArrow_target a previous.target_eq]
          rw [path_cast_comp_cast_toPath (Q := Q) previous.result.path
            signedArrow previous.source_eq previous.target_eq,
            previous.path_cast_eq]
          rfl }

end NegativeExtension

namespace PositiveExtension

/-- Replay a positive arm after a different certified prefix while retaining
the fact that every replayed letter is positive. -/
structure RebasePositiveResult {C D : Word R}
    (arm : PositiveExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : PositiveExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp arm.toRightExtension.suffixPath

/-- Construct the sign-preserving replay of a positive arm. -/
def rebasePositive {C D : Word R}
    (arm : PositiveExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp arm.toRightExtension.suffixPath)) :
    RebasePositiveResult arm basePath hbase := by
  induction arm with
  | base =>
      exact {
        result := ofStringPath basePath hbase
        rebased := .base
        source_eq := rfl
        target_eq := rfl
        path_cast_eq := rfl }
  | @step D arm z a h ih =>
      have hprefix : IsString R
          (basePath.comp arm.toRightExtension.suffixPath) := by
        apply IsString.of_contiguousSubpath R hfull
        refine ⟨Quiver.Path.nil, (positiveArrow a).toPath, ?_⟩
        simp only [Quiver.Path.nil_comp, PositiveExtension.toRightExtension,
          RightExtension.suffixPath, Quiver.Path.comp_assoc]
      let previous := ih hprefix
      let castArrow : previous.result.target ⟶ z :=
        @Quiver.Hom.cast Q _ D.target z previous.result.target z
          previous.target_eq.symm rfl a
      let signedArrow : @Quiver.Hom (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) D.target z := positiveArrow a
      have hcastValid : IsString R
          ((@Quiver.Path.cast (Quiver.Symmetrify Q)
            (Quiver.symmetrifyQuiver Q)
            previous.result.source previous.result.target source D.target
            previous.source_eq previous.target_eq previous.result.path).comp
            signedArrow.toPath) := by
        rw [previous.path_cast_eq]
        simpa only [PositiveExtension.toRightExtension,
          RightExtension.suffixPath, Quiver.Path.comp_assoc,
          append_target, signedArrow] using hfull
      have hvalid : IsString R
          (previous.result.path.comp (positiveArrow castArrow).toPath) := by
        have hcast := isString_comp_cast_toPath (Q := Q) R previous.result.path
          signedArrow previous.source_eq previous.target_eq hcastValid
        simpa only [castArrow, signedArrow,
          cast_positiveArrow_source a previous.target_eq] using hcast
      exact {
        result := append R previous.result (positiveArrow castArrow) hvalid
        rebased := .step previous.rebased castArrow hvalid
        source_eq := previous.source_eq
        target_eq := rfl
        path_cast_eq := by
          change
            (@Quiver.Path.cast (Quiver.Symmetrify Q)
              (Quiver.symmetrifyQuiver Q)
              previous.result.source z source z previous.source_eq rfl
              (previous.result.path.comp
                (positiveArrow castArrow).toPath)) =
              basePath.comp
                (arm.toRightExtension.suffixPath.comp
                  (positiveArrow a).toPath)
          rw [← cast_positiveArrow_source a previous.target_eq]
          rw [path_cast_comp_cast_toPath (Q := Q) previous.result.path
            signedArrow previous.source_eq previous.target_eq,
            previous.path_cast_eq]
          rfl }

end PositiveExtension

namespace HookExtension

@[simp]
theorem steps_transport_source {C C' D : Word R}
    (h : C = C') (hook : HookExtension C D) :
    (Eq.mp (congrArg (fun W : Word R ↦ HookExtension W D) h) hook).steps =
      hook.steps := by
  cases h
  rfl

@[simp]
theorem steps_transport_result {C D D' : Word R}
    (h : D = D') (hook : HookExtension C D) :
    (Eq.mp (congrArg (fun W : Word R ↦ HookExtension C W) h) hook).steps =
      hook.steps := by
  cases h
  rfl

/-- Replacing the prefix before a complete hook suffix does not destroy the
deep at the hook endpoint.  The initial positive hook arrow is a negative
barrier after reversal, so a newly appended negative arrow would also extend
the original hook result. -/
theorem rebasedPath_startsInDeep {C D : Word R}
    (hook : HookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hfull : IsString R
      (basePath.comp
        hook.toPositiveBoundaryExtension.toRightExtension.suffixPath)) :
    (ofStringPath
      (basePath.comp
        hook.toPositiveBoundaryExtension.toRightExtension.suffixPath)
      hfull).StartsInDeep := by
  intro z a hnew
  apply hook.maximal a
  let suffix :=
    hook.toPositiveBoundaryExtension.toRightExtension.suffixPath
  let ordinaryArrow : z ⟶ D.target := a
  let signedArrow : @Quiver.Hom (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) D.target z := negativeArrow ordinaryArrow
  have hsuffix : suffix =
      (positiveArrow hook.arrow).toPath.comp
        hook.tail.toRightExtension.suffixPath := by
    exact hook.toPositiveBoundaryExtension.toRightExtension_suffixPath
  have horiginal : IsString R (C.path.comp suffix) := by
    exact hook.toPositiveBoundaryExtension.toRightExtension.comp_suffixPath_isString
  have hnewExplicit : IsString R
      ((basePath.comp suffix).comp signedArrow.toPath) := by
    exact hnew
  have hsuffixNew : IsString R (suffix.comp signedArrow.toPath) := by
    apply IsString.of_contiguousSubpath R hnewExplicit
    refine ⟨basePath, Quiver.Path.nil, ?_⟩
    simp only [Quiver.Path.comp_nil, Quiver.Path.comp_assoc]
  have hsuffixPos : 0 < suffix.length := by
    rw [hsuffix, Quiver.Path.length_comp,
      Quiver.Path.length_toPath]
    omega
  have hreduced : IsReduced
      (C.path.comp (suffix.comp signedArrow.toPath)) :=
    isReduced_comp_of_overlap C.path suffix signedArrow.toPath hsuffixPos
      horiginal.1 hsuffixNew.1
  have hnil : AvoidsRelations R
      (Quiver.Path.nil : SignedPath z z) := by
    apply AvoidsRelations.of_contiguousSubpath R hnewExplicit.2.1
    refine ⟨(basePath.comp suffix).comp signedArrow.toPath,
      Quiver.Path.nil, ?_⟩
    simp only [Quiver.Path.comp_nil]
  have hforward : AvoidsRelations R
      ((C.path.comp suffix).comp signedArrow.toPath) := by
    have hglue : AvoidsRelations R
        ((C.path.comp suffix).comp
          ((negativeArrow ordinaryArrow).toPath.comp
            (Quiver.Path.nil : SignedPath z z))) :=
      avoidsRelations_comp_negativeArrow_comp
        (a := C.source) (b := D.target) (d := z) (x := z) R
        (C.path.comp suffix) ordinaryArrow
        (Quiver.Path.nil : SignedPath z z) horiginal.2.1 hnil
    intro x y p hp
    apply hglue p
    simpa only [signedArrow, Quiver.Path.comp_nil,
      Quiver.Path.comp_assoc] using hp
  let reverseLeft : SignedPath z hook.vertex :=
    (positiveArrow ordinaryArrow).toPath.comp
      hook.tail.toRightExtension.suffixPath.reverse
  have hreverseLeft : AvoidsRelations R reverseLeft := by
    apply AvoidsRelations.of_contiguousSubpath R hnewExplicit.2.2
    refine ⟨Quiver.Path.nil,
      (negativeArrow hook.arrow).toPath.comp basePath.reverse, ?_⟩
    rw [hsuffix]
    simp only [reverseLeft, signedArrow, Quiver.Path.nil_comp,
      Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_negativeArrow, reverse_positiveArrow,
      Quiver.Path.comp_assoc]
    rfl
  have hreverse : AvoidsRelations R
      (C.path.comp (suffix.comp signedArrow.toPath)).reverse := by
    have hglue : AvoidsRelations R
        (reverseLeft.comp
          ((negativeArrow hook.arrow).toPath.comp C.path.reverse)) :=
      avoidsRelations_comp_negativeArrow_comp
        (a := z) (b := hook.vertex) (d := C.source) (x := C.target) R
        reverseLeft hook.arrow C.path.reverse
        hreverseLeft C.isString.2.2
    have hpath :
        (C.path.comp (suffix.comp signedArrow.toPath)).reverse =
          reverseLeft.comp
            ((negativeArrow hook.arrow).toPath.comp C.path.reverse) := by
      rw [hsuffix]
      simp only [reverseLeft, signedArrow, Quiver.Path.reverse_comp,
        Quiver.Path.reverse_toPath, reverse_negativeArrow,
        reverse_positiveArrow, Quiver.Path.comp_assoc]
      rfl
    rw [hpath]
    intro x y p hp
    exact hglue p hp
  have hexplicit : IsString R
      ((C.path.comp suffix).comp signedArrow.toPath) := by
    refine ⟨?_, hforward, ?_⟩
    · exact hreduced
    · exact hreverse
  let extension := hook.toPositiveBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hcast : IsString R
      ((@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        D.source D.target C.source D.target
        extension.source_eq rfl D.path).comp signedArrow.toPath) := by
    rw [hfactor]
    exact hexplicit
  have hresult := isString_comp_cast_toPath (Q := Q) R D.path
    signedArrow extension.source_eq rfl hcast
  simpa only [signedArrow, Quiver.Hom.cast_rfl_rfl] using hresult

/-- The result of replaying a complete hook after another certified prefix. -/
structure RebaseResult {C D : Word R}
    (hook : HookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : HookExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp
        hook.toPositiveBoundaryExtension.toRightExtension.suffixPath

/-- Replay a complete hook, retaining both the negative tail and endpoint
maximality. -/
def rebase {C D : Word R}
    (hook : HookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp
        hook.toPositiveBoundaryExtension.toRightExtension.suffixPath)) :
    RebaseResult hook basePath hbase := by
  have hsuffix :=
    hook.toPositiveBoundaryExtension.toRightExtension_suffixPath
  change hook.toPositiveBoundaryExtension.toRightExtension.suffixPath =
    (positiveArrow hook.arrow).toPath.comp
      hook.tail.toRightExtension.suffixPath at hsuffix
  have hfullExplicit : IsString R
      (basePath.comp ((positiveArrow hook.arrow).toPath.comp
        hook.tail.toRightExtension.suffixPath)) := by
    rw [← hsuffix]
    exact hfull
  have hvalid : IsString R
      (basePath.comp (positiveArrow hook.arrow).toPath) := by
    apply IsString.of_contiguousSubpath R hfullExplicit
    refine ⟨Quiver.Path.nil,
      hook.tail.toRightExtension.suffixPath, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
  let baseWord : Word R := ofStringPath basePath hbase
  let firstWord : Word R :=
    append R baseWord (positiveArrow hook.arrow) hvalid
  have htailFull : IsString R
      (firstWord.path.comp hook.tail.toRightExtension.suffixPath) := by
    change IsString R
      ((basePath.comp (positiveArrow hook.arrow).toPath).comp
        hook.tail.toRightExtension.suffixPath)
    rw [Quiver.Path.comp_assoc]
    exact hfullExplicit
  let tailReplay := hook.tail.rebaseNegative
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : NegativeExtension firstWord tailReplay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ NegativeExtension W tailReplay.result)
        hreplayBase)
      tailReplay.rebased
  have hpath :
      firstWord.path.comp hook.tail.toRightExtension.suffixPath =
        basePath.comp
          hook.toPositiveBoundaryExtension.toRightExtension.suffixPath := by
    change
      (basePath.comp (positiveArrow hook.arrow).toPath).comp
          hook.tail.toRightExtension.suffixPath = _
    rw [Quiver.Path.comp_assoc, ← hsuffix]
  have hresult : tailReplay.result =
      ofStringPath
        (basePath.comp
          hook.toPositiveBoundaryExtension.toRightExtension.suffixPath)
        hfull := by
    apply Word.ext
    · exact tailReplay.source_eq
    · exact tailReplay.target_eq
    · exact HEq.trans
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          tailReplay.source_eq tailReplay.target_eq
          tailReplay.result.path).symm
        (heq_of_eq (tailReplay.path_cast_eq.trans hpath))
  let rebased : HookExtension baseWord tailReplay.result := {
    vertex := hook.vertex
    arrow := hook.arrow
    valid := hvalid
    tail := replayTail
    maximal := by
      rw [hresult]
      exact hook.rebasedPath_startsInDeep basePath hfull }
  exact {
    result := tailReplay.result
    rebased := rebased
    source_eq := tailReplay.source_eq
    target_eq := tailReplay.target_eq
    path_cast_eq := tailReplay.path_cast_eq.trans hpath }

/-- Replaying a hook preserves its total number of letters. -/
@[simp]
theorem rebase_steps {C D : Word R}
    (hook : HookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp
        hook.toPositiveBoundaryExtension.toRightExtension.suffixPath)) :
    (hook.rebase basePath hbase hfull).rebased.steps = hook.steps := by
  let replay := hook.rebase basePath hbase hfull
  change replay.rebased.steps = hook.steps
  have hresult := replay.rebased.result_length
  have hpath := congrArg Quiver.Path.length replay.path_cast_eq
  have hsuffix :=
    hook.toPositiveBoundaryExtension.toRightExtension.suffixPath_length
  have hsteps :
      hook.toPositiveBoundaryExtension.toRightExtension.steps = hook.steps := by
    simp only [HookExtension.toPositiveBoundaryExtension,
      PositiveBoundaryExtension.toRightExtension_steps,
      NegativeExtension.toRightExtension_steps, HookExtension.steps]
  change replay.result.length =
      basePath.length + replay.rebased.steps at hresult
  simp only [path_cast_length, Quiver.Path.length_comp] at hpath
  change replay.result.length =
      basePath.length +
        hook.toPositiveBoundaryExtension.toRightExtension.suffixPath.length
      at hpath
  rw [hsuffix, hsteps] at hpath
  omega

end HookExtension

namespace CohookExtension

@[simp]
theorem steps_transport_source {C C' D : Word R}
    (h : C = C') (cohook : CohookExtension C D) :
    (Eq.mp (congrArg (fun W : Word R ↦ CohookExtension W D) h)
      cohook).steps = cohook.steps := by
  cases h
  rfl

@[simp]
theorem steps_transport_result {C D D' : Word R}
    (h : D = D') (cohook : CohookExtension C D) :
    (Eq.mp (congrArg (fun W : Word R ↦ CohookExtension C W) h)
      cohook).steps = cohook.steps := by
  cases h
  rfl

/-- Replacing the prefix before a complete cohook suffix does not destroy the
peak at the cohook endpoint.  The initial negative cohook arrow blocks
forward relations, while a newly appended positive arrow becomes a negative
outer boundary after reversal. -/
theorem rebasedPath_startsOnPeak {C D : Word R}
    (cohook : CohookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hfull : IsString R
      (basePath.comp
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)) :
    (ofStringPath
      (basePath.comp
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)
      hfull).StartsOnPeak := by
  intro z a hnew
  apply cohook.maximal a
  let suffix :=
    cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath
  let ordinaryArrow : D.target ⟶ z := a
  let signedArrow : @Quiver.Hom (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) D.target z := positiveArrow ordinaryArrow
  have hsuffix : suffix =
      (negativeArrow cohook.arrow).toPath.comp
        cohook.tail.toRightExtension.suffixPath := by
    exact cohook.toNegativeBoundaryExtension.toRightExtension_suffixPath
  have horiginal : IsString R (C.path.comp suffix) := by
    exact cohook.toNegativeBoundaryExtension.toRightExtension.comp_suffixPath_isString
  have hnewExplicit : IsString R
      ((basePath.comp suffix).comp signedArrow.toPath) := by
    exact hnew
  have hsuffixNew : IsString R (suffix.comp signedArrow.toPath) := by
    apply IsString.of_contiguousSubpath R hnewExplicit
    refine ⟨basePath, Quiver.Path.nil, ?_⟩
    simp only [Quiver.Path.comp_nil, Quiver.Path.comp_assoc]
  have hsuffixPos : 0 < suffix.length := by
    rw [hsuffix, Quiver.Path.length_comp,
      Quiver.Path.length_toPath]
    omega
  have hreduced : IsReduced
      (C.path.comp (suffix.comp signedArrow.toPath)) :=
    isReduced_comp_of_overlap C.path suffix signedArrow.toPath hsuffixPos
      horiginal.1 hsuffixNew.1
  let forwardRight : SignedPath cohook.vertex z :=
    cohook.tail.toRightExtension.suffixPath.comp
      (positiveArrow ordinaryArrow).toPath
  have hforwardRight : AvoidsRelations R forwardRight := by
    apply AvoidsRelations.of_contiguousSubpath R hnewExplicit.2.1
    refine ⟨basePath.comp (negativeArrow cohook.arrow).toPath,
      Quiver.Path.nil, ?_⟩
    rw [hsuffix]
    simp only [forwardRight, signedArrow, Quiver.Path.comp_nil,
      Quiver.Path.comp_assoc]
    rfl
  have hforward : AvoidsRelations R
      (C.path.comp (suffix.comp signedArrow.toPath)) := by
    have hglue : AvoidsRelations R
        (C.path.comp
          ((negativeArrow cohook.arrow).toPath.comp forwardRight)) :=
      avoidsRelations_comp_negativeArrow_comp
        (a := C.source) (b := C.target) (d := z)
        (x := cohook.vertex) R C.path cohook.arrow forwardRight
        C.isString.2.1 hforwardRight
    have hpath :
        C.path.comp (suffix.comp signedArrow.toPath) =
          C.path.comp
            ((negativeArrow cohook.arrow).toPath.comp forwardRight) := by
      rw [hsuffix]
      simp only [forwardRight, signedArrow, Quiver.Path.comp_assoc]
      rfl
    rw [hpath]
    intro x y p hp
    exact hglue p hp
  have hnil : AvoidsRelations R
      (Quiver.Path.nil : SignedPath z z) := by
    apply AvoidsRelations.of_contiguousSubpath R hnewExplicit.2.2
    refine ⟨Quiver.Path.nil,
      ((basePath.comp suffix).comp signedArrow.toPath).reverse, ?_⟩
    simp only [Quiver.Path.nil_comp]
  have hreverse : AvoidsRelations R
      (C.path.comp (suffix.comp signedArrow.toPath)).reverse := by
    have hglue : AvoidsRelations R
        ((Quiver.Path.nil : SignedPath z z).comp
          ((negativeArrow ordinaryArrow).toPath.comp
            (C.path.comp suffix).reverse)) :=
      avoidsRelations_comp_negativeArrow_comp
        (a := z) (b := z) (d := C.source) (x := D.target) R
        (Quiver.Path.nil : SignedPath z z) ordinaryArrow
        (C.path.comp suffix).reverse hnil horiginal.2.2
    have hpath :
        (C.path.comp (suffix.comp signedArrow.toPath)).reverse =
          (Quiver.Path.nil : SignedPath z z).comp
            ((negativeArrow ordinaryArrow).toPath.comp
              (C.path.comp suffix).reverse) := by
      simp only [signedArrow, Quiver.Path.reverse_comp,
        Quiver.Path.reverse_toPath, reverse_positiveArrow,
        Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
    rw [hpath]
    intro x y p hp
    exact hglue p hp
  have hexplicit : IsString R
      ((C.path.comp suffix).comp signedArrow.toPath) := by
    refine ⟨?_, ?_, ?_⟩
    · exact hreduced
    · intro x y p hp
      apply hforward p
      simpa only [Quiver.Path.comp_assoc] using hp
    · have hpath :
          ((C.path.comp suffix).comp signedArrow.toPath).reverse =
            (C.path.comp (suffix.comp signedArrow.toPath)).reverse := by
          rw [Quiver.Path.comp_assoc]
      rw [hpath]
      intro x y p hp
      exact hreverse p hp
  let extension := cohook.toNegativeBoundaryExtension.toRightExtension
  have hfactor := extension.path_cast_comp_suffixPath
  have hcast : IsString R
      ((@Quiver.Path.cast (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q)
        D.source D.target C.source D.target
        extension.source_eq rfl D.path).comp signedArrow.toPath) := by
    rw [hfactor]
    exact hexplicit
  have hresult := isString_comp_cast_toPath (Q := Q) R D.path
    signedArrow extension.source_eq rfl hcast
  simpa only [signedArrow, Quiver.Hom.cast_rfl_rfl] using hresult

/-- The result of replaying a complete cohook after another certified
prefix. -/
structure RebaseResult {C D : Word R}
    (cohook : CohookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath) where
  result : Word R
  rebased : CohookExtension (ofStringPath basePath hbase) result
  source_eq : result.source = source
  target_eq : result.target = D.target
  path_cast_eq :
    (@Quiver.Path.cast (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) result.source result.target
      source D.target source_eq target_eq result.path) =
      basePath.comp
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath

/-- Replay a complete cohook, retaining both the positive tail and endpoint
maximality. -/
def rebase {C D : Word R}
    (cohook : CohookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)) :
    RebaseResult cohook basePath hbase := by
  have hsuffix :=
    cohook.toNegativeBoundaryExtension.toRightExtension_suffixPath
  change cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath =
    (negativeArrow cohook.arrow).toPath.comp
      cohook.tail.toRightExtension.suffixPath at hsuffix
  have hfullExplicit : IsString R
      (basePath.comp ((negativeArrow cohook.arrow).toPath.comp
        cohook.tail.toRightExtension.suffixPath)) := by
    rw [← hsuffix]
    exact hfull
  have hvalid : IsString R
      (basePath.comp (negativeArrow cohook.arrow).toPath) := by
    apply IsString.of_contiguousSubpath R hfullExplicit
    refine ⟨Quiver.Path.nil,
      cohook.tail.toRightExtension.suffixPath, ?_⟩
    simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc]
  let baseWord : Word R := ofStringPath basePath hbase
  let firstWord : Word R :=
    append R baseWord (negativeArrow cohook.arrow) hvalid
  have htailFull : IsString R
      (firstWord.path.comp cohook.tail.toRightExtension.suffixPath) := by
    change IsString R
      ((basePath.comp (negativeArrow cohook.arrow).toPath).comp
        cohook.tail.toRightExtension.suffixPath)
    rw [Quiver.Path.comp_assoc]
    exact hfullExplicit
  let tailReplay := cohook.tail.rebasePositive
    firstWord.path firstWord.isString htailFull
  have hreplayBase :
      ofStringPath firstWord.path firstWord.isString = firstWord :=
    ofStringPath_word_path firstWord
  let replayTail : PositiveExtension firstWord tailReplay.result :=
    Eq.mp
      (congrArg (fun W : Word R ↦ PositiveExtension W tailReplay.result)
        hreplayBase)
      tailReplay.rebased
  have hpath :
      firstWord.path.comp cohook.tail.toRightExtension.suffixPath =
        basePath.comp
          cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath := by
    change
      (basePath.comp (negativeArrow cohook.arrow).toPath).comp
          cohook.tail.toRightExtension.suffixPath = _
    rw [Quiver.Path.comp_assoc, ← hsuffix]
  have hresult : tailReplay.result =
      ofStringPath
        (basePath.comp
          cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)
        hfull := by
    apply Word.ext
    · exact tailReplay.source_eq
    · exact tailReplay.target_eq
    · exact HEq.trans
        (@Quiver.Path.cast_heq (Quiver.Symmetrify Q)
          (Quiver.symmetrifyQuiver Q) _ _ _ _
          tailReplay.source_eq tailReplay.target_eq
          tailReplay.result.path).symm
        (heq_of_eq (tailReplay.path_cast_eq.trans hpath))
  let rebased : CohookExtension baseWord tailReplay.result := {
    vertex := cohook.vertex
    arrow := cohook.arrow
    valid := hvalid
    tail := replayTail
    maximal := by
      rw [hresult]
      exact cohook.rebasedPath_startsOnPeak basePath hfull }
  exact {
    result := tailReplay.result
    rebased := rebased
    source_eq := tailReplay.source_eq
    target_eq := tailReplay.target_eq
    path_cast_eq := tailReplay.path_cast_eq.trans hpath }

/-- Replaying a cohook preserves its total number of letters. -/
@[simp]
theorem rebase_steps {C D : Word R}
    (cohook : CohookExtension C D)
    {source : Q} (basePath : SignedPath source C.target)
    (hbase : IsString R basePath)
    (hfull : IsString R
      (basePath.comp
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath)) :
    (cohook.rebase basePath hbase hfull).rebased.steps = cohook.steps := by
  let replay := cohook.rebase basePath hbase hfull
  change replay.rebased.steps = cohook.steps
  have hresult := replay.rebased.result_length
  have hpath := congrArg Quiver.Path.length replay.path_cast_eq
  have hsuffix :=
    cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath_length
  have hsteps :
      cohook.toNegativeBoundaryExtension.toRightExtension.steps =
        cohook.steps := by
    simp only [CohookExtension.toNegativeBoundaryExtension,
      NegativeBoundaryExtension.toRightExtension_steps,
      PositiveExtension.toRightExtension_steps, CohookExtension.steps]
  change replay.result.length =
      basePath.length + replay.rebased.steps at hresult
  simp only [path_cast_length, Quiver.Path.length_comp] at hpath
  change replay.result.length =
      basePath.length +
        cohook.toNegativeBoundaryExtension.toRightExtension.suffixPath.length
      at hpath
  rw [hsuffix, hsteps] at hpath
  omega

end CohookExtension

end MagnitudeConjecture.BoundQuiver.StringWord.Word
