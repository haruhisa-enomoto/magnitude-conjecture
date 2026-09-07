import MagnitudeConjecture.Algebra.StringFiniteModule
import MagnitudeConjecture.Algebra.StringLeftBoundaryExtension
import MagnitudeConjecture.Algebra.StringPureEndpoint
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.UniserialObject

/-!
# Mixed-sign strings are not uniserial

A change of orientation in a string word exposes two literal subwords whose
coordinate inclusions are incomparable.  This is the word-level converse
needed to identify a uniserial classified string with one of the pure-sign
endpoint words.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q} [Fintype Q]

/-- The Boolean sign of one letter of the symmetrified quiver. -/
def signedArrowSign {x y : Q} : SignedArrow x y → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

@[simp]
theorem signedArrowSign_positive {x y : Q} (a : x ⟶ y) :
    signedArrowSign (positiveArrow a) = false :=
  rfl

@[simp]
theorem signedArrowSign_negative {x y : Q} (a : x ⟶ y) :
    signedArrowSign (negativeArrow a) = true :=
  rfl

/-- A literal pair of consecutive letters with different signs. -/
structure AdjacentSignChange {x y : Q} (p : SignedPath x y) where
  leftVertex : Q
  centerVertex : Q
  rightVertex : Q
  leftPath : SignedPath x leftVertex
  earlier : SignedArrow leftVertex centerVertex
  later : SignedArrow centerVertex rightVertex
  rightPath : SignedPath rightVertex y
  path_eq : p = ((leftPath.cons earlier).cons later).comp rightPath
  sign_ne : signedArrowSign earlier ≠ signedArrowSign later

/-- Appending one letter after an existing adjacent sign change preserves
the witness. -/
private def AdjacentSignChange.append
    {x y z : Q} {p : SignedPath x y}
    (change : AdjacentSignChange p) (e : SignedArrow y z) :
    AdjacentSignChange (p.cons e) := by
  rcases change with
    ⟨leftVertex, centerVertex, rightVertex, leftPath, earlier, later,
      rightPath, path_eq, sign_ne⟩
  subst p
  exact {
    leftVertex := leftVertex
    centerVertex := centerVertex
    rightVertex := rightVertex
    leftPath := leftPath
    earlier := earlier
    later := later
    rightPath := rightPath.cons e
    path_eq := rfl
    sign_ne := sign_ne }

/-- A signed path containing both signs has two consecutive letters with
different signs. -/
theorem adjacentSignChange_of_mem_signedPathSigns
    {x y : Q} (p : SignedPath x y)
    (hpositive : false ∈ signedPathSigns p)
    (hnegative : true ∈ signedPathSigns p) :
    Nonempty (AdjacentSignChange p) := by
  induction hlength : p.length using Nat.strong_induction_on
      generalizing x y with
  | h n ih =>
    cases p with
    | nil => simp [signedPathSigns] at hpositive
    | @cons z y p e =>
      have hpLength : p.length < n := by
        simp only [Quiver.Path.length_cons] at hlength
        omega
      cases e with
      | inl a =>
          have hnegativeP : true ∈ signedPathSigns p := by
            simpa [signedPathSigns] using hnegative
          by_cases hp : false ∈ signedPathSigns p
          · obtain ⟨change⟩ := ih p.length hpLength p hp hnegativeP rfl
            exact ⟨change.append (positiveArrow a)⟩
          · cases p with
            | nil => simp [signedPathSigns] at hnegativeP
            | @cons w z p e =>
                cases e with
                | inl b =>
                    exact False.elim (hp (by simp [signedPathSigns]))
                | inr b =>
                    exact ⟨{
                      leftVertex := w
                      centerVertex := z
                      rightVertex := y
                      leftPath := p
                      earlier := negativeArrow b
                      later := positiveArrow a
                      rightPath := Quiver.Path.nil
                      path_eq := rfl
                      sign_ne := by simp }⟩
      | inr a =>
          have hpositiveP : false ∈ signedPathSigns p := by
            simpa [signedPathSigns] using hpositive
          by_cases hn : true ∈ signedPathSigns p
          · obtain ⟨change⟩ := ih p.length hpLength p hpositiveP hn rfl
            exact ⟨change.append (negativeArrow a)⟩
          · cases p with
            | nil => simp [signedPathSigns] at hpositiveP
            | @cons w z p e =>
                cases e with
                | inl b =>
                    exact ⟨{
                      leftVertex := w
                      centerVertex := z
                      rightVertex := y
                      leftPath := p
                      earlier := positiveArrow b
                      later := negativeArrow a
                      rightPath := Quiver.Path.nil
                      path_eq := rfl
                      sign_ne := by simp }⟩
                | inr b =>
                    exact False.elim (hn (by simp [signedPathSigns]))

/-- The sign list has one entry for every path letter. -/
@[simp]
theorem signedPathSigns_length
    {x y : Quiver.Symmetrify Q}
    (p : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y) :
    (signedPathSigns p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      cases e <;> simp [signedPathSigns, ih]

/-- If every letter in a right extension from a vertex word is positive,
the extension is a positive arm. -/
private theorem RightExtension.positive_of_result_signs_eq
    {hR : IsAdmissible R} {x : Q} {D : Word R}
    (extension : RightExtension (vertex R hR x) D)
    (hsigns : signedPathSigns D.path =
      List.replicate D.length false) :
    Nonempty (PositiveExtension (vertex R hR x) D) := by
  induction extension with
  | base => exact ⟨PositiveExtension.base⟩
  | @step E extension z e h ih =>
      cases e with
      | inl a =>
          have hE : signedPathSigns E.path =
              List.replicate E.length false := by
            change false :: signedPathSigns E.path =
              List.replicate (E.length + 1) false at hsigns
            simpa only [List.replicate_succ, List.cons.injEq, true_and] using
              hsigns
          obtain ⟨positive⟩ := ih hE
          exact ⟨PositiveExtension.step positive a h⟩
      | inr a =>
          change true :: signedPathSigns E.path =
            List.replicate (E.length + 1) false at hsigns
          simp [List.replicate_succ] at hsigns

/-- The sign-list description of a pure-positive word is an equivalence. -/
theorem isPurePositive_iff_signedPathSigns_eq
    (hR : IsAdmissible R) (C : Word R) :
    C.IsPurePositive hR ↔
      signedPathSigns C.path = List.replicate C.length false := by
  constructor
  · exact fun h ↦ h.signedPathSigns_eq hR
  · intro hsigns
    obtain ⟨extension⟩ := rightExtensionFromVertex_nonempty hR C
    exact extension.positive_of_result_signs_eq hsigns

/-- The sign-list description of a pure-negative word is an equivalence. -/
theorem isPureNegative_iff_signedPathSigns_eq
    (hR : IsAdmissible R) (C : Word R) :
    C.IsPureNegative hR ↔
      signedPathSigns C.path = List.replicate C.length true := by
  constructor
  · exact fun h ↦ h.signedPathSigns_eq hR
  · intro hsigns
    apply (isPurePositive_iff_signedPathSigns_eq hR C.reverse).2
    change signedPathSigns C.path.reverse =
      List.replicate C.reverse.length false
    rw [signedPathSigns_reverse, hsigns]
    simp

/-- A certified suffix can be appended one letter at a time, producing a
right-extension record from its certified prefix. -/
private theorem rightExtension_of_comp_nonempty
    {x y z : Q} (p : SignedPath x y) (q : SignedPath y z)
    (hp : IsString R p) :
    ∀ hfull : IsString R (p.comp q),
      Nonempty
        (RightExtension (ofStringPath p hp)
          (ofStringPath (p.comp q) hfull)) := by
  induction hlength : q.length using Nat.strong_induction_on
      generalizing y z with
  | h n ih =>
    cases q with
    | nil =>
        intro hfull
        have hword : ofStringPath (p.comp Quiver.Path.nil) hfull =
            ofStringPath p hp := by
          apply Word.ext <;> simp [ofStringPath]
        exact ⟨Eq.mpr
          (congrArg
            (fun W : Word R ↦ RightExtension (ofStringPath p hp) W)
            hword)
          RightExtension.base⟩
    | @cons middle z q e =>
        intro hfull
        have hn : q.length + 1 = n := by
          simpa only [Quiver.Path.length_cons] using hlength
        have hprefixSub : IsContiguousSubpath (p.comp q)
            (p.comp (q.cons e)) := by
          refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
          simp only [Quiver.Path.nil_comp,
            Quiver.Path.comp_toPath_eq_cons, Quiver.Path.comp_cons]
        have hprefix : IsString R (p.comp q) :=
          IsString.of_contiguousSubpath R hfull hprefixSub
        let prefixWord : Word R := ofStringPath (p.comp q) hprefix
        have happend : IsString R (prefixWord.path.comp e.toPath) := by
          simpa only [prefixWord, ofStringPath,
            Quiver.Path.comp_toPath_eq_cons, Quiver.Path.comp_cons] using
            hfull
        have hlt : q.length < n := by omega
        obtain ⟨extension⟩ := ih q.length hlt p q hp rfl hprefix
        let next : RightExtension (ofStringPath p hp)
            (append R prefixWord e happend) :=
          RightExtension.step extension e happend
        have hword : append R prefixWord e happend =
            ofStringPath (p.comp (q.cons e)) hfull := by
          apply Word.ext
          · rfl
          · rfl
          · exact HEq.rfl
        exact ⟨Eq.mp
          (congrArg
            (fun W : Word R ↦ RightExtension (ofStringPath p hp) W)
            hword)
          next⟩

/-- A negative-boundary prefix inclusion, bundled in the finite-dimensional
module category. -/
def NegativeBoundaryExtension.finiteModuleInclusion
    {L C : Word R} (left : NegativeBoundaryExtension L C)
    (hmono : IsMonomial R) :
    L.finiteRightModule hmono ⟶ C.finiteRightModule hmono :=
  ObjectProperty.homMk
    (ObjectProperty.homMk (left.rightModuleInclusion hmono))

instance NegativeBoundaryExtension.finiteModuleInclusion_mono
    {L C : Word R} (left : NegativeBoundaryExtension L C)
    (hmono : IsMonomial R) :
    Mono (left.finiteModuleInclusion hmono) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := (Category R)ᵒᵖ) k).ι
  let K := (CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k).ι
  haveI : Mono (K.map (J.map (left.finiteModuleInclusion hmono))) := by
    change Mono (left.rightModuleInclusion hmono)
    infer_instance
  haveI : Mono (J.map (left.finiteModuleInclusion hmono)) :=
    K.mono_of_mono_map
      (show Mono (K.map (J.map (left.finiteModuleInclusion hmono))) from
        inferInstance)
  exact J.mono_of_mono_map
    (show Mono (J.map (left.finiteModuleInclusion hmono)) from inferInstance)

/-- A negative left-boundary suffix inclusion, bundled in the finite-
dimensional module category. -/
def LeftNegativeBoundaryExtension.finiteModuleInclusion
    {S : Word R} (right : LeftNegativeBoundaryExtension S)
    (hmono : IsMonomial R) :
    S.finiteRightModule hmono ⟶ right.result.finiteRightModule hmono :=
  ObjectProperty.homMk
    (ObjectProperty.homMk (right.moduleMap hmono))

instance LeftNegativeBoundaryExtension.finiteModuleInclusion_mono
    {S : Word R} (right : LeftNegativeBoundaryExtension S)
    (hmono : IsMonomial R) :
    Mono (right.finiteModuleInclusion hmono) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := (Category R)ᵒᵖ) k).ι
  let K := (CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k).ι
  haveI : Mono (K.map (J.map (right.finiteModuleInclusion hmono))) := by
    change Mono (right.moduleMap hmono)
    infer_instance
  haveI : Mono (J.map (right.finiteModuleInclusion hmono)) :=
    K.mono_of_mono_map
      (show Mono (K.map (J.map (right.finiteModuleInclusion hmono))) from
        inferInstance)
  exact J.mono_of_mono_map
    (show Mono (J.map (right.finiteModuleInclusion hmono)) from inferInstance)

/-- A prefix and suffix entering a word through negative boundaries give
incomparable subobjects when each contains a position absent from the other.
The numerical hypotheses state precisely that the left source occurs before
the suffix starts and that the right target occurs after the prefix ends. -/
theorem not_isUniserialObject_of_separated_negativeBoundaries
    {L S : Word R}
    (right : LeftNegativeBoundaryExtension S)
    (left : NegativeBoundaryExtension L right.result)
    (hmono : IsMonomial R)
    (hstart : 0 < right.steps)
    (hend : L.length < right.steps + S.length) :
    ¬ IsUniserialObject (right.result.finiteRightModule hmono) := by
  let f := left.finiteModuleInclusion hmono
  let g := right.finiteModuleInclusion hmono
  let P : Subobject (right.result.finiteRightModule hmono) := Subobject.mk f
  let Q : Subobject (right.result.finiteRightModule hmono) := Subobject.mk g
  intro hU
  rcases hU.total P Q with hPQ | hQP
  · let t := Subobject.ofMkLEMk f g hPQ
    have hfac : t ≫ g = f := Subobject.ofMkLEMk_comp hPQ
    have happ := congrArg
      (fun q ↦ q.hom.hom.app
        (Opposite.op (BoundQuiver.obj R L.source))) hfac
    have hv := congrArg
      (fun q ↦ q (Finsupp.single L.sourcePosition (1 : k))) happ
    let i := left.toRightExtension.position L.sourcePosition
    have hnotRight : ¬ ∃ j : S.PositionAt L.source,
        right.position j = i := by
      rintro ⟨j, hj⟩
      have hindex := congrArg PositionAt.index hj
      rw [right.position_index, left.toRightExtension.position_index] at hindex
      change right.steps + j.index = L.sourcePosition.index at hindex
      rw [sourcePosition_index] at hindex
      omega
    have hzero : right.spaceInclusion L.source
        (t.hom.hom.app (Opposite.op (BoundQuiver.obj R L.source))
          (Finsupp.single L.sourcePosition (1 : k))) i = 0 :=
      right.spaceInclusion_apply_of_not_exists _ i hnotRight
    have hone : left.toRightExtension.spaceInclusion L.source
        (Finsupp.single L.sourcePosition (1 : k)) i = 1 := by
      rw [RightExtension.spaceInclusion_single]
      simp [i]
    have hcoeff := congrArg (fun w : right.result.Space L.source ↦ w i) hv
    change right.spaceInclusion L.source
        (t.hom.hom.app (Opposite.op (BoundQuiver.obj R L.source))
          (Finsupp.single L.sourcePosition (1 : k))) i =
      left.toRightExtension.spaceInclusion L.source
        (Finsupp.single L.sourcePosition (1 : k)) i at hcoeff
    rw [hzero, hone] at hcoeff
    exact zero_ne_one hcoeff
  · let t := Subobject.ofMkLEMk g f hQP
    have hfac : t ≫ f = g := Subobject.ofMkLEMk_comp hQP
    have happ := congrArg
      (fun q ↦ q.hom.hom.app
        (Opposite.op (BoundQuiver.obj R S.target))) hfac
    have hv := congrArg
      (fun q ↦ q (Finsupp.single S.targetPosition (1 : k))) happ
    let i := right.position S.targetPosition
    have hnotLeft : ¬ ∃ j : L.PositionAt S.target,
        left.toRightExtension.position j = i := by
      rintro ⟨j, hj⟩
      have hindex := congrArg PositionAt.index hj
      rw [left.toRightExtension.position_index, right.position_index] at hindex
      have hjle := j.index_le
      change j.index = right.steps + S.length at hindex
      omega
    have hzero : left.toRightExtension.spaceInclusion S.target
        (t.hom.hom.app (Opposite.op (BoundQuiver.obj R S.target))
          (Finsupp.single S.targetPosition (1 : k))) i = 0 :=
      left.toRightExtension.spaceInclusion_apply_of_not_exists _ i hnotLeft
    have hone : right.spaceInclusion S.target
        (Finsupp.single S.targetPosition (1 : k)) i = 1 := by
      rw [LeftNegativeBoundaryExtension.spaceInclusion_single]
      simp [i]
    have hcoeff := congrArg (fun w : right.result.Space S.target ↦ w i) hv
    change left.toRightExtension.spaceInclusion S.target
        (t.hom.hom.app (Opposite.op (BoundQuiver.obj R S.target))
          (Finsupp.single S.targetPosition (1 : k))) i =
      right.spaceInclusion S.target
        (Finsupp.single S.targetPosition (1 : k)) i at hcoeff
    rw [hzero, hone] at hcoeff
    exact zero_ne_one hcoeff

/-- A positive letter followed by a negative letter produces two
incomparable subword inclusions meeting at the intervening peak. -/
private theorem not_isUniserialObject_of_positive_negative_factorization
    (C : Word R)
    {previous center next : Q}
    (leftPath : SignedPath C.source previous)
    (a : previous ⟶ center) (b : next ⟶ center)
    (rightPath : SignedPath next C.target)
    (hpath : C.path =
      ((leftPath.cons (positiveArrow (Q := Q) a)).cons
        (negativeArrow b)).comp
        rightPath)
    (hmono : IsMonomial R) :
    ¬ IsUniserialObject (C.finiteRightModule hmono) := by
  let firstPath := leftPath.cons (positiveArrow (Q := Q) a)
  let prefixPath := firstPath.cons (negativeArrow b)
  let fullPath := prefixPath.comp rightPath
  let suffixPath := (negativeArrow b).toPath.comp rightPath
  have hfullFactor : fullPath = firstPath.comp suffixPath := by
    change (firstPath.cons (negativeArrow b)).comp rightPath =
      firstPath.comp ((negativeArrow b).toPath.comp rightPath)
    rw [← Quiver.Path.comp_toPath_eq_cons]
    exact Quiver.Path.comp_assoc _ _ _
  have hfull : IsString R fullPath := by
    change IsString R
      (((leftPath.cons (positiveArrow (Q := Q) a)).cons
        (negativeArrow b)).comp rightPath)
    rw [← hpath]
    exact C.isString
  have hfirst : IsString R firstPath := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil,
      (negativeArrow b).toPath.comp rightPath, ?_⟩
    calc
      fullPath = firstPath.comp suffixPath := hfullFactor
      _ = Quiver.Path.nil.comp
          (firstPath.comp suffixPath) :=
        (Quiver.Path.nil_comp _).symm
  have hprefix : IsString R prefixPath := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil, rightPath, ?_⟩
    simp [fullPath]
  have hsuffix : IsString R suffixPath := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨firstPath, Quiver.Path.nil, ?_⟩
    calc
      fullPath = firstPath.comp suffixPath := hfullFactor
      _ = firstPath.comp (suffixPath.comp Quiver.Path.nil) := by
        rw [Quiver.Path.comp_nil]
  let L : Word R := ofStringPath firstPath hfirst
  let S : Word R := ofStringPath suffixPath hsuffix
  let W : Word R := ofStringPath fullPath hfull
  have hvalidLeft : IsString R
      (L.path.comp (negativeArrow b).toPath) := by
    simpa [L, firstPath, prefixPath, ofStringPath,
      Quiver.Path.comp_toPath_eq_cons] using hprefix
  let firstLeft : Word R :=
    append R L (negativeArrow b) hvalidLeft
  have htailFull : IsString R (firstLeft.path.comp rightPath) := by
    simpa [firstLeft, L, W, fullPath, prefixPath, firstPath,
      append_path, ofStringPath, Quiver.Path.comp_toPath_eq_cons] using hfull
  let tailLeft0 := Classical.choice
    (rightExtension_of_comp_nonempty firstLeft.path rightPath
      firstLeft.isString htailFull)
  have htailTarget :
      ofStringPath (firstLeft.path.comp rightPath) htailFull = W := by
    apply Word.ext
    · rfl
    · rfl
    · exact HEq.rfl
  let tailLeft : RightExtension firstLeft W :=
    Eq.mp
      (congrArg (fun X : Word R ↦ RightExtension firstLeft X) htailTarget)
      tailLeft0
  let leftW : NegativeBoundaryExtension L W := {
    vertex := next
    arrow := b
    valid := hvalidLeft
    tail := tailLeft }
  let SR := S.reverse
  have hfirstReverse : firstPath.reverse =
      (negativeArrow a).toPath.comp leftPath.reverse := by
    change (leftPath.cons (positiveArrow (Q := Q) a)).reverse = _
    rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.reverse_comp]
    calc
      (positiveArrow (Q := Q) a).toPath.reverse.comp leftPath.reverse =
          (Quiver.reverse (positiveArrow (Q := Q) a)).toPath.comp
            leftPath.reverse := rfl
      _ = (negativeArrow a).toPath.comp leftPath.reverse :=
        congrArg (fun e ↦ e.toPath.comp leftPath.reverse)
          (reverse_positiveArrow a)
  have hreverseFactor : W.reverse.path =
      (SR.path.comp (negativeArrow a).toPath).comp leftPath.reverse := by
    change fullPath.reverse =
      (suffixPath.reverse.comp (negativeArrow a).toPath).comp
        leftPath.reverse
    calc
      fullPath.reverse = (firstPath.comp suffixPath).reverse :=
        congrArg Quiver.Path.reverse hfullFactor
      _ = suffixPath.reverse.comp firstPath.reverse :=
        Quiver.Path.reverse_comp _ _
      _ = suffixPath.reverse.comp
          ((negativeArrow a).toPath.comp leftPath.reverse) := by
        rw [hfirstReverse]
      _ = (suffixPath.reverse.comp (negativeArrow a).toPath).comp
          leftPath.reverse := (Quiver.Path.comp_assoc _ _ _).symm
  have hvalidRight : IsString R
      (SR.path.comp (negativeArrow a).toPath) := by
    apply IsString.of_contiguousSubpath R W.reverse.isString
    refine ⟨Quiver.Path.nil, leftPath.reverse, ?_⟩
    calc
      W.reverse.path =
          (SR.path.comp (negativeArrow a).toPath).comp leftPath.reverse :=
        hreverseFactor
      _ = Quiver.Path.nil.comp
          ((SR.path.comp (negativeArrow a).toPath).comp
            leftPath.reverse) := (Quiver.Path.nil_comp _).symm
  let firstRight : Word R :=
    append R SR (negativeArrow a) hvalidRight
  have htailRightFull :
      IsString R (firstRight.path.comp leftPath.reverse) := by
    have hfirstRightPath : firstRight.path =
        SR.path.comp (negativeArrow a).toPath := rfl
    rw [hfirstRightPath]
    exact Eq.mp (congrArg (IsString R) hreverseFactor)
      W.reverse.isString
  let tailRight0 := Classical.choice
    (rightExtension_of_comp_nonempty firstRight.path leftPath.reverse
      firstRight.isString htailRightFull)
  have htailRightTarget :
      ofStringPath (firstRight.path.comp leftPath.reverse)
          htailRightFull = W.reverse := by
    apply Word.ext
    · rfl
    · rfl
    · have hfirstRightPath : firstRight.path =
          SR.path.comp (negativeArrow a).toPath := rfl
      exact heq_of_eq ((congrArg
        (fun p ↦ p.comp leftPath.reverse) hfirstRightPath).trans
          hreverseFactor.symm)
  let tailRight : RightExtension firstRight W.reverse :=
    Eq.mp
      (congrArg
        (fun X : Word R ↦ RightExtension firstRight X) htailRightTarget)
      tailRight0
  let negativeRight : NegativeBoundaryExtension SR W.reverse := {
    vertex := previous
    arrow := a
    valid := hvalidRight
    tail := tailRight }
  let right : LeftNegativeBoundaryExtension S := {
    reverseResult := W.reverse
    extension := negativeRight }
  have hrightResult : right.result = W := by
    exact reverse_reverse R W
  let left : NegativeBoundaryExtension L right.result :=
    Eq.mp
      (congrArg
        (fun X : Word R ↦ NegativeBoundaryExtension L X)
        hrightResult.symm)
      leftW
  have hLltW : L.length < W.length := by
    dsimp [L, W, fullPath, prefixPath, firstPath, ofStringPath, Word.length]
    simp only [Quiver.Path.length_comp, Quiver.Path.length_cons]
    omega
  have hSltW : S.length < W.length := by
    dsimp [S, W, fullPath, prefixPath, firstPath, suffixPath,
      ofStringPath, Word.length]
    simp only [Quiver.Path.length_comp, Quiver.Path.length_cons,
      Quiver.Path.length_toPath]
    omega
  have hrightLength := right.result_length
  rw [hrightResult] at hrightLength
  have hstart : 0 < right.steps := by omega
  have hend : L.length < right.steps + S.length := by omega
  have hnotW :=
    not_isUniserialObject_of_separated_negativeBoundaries
      right left hmono hstart hend
  have hWC : W = C := by
    apply Word.ext
    · rfl
    · rfl
    · exact heq_of_eq hpath.symm
  intro hC
  apply hnotW
  have hresultC : right.result = C := hrightResult.trans hWC
  exact IsUniserialObject.congr hC
    (eqToIso
      (congrArg
        (fun X : Word R ↦ X.finiteRightModule hmono) hresultC.symm))

/-- A negative letter followed by a positive letter produces two disjoint
incomparable subword inclusions on the two sides of the intervening valley. -/
private theorem not_isUniserialObject_of_negative_positive_factorization
    (C : Word R)
    {previous center next : Q}
    (leftPath : SignedPath C.source previous)
    (a : center ⟶ previous) (b : center ⟶ next)
    (rightPath : SignedPath next C.target)
    (hpath : C.path =
      ((leftPath.cons (negativeArrow (Q := Q) a)).cons
        (positiveArrow (Q := Q) b)).comp rightPath)
    (hmono : IsMonomial R) :
    ¬ IsUniserialObject (C.finiteRightModule hmono) := by
  let firstPrefix := leftPath.cons (negativeArrow (Q := Q) a)
  let fullPrefix := firstPrefix.cons (positiveArrow (Q := Q) b)
  let fullPath := fullPrefix.comp rightPath
  have hfull : IsString R fullPath := by
    change IsString R
      (((leftPath.cons (negativeArrow (Q := Q) a)).cons
        (positiveArrow (Q := Q) b)).comp rightPath)
    rw [← hpath]
    exact C.isString
  have hleft : IsString R leftPath := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil,
      (negativeArrow (Q := Q) a).toPath.comp
        ((positiveArrow (Q := Q) b).toPath.comp rightPath), ?_⟩
    calc
      fullPath = leftPath.comp
          ((negativeArrow (Q := Q) a).toPath.comp
            ((positiveArrow (Q := Q) b).toPath.comp rightPath)) := by
        dsimp only [fullPath, fullPrefix, firstPrefix]
        rw [← Quiver.Path.comp_toPath_eq_cons,
          ← Quiver.Path.comp_toPath_eq_cons]
        simp only [Quiver.Path.comp_assoc]
      _ = Quiver.Path.nil.comp
          (leftPath.comp
            ((negativeArrow (Q := Q) a).toPath.comp
              ((positiveArrow (Q := Q) b).toPath.comp rightPath))) :=
        (Quiver.Path.nil_comp _).symm
  have hfirstPrefix : IsString R firstPrefix := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil,
      (positiveArrow (Q := Q) b).toPath.comp rightPath, ?_⟩
    calc
      fullPath = firstPrefix.comp
          ((positiveArrow (Q := Q) b).toPath.comp rightPath) := by
        dsimp only [fullPath, fullPrefix]
        rw [← Quiver.Path.comp_toPath_eq_cons]
        exact Quiver.Path.comp_assoc _ _ _
      _ = Quiver.Path.nil.comp
          (firstPrefix.comp
            ((positiveArrow (Q := Q) b).toPath.comp rightPath)) :=
        (Quiver.Path.nil_comp _).symm
  have hfullPrefix : IsString R fullPrefix := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨Quiver.Path.nil, rightPath, ?_⟩
    simp [fullPath]
  have hright : IsString R rightPath := by
    apply IsString.of_contiguousSubpath R hfull
    refine ⟨fullPrefix, Quiver.Path.nil, ?_⟩
    calc
      fullPath = fullPrefix.comp rightPath := rfl
      _ = fullPrefix.comp (rightPath.comp Quiver.Path.nil) := by
        rw [Quiver.Path.comp_nil]
  let L : Word R := ofStringPath leftPath hleft
  let S : Word R := ofStringPath rightPath hright
  let W : Word R := ofStringPath fullPath hfull
  have hvalidLeft : IsString R
      (L.path.comp (negativeArrow (Q := Q) a).toPath) := by
    simpa [L, firstPrefix, ofStringPath,
      Quiver.Path.comp_toPath_eq_cons] using hfirstPrefix
  let firstLeft : Word R :=
    append R L (negativeArrow (Q := Q) a) hvalidLeft
  have hvalidSecond : IsString R
      (firstLeft.path.comp (positiveArrow (Q := Q) b).toPath) := by
    simpa [firstLeft, L, fullPrefix, firstPrefix, append_path,
      ofStringPath, Quiver.Path.comp_toPath_eq_cons] using hfullPrefix
  let secondLeft : Word R :=
    append R firstLeft (positiveArrow (Q := Q) b) hvalidSecond
  have htailFull : IsString R (secondLeft.path.comp rightPath) := by
    simpa [secondLeft, firstLeft, L, W, fullPath, fullPrefix,
      firstPrefix, append_path, ofStringPath,
      Quiver.Path.comp_toPath_eq_cons] using hfull
  let tailRest0 := Classical.choice
    (rightExtension_of_comp_nonempty secondLeft.path rightPath
      secondLeft.isString htailFull)
  have htailTarget :
      ofStringPath (secondLeft.path.comp rightPath) htailFull = W := by
    apply Word.ext
    · rfl
    · rfl
    · have hsecondLeftPath : secondLeft.path = fullPrefix := rfl
      exact heq_of_eq
        ((congrArg (fun p ↦ p.comp rightPath) hsecondLeftPath).trans rfl)
  let tailRest : RightExtension secondLeft W :=
    Eq.mp
      (congrArg (fun X : Word R ↦ RightExtension secondLeft X) htailTarget)
      tailRest0
  let secondStep : RightExtension firstLeft secondLeft :=
    RightExtension.step
      (RightExtension.base : RightExtension firstLeft firstLeft)
      (positiveArrow (Q := Q) b) hvalidSecond
  let tailLeft : RightExtension firstLeft W := secondStep.trans tailRest
  let leftW : NegativeBoundaryExtension L W := {
    vertex := center
    arrow := a
    valid := hvalidLeft
    tail := tailLeft }
  let SR := S.reverse
  have hfullReverse : fullPath.reverse =
      rightPath.reverse.comp
        ((negativeArrow b).toPath.comp
          ((positiveArrow (Q := Q) a).toPath.comp leftPath.reverse)) := by
    dsimp only [fullPath, fullPrefix, firstPrefix]
    rw [Quiver.Path.reverse_comp]
    rw [← Quiver.Path.comp_toPath_eq_cons,
      Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_positiveArrow]
    rw [← Quiver.Path.comp_toPath_eq_cons,
      Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_negativeArrow]
  have hvalidRight : IsString R
      (SR.path.comp (negativeArrow b).toPath) := by
    apply IsString.of_contiguousSubpath R W.reverse.isString
    refine ⟨Quiver.Path.nil,
      (positiveArrow (Q := Q) a).toPath.comp leftPath.reverse, ?_⟩
    change fullPath.reverse = Quiver.Path.nil.comp
      ((rightPath.reverse.comp (negativeArrow b).toPath).comp
        ((positiveArrow (Q := Q) a).toPath.comp leftPath.reverse))
    calc
      fullPath.reverse = rightPath.reverse.comp
          ((negativeArrow b).toPath.comp
            ((positiveArrow (Q := Q) a).toPath.comp leftPath.reverse)) :=
        hfullReverse
      _ = (rightPath.reverse.comp (negativeArrow b).toPath).comp
          ((positiveArrow (Q := Q) a).toPath.comp leftPath.reverse) :=
        (Quiver.Path.comp_assoc _ _ _).symm
      _ = Quiver.Path.nil.comp
          ((rightPath.reverse.comp (negativeArrow b).toPath).comp
            ((positiveArrow (Q := Q) a).toPath.comp leftPath.reverse)) :=
        (Quiver.Path.nil_comp _).symm
  let firstRight : Word R :=
    append R SR (negativeArrow b) hvalidRight
  have hvalidRightSecond : IsString R
      (firstRight.path.comp (positiveArrow (Q := Q) a).toPath) := by
    apply IsString.of_contiguousSubpath R W.reverse.isString
    refine ⟨Quiver.Path.nil, leftPath.reverse, ?_⟩
    change fullPath.reverse = Quiver.Path.nil.comp
      (((rightPath.reverse.comp (negativeArrow b).toPath).comp
        (positiveArrow (Q := Q) a).toPath).comp leftPath.reverse)
    calc
      fullPath.reverse = rightPath.reverse.comp
          ((negativeArrow b).toPath.comp
            ((positiveArrow (Q := Q) a).toPath.comp leftPath.reverse)) :=
        hfullReverse
      _ = ((rightPath.reverse.comp (negativeArrow b).toPath).comp
          (positiveArrow (Q := Q) a).toPath).comp leftPath.reverse := by
        simp only [Quiver.Path.comp_assoc]
      _ = Quiver.Path.nil.comp
          (((rightPath.reverse.comp (negativeArrow b).toPath).comp
            (positiveArrow (Q := Q) a).toPath).comp leftPath.reverse) :=
        (Quiver.Path.nil_comp _).symm
  let secondRight : Word R :=
    append R firstRight (positiveArrow (Q := Q) a) hvalidRightSecond
  have htailRightFull :
      IsString R (secondRight.path.comp leftPath.reverse) := by
    change IsString R
      (((rightPath.reverse.comp (negativeArrow b).toPath).comp
        (positiveArrow (Q := Q) a).toPath).comp leftPath.reverse)
    have hreassoc :
        ((rightPath.reverse.comp (negativeArrow b).toPath).comp
            (positiveArrow (Q := Q) a).toPath).comp leftPath.reverse =
          fullPath.reverse := by
      rw [hfullReverse]
      simp only [Quiver.Path.comp_assoc]
    rw [hreassoc]
    exact W.reverse.isString
  let tailRightRest0 := Classical.choice
    (rightExtension_of_comp_nonempty secondRight.path leftPath.reverse
      secondRight.isString htailRightFull)
  have htailRightTarget :
      ofStringPath (secondRight.path.comp leftPath.reverse)
          htailRightFull = W.reverse := by
    apply Word.ext
    · rfl
    · rfl
    · change secondRight.path.comp leftPath.reverse ≍ fullPath.reverse
      have hsecondRightPath : secondRight.path =
          (rightPath.reverse.comp (negativeArrow b).toPath).comp
            (positiveArrow (Q := Q) a).toPath := rfl
      apply heq_of_eq
      calc
        secondRight.path.comp leftPath.reverse =
            ((rightPath.reverse.comp (negativeArrow b).toPath).comp
              (positiveArrow (Q := Q) a).toPath).comp leftPath.reverse :=
          congrArg (fun p ↦ p.comp leftPath.reverse) hsecondRightPath
        _ = fullPath.reverse := by
          rw [hfullReverse]
          simp only [Quiver.Path.comp_assoc]
  let tailRightRest : RightExtension secondRight W.reverse :=
    Eq.mp
      (congrArg
        (fun X : Word R ↦ RightExtension secondRight X) htailRightTarget)
      tailRightRest0
  let secondRightStep : RightExtension firstRight secondRight :=
    RightExtension.step
      (RightExtension.base : RightExtension firstRight firstRight)
      (positiveArrow (Q := Q) a) hvalidRightSecond
  let tailRight : RightExtension firstRight W.reverse :=
    secondRightStep.trans tailRightRest
  let negativeRight : NegativeBoundaryExtension SR W.reverse := {
    vertex := center
    arrow := b
    valid := hvalidRight
    tail := tailRight }
  let right : LeftNegativeBoundaryExtension S := {
    reverseResult := W.reverse
    extension := negativeRight }
  have hrightResult : right.result = W := reverse_reverse R W
  let left : NegativeBoundaryExtension L right.result :=
    Eq.mp
      (congrArg
        (fun X : Word R ↦ NegativeBoundaryExtension L X)
        hrightResult.symm)
      leftW
  have hLltW : L.length < W.length := by
    dsimp [L, W, fullPath, fullPrefix, firstPrefix,
      ofStringPath, Word.length]
    simp only [Quiver.Path.length_comp, Quiver.Path.length_cons]
    omega
  have hSltW : S.length < W.length := by
    dsimp [S, W, fullPath, fullPrefix, firstPrefix,
      ofStringPath, Word.length]
    simp only [Quiver.Path.length_comp, Quiver.Path.length_cons]
    omega
  have hrightLength := right.result_length
  rw [hrightResult] at hrightLength
  have hstart : 0 < right.steps := by omega
  have hend : L.length < right.steps + S.length := by omega
  have hnotW :=
    not_isUniserialObject_of_separated_negativeBoundaries
      right left hmono hstart hend
  have hWC : W = C := by
    apply Word.ext
    · rfl
    · rfl
    · exact heq_of_eq hpath.symm
  intro hC
  apply hnotW
  have hresultC : right.result = C := hrightResult.trans hWC
  exact IsUniserialObject.congr hC
    (eqToIso
      (congrArg
        (fun X : Word R ↦ X.finiteRightModule hmono) hresultC.symm))

/-- A literal finite string module whose word contains both signs is not
uniserial. -/
theorem not_isUniserialObject_of_mixed_signedPathSigns
    (C : Word R) (hmono : IsMonomial R)
    (hpositive : false ∈ signedPathSigns C.path)
    (hnegative : true ∈ signedPathSigns C.path) :
    ¬ IsUniserialObject (C.finiteRightModule hmono) := by
  obtain ⟨change⟩ :=
    adjacentSignChange_of_mem_signedPathSigns C.path hpositive hnegative
  rcases change with
    ⟨leftVertex, centerVertex, rightVertex, leftPath, earlier, later,
      rightPath, path_eq, sign_ne⟩
  cases earlier with
  | inl a =>
      cases later with
      | inl b => exact False.elim (sign_ne rfl)
      | inr b =>
          exact not_isUniserialObject_of_positive_negative_factorization
            C leftPath a b rightPath path_eq hmono
  | inr a =>
      cases later with
      | inl b =>
          exact not_isUniserialObject_of_negative_positive_factorization
            C leftPath a b rightPath path_eq hmono
      | inr b => exact False.elim (sign_ne rfl)

/-- A uniserial literal finite string has only one sign: it is a pure
positive or a pure negative endpoint word. -/
theorem isPurePositive_or_isPureNegative_of_isUniserialObject
    (hR : IsAdmissible R) (C : Word R) (hmono : IsMonomial R)
    (hC : IsUniserialObject (C.finiteRightModule hmono)) :
    C.IsPurePositive hR ∨ C.IsPureNegative hR := by
  by_contra hpure
  rw [not_or] at hpure
  have hpositive : false ∈ signedPathSigns C.path := by
    by_contra hfalse
    have hall : ∀ b ∈ signedPathSigns C.path, b = true := by
      intro b hb
      cases b
      · exact False.elim (hfalse hb)
      · rfl
    have hsigns : signedPathSigns C.path =
        List.replicate C.length true := by
      have hrep := (List.eq_replicate_length).2 hall
      change signedPathSigns C.path =
        List.replicate C.path.length true
      rw [signedPathSigns_length] at hrep
      exact hrep
    exact hpure.2
      ((isPureNegative_iff_signedPathSigns_eq hR C).2 hsigns)
  have hnegative : true ∈ signedPathSigns C.path := by
    by_contra htrue
    have hall : ∀ b ∈ signedPathSigns C.path, b = false := by
      intro b hb
      cases b
      · rfl
      · exact False.elim (htrue hb)
    have hsigns : signedPathSigns C.path =
        List.replicate C.length false := by
      have hrep := (List.eq_replicate_length).2 hall
      change signedPathSigns C.path =
        List.replicate C.path.length false
      rw [signedPathSigns_length] at hrep
      exact hrep
    exact hpure.1
      ((isPurePositive_iff_signedPathSigns_eq hR C).2 hsigns)
  exact (C.not_isUniserialObject_of_mixed_signedPathSigns hmono
    hpositive hnegative) hC

end MagnitudeConjecture.BoundQuiver.StringWord.Word
