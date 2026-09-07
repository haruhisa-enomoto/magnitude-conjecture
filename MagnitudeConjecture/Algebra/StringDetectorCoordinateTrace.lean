import MagnitudeConjecture.Algebra.StringDetectorCoordinateSubspace
import MagnitudeConjecture.Algebra.StringGraphComponentConvexity
import MagnitudeConjecture.Algebra.StringReducedReverse

/-!
# Tracing detector coordinates through a literal string

A basis coordinate which survives the difference between two transported
coordinate subspaces cannot arise from a kernel contribution at an inverse
letter: such a contribution belongs to both transports.  It therefore has a
unique predecessor at every signed letter.  Iterating this observation turns
a surviving detector coordinate into a literal occurrence of the detector
word in the evaluated string.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A signed arrow of one word is realized by adjacent positions of another
word, respecting the signed direction. -/
def SignedArrowPositionStep (D : Word R) {x y : Q}
    (e : SignedArrow x y) (i : D.PositionAt x) (j : D.PositionAt y) : Prop :=
  match e with
  | Sum.inl a => D.ArrowStep a i j
  | Sum.inr a => D.ArrowStep a j i

/-- The signed formulation says directly that the target position is one
letter forward or the source position is one reversed letter forward. -/
theorem signedArrowPositionStep_iff (D : Word R) {x y : Q}
    (e : SignedArrow x y) (i : D.PositionAt x) (j : D.PositionAt y) :
    D.SignedArrowPositionStep e i j ↔
      j.1 = i.1.comp e.toPath ∨
        i.1 = j.1.comp (Quiver.reverse e).toPath := by
  cases e with
  | inl a => rfl
  | inr a =>
      change
        (i.1 = j.1.comp (positiveArrow a).toPath ∨
            j.1 = i.1.comp (negativeArrow a).toPath) ↔ _
      constructor <;> intro h <;> rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h

/-- A realized signed arrow changes the word-position index by one. -/
theorem SignedArrowPositionStep.index (D : Word R) {x y : Q}
    {e : SignedArrow x y} {i : D.PositionAt x} {j : D.PositionAt y}
    (hstep : D.SignedArrowPositionStep e i j) :
    j.index = i.index + 1 ∨ i.index = j.index + 1 := by
  cases e with
  | inl a => exact ArrowStep.index D a i j hstep
  | inr a =>
      rcases ArrowStep.index D a j i hstep with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- A complete signed path is realized by a consecutive position walk in a
literal string word. -/
def SignedPathPositionReach (D : Word R) :
    {x y : Q} → SignedPath x y → D.PositionAt x → D.PositionAt y → Prop
  | _, _, Quiver.Path.nil, i, j => i = j
  | _, _, Quiver.Path.cons p e, i, l =>
      ∃ j, D.SignedPathPositionReach p i j ∧
        D.SignedArrowPositionStep e j l

@[simp]
theorem signedPathPositionReach_nil (D : Word R) {x : Q}
    (i j : D.PositionAt x) :
    D.SignedPathPositionReach (Quiver.Path.nil : SignedPath x x) i j ↔
      i = j := by
  simp [SignedPathPositionReach]

@[simp]
theorem signedPathPositionReach_cons (D : Word R)
    {x y z : Q} (p : SignedPath x y) (e : SignedArrow y z)
    (i : D.PositionAt x) (l : D.PositionAt z) :
    D.SignedPathPositionReach (p.cons e) i l ↔
      ∃ j, D.SignedPathPositionReach p i j ∧
        D.SignedArrowPositionStep e j l := by
  simp [SignedPathPositionReach]

/-- A basis coordinate surviving the difference of two one-arrow transports
has a predecessor which survives the original difference. -/
theorem exists_positionStep_of_single_mem_signedArrowSubspace_not_mem
    (D : Word R) (hmono : IsMonomial R)
    {x y : Q} (e : SignedArrow x y)
    {U V : Submodule k (D.Space x)}
    (hV : D.IsCoordinateSubspace V)
    (j : D.PositionAt y)
    (hjV : Finsupp.single j (1 : k) ∈
      signedArrowSubspace (D.rightModule hmono) e V)
    (hjU : Finsupp.single j (1 : k) ∉
      signedArrowSubspace (D.rightModule hmono) e U) :
    ∃ i : D.PositionAt x,
      D.SignedArrowPositionStep e i j ∧
        Finsupp.single i (1 : k) ∈ V ∧
        Finsupp.single i (1 : k) ∉ U := by
  classical
  cases e with
  | inl a =>
      simp only [signedArrowSubspace] at hjV hjU
      rw [D.moduleArrowMap_rightModule hmono a] at hjV hjU
      change Finsupp.single j (1 : k) ∈ V.map (D.arrowLinearMap a) at hjV
      change Finsupp.single j (1 : k) ∉ U.map (D.arrowLinearMap a) at hjU
      rcases hjV with ⟨w, hwV, hmap⟩
      change D.arrowLinearMap a w = Finsupp.single j (1 : k) at hmap
      have hexists : ∃ i : D.PositionAt x, D.ArrowStep a i j := by
        by_contra hnone
        have hzero := D.arrowLinearMap_apply_eq_zero_of_not_exists_source
          a w j hnone
        have hvalue := congrArg (fun z : D.Space y ↦ z j) hmap
        rw [hzero, Finsupp.single_eq_same] at hvalue
        exact one_ne_zero hvalue.symm
      let i := Classical.choose hexists
      have hij : D.ArrowStep a i j := Classical.choose_spec hexists
      have hvalue := congrArg (fun z : D.Space y ↦ z j) hmap
      rw [D.arrowLinearMap_apply_of_step a w i j hij,
        Finsupp.single_eq_same] at hvalue
      have hiV : Finsupp.single i (1 : k) ∈ V := by
        simpa only [hvalue] using hV w hwV i
      refine ⟨i, hij, hiV, ?_⟩
      intro hiU
      apply hjU
      refine ⟨Finsupp.single i (1 : k), hiU, ?_⟩
      exact D.arrowLinearMap_single_one_of_step a i j hij
  | inr a =>
      simp only [signedArrowSubspace] at hjV hjU
      rw [D.moduleArrowMap_rightModule hmono a] at hjV hjU
      change D.arrowLinearMap a (Finsupp.single j (1 : k)) ∈ V at hjV
      change D.arrowLinearMap a (Finsupp.single j (1 : k)) ∉ U at hjU
      have hexists : ∃ i : D.PositionAt x, D.ArrowStep a j i := by
        by_contra hnone
        have hzero := D.arrowOnBasis_eq_zero_of_not_exists a j hnone
        apply hjU
        rw [D.arrowLinearMap_single, hzero, smul_zero]
        exact U.zero_mem
      let i := Classical.choose hexists
      have hij : D.ArrowStep a j i := Classical.choose_spec hexists
      have himage : D.arrowLinearMap a (Finsupp.single j (1 : k)) =
          Finsupp.single i (1 : k) :=
        D.arrowLinearMap_single_one_of_step a j i hij
      refine ⟨i, hij, ?_, ?_⟩
      · rw [← himage]
        exact hjV
      · intro hiU
        apply hjU
        rw [himage]
        exact hiU

/-- A basis coordinate surviving the difference of two signed-path
transports traces back to a source basis coordinate surviving the original
difference. -/
theorem exists_positionReach_of_single_mem_signedPathSubspace_not_mem
    (D : Word R) (hmono : IsMonomial R) :
    ∀ {x y : Q} (p : SignedPath x y)
      {U V : Submodule k (D.Space x)},
      D.IsCoordinateSubspace V →
        ∀ (j : D.PositionAt y),
          Finsupp.single j (1 : k) ∈
              signedPathSubspace (D.rightModule hmono) p V →
            Finsupp.single j (1 : k) ∉
              signedPathSubspace (D.rightModule hmono) p U →
            ∃ i : D.PositionAt x,
              D.SignedPathPositionReach p i j ∧
                Finsupp.single i (1 : k) ∈ V ∧
                Finsupp.single i (1 : k) ∉ U := by
  intro x y p
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
      cases p with
      | nil =>
          intro U V hV j hjV hjU
          rw [signedPathSubspace_nil] at hjV hjU
          exact ⟨j, (D.signedPathPositionReach_nil j j).2 rfl, hjV, hjU⟩
      | @cons y z p e =>
          change Q at y
          intro U V hV l hlV hlU
          rw [signedPathSubspace_cons] at hlV hlU
          have htransportCoordinate : D.IsCoordinateSubspace
              (signedPathSubspace (D.rightModule hmono) p V) := by
            intro w hw i
            exact D.signedPathSubspace_coordinatePart hmono p hV w hw i
          rcases D.exists_positionStep_of_single_mem_signedArrowSubspace_not_mem
              hmono e htransportCoordinate l hlV hlU with
            ⟨j, hstep, hjV, hjU⟩
          have hlt : p.length < n := by
            simp only [Quiver.Path.length_cons] at hlength
            omega
          rcases ih p.length hlt p rfl hV j hjV hjU with
            ⟨i, hreach, hiV, hiU⟩
          exact ⟨i, (D.signedPathPositionReach_cons p e i l).2
            ⟨j, hreach, hstep⟩, hiV, hiU⟩

private theorem morphismCoefficientPosition_eqvGen_source_of_positionReach
    (C D : Word R) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) C.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x C.target)
      (hpq : C.path = p.comp q)
      {i : D.PositionAt C.source} {j : D.PositionAt x},
      D.SignedPathPositionReach p i j →
        Relation.EqvGen (C.MorphismCoefficientStep D)
          (⟨x, (⟨p, q, hpq⟩ : C.PositionAt x), j⟩ :
            C.MorphismCoefficientPosition D)
          ⟨C.source, C.sourcePosition, i⟩ := by
  intro x p
  induction p with
  | nil =>
      intro q hpq i j hreach
      have hij : i = j := (D.signedPathPositionReach_nil i j).1 hreach
      subst j
      have hposition :
          (⟨Quiver.Path.nil, q, hpq⟩ : C.PositionAt C.source) =
            C.sourcePosition := by
        apply PositionAt.ext_index
        rfl
      rw [hposition]
      exact Relation.EqvGen.refl _
  | @cons y z p e ih =>
      intro q hpq i j hreach
      rcases (D.signedPathPositionReach_cons p e i j).1 hreach with
        ⟨jprev, hprevReach, hlast⟩
      have hprefix : C.path = p.comp (e.toPath.comp q) := by
        calc
          C.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : C.PositionAt y :=
        ⟨p, e.toPath.comp q, hprefix⟩
      have hprev : Relation.EqvGen (C.MorphismCoefficientStep D)
          (⟨y, iprev, jprev⟩ : C.MorphismCoefficientPosition D)
          ⟨C.source, C.sourcePosition, i⟩ :=
        ih (e.toPath.comp q) hprefix hprevReach
      rcases e with a | a
      · let icurr : C.PositionAt z :=
          ⟨p.cons (Sum.inl a), q, hpq⟩
        have hstepC : C.ArrowStep a iprev icurr := Or.inl rfl
        have hstepD : D.ArrowStep a jprev j := by
          exact hlast
        have hedge : C.MorphismCoefficientStep D
            (⟨y, iprev, jprev⟩ : C.MorphismCoefficientPosition D)
            ⟨z, icurr, j⟩ :=
          MorphismCoefficientStep.ofArrow a iprev icurr jprev j
            hstepC hstepD
        change Relation.EqvGen (C.MorphismCoefficientStep D)
          (⟨z, icurr, j⟩ : C.MorphismCoefficientPosition D) _
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hedge)) hprev
      · let icurr : C.PositionAt z :=
          ⟨p.cons (Sum.inr a), q, hpq⟩
        have hstepC : C.ArrowStep a icurr iprev := Or.inr rfl
        have hstepD : D.ArrowStep a j jprev := by
          exact hlast
        have hedge : C.MorphismCoefficientStep D
            (⟨z, icurr, j⟩ : C.MorphismCoefficientPosition D)
            ⟨y, iprev, jprev⟩ :=
          MorphismCoefficientStep.ofArrow a icurr iprev j jprev
            hstepC hstepD
        change Relation.EqvGen (C.MorphismCoefficientStep D)
          (⟨z, icurr, j⟩ : C.MorphismCoefficientPosition D) _
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ hedge) hprev

/-- A realized complete word path places its two endpoint pairs in one
matched-coefficient component. -/
theorem morphismCoefficientPosition_eqvGen_of_positionReach
    (C D : Word R) {i : D.PositionAt C.source}
    {j : D.PositionAt C.target}
    (hreach : D.SignedPathPositionReach C.path i j) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨C.source, C.sourcePosition, i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨C.target, C.targetPosition, j⟩ := by
  have hreverse := C.morphismCoefficientPosition_eqvGen_source_of_positionReach
    D C.path Quiver.Path.nil (by simp) hreach
  have htarget :
      (⟨C.path, Quiver.Path.nil, by simp⟩ : C.PositionAt C.target) =
        C.targetPosition := by
    apply PositionAt.ext_index
    rfl
  rw [htarget] at hreverse
  exact hreverse.symm

/-- A realized complete word has constant position slope in the evaluated
literal string. -/
theorem positionReach_endpointSlope (C D : Word R)
    {i : D.PositionAt C.source} {j : D.PositionAt C.target}
    (hreach : D.SignedPathPositionReach C.path i j) :
    j.index = i.index + C.length ∨
      i.index = j.index + C.length := by
  let first : C.MorphismCoefficientPosition D :=
    ⟨C.source, C.sourcePosition, i⟩
  let last : C.MorphismCoefficientPosition D :=
    ⟨C.target, C.targetPosition, j⟩
  have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
      first last :=
    C.morphismCoefficientPosition_eqvGen_of_positionReach D hreach
  have hslope :=
    C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le D
      hcomponent (by
        change C.sourcePosition.index ≤ C.targetPosition.index
        simp)
  change j.index = i.index + (C.length - 0) ∨
    i.index = j.index + (C.length - 0) at hslope
  simpa using hslope

/-- In the increasing slope, a realized signed path is literally the segment
between the two position prefixes. -/
theorem positionReach_prefix_eq_of_forward (D : Word R) :
    ∀ {x y : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x y), IsString R p →
      ∀ (i : D.PositionAt (show Q from x))
        (j : D.PositionAt (show Q from y)),
        D.SignedPathPositionReach p i j →
          j.index = i.index + p.length →
            j.1 = i.1.comp p := by
  intro x y p
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil =>
        intro _ i j hreach _
        have hij : i = j := (D.signedPathPositionReach_nil i j).1 hreach
        subst j
        simp
    | @cons y z p e =>
      intro hstring i l hreach hslope
      have hn : p.length + 1 = n := by
        simpa only [Quiver.Path.length_cons] using hlength
      rcases (D.signedPathPositionReach_cons p e i l).1 hreach with
        ⟨j, hprev, hlast⟩
      have hpSub : IsContiguousSubpath p (p.cons e) := by
        refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
        simp only [Quiver.Path.nil_comp, Quiver.Path.comp_toPath_eq_cons]
      have hpString : IsString R p :=
        IsString.of_contiguousSubpath R hstring hpSub
      let prefixWord : Word R :=
        { source := (show Q from x)
          target := (show Q from y)
          path := p
          isString := hpString }
      have hprevSlope := prefixWord.positionReach_endpointSlope D hprev
      change j.index = i.index + p.length ∨
        i.index = j.index + p.length at hprevSlope
      have hlastIndex := hlast.index D
      have hprevForward : j.index = i.index + p.length := by
        rcases hprevSlope with hforward | hreverse <;>
          rcases hlastIndex with hlastForward | hlastReverse <;>
          omega
      have hlastForward : l.index = j.index + 1 := by
        rcases hlastIndex with hlastForward | hlastReverse
        · exact hlastForward
        · omega
      have hlt : p.length < n := by
        omega
      have hprevEq := ih p.length hlt p rfl hpString i j hprev hprevForward
      rcases (D.signedArrowPositionStep_iff e j l).1 hlast with
        hforward | hreverse
      · calc
          l.1 = j.1.comp e.toPath := hforward
          _ = (i.1.comp p).comp e.toPath := by rw [hprevEq]
          _ = i.1.comp (p.cons e) := by
            simp only [← Quiver.Path.comp_toPath_eq_cons,
              Quiver.Path.comp_assoc]
      · have hlength := congrArg Quiver.Path.length hreverse
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change j.index = l.index + 1 at hlength
        omega

/-- In the decreasing slope, the source prefix is the target prefix followed
by the reverse of the realized signed path. -/
theorem positionReach_prefix_eq_of_reverse (D : Word R) :
    ∀ {x y : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x y), IsString R p →
      ∀ (i : D.PositionAt (show Q from x))
        (j : D.PositionAt (show Q from y)),
        D.SignedPathPositionReach p i j →
          i.index = j.index + p.length →
            i.1 = j.1.comp p.reverse := by
  intro x y p
  induction hlength : p.length using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil =>
        intro _ i j hreach _
        have hij : i = j := (D.signedPathPositionReach_nil i j).1 hreach
        subst j
        simp
    | @cons y z p e =>
      intro hstring i l hreach hslope
      have hn : p.length + 1 = n := by
        simpa only [Quiver.Path.length_cons] using hlength
      rcases (D.signedPathPositionReach_cons p e i l).1 hreach with
        ⟨j, hprev, hlast⟩
      have hpSub : IsContiguousSubpath p (p.cons e) := by
        refine ⟨Quiver.Path.nil, e.toPath, ?_⟩
        simp only [Quiver.Path.nil_comp, Quiver.Path.comp_toPath_eq_cons]
      have hpString : IsString R p :=
        IsString.of_contiguousSubpath R hstring hpSub
      let prefixWord : Word R :=
        { source := (show Q from x)
          target := (show Q from y)
          path := p
          isString := hpString }
      have hprevSlope := prefixWord.positionReach_endpointSlope D hprev
      change j.index = i.index + p.length ∨
        i.index = j.index + p.length at hprevSlope
      have hlastIndex := hlast.index D
      have hprevReverse : i.index = j.index + p.length := by
        rcases hprevSlope with hforward | hreverse <;>
          rcases hlastIndex with hlastForward | hlastReverse <;>
          omega
      have hlastReverse : j.index = l.index + 1 := by
        rcases hlastIndex with hlastForward | hlastReverse
        · omega
        · exact hlastReverse
      have hlt : p.length < n := by
        omega
      have hprevEq := ih p.length hlt p rfl hpString i j hprev hprevReverse
      rcases (D.signedArrowPositionStep_iff e j l).1 hlast with
        hforward | hreverse
      · have hlength := congrArg Quiver.Path.length hforward
        simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          at hlength
        change l.index = j.index + 1 at hlength
        omega
      · calc
          i.1 = j.1.comp p.reverse := hprevEq
          _ = (l.1.comp (Quiver.reverse e).toPath).comp p.reverse := by
            rw [hreverse]
          _ = l.1.comp ((Quiver.reverse e).toPath.comp p.reverse) :=
            Quiver.Path.comp_assoc _ _ _
          _ = l.1.comp (p.cons e).reverse := by
            simp only [← Quiver.Path.comp_toPath_eq_cons,
              Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath]

/-- A complete occurrence of a reduced word inside itself can only end at
the canonical target position.  The decreasing slope would make the whole
word a reverse palindrome, which reducedness excludes unless its length is
zero. -/
theorem positionReach_self_eq_targetPosition (C : Word R)
    {i : C.PositionAt C.source} {j : C.PositionAt C.target}
    (hreach : C.SignedPathPositionReach C.path i j) :
    j = C.targetPosition := by
  rcases C.positionReach_endpointSlope C hreach with hforward | hreverse
  · apply PositionAt.ext_index
    rw [C.targetPosition_index]
    have hiNonnegative : 0 ≤ i.index := Nat.zero_le _
    have hjBound := j.index_le
    omega
  · have hiLength : i.index = C.length := by
      have hiBound := i.index_le
      omega
    have hjZero : j.index = 0 := by omega
    have hsourceTarget : C.source = C.target :=
      i.eq_target_of_index_eq_length hiLength
    rcases C with ⟨source, target, path, hstring⟩
    change source = target at hsourceTarget
    cases hsourceTarget
    let C' : Word R :=
      { source := source
        target := source
        path := path
        isString := hstring }
    have hiTarget : i = C'.targetPosition :=
      PositionAt.ext_index hiLength
    have hjSource : j = C'.sourcePosition :=
      PositionAt.ext_index (hjZero.trans C'.sourcePosition_index.symm)
    subst i
    subst j
    have hpathReverse := C'.positionReach_prefix_eq_of_reverse
      C'.path C'.isString C'.targetPosition C'.sourcePosition
        hreach hreverse
    have hpathEq : C'.path = C'.path.reverse := by
      simpa only [sourcePosition, targetPosition, Quiver.Path.nil_comp]
        using hpathReverse
    have hzero := IsReduced.length_eq_zero_of_eq_reverse
      C'.path C'.isString.1 hpathEq
    apply PositionAt.ext_index
    rw [C'.targetPosition_index, C'.sourcePosition_index]
    exact hzero.symm

end MagnitudeConjecture.BoundQuiver.StringWord.Word
