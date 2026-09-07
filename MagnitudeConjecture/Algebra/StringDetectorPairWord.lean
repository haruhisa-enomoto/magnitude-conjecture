import MagnitudeConjecture.Algebra.StringDetectorGrid
import MagnitudeConjecture.Algebra.StringReverse

/-!
# Complete words represented by endpoint-word pairs

Ringel's finite grid is indexed by pairs of endpoint words with opposite
polarizations.  This file relates a nonzero pair layer to the complete string
obtained by traversing the right word and then the inverse of the left word.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}

/-- Transport along an ordinary positive path is direct image under the
corresponding module path map. -/
theorem signedPathSubspace_positivePath
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (p : Quiver.Path x y)
    (U : Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations x)))) :
    signedPathSubspace N (positivePath p) U =
      U.map (modulePathMap N p).hom := by
  induction p with
  | nil => simp
  | @cons y z p a ih =>
      rw [positivePath_cons, signedPathSubspace_comp, ih,
        positivePath_toPath, signedPathSubspace_toPath,
        signedArrowSubspace_positive,
        modulePathMap_cons]
      rw [← Submodule.map_comp]
      rfl

/-- Transport along the inverse of an ordinary positive path is inverse image
under the corresponding module path map. -/
theorem signedPathSubspace_positivePath_reverse
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    {x y : Q} (p : Quiver.Path x y)
    (U : Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations y)))) :
    signedPathSubspace N (positivePath p).reverse U =
      U.comap (modulePathMap N p).hom := by
  induction p with
  | nil => simp
  | @cons y z p a ih =>
      rw [positivePath_cons, Quiver.Path.reverse_comp,
        positivePath_toPath,
        Quiver.Path.reverse_toPath]
      change signedPathSubspace N
          ((negativeArrow a).toPath.comp (positivePath p).reverse) U = _
      rw [signedPathSubspace_comp, signedPathSubspace_toPath,
        signedArrowSubspace_negative, ih, modulePathMap_cons]
      rw [← Submodule.comap_comp]
      rfl

/-- The image transported along the first half of a zero ordinary path lies
in the inverse image of every subspace along the second half. -/
theorem signedPathSubspace_positivePath_le_reverse_of_pathMap_comp_eq_zero
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {w x y : Q} (p : Quiver.Path w x) (q : Quiver.Path x y)
    (U : Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations w))))
    (V : Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations y))))
    (hzero : pathMap P.toPresentation.relations (p.comp q) = 0) :
    signedPathSubspace N (positivePath p) U ≤
      signedPathSubspace N (positivePath q).reverse V := by
  rw [signedPathSubspace_positivePath,
    signedPathSubspace_positivePath_reverse]
  rintro z ⟨v, hv, rfl⟩
  change modulePathMap N q (modulePathMap N p v) ∈ V
  have hmorphism : modulePathMap N p ≫ modulePathMap N q = 0 := by
    rw [← modulePathMap_comp]
    unfold modulePathMap
    rw [hzero]
    exact N.map_zero _ _
  have happly := congrArg (fun f ↦ f.hom v) hmorphism
  change modulePathMap N q (modulePathMap N p v) = 0 at happly
  rw [happly]
  exact Submodule.zero_mem V

/-- Transporting the whole space through two positive path pieces whose
composite is a relation gives the zero subspace. -/
theorem signedPathSubspace_positivePath_comp_top_eq_bot_of_pathMap_comp_eq_zero
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {w x y : Q} (p : Quiver.Path w x) (q : Quiver.Path x y)
    (hzero : pathMap P.toPresentation.relations (p.comp q) = 0) :
    signedPathSubspace N (positivePath q)
        (signedPathSubspace N (positivePath p) ⊤) = ⊥ := by
  rw [signedPathSubspace_positivePath,
    signedPathSubspace_positivePath, ← Submodule.map_comp]
  have hmorphism : modulePathMap N p ≫ modulePathMap N q = 0 := by
    rw [← modulePathMap_comp]
    unfold modulePathMap
    rw [hzero]
    exact N.map_zero _ _
  have hlinear := congrArg (fun f ↦ f.hom) hmorphism
  change (modulePathMap N q).hom.comp (modulePathMap N p).hom = 0 at hlinear
  rw [hlinear]
  simp

/-- Dually, inverse transport through the first piece of a zero positive
composite sends the kernel boundary of the second piece to the whole space. -/
theorem signedPathSubspace_positivePath_reverse_comap_bot_eq_top_of_pathMap_comp_eq_zero
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {w x y : Q} (p : Quiver.Path w x) (q : Quiver.Path x y)
    (hzero : pathMap P.toPresentation.relations (p.comp q) = 0) :
    signedPathSubspace N (positivePath p).reverse
        ((⊥ : Submodule k (N.obj (Opposite.op
          (obj P.toPresentation.relations y)))).comap
            (modulePathMap N q).hom) = ⊤ := by
  rw [signedPathSubspace_positivePath_reverse, ← Submodule.comap_comp]
  have hmorphism : modulePathMap N p ≫ modulePathMap N q = 0 := by
    rw [← modulePathMap_comp]
    unfold modulePathMap
    rw [hzero]
    exact N.map_zero _ _
  have hlinear := congrArg (fun f ↦ f.hom) hmorphism
  change (modulePathMap N q).hom.comp (modulePathMap N p).hom = 0 at hlinear
  rw [hlinear]
  simp

/-- If relation avoidance fails only after two relation-avoiding signed paths
are joined, a killed positive ordinary path crosses the join with a nonempty
piece on each side. -/
theorem exists_positive_relation_crossing_comp
    {a x b : Q} (left : SignedPath a x) (right : SignedPath x b)
    (hleft : AvoidsRelations P.toPresentation.relations left)
    (hright : AvoidsRelations P.toPresentation.relations right)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (left.comp right)) :
    ∃ (c d : Q) (p : Quiver.Path c x) (q : Quiver.Path x d)
        (before : SignedPath a c) (after : SignedPath d b),
      left = before.comp (positivePath p) ∧
        right = (positivePath q).comp after ∧
        0 < p.length ∧ 0 < q.length ∧
        pathMap P.toPresentation.relations (p.comp q) = 0 := by
  unfold AvoidsRelations at hnot
  push Not at hnot
  obtain ⟨c, d, r, hsub, hrzero⟩ := hnot
  rcases hsub with ⟨before, after, hfactor⟩
  have htotal : before.comp ((positivePath r).comp after) =
      left.comp right := hfactor.symm
  have hnotLeft : ¬ IsContiguousSubpath (positivePath r) left := by
    intro hrleft
    exact (hleft r hrleft) hrzero
  have hnotRight : ¬ IsContiguousSubpath (positivePath r) right := by
    intro hrright
    exact (hright r hrright) hrzero
  have hbeforeLt : before.length < left.length := by
    by_contra hnotlt
    have hle : left.length ≤ before.length := Nat.le_of_not_gt hnotlt
    obtain ⟨tail, hbefore⟩ :=
      path_exists_comp_of_comp_eq_comp_of_length_le hfactor hle
    apply hnotRight
    refine ⟨tail, after, ?_⟩
    apply Quiver.Path.comp_injective_right left
    calc
      left.comp right = before.comp ((positivePath r).comp after) :=
        hfactor
      _ = (left.comp tail).comp ((positivePath r).comp after) := by
        rw [hbefore]
      _ = left.comp (tail.comp ((positivePath r).comp after)) :=
        Quiver.Path.comp_assoc _ _ _
  have hcrosses : left.length < before.length + r.length := by
    by_contra hnotlt
    have hle : (before.comp (positivePath r)).length ≤ left.length := by
      simp only [Quiver.Path.length_comp, positivePath_length]
      exact Nat.le_of_not_gt hnotlt
    have htotal' : (before.comp (positivePath r)).comp after =
        left.comp right := by
      simpa only [Quiver.Path.comp_assoc] using htotal
    obtain ⟨tail, hleftFactor⟩ :=
      path_exists_comp_of_comp_eq_comp_of_length_le htotal' hle
    apply hnotLeft
    refine ⟨before, tail, ?_⟩
    simpa only [Quiver.Path.comp_assoc] using hleftFactor
  let n := left.length - before.length
  have hnle : n ≤ r.length := by
    dsimp only [n]
    omega
  obtain ⟨middle, p, q, hr, hpLength⟩ :=
    r.exists_eq_comp_of_le_length hnle
  have hprefixLength : (before.comp (positivePath p)).length =
      left.length := by
    simp only [Quiver.Path.length_comp, positivePath_length, hpLength]
    dsimp only [n]
    omega
  have hdecomp : (before.comp (positivePath p)).comp
      ((positivePath q).comp after) = left.comp right := by
    calc
      (before.comp (positivePath p)).comp
          ((positivePath q).comp after) =
        before.comp (((positivePath p).comp
          (positivePath q)).comp after) := by
            simp only [Quiver.Path.comp_assoc]
      _ = before.comp ((positivePath (p.comp q)).comp after) := by
        rw [positivePath_comp]
      _ = before.comp ((positivePath r).comp after) := by rw [hr]
      _ = left.comp right := htotal
  obtain ⟨hmiddle, hprefix, hsuffix⟩ :=
    path_comp_decomposition_unique hdecomp hprefixLength
  cases hmiddle
  have hrLength : r.length = p.length + q.length := by
    rw [hr, Quiver.Path.length_comp]
  have hpPos : 0 < p.length := by
    rw [hpLength]
    dsimp only [n]
    omega
  have hqPos : 0 < q.length := by
    omega
  refine ⟨c, d, p, q, before, after, hprefix.eq.symm,
    hsuffix.eq.symm, hpPos, hqPos, ?_⟩
  rw [← hr]
  exact hrzero

namespace EndpointWord

variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- Prefixing a path to a nonempty signed suffix does not change its
intrinsic target sign. -/
theorem signedPathTargetSign_comp_of_right_length_pos
    {x y z : Q} (p : SignedPath x y) (q : SignedPath y z)
    (hq : 0 < q.length) :
    signedPathTargetSign S (p.comp q) = signedPathTargetSign S q := by
  cases q with
  | nil => simp at hq
  | cons q e => simp only [Quiver.Path.comp_cons,
      signedPathTargetSign_cons]

/-- A zero-length suffix contributes no target sign to a composite. -/
theorem signedPathTargetSign_comp_of_right_length_zero
    {x y z : Q} (p : SignedPath x y) (q : SignedPath y z)
    (hq : q.length = 0) :
    signedPathTargetSign S (p.comp q) = signedPathTargetSign S p := by
  cases q with
  | nil => rfl
  | cons q e => simp at hq

/-- Appending a suffix to a nonempty signed path does not change its
intrinsic source sign. -/
theorem signedPathSourceSign_comp_of_left_length_pos
    {x y z : Q} (p : SignedPath x y) (q : SignedPath y z)
    (hp : 0 < p.length) :
    signedPathSourceSign S (p.comp q) = signedPathSourceSign S p := by
  unfold signedPathSourceSign
  rw [Quiver.Path.reverse_comp,
    signedPathTargetSign_comp_of_right_length_pos]
  simpa only [length_reverse] using hp

/-- A zero-length prefix contributes no source sign to a composite. -/
theorem signedPathSourceSign_comp_of_left_length_zero
    {x y z : Q} (p : SignedPath x y) (q : SignedPath y z)
    (hp : p.length = 0) :
    signedPathSourceSign S (p.comp q) = signedPathSourceSign S q := by
  unfold signedPathSourceSign
  rw [Quiver.Path.reverse_comp,
    signedPathTargetSign_comp_of_right_length_zero]
  simpa only [length_reverse] using hp

/-- Once a path is nonempty, the fallback Boolean in its source-sign
convention is irrelevant. -/
theorem signedPathSourceSignOr_eq_of_length_pos
    {x y : Q} (p : SignedPath x y) (hp : 0 < p.length)
    (a b : Bool) :
    signedPathSourceSignOr S a p = signedPathSourceSignOr S b p := by
  unfold signedPathSourceSignOr signedPathSourceSign
  cases hreverse : p.reverse with
  | nil =>
      have hzero : p.length = 0 := by
        rw [← length_reverse p, hreverse]
        rfl
      omega
  | cons q e => rfl

/-- Once a path is nonempty, the fallback Boolean in its target-sign
convention is irrelevant. -/
theorem signedPathTargetSignOr_eq_of_length_pos
    {x y : Q} (p : SignedPath x y) (hp : 0 < p.length)
    (a b : Bool) :
    signedPathTargetSignOr S a p = signedPathTargetSignOr S b p := by
  cases p with
  | nil => simp at hp
  | cons q e => rfl

/-- A zero-length path uses exactly its prescribed source-sign fallback. -/
theorem signedPathSourceSignOr_eq_of_length_zero
    {x y : Q} (p : SignedPath x y) (hp : p.length = 0)
    (a : Bool) :
    signedPathSourceSignOr S a p = a := by
  unfold signedPathSourceSignOr signedPathSourceSign
  cases hreverse : p.reverse with
  | nil => rfl
  | cons q e =>
      have hpos : 0 < p.reverse.length := by rw [hreverse]; simp
      rw [length_reverse] at hpos
      omega

/-- A zero-length path uses exactly its prescribed target-sign fallback. -/
theorem signedPathTargetSignOr_eq_of_length_zero
    {x y : Q} (p : SignedPath x y) (hp : p.length = 0)
    (a : Bool) :
    signedPathTargetSignOr S a p = a := by
  cases p with
  | nil => rfl
  | cons q e => simp at hp

/-- The polarized trivial word at the source of an endpoint word whose source
sign agrees with that word.  Transporting its boundary filtration along the
word is the contextual filtration coming from a trivial outer endpoint. -/
def sourceVertex (C : EndpointWord S u₀ t) :
    EndpointWord S C.source (Bool.not C.sourceSign) :=
  EndpointWord.vertex P S C.source (Bool.not C.sourceSign)

@[simp]
theorem sourceVertex_path (C : EndpointWord S u₀ t) :
    C.sourceVertex.path = Quiver.Path.nil :=
  rfl

@[simp]
theorem sourceVertex_sourceSign (C : EndpointWord S u₀ t) :
    C.sourceVertex.sourceSign = C.sourceSign := by
  simp [sourceVertex]

/-- A positively oriented arrow with the boundary sign selected at the source
of `C` cannot cancel the first letter of `C`. -/
theorem isReduced_positiveArrow_comp_of_sourceSign
    (C : EndpointWord S u₀ t) {v : Q} (a : v ⟶ C.source)
    (hsign : C.sourceSign = Bool.not (S.targetSign a)) :
    IsReduced ((positiveArrow a).toPath.comp C.path) := by
  by_cases hzero : C.path.length = 0
  · apply isReduced_of_length_lt_two
    simp [hzero]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    obtain ⟨w, e, tail, htailLength, hpath⟩ :=
      C.path.eq_toPath_comp_of_length_eq_succ hn
    change Q at w
    have htailReduced : IsReduced (e.toPath.comp tail) := by
      rw [← hpath]
      exact C.isString.1
    have htwo : IsReduced
        ((positiveArrow a).toPath.comp e.toPath) := by
      cases e with
      | inl b =>
          exact Word.isReduced_positiveArrow_comp_positiveArrow a b
      | inr b =>
          apply Word.isReduced_positiveArrow_comp_negativeArrow_of_costar_ne
          intro hab
          have habSign := congrArg
            (S.atVertex C.source).targetSign hab
          change S.targetSign a = S.targetSign b at habSign
          have hCsource : C.sourceSign = S.targetSign b := by
            unfold EndpointWord.sourceSign signedPathSourceSignOr
            rw [hpath, signedPathSourceSign_toPath_comp]
            rfl
          have hself : S.targetSign a = Bool.not (S.targetSign a) :=
            habSign.trans (hCsource.symm.trans hsign)
          exact (Bool.not_eq_self (S.targetSign a)).mp hself.symm
    rw [hpath]
    exact isReduced_comp_of_overlap (positiveArrow a).toPath e.toPath tail
      (by simp) htwo htailReduced

/-- A formally inverse arrow with the inverse-boundary source sign likewise
cannot cancel the first letter of `C`. -/
theorem isReduced_negativeArrow_comp_of_sourceSign
    (C : EndpointWord S u₀ t) {v : Q} (a : C.source ⟶ v)
    (hsign : C.sourceSign = Bool.not (S.sourceSign a)) :
    IsReduced ((negativeArrow a).toPath.comp C.path) := by
  by_cases hzero : C.path.length = 0
  · apply isReduced_of_length_lt_two
    simp [hzero]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    obtain ⟨w, e, tail, htailLength, hpath⟩ :=
      C.path.eq_toPath_comp_of_length_eq_succ hn
    change Q at w
    have htailReduced : IsReduced (e.toPath.comp tail) := by
      rw [← hpath]
      exact C.isString.1
    have htwo : IsReduced
        ((negativeArrow a).toPath.comp e.toPath) := by
      cases e with
      | inl b =>
          apply Word.isReduced_negativeArrow_comp_positiveArrow_of_star_ne
          intro hab
          have habSign := congrArg
            (S.atVertex C.source).sourceSign hab
          change S.sourceSign a = S.sourceSign b at habSign
          have hCsource : C.sourceSign = S.sourceSign b := by
            unfold EndpointWord.sourceSign signedPathSourceSignOr
            rw [hpath, signedPathSourceSign_toPath_comp]
            rfl
          have hself : S.sourceSign a = Bool.not (S.sourceSign a) :=
            habSign.trans (hCsource.symm.trans hsign)
          exact (Bool.not_eq_self (S.sourceSign a)).mp hself.symm
      | inr b =>
          exact Word.isReduced_negativeArrow_comp_negativeArrow a b
    rw [hpath]
    exact isReduced_comp_of_overlap (negativeArrow a).toPath e.toPath tail
      (by simp) htwo htailReduced

/-- A negative source extension has a negative outer boundary, so its forward
orientation inherits relation avoidance from `C`. -/
theorem avoidsRelations_negativeArrow_comp
    (C : EndpointWord S u₀ t) {v : Q} (a : C.source ⟶ v) :
    AvoidsRelations P.toPresentation.relations
      ((negativeArrow a).toPath.comp C.path) := by
  have hnil : AvoidsRelations P.toPresentation.relations
      (Quiver.Path.nil : SignedPath v v) :=
    avoidsRelations_of_length_lt_two P.toPresentation.relations
      P.toPresentation.admissible _ (by simp)
  have hglue : AvoidsRelations P.toPresentation.relations
      ((Quiver.Path.nil : SignedPath v v).comp
        ((negativeArrow a).toPath.comp C.path)) :=
    avoidsRelations_comp_negativeArrow_comp
      (a := v) (b := v) (d := u₀) (x := C.source)
      P.toPresentation.relations (Quiver.Path.nil : SignedPath v v)
        a C.path hnil C.isString.2.1
  intro x y p hp
  apply hglue p
  simpa only [Quiver.Path.nil_comp] using hp

/-- Therefore a sign-compatible inverse source extension which is not a
string must fail by a monomial relation in the reversed orientation. -/
theorem not_avoidsRelations_reverse_negativeArrow_comp_of_not_isString
    (C : EndpointWord S u₀ t) {v : Q} (a : C.source ⟶ v)
    (hsign : C.sourceSign = Bool.not (S.sourceSign a))
    (hnot : ¬ IsString P.toPresentation.relations
      ((negativeArrow a).toPath.comp C.path)) :
    ¬ AvoidsRelations P.toPresentation.relations
      ((negativeArrow a).toPath.comp C.path).reverse := by
  intro havoids
  exact hnot ⟨isReduced_negativeArrow_comp_of_sourceSign C a hsign,
    avoidsRelations_negativeArrow_comp C a, havoids⟩

/-- Reversing a positive source extension places a negative arrow at the
outer boundary, so no new positive relation can occur there. -/
theorem avoidsRelations_reverse_positiveArrow_comp
    (C : EndpointWord S u₀ t) {v : Q} (a : v ⟶ C.source) :
    AvoidsRelations P.toPresentation.relations
      ((positiveArrow a).toPath.comp C.path).reverse := by
  have hnil : AvoidsRelations P.toPresentation.relations
      (Quiver.Path.nil : SignedPath v v) :=
    avoidsRelations_of_length_lt_two P.toPresentation.relations
      P.toPresentation.admissible _ (by simp)
  have hglue : AvoidsRelations P.toPresentation.relations
      (C.path.reverse.comp ((negativeArrow a).toPath.comp
        (Quiver.Path.nil : SignedPath v v))) :=
    avoidsRelations_comp_negativeArrow_comp
      (a := u₀) (b := C.source) (d := v) (x := v)
      P.toPresentation.relations C.path.reverse a
        (Quiver.Path.nil : SignedPath v v) C.isString.2.2 hnil
  rw [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    reverse_positiveArrow]
  change AvoidsRelations P.toPresentation.relations
    (C.path.reverse.comp (negativeArrow a).toPath)
  intro x y p hp
  apply hglue p
  simpa only [Quiver.Path.comp_nil] using hp

/-- Consequently, a sign-compatible positive source extension which is not a
string must fail by a forward monomial relation. -/
theorem not_avoidsRelations_positiveArrow_comp_of_not_isString
    (C : EndpointWord S u₀ t) {v : Q} (a : v ⟶ C.source)
    (hsign : C.sourceSign = Bool.not (S.targetSign a))
    (hnot : ¬ IsString P.toPresentation.relations
      ((positiveArrow a).toPath.comp C.path)) :
    ¬ AvoidsRelations P.toPresentation.relations
      ((positiveArrow a).toPath.comp C.path) := by
  intro havoids
  exact hnot ⟨isReduced_positiveArrow_comp_of_sourceSign C a hsign,
    havoids, avoidsRelations_reverse_positiveArrow_comp C a⟩

/-- If a compatible positive source arrow fails only because a relation
appears after it is attached to `C`, transporting its image along `C` gives
exactly the transported zero space. -/
theorem signedPathSubspace_map_top_eq_zeroSubspace_of_not_avoids_prepend
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t) {v : Q} (a : v ⟶ C.source)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      ((positiveArrow a).toPath.comp C.path)) :
    signedPathSubspace N C.path
        ((⊤ : Submodule k (N.obj (Opposite.op
          (obj P.toPresentation.relations v)))).map
            (moduleArrowMap N a).hom) = zeroSubspace N C := by
  have hleftAvoids : AvoidsRelations P.toPresentation.relations
      (positiveArrow a).toPath :=
    avoidsRelations_of_length_lt_two P.toPresentation.relations
      P.toPresentation.admissible _ (by simp)
  obtain ⟨c, d, p, q, before, after, hleft, hright, hp, hq, hzero⟩ :=
    exists_positive_relation_crossing_comp
      (positiveArrow a).toPath C.path hleftAvoids C.isString.2.1 hnot
  have hbeforeZero : before.length = 0 := by
    have hlength := congrArg Quiver.Path.length hleft
    simp only [Quiver.Path.length_toPath, Quiver.Path.length_comp,
      positivePath_length] at hlength
    omega
  have hsource := before.eq_of_length_zero hbeforeZero
  cases hsource
  have hbeforeNil := before.eq_nil_of_length_zero hbeforeZero
  subst before
  simp only [Quiver.Path.nil_comp] at hleft
  unfold zeroSubspace
  rw [← signedArrowSubspace_positive N a ⊤,
    ← signedPathSubspace_toPath N (positiveArrow a) ⊤]
  rw [← signedPathSubspace_comp, hleft, hright,
    signedPathSubspace_comp, signedPathSubspace_comp,
    signedPathSubspace_comp]
  rw [signedPathSubspace_positivePath_comp_top_eq_bot_of_pathMap_comp_eq_zero
    N p q hzero]
  rw [signedPathSubspace_positivePath]
  simp

/-- If a compatible inverse source arrow fails only because a relation
appears after reversal, transporting its kernel boundary along `C` gives
exactly the transported whole space. -/
theorem signedPathSubspace_comap_bot_eq_wholeSubspace_of_not_avoids_reverse_prepend
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (C : EndpointWord S u₀ t) {v : Q} (a : C.source ⟶ v)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      ((negativeArrow a).toPath.comp C.path).reverse) :
    signedPathSubspace N C.path
        ((⊥ : Submodule k (N.obj (Opposite.op
          (obj P.toPresentation.relations v)))).comap
            (moduleArrowMap N a).hom) = wholeSubspace N C := by
  have hrightAvoids : AvoidsRelations P.toPresentation.relations
      (positiveArrow a).toPath :=
    avoidsRelations_of_length_lt_two P.toPresentation.relations
      P.toPresentation.admissible _ (by simp)
  have hnot' : ¬ AvoidsRelations P.toPresentation.relations
      (C.path.reverse.comp (positiveArrow a).toPath) := by
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
      reverse_negativeArrow] using hnot
  obtain ⟨c, d, p, q, before, after, hleft, hright, hp, hq, hzero⟩ :=
    exists_positive_relation_crossing_comp
      C.path.reverse (positiveArrow a).toPath C.isString.2.2
        hrightAvoids hnot'
  have hafterZero : after.length = 0 := by
    have hlength := congrArg Quiver.Path.length hright
    simp only [Quiver.Path.length_toPath, Quiver.Path.length_comp,
      positivePath_length] at hlength
    omega
  have htarget := after.eq_of_length_zero hafterZero
  cases htarget
  have hafterNil := after.eq_nil_of_length_zero hafterZero
  subst after
  simp only [Quiver.Path.comp_nil] at hright
  have hC : C.path = (positivePath p).reverse.comp before.reverse := by
    have hreverse := congrArg Quiver.Path.reverse hleft
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_reverse]
      using hreverse
  unfold wholeSubspace
  rw [← signedArrowSubspace_negative N a ⊥,
    ← signedPathSubspace_toPath N (negativeArrow a) ⊥]
  have hnegative : (negativeArrow a).toPath = (positivePath q).reverse := by
    have hreverse := congrArg Quiver.Path.reverse hright
    simpa only [Quiver.Path.reverse_toPath, reverse_positiveArrow]
      using hreverse
  rw [hnegative]
  have hqtransport : signedPathSubspace N (positivePath q).reverse ⊥ =
      ((⊥ : Submodule k (N.obj (Opposite.op
        (obj P.toPresentation.relations v)))).comap
          (modulePathMap N q).hom) :=
    signedPathSubspace_positivePath_reverse N q ⊥
  rw [hC, signedPathSubspace_comp, signedPathSubspace_comp, hqtransport,
    signedPathSubspace_positivePath_reverse_comap_bot_eq_top_of_pathMap_comp_eq_zero
      N p q hzero]
  rw [signedPathSubspace_positivePath_reverse]
  simp

/-- The lower filtration of an endpoint word may equivalently be obtained by
starting with the matching polarized trivial word at its source and then
transporting that boundary along the word.  If the trivial boundary arrow no
longer extends the word, the intervening monomial relation makes its
transport equal to the transported zero space. -/
theorem lowerSubspace_eq_sourceVertexBoundaryTransport
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (C : EndpointWord S u₀ t) :
    lowerSubspace N C =
      signedPathSubspace N C.path
        (lowerBoundarySubspace N C.sourceVertex) := by
  classical
  by_cases hinc : Nonempty C.IncomingExtension
  · let inc := Classical.choice hinc
    let incSource : C.sourceVertex.IncomingExtension :=
      ⟨inc.1,
        isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible _ (by
            change ((positiveArrow inc.1.2).toPath.comp
              (Quiver.Path.nil : SignedPath C.source C.source)).length < 2
            simp),
        (sourceVertex_sourceSign C).trans inc.2.2⟩
    let hsource : Nonempty C.sourceVertex.IncomingExtension := ⟨incSource⟩
    have hchosen : Classical.choice hinc = inc := rfl
    have hchosenSource : Classical.choice hsource = incSource :=
      @Subsingleton.elim _ C.sourceVertex.incomingExtension_subsingleton _ _
    unfold lowerSubspace
    simp only [lowerBoundarySubspace, hinc, hsource, dite_true]
    rw [hchosen, hchosenSource]
    rfl
  · by_cases hsource : Nonempty C.sourceVertex.IncomingExtension
    · let incSource := Classical.choice hsource
      let a : incSource.1.1 ⟶ C.source := incSource.1.2
      have hsign : C.sourceSign = Bool.not (S.targetSign a) := by
        exact (sourceVertex_sourceSign C).symm.trans incSource.2.2
      have hnotString : ¬ IsString P.toPresentation.relations
          ((positiveArrow a).toPath.comp C.path) := by
        intro hstring
        apply hinc
        exact ⟨⟨incSource.1, hstring, hsign⟩⟩
      have hnotAvoids : ¬ AvoidsRelations P.toPresentation.relations
          ((positiveArrow a).toPath.comp C.path) :=
        not_avoidsRelations_positiveArrow_comp_of_not_isString
          C a hsign hnotString
      unfold lowerSubspace
      simp only [lowerBoundarySubspace, hinc, hsource, dite_false,
        dite_true]
      exact (signedPathSubspace_map_top_eq_zeroSubspace_of_not_avoids_prepend
        N C a hnotAvoids).symm
    · unfold lowerSubspace
      simp only [lowerBoundarySubspace, hinc, hsource, dite_false]
      rfl

/-- The upper filtration has the same contextual description from the
matching polarized trivial source word.  When its inverse boundary arrow no
longer extends `C`, the reversed monomial relation makes the transported
kernel equal the transported whole space. -/
theorem upperSubspace_eq_sourceVertexBoundaryTransport
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (C : EndpointWord S u₀ t) :
    upperSubspace N C =
      signedPathSubspace N C.path
        (upperBoundarySubspace N C.sourceVertex) := by
  classical
  by_cases hout : Nonempty C.OutgoingInverseExtension
  · let out := Classical.choice hout
    let outSource : C.sourceVertex.OutgoingInverseExtension :=
      ⟨out.1,
        isString_of_length_lt_two P.toPresentation.relations
          P.toPresentation.admissible _ (by
            change ((negativeArrow out.1.2).toPath.comp
              (Quiver.Path.nil : SignedPath C.source C.source)).length < 2
            simp),
        (sourceVertex_sourceSign C).trans out.2.2⟩
    let hsource : Nonempty C.sourceVertex.OutgoingInverseExtension :=
      ⟨outSource⟩
    have hchosen : Classical.choice hout = out := rfl
    have hchosenSource : Classical.choice hsource = outSource :=
      @Subsingleton.elim _ C.sourceVertex.outgoingInverseExtension_subsingleton
        _ _
    unfold upperSubspace
    simp only [upperBoundarySubspace, hout, hsource, dite_true]
    rw [hchosen, hchosenSource]
    rfl
  · by_cases hsource : Nonempty C.sourceVertex.OutgoingInverseExtension
    · let outSource := Classical.choice hsource
      let a : C.source ⟶ outSource.1.1 := outSource.1.2
      have hsign : C.sourceSign = Bool.not (S.sourceSign a) := by
        exact (sourceVertex_sourceSign C).symm.trans outSource.2.2
      have hnotString : ¬ IsString P.toPresentation.relations
          ((negativeArrow a).toPath.comp C.path) := by
        intro hstring
        apply hout
        exact ⟨⟨outSource.1, hstring, hsign⟩⟩
      have hnotAvoids : ¬ AvoidsRelations P.toPresentation.relations
          ((negativeArrow a).toPath.comp C.path).reverse :=
        not_avoidsRelations_reverse_negativeArrow_comp_of_not_isString
          C a hsign hnotString
      unfold upperSubspace
      simp only [upperBoundarySubspace, hout, hsource, dite_false,
        dite_true]
      exact
        (signedPathSubspace_comap_bot_eq_wholeSubspace_of_not_avoids_reverse_prepend
          N C a hnotAvoids).symm
    · unfold upperSubspace
      simp only [upperBoundarySubspace, hout, hsource, dite_false]
      rfl

/-- The complete signed string represented by a valid endpoint-word pair. -/
def pairWord
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) : Word P.toPresentation.relations where
  source := R.source
  target := L.source
  path := R.path.comp L.path.reverse
  isString := hstring

/-- The original join is a displayed position of the complete pair word. -/
def pairPosition
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) : (pairWord L R hstring).Position :=
  ⟨u₀, ⟨R.path, L.path.reverse, rfl⟩⟩

@[simp]
theorem pairPosition_vertex
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    (pairPosition L R hstring).1 = u₀ :=
  rfl

@[simp]
theorem pairPosition_prefix
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    (pairPosition L R hstring).2.1 = R.path :=
  rfl

@[simp]
theorem pairPosition_suffix
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    (pairPosition L R hstring).2.suffix = L.path.reverse :=
  Quiver.Path.comp_injective_right R.path (by
    have hfactor :=
      (pairPosition L R hstring).2.prefix_comp_suffix
    change R.path.comp L.path.reverse =
      R.path.comp (pairPosition L R hstring).2.suffix at hfactor
    exact hfactor.symm)

/-- For a nontrivial complete pair word, the canonical detector endpoint has
the same source polarization as the right half. -/
theorem detectorEndpoint_pairWord_sourceSign_of_length_pos
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    (EndpointWord.ofWord S (pairWord L R hstring)).sourceSign =
      R.sourceSign := by
  by_cases hRpos : 0 < R.path.length
  · unfold EndpointWord.ofWord EndpointWord.sourceSign
    unfold pairWord
    rw [signedPathSourceSignOr,
      signedPathSourceSign_comp_of_left_length_pos R.path L.path.reverse hRpos]
    exact signedPathSourceSignOr_eq_of_length_pos R.path hRpos _ _
  · have hRzero : R.path.length = 0 := Nat.eq_zero_of_not_pos hRpos
    have hLpos : 0 < L.path.length := by
      change 0 < (R.path.comp L.path.reverse).length at hlength
      simp only [Quiver.Path.length_comp, length_reverse, hRzero,
        zero_add] at hlength
      exact hlength
    unfold EndpointWord.ofWord EndpointWord.sourceSign
    unfold pairWord
    rw [signedPathSourceSignOr,
      signedPathSourceSign_comp_of_left_length_zero R.path L.path.reverse hRzero,
      signedPathSourceSign_reverse]
    rw [show (signedPathTargetSign S L.path).getD
        (Bool.not (signedPathTargetSignOr S false
          (R.path.comp L.path.reverse))) =
          signedPathTargetSignOr S (Bool.not t) L.path by
      exact signedPathTargetSignOr_eq_of_length_pos L.path hLpos _ _]
    rw [L.targetSign_eq]
    exact (signedPathSourceSignOr_eq_of_length_zero
      R.path hRzero (Bool.not t)).symm

/-- For a nontrivial complete pair word, its opposite trivial endpoint has
the same source polarization as the left half. -/
theorem detectorEndpoint_pairWord_oppositeVertex_sourceSign_of_length_pos
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hstring : IsString P.toPresentation.relations
      (R.path.comp L.path.reverse))
    (hlength : 0 < (pairWord L R hstring).length) :
    (EndpointWord.ofWord S (pairWord L R hstring)).oppositeVertex.sourceSign =
      L.sourceSign := by
  simp only [oppositeVertex, EndpointWord.vertex_sourceSign, Bool.not_not]
  change signedPathTargetSignOr S false
      (R.path.comp L.path.reverse) = L.sourceSign
  by_cases hLpos : 0 < L.path.length
  · unfold EndpointWord.sourceSign
    rw [signedPathTargetSignOr,
      signedPathTargetSign_comp_of_right_length_pos R.path L.path.reverse]
    · rw [signedPathTargetSign_reverse]
      exact signedPathSourceSignOr_eq_of_length_pos L.path hLpos _ _
    · simpa only [length_reverse] using hLpos
  · have hLzero : L.path.length = 0 := Nat.eq_zero_of_not_pos hLpos
    have hRpos : 0 < R.path.length := by
      change 0 < (R.path.comp L.path.reverse).length at hlength
      simp only [Quiver.Path.length_comp, length_reverse, hLzero,
        add_zero] at hlength
      exact hlength
    unfold EndpointWord.sourceSign
    rw [signedPathTargetSignOr,
      signedPathTargetSign_comp_of_right_length_zero R.path L.path.reverse]
    · rw [show (signedPathTargetSign S R.path).getD false =
          signedPathTargetSignOr S t R.path by
        exact signedPathTargetSignOr_eq_of_length_pos R.path hRpos _ _]
      rw [R.targetSign_eq]
      simpa only [Bool.not_not] using
        (signedPathSourceSignOr_eq_of_length_zero (S := S)
          L.path hLzero (Bool.not (Bool.not t))).symm
    · simpa only [length_reverse] using hLzero

/-- Endpoint words of opposite target polarization cannot cancel when their
target ends are joined. -/
theorem pairPath_isReduced
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    IsReduced (R.path.comp L.path.reverse) := by
  rcases L with ⟨Lsource, Lpath, hLstring, hLsign⟩
  rcases R with ⟨Rsource, Rpath, hRstring, hRsign⟩
  cases Rpath with
  | nil =>
      rw [EndpointWord.path, Quiver.Path.nil_comp]
      exact (isReduced_reverse_iff Lpath).2 hLstring.1
  | @cons Ry _ Rprefix e =>
      cases Lpath with
      | nil =>
          change IsReduced (Quiver.Path.cons Rprefix e)
          exact hRstring.1
      | @cons Ly _ Lprefix f =>
          change Q at Ry Ly
          have heSign : signedArrowTargetSign S e = t := by
            simpa only [signedPathTargetSignOr,
              signedPathTargetSign_cons, Option.getD_some] using hRsign
          have hfSign : signedArrowTargetSign S f = Bool.not t := by
            simpa only [signedPathTargetSignOr,
              signedPathTargetSign_cons, Option.getD_some] using hLsign
          have htwo : IsReduced
              (e.toPath.comp (Quiver.reverse f).toPath) :=
            by
              cases e with
              | inl a =>
                  cases f with
                  | inl b =>
                      change S.targetSign a = t at heSign
                      change S.targetSign b = Bool.not t at hfSign
                      apply Word.isReduced_positiveArrow_comp_negativeArrow_of_costar_ne
                      intro hab
                      have hsign := congrArg
                        (S.atVertex u₀).targetSign hab
                      change S.targetSign a = S.targetSign b at hsign
                      have ht : t = Bool.not t :=
                        heSign.symm.trans (hsign.trans hfSign)
                      exact (Bool.not_eq_self t).mp ht.symm
                  | inr b =>
                      exact Word.isReduced_positiveArrow_comp_positiveArrow a b
              | inr a =>
                  cases f with
                  | inl b =>
                      exact Word.isReduced_negativeArrow_comp_negativeArrow a b
                  | inr b =>
                      change S.sourceSign a = t at heSign
                      change S.sourceSign b = Bool.not t at hfSign
                      apply Word.isReduced_negativeArrow_comp_positiveArrow_of_star_ne
                      intro hab
                      have hsign := congrArg
                        (S.atVertex u₀).sourceSign hab
                      change S.sourceSign a = S.sourceSign b at hsign
                      have ht : t = Bool.not t :=
                        heSign.symm.trans (hsign.trans hfSign)
                      exact (Bool.not_eq_self t).mp ht.symm
          have hLreverse : IsReduced
              ((Quiver.Path.cons Lprefix f).reverse) :=
            (isReduced_reverse_iff (Quiver.Path.cons Lprefix f)).2
              hLstring.1
          have hright : IsReduced
              (e.toPath.comp ((Quiver.reverse f).toPath.comp
                Lprefix.reverse)) := by
            apply isReduced_comp_of_overlap e.toPath
              (Quiver.reverse f).toPath Lprefix.reverse (by simp)
            · exact htwo
            · rw [← Quiver.Path.comp_toPath_eq_cons,
                Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath] at hLreverse
              exact hLreverse
          have htotal : IsReduced
              (Rprefix.comp (e.toPath.comp
                ((Quiver.reverse f).toPath.comp Lprefix.reverse))) := by
            apply isReduced_comp_of_overlap Rprefix e.toPath
              ((Quiver.reverse f).toPath.comp Lprefix.reverse) (by simp)
            · have hRreduced : IsReduced
                  (Quiver.Path.cons Rprefix e) := hRstring.1
              rw [← Quiver.Path.comp_toPath_eq_cons] at hRreduced
              unfold IsReduced at hRreduced ⊢
              intro a b g hg
              exact hRreduced g hg
            · exact hright
          change IsReduced ((Quiver.Path.cons Rprefix e).comp
            (Quiver.Path.cons Lprefix f).reverse)
          rw [← Quiver.Path.comp_toPath_eq_cons Rprefix e,
            ← Quiver.Path.comp_toPath_eq_cons Lprefix f,
            Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
            Quiver.Path.comp_assoc]
          unfold IsReduced at htotal ⊢
          intro a b g hg
          exact htotal g hg

/-- If an ordinary monomial relation first appears across the join of two
endpoint words, the upper subspace of the first word is already contained in
the lower subspace of the second. -/
theorem upperSubspace_le_lowerSubspace_of_not_avoids_join
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {s₁ s₂ : Bool} (C : EndpointWord S u₀ s₁)
    (D : EndpointWord S u₀ s₂)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (C.path.comp D.path.reverse)) :
    upperSubspace N C ≤ lowerSubspace N D := by
  obtain ⟨c, d, p, q, before, after, hC, hDreverse, hp, hq, hzero⟩ :=
    exists_positive_relation_crossing_comp C.path D.path.reverse
      C.isString.2.1 D.isString.2.2 hnot
  have hD : D.path = after.reverse.comp (positivePath q).reverse := by
    have hreverse := congrArg Quiver.Path.reverse hDreverse
    simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_reverse] using
      hreverse
  rw [upperSubspace, hC, signedPathSubspace_comp,
    lowerSubspace, hD, signedPathSubspace_comp]
  exact signedPathSubspace_positivePath_le_reverse_of_pathMap_comp_eq_zero
    N p q (signedPathSubspace N before (upperBoundarySubspace N C))
      (signedPathSubspace N after.reverse (lowerBoundarySubspace N D)) hzero

/-- A forward relation already crossing a join continues to cross after an
arbitrary source extension of its left word. -/
theorem upperSubspace_descendant_le_lowerSubspace_of_not_avoids_join
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {s₁ s₂ : Bool} (C : EndpointWord S u₀ s₁)
    (D : EndpointWord S u₀ s₂)
    (E : EndpointWord S u₀ s₁)
    (pref : SignedPath E.source C.source)
    (hpath : E.path = pref.comp C.path)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (C.path.comp D.path.reverse)) :
    upperSubspace N E ≤ lowerSubspace N D := by
  apply upperSubspace_le_lowerSubspace_of_not_avoids_join N E D
  intro havoids
  apply hnot
  apply AvoidsRelations.of_contiguousSubpath
    P.toPresentation.relations havoids
  refine ⟨pref, Quiver.Path.nil, ?_⟩
  rw [hpath, Quiver.Path.comp_nil, Quiver.Path.comp_assoc]

/-- If a forward relation crosses the join after `C`, every vector in the
transported whole space of `C` is either already in its transported zero
space or lies in the lower subspace of the opposite word.  This packages the
collapse of the entire finite source-extension subtree, not just its first
interval. -/
theorem wholeSubspace_le_zeroSubspace_sup_lowerSubspace_of_not_avoids_join
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {s₁ s₂ : Bool} (C : EndpointWord S u₀ s₁)
    (D : EndpointWord S u₀ s₂)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (C.path.comp D.path.reverse)) :
    wholeSubspace N C ≤ zeroSubspace N C ⊔ lowerSubspace N D := by
  intro x hxWhole
  by_cases hxZero : x ∈ zeroSubspace N C
  · exact (show zeroSubspace N C ≤
      zeroSubspace N C ⊔ lowerSubspace N D from le_sup_left) hxZero
  · obtain ⟨E, pref, hpath, hxUpper, _⟩ :=
      exists_descendant_mem_upperSubspace_not_mem_lowerSubspace
        N C x hxWhole hxZero
    apply (show lowerSubspace N D ≤
      zeroSubspace N C ⊔ lowerSubspace N D from le_sup_right)
    exact upperSubspace_descendant_le_lowerSubspace_of_not_avoids_join
      N C D E pref hpath hnot hxUpper

/-- In the finite-word case, a relation crossing the join forces the first
word's upper subspace all the way into the transported zero space of the
second word.  Otherwise descendant coverage of the second word would produce
an interval simultaneously above and below the same vector. -/
theorem upperSubspace_le_zeroSubspace_of_not_avoids_join
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {s₁ s₂ : Bool} (C : EndpointWord S u₀ s₁)
    (D : EndpointWord S u₀ s₂)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (C.path.comp D.path.reverse)) :
    upperSubspace N C ≤ zeroSubspace N D := by
  intro x hxUpper
  have hxWhole : x ∈ wholeSubspace N D :=
    (lowerSubspace_le_upperSubspace N D).trans
      (upperSubspace_le_wholeSubspace N D)
        (upperSubspace_le_lowerSubspace_of_not_avoids_join
          N C D hnot hxUpper)
  by_contra hxZero
  obtain ⟨E, pref, hpath, hxEUpper, hxENotLower⟩ :=
    exists_descendant_mem_upperSubspace_not_mem_lowerSubspace
      N D x hxWhole hxZero
  apply hxENotLower
  apply upperSubspace_le_lowerSubspace_of_not_avoids_join N C E
  · intro havoids
    apply hnot
    apply AvoidsRelations.of_contiguousSubpath
      P.toPresentation.relations havoids
    refine ⟨Quiver.Path.nil, pref.reverse, ?_⟩
    rw [hpath, Quiver.Path.reverse_comp, Quiver.Path.nil_comp,
      Quiver.Path.comp_assoc]
  · exact hxUpper

/-- If the positive source extension defining `R⁻` ceases to avoid relations
after the left half is attached, its contribution is already accounted for
by the transported zero space of `R` together with `L⁻`. -/
theorem lowerSubspace_right_le_zeroSubspace_sup_lowerSubspace_left_of_not_avoids
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (inc : R.IncomingExtension)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      ((R.prependIncoming inc).path.comp L.path.reverse)) :
    lowerSubspace N R ≤ zeroSubspace N R ⊔ lowerSubspace N L := by
  rw [← wholeSubspace_prependIncoming N R inc,
    ← zeroSubspace_prependIncoming N R inc]
  exact wholeSubspace_le_zeroSubspace_sup_lowerSubspace_of_not_avoids_join
    N (R.prependIncoming inc) L hnot

/-- The symmetric collapse for a positive source extension of the left half.
It is the reverse-orientation boundary correction used at the other end of a
complete pair word. -/
theorem lowerSubspace_left_le_zeroSubspace_sup_lowerSubspace_right_of_not_avoids
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (inc : L.IncomingExtension)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      ((L.prependIncoming inc).path.comp R.path.reverse)) :
    lowerSubspace N L ≤ zeroSubspace N L ⊔ lowerSubspace N R := by
  rw [← wholeSubspace_prependIncoming N L inc,
    ← zeroSubspace_prependIncoming N L inc]
  exact wholeSubspace_le_zeroSubspace_sup_lowerSubspace_of_not_avoids_join
    N (L.prependIncoming inc) R hnot

/-- If an inverse source extension of the right half ceases to avoid
relations in the reverse orientation after the left half is attached, the
left upper subspace is already contained in the old right upper subspace. -/
theorem upperSubspace_left_le_upperSubspace_right_of_not_avoids_outgoing
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (out : R.OutgoingInverseExtension)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (L.path.comp (R.prependOutgoingInverse out).path.reverse)) :
    upperSubspace N L ≤ upperSubspace N R := by
  rw [← zeroSubspace_prependOutgoingInverse N R out]
  exact upperSubspace_le_zeroSubspace_of_not_avoids_join
    N L (R.prependOutgoingInverse out) hnot

/-- The symmetric inverse-extension correction at the left half. -/
theorem upperSubspace_right_le_upperSubspace_left_of_not_avoids_outgoing
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (out : L.OutgoingInverseExtension)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (R.path.comp (L.prependOutgoingInverse out).path.reverse)) :
    upperSubspace N R ≤ upperSubspace N L := by
  rw [← zeroSubspace_prependOutgoingInverse N L out]
  exact upperSubspace_le_zeroSubspace_of_not_avoids_join
    N R (L.prependOutgoingInverse out) hnot

/-- A forward relation crossing the pair join kills the right upper word
subspace modulo the left lower word subspace. -/
theorem upperSubspace_right_le_lowerSubspace_left_of_not_avoids_pairPath
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    upperSubspace N R ≤ lowerSubspace N L :=
  upperSubspace_le_lowerSubspace_of_not_avoids_join N R L hnot

/-- A relation crossing the reverse of the pair join kills the left upper
word subspace modulo the right lower word subspace. -/
theorem upperSubspace_left_le_lowerSubspace_right_of_not_avoids_reverse_pairPath
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ AvoidsRelations P.toPresentation.relations
      (R.path.comp L.path.reverse).reverse) :
    upperSubspace N L ≤ lowerSubspace N R := by
  apply upperSubspace_le_lowerSubspace_of_not_avoids_join N L R
  simpa only [Quiver.Path.reverse_comp, Quiver.Path.reverse_reverse] using hnot

/-- Since opposite polarization already makes the join reduced, failure of
the pair join to be a string is exactly a relation failure in one of its two
orientations. -/
theorem not_avoids_pairPath_or_reverse_of_not_isString
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    (¬ AvoidsRelations P.toPresentation.relations
        (R.path.comp L.path.reverse)) ∨
      ¬ AvoidsRelations P.toPresentation.relations
        (R.path.comp L.path.reverse).reverse := by
  by_cases hforward : AvoidsRelations P.toPresentation.relations
      (R.path.comp L.path.reverse)
  · right
    intro hreverse
    exact hnot ⟨pairPath_isReduced L R, hforward, hreverse⟩
  · exact Or.inl hforward

/-- An invalid endpoint-word pair has zero pair detector: its numerator is
already contained in its denominator. -/
theorem pairDetectorNumerator_le_pairDetectorDenominator_of_not_isString
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    pairDetectorNumerator N L R ≤ pairDetectorDenominator N L R := by
  rcases not_avoids_pairPath_or_reverse_of_not_isString L R hnot with
    hforward | hreverse
  · have hle :=
      upperSubspace_right_le_lowerSubspace_left_of_not_avoids_pairPath
        N L R hforward
    intro x hx
    apply (show lowerSubspace N L ⊓ upperSubspace N R ≤
      pairDetectorDenominator N L R from le_sup_right)
    exact ⟨hle hx.2, hx.2⟩
  · have hle :=
      upperSubspace_left_le_lowerSubspace_right_of_not_avoids_reverse_pairPath
        N L R hreverse
    intro x hx
    apply (show upperSubspace N L ⊓ lowerSubspace N R ≤
      pairDetectorDenominator N L R from le_sup_left)
    exact ⟨hx.1, hle hx.1⟩

/-- Equivalently, the numerator and denominator of an invalid pair detector
coincide. -/
theorem pairDetectorDenominator_eq_numerator_of_not_isString
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    pairDetectorDenominator N L R = pairDetectorNumerator N L R := by
  apply le_antisymm
  · exact pairDetectorDenominator_le_pairDetectorNumerator N L R
  · exact pairDetectorNumerator_le_pairDetectorDenominator_of_not_isString
      N L R hnot

/-- In Ringel's finite grid, an invalid pair is literally a repeated
filtration endpoint. -/
theorem pairGridLower_eq_pairGridUpper_of_not_isString
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    pairGridLower N L R = pairGridUpper N L R := by
  rcases not_avoids_pairPath_or_reverse_of_not_isString L R hnot with
    hforward | hreverse
  · have hupper :=
      upperSubspace_right_le_lowerSubspace_left_of_not_avoids_pairPath
        N L R hforward
    have hlower : lowerSubspace N R ≤ lowerSubspace N L :=
      (lowerSubspace_le_upperSubspace N R).trans hupper
    rw [pairGridLower, pairGridUpper, sup_eq_right.mpr hlower,
      sup_eq_right.mpr hupper]
  · have hupper :=
      upperSubspace_left_le_lowerSubspace_right_of_not_avoids_reverse_pairPath
        N L R hreverse
    have hlower : lowerSubspace N L ≤ lowerSubspace N R :=
      (lowerSubspace_le_upperSubspace N L).trans hupper
    rw [pairGridLower, pairGridUpper, sup_eq_left.mpr hlower,
      inf_eq_right.mpr hupper,
      inf_eq_right.mpr
        ((hupper.trans (lowerSubspace_le_upperSubspace N R)).trans le_sup_left)]

/-- The pair-detector quotient of an invalid pair is a zero vector space. -/
theorem pairDetectorSpace_subsingleton_of_not_isString
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    Subsingleton (PairDetectorSpace N L R) := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          apply (Submodule.Quotient.eq
            (pairDetectorDenominatorInNumerator N L R)).mpr
          change x.1 - y.1 ∈ pairDetectorDenominator N L R
          rw [pairDetectorDenominator_eq_numerator_of_not_isString
            N L R hnot]
          exact (pairDetectorNumerator N L R).sub_mem x.2 y.2

/-- The corresponding grid quotient is likewise a zero vector space. -/
theorem pairGridSpace_subsingleton_of_not_isString
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (hnot : ¬ IsString P.toPresentation.relations
      (R.path.comp L.path.reverse)) :
    Subsingleton (PairGridSpace N L R) := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          apply (Submodule.Quotient.eq (pairGridLowerInUpper N L R)).mpr
          change x.1 - y.1 ∈ pairGridLower N L R
          rw [pairGridLower_eq_pairGridUpper_of_not_isString N L R hnot]
          exact (pairGridUpper N L R).sub_mem x.2 y.2

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
