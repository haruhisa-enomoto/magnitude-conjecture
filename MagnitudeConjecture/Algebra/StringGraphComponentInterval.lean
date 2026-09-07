import MagnitudeConjecture.Algebra.StringMorphismSupport

/-!
# Interval structure of string coefficient components

Orienting every matched coefficient edge by increasing source-word index
makes the edge relation a partial bijection.  Church--Rosser then shows that
each connected coefficient component embeds in both word-position lines.
This is the graph-theoretic core of identifying graph-map components with
oriented common intervals.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The matched coefficient edges, oriented by increasing source-word
index. -/
def MorphismCoefficientForwardStep (C D : Word R) :
    C.MorphismCoefficientPosition D →
      C.MorphismCoefficientPosition D → Prop :=
  fun p q ↦
    Relation.SymmGen (C.MorphismCoefficientStep D) p q ∧
      q.inputIndex = p.inputIndex + 1

/-- An oriented coefficient edge has at most one successor. -/
theorem morphismCoefficientForwardStep_rightUnique (C D : Word R) :
    Relator.RightUnique (C.MorphismCoefficientForwardStep D) := by
  rintro p q r ⟨hpq, hpqIndex⟩ ⟨hpr, hprIndex⟩
  have hinput : q.inputPosition = r.inputPosition :=
    Position.ext_index (hpqIndex.trans hprIndex.symm)
  rcases hpq with hpq | hpq <;> rcases hpr with hpr | hpr
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hpr with
      | ofArrow b _ l _ l' hil hil' =>
        cases hinput
        have hab : a = b := C.arrow_eq_of_arrowSteps hij hil
        subst b
        have hj'l' : j' = l' := by
          have hsub :
              (⟨j', hij'⟩ : {t : D.PositionAt _ // D.ArrowStep a i' t}) =
                ⟨l', hil'⟩ :=
            @Subsingleton.elim _ (D.arrowStep_subsingleton a i') _ _
          exact congrArg Subtype.val hsub
        subst l'
        rfl
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hpr with
      | ofArrow b l _ l' _ hli hli' =>
        cases hinput
        exact False.elim
          (C.not_arrowSteps_reverse_of_index_add_one hij hli hpqIndex)
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hpr with
      | ofArrow b _ l _ l' hil hil' =>
        cases hinput
        exact False.elim
          (C.not_arrowSteps_reverse_of_index_add_one hil hij hprIndex)
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hpr with
      | ofArrow b l _ l' _ hli hli' =>
        cases hinput
        have hab : a = b := C.arrow_eq_of_arrowSteps hij hli
        subst b
        have hi'l' : i' = l' := by
          have hsub :
              (⟨i', hij'⟩ : {t : D.PositionAt _ // D.ArrowStep a t j'}) =
                ⟨l', hli'⟩ :=
            @Subsingleton.elim _ (D.arrowStep_source_subsingleton a j') _ _
          exact congrArg Subtype.val hsub
        subst l'
        rfl

/-- An oriented coefficient edge has at most one predecessor. -/
theorem morphismCoefficientForwardStep_leftUnique (C D : Word R) :
    Relator.LeftUnique (C.MorphismCoefficientForwardStep D) := by
  rintro p r q ⟨hpq, hpqIndex⟩ ⟨hrq, hrqIndex⟩
  have hinput : p.inputPosition = r.inputPosition :=
    Position.ext_index (Nat.add_right_cancel (hpqIndex.symm.trans hrqIndex))
  rcases hpq with hpq | hpq <;> rcases hrq with hrq | hrq
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hrq with
      | ofArrow b l _ l' _ hlj hlj' =>
        cases hinput
        have hab : a = b := C.arrow_eq_of_arrowSteps hij hlj
        subst b
        have hi'l' : i' = l' := by
          have hsub :
              (⟨i', hij'⟩ : {t : D.PositionAt _ // D.ArrowStep a t j'}) =
                ⟨l', hlj'⟩ :=
            @Subsingleton.elim _ (D.arrowStep_source_subsingleton a j') _ _
          exact congrArg Subtype.val hsub
        subst l'
        rfl
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hrq with
      | ofArrow b _ l _ l' hil hil' =>
        cases hinput
        exact False.elim
          (C.not_arrowSteps_reverse_of_index_add_one hij hil hpqIndex)
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hrq with
      | ofArrow b l _ l' _ hli hli' =>
        cases hinput
        exact False.elim
          (C.not_arrowSteps_reverse_of_index_add_one hli hij hrqIndex)
  · cases hpq with
    | ofArrow a i j i' j' hij hij' =>
      cases hrq with
      | ofArrow b _ l _ l' hil hil' =>
        cases hinput
        have hab : a = b := C.arrow_eq_of_arrowSteps hij hil
        subst b
        have hj'l' : j' = l' := by
          have hsub :
              (⟨j', hij'⟩ : {t : D.PositionAt _ // D.ArrowStep a i' t}) =
                ⟨l', hil'⟩ :=
            @Subsingleton.elim _ (D.arrowStep_subsingleton a i') _ _
          exact congrArg Subtype.val hsub
        subst l'
        rfl

/-- Every unoriented matched edge has a unique orientation by increasing
source-word index. -/
theorem morphismCoefficientForwardStep_or_reverse (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.SymmGen (C.MorphismCoefficientStep D) p q) :
    C.MorphismCoefficientForwardStep D p q ∨
      C.MorphismCoefficientForwardStep D q p := by
  have hindex :
      q.inputIndex = p.inputIndex + 1 ∨
        p.inputIndex = q.inputIndex + 1 := by
    rcases hpq with hpq | hpq
    · exact (MorphismCoefficientStep.index C D hpq).1
    · rcases (MorphismCoefficientStep.index C D hpq).1 with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases hindex with h | h
  · exact Or.inl ⟨hpq, h⟩
  · exact Or.inr ⟨hpq.symm, h⟩

/-- Matched-step connectivity is generated by the forward-oriented edge
relation. -/
theorem morphismCoefficientStep_eqvGen_forward (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    Relation.EqvGen (C.MorphismCoefficientForwardStep D) p q := by
  induction hpq with
  | rel p q hpq =>
      rcases C.morphismCoefficientForwardStep_or_reverse D
          (Relation.SymmGen.of_rel hpq) with h | h
      · exact Relation.EqvGen.rel _ _ h
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)
  | refl => exact Relation.EqvGen.refl _
  | symm p q _ hpq => exact Relation.EqvGen.symm _ _ hpq
  | trans p q r _ _ hpq hqr => exact Relation.EqvGen.trans _ _ _ hpq hqr

/-- Two vertices in one coefficient component have a common descendant for
the forward-oriented relation. -/
theorem exists_common_morphismCoefficientForwardStep_of_eqvGen (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    ∃ r, Relation.ReflTransGen (C.MorphismCoefficientForwardStep D) p r ∧
      Relation.ReflTransGen (C.MorphismCoefficientForwardStep D) q r := by
  let forward := C.MorphismCoefficientForwardStep D
  have hdiamond : ∀ a b c, forward a b → forward a c →
      ∃ d, Relation.ReflGen forward b d ∧
        Relation.ReflTransGen forward c d := by
    intro a b c hab hac
    have hbc : b = c := C.morphismCoefficientForwardStep_rightUnique D hab hac
    subst c
    exact ⟨b, Relation.ReflGen.refl, Relation.ReflTransGen.refl⟩
  have hequiv : Equivalence
      (Relation.Join (Relation.ReflTransGen forward)) :=
    Relation.equivalence_join_reflTransGen hdiamond
  letI : IsEquiv _ (Relation.Join (Relation.ReflTransGen forward)) :=
    hequiv.isEquiv
  have hforward : Relation.EqvGen forward p q :=
    C.morphismCoefficientStep_eqvGen_forward D hpq
  change Relation.Join (Relation.ReflTransGen forward) p q
  apply Relation.EqvGen.eqvGen_le _ _ _ hforward
  intro a b hab
  exact ⟨b, Relation.ReflTransGen.single hab,
    Relation.ReflTransGen.refl⟩

/-- A forward coefficient walk weakly increases the source-word index. -/
theorem inputIndex_le_of_reflTransGen_morphismCoefficientForwardStep (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.ReflTransGen
      (C.MorphismCoefficientForwardStep D) p q) :
    p.inputIndex ≤ q.inputIndex := by
  induction hpq with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      have hsucc := hstep.2
      omega

/-- A forward coefficient walk whose endpoints have equal source index is
reflexive. -/
theorem eq_of_reflTransGen_morphismCoefficientForwardStep_of_inputIndex_eq (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.ReflTransGen
      (C.MorphismCoefficientForwardStep D) p q)
    (hindex : p.inputIndex = q.inputIndex) : p = q := by
  rcases hpq.cases_tail with h | ⟨r, hpr, hrq⟩
  · exact h.symm
  · have hle := C.inputIndex_le_of_reflTransGen_morphismCoefficientForwardStep D hpr
    have hsucc := hrq.2
    exfalso
    omega

/-- A connected coefficient component contains at most one vertex above each
source-word position. -/
theorem eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q)
    (hindex : p.inputIndex = q.inputIndex) : p = q := by
  obtain ⟨r, hpr, hqr⟩ := C.exists_common_morphismCoefficientForwardStep_of_eqvGen D hpq
  let forward := C.MorphismCoefficientForwardStep D
  have hrp : Relation.ReflTransGen (Function.swap forward) r p :=
    Relation.reflTransGen_swap.mpr hpr
  have hrq : Relation.ReflTransGen (Function.swap forward) r q :=
    Relation.reflTransGen_swap.mpr hqr
  have hreverseRightUnique : Relator.RightUnique (Function.swap forward) :=
    (C.morphismCoefficientForwardStep_leftUnique D).flip
  rcases Relation.ReflTransGen.total_of_right_unique
      hreverseRightUnique hrp hrq with hpq' | hqp'
  · have hqp : Relation.ReflTransGen forward q p :=
      Relation.reflTransGen_swap.mp hpq'
    exact (C.eq_of_reflTransGen_morphismCoefficientForwardStep_of_inputIndex_eq D
      hqp hindex.symm).symm
  · have hpq : Relation.ReflTransGen forward p q :=
      Relation.reflTransGen_swap.mp hqp'
    exact C.eq_of_reflTransGen_morphismCoefficientForwardStep_of_inputIndex_eq D hpq hindex

/-- Transpose a coefficient position by interchanging its two word
positions. -/
def morphismCoefficientPositionTranspose (C D : Word R) :
    C.MorphismCoefficientPosition D ≃
      D.MorphismCoefficientPosition C where
  toFun := fun ⟨x, i, j⟩ ↦ ⟨x, j, i⟩
  invFun := fun ⟨x, j, i⟩ ↦ ⟨x, i, j⟩
  left_inv := by rintro ⟨x, i, j⟩; rfl
  right_inv := by rintro ⟨x, j, i⟩; rfl

@[simp]
theorem morphismCoefficientPositionTranspose_inputIndex
    (C D : Word R) (p : C.MorphismCoefficientPosition D) :
    (C.morphismCoefficientPositionTranspose D p).inputIndex =
      p.outputIndex := by
  rcases p with ⟨x, i, j⟩
  rfl

@[simp]
theorem morphismCoefficientPositionTranspose_outputIndex
    (C D : Word R) (p : C.MorphismCoefficientPosition D) :
    (C.morphismCoefficientPositionTranspose D p).outputIndex =
      p.inputIndex := by
  rcases p with ⟨x, i, j⟩
  rfl

@[simp]
theorem morphismCoefficientPositionTranspose_transpose
    (C D : Word R) (p : C.MorphismCoefficientPosition D) :
    D.morphismCoefficientPositionTranspose C
        (C.morphismCoefficientPositionTranspose D p) = p := by
  rcases p with ⟨x, i, j⟩
  rfl

/-- Transposition preserves one matched coefficient edge. -/
theorem MorphismCoefficientStep.transpose (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : C.MorphismCoefficientStep D p q) :
    D.MorphismCoefficientStep C
      (C.morphismCoefficientPositionTranspose D p)
      (C.morphismCoefficientPositionTranspose D q) := by
  cases hpq with
  | ofArrow a i j i' j' hij hij' =>
      exact MorphismCoefficientStep.ofArrow a i' j' i j hij' hij

/-- Transposition preserves generated coefficient components. -/
theorem morphismCoefficientStep_eqvGen_transpose (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    Relation.EqvGen (D.MorphismCoefficientStep C)
      (C.morphismCoefficientPositionTranspose D p)
      (C.morphismCoefficientPositionTranspose D q) := by
  induction hpq with
  | rel p q hpq =>
      exact Relation.EqvGen.rel _ _ (hpq.transpose C D)
  | refl => exact Relation.EqvGen.refl _
  | symm p q _ hpq => exact Relation.EqvGen.symm _ _ hpq
  | trans p q r _ _ hpq hqr => exact Relation.EqvGen.trans _ _ _ hpq hqr

/-- A connected coefficient component contains at most one vertex above each
target-word position. -/
theorem eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq (C D : Word R)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q)
    (hindex : p.outputIndex = q.outputIndex) : p = q := by
  apply (C.morphismCoefficientPositionTranspose D).injective
  exact D.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq C
    (C.morphismCoefficientStep_eqvGen_transpose D hpq) (by simpa using hindex)

/-- The vertices in the generated coefficient component of a chosen root. -/
def MorphismCoefficientComponentSupport (C D : Word R)
    (root : C.MorphismCoefficientPosition D) :=
  {p : C.MorphismCoefficientPosition D //
    Relation.EqvGen (C.MorphismCoefficientStep D) root p}

instance morphismCoefficientComponentSupport_finite
    (C D : Word R) (root : C.MorphismCoefficientPosition D) :
    Finite (C.MorphismCoefficientComponentSupport D root) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- A coefficient component embeds into the source word's finite position
line. -/
def morphismCoefficientComponentSupportInputEmbedding
    (C D : Word R) (root : C.MorphismCoefficientPosition D) :
    C.MorphismCoefficientComponentSupport D root ↪
      Fin (C.length + 1) where
  toFun p := ⟨p.1.inputIndex, Nat.lt_succ_of_le p.1.2.1.index_le⟩
  inj' p q hpq := by
    apply Subtype.ext
    apply C.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq D
    · exact Relation.EqvGen.trans _ root _
        (Relation.EqvGen.symm _ _ p.2) q.2
    · exact congrArg Fin.val hpq

/-- A coefficient component embeds into the target word's finite position
line. -/
def morphismCoefficientComponentSupportOutputEmbedding
    (C D : Word R) (root : C.MorphismCoefficientPosition D) :
    C.MorphismCoefficientComponentSupport D root ↪
      Fin (D.length + 1) where
  toFun p := ⟨p.1.outputIndex, Nat.lt_succ_of_le p.1.2.2.index_le⟩
  inj' p q hpq := by
    apply Subtype.ext
    apply C.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq D
    · exact Relation.EqvGen.trans _ root _
        (Relation.EqvGen.symm _ _ p.2) q.2
    · exact congrArg Fin.val hpq

end MagnitudeConjecture.BoundQuiver.StringWord.Word
