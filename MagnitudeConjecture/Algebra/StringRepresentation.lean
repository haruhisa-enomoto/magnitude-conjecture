import MagnitudeConjecture.Algebra.StringWord
import MagnitudeConjecture.CategoryTheory.LinearPathLift
import MagnitudeConjecture.CategoryTheory.LinearIdealQuotientLift
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# The canonical representation carried by a string word

The basis vectors of a string representation are the occurrences of vertices
along the word.  We represent an occurrence by the prefix ending there.  This
retains repeated visits to the same displayed vertex without choosing numeric
coordinates.

A displayed arrow acts between two prefix occurrences when the word traverses
that arrow positively between them, or traverses its formal inverse in the
opposite direction.  Reduction makes the resulting target occurrence unique.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord

variable {R : RelationFamily k Q}

namespace Word

theorem midpoint_eq_of_comp_eq_of_left_length_eq
    {V : Type*} [Quiver V] {s x y t : V}
    {p : Quiver.Path s x} {q : Quiver.Path x t}
    {p' : Quiver.Path s y} {q' : Quiver.Path y t}
    (hcomp : p.comp q = p'.comp q') (hlength : p.length = p'.length) :
    x = y := by
  have hp :
      (p.comp q).vertices[p.length]? = some x := by
    let hbound : p.length < (p.comp q).vertices.length := by simp
    rw [getElem?_pos (p.comp q).vertices p.length hbound]
    exact congrArg some (Quiver.Path.vertices_comp_get_length_eq p q)
  have hp' :
      (p'.comp q').vertices[p.length]? = some y := by
    have hpBase : (p'.comp q').vertices[p'.length]? = some y := by
      let hbound : p'.length < (p'.comp q').vertices.length := by simp
      rw [getElem?_pos (p'.comp q').vertices p'.length hbound]
      exact congrArg some (Quiver.Path.vertices_comp_get_length_eq p' q')
    simpa only [hlength] using hpBase
  have hget :
      (p.comp q).vertices[p.length]? =
        (p'.comp q').vertices[p.length]? :=
    congrArg (fun r : Quiver.Path s t ↦ r.vertices[p.length]?) hcomp
  exact Option.some.inj (hp.symm.trans (hget.trans hp'))

/-- A positive signed arrow can never equal a negative signed arrow with the
same signed endpoints. -/
theorem positiveArrow_ne_negativeArrow {a b : Q}
    (e : a ⟶ b) (f : b ⟶ a) :
    positiveArrow e ≠ negativeArrow f :=
  Sum.inl_ne_inr

/-- An occurrence of `x` along a word, represented by the prefix ending at
that occurrence. -/
def PositionAt (C : Word R) (x : Q) :=
  {p : SignedPath C.source x //
    ∃ q : SignedPath x C.target, C.path = p.comp q}

namespace PositionAt

/-- The length of the prefix representing a position. -/
def index {C : Word R} {x : Q} (i : C.PositionAt x) : ℕ :=
  i.1.length

/-- The prefix length of a position is at most the word length. -/
theorem index_le {C : Word R} {x : Q} (i : C.PositionAt x) :
    i.index ≤ C.length := by
  rcases i.2 with ⟨q, hq⟩
  rw [Word.length, hq, Quiver.Path.length_comp]
  exact Nat.le_add_right _ _

/-- A position at the final word index lies at the target vertex. -/
theorem eq_target_of_index_eq_length
    {C : Word R} {x : Q} (i : C.PositionAt x)
    (h : i.index = C.length) : x = C.target := by
  rcases i.2 with ⟨q, hq⟩
  have hlength := congrArg Quiver.Path.length hq
  rw [Quiver.Path.length_comp] at hlength
  have hqzero : q.length = 0 := by
    change i.1.length = C.path.length at h
    omega
  have hx := q.eq_of_length_zero hqzero
  exact hx

/-- Two prefix positions at the same vertex with the same index coincide. -/
theorem ext_index {C : Word R} {x : Q} {i j : C.PositionAt x}
    (h : i.index = j.index) : i = j := by
  rcases i with ⟨p, q, hp⟩
  rcases j with ⟨p', q', hp'⟩
  apply Subtype.ext
  have hlength : p.length = p'.length := h
  exact ((Quiver.Path.comp_inj' hlength).1 (hp.symm.trans hp')).1

/-- Prefix length embeds the positions at a fixed displayed vertex into the
finite interval of word indices. -/
def indexEmbedding (C : Word R) (x : Q) :
    C.PositionAt x ↪ Fin (C.length + 1) where
  toFun i := ⟨i.index, Nat.lt_succ_of_le i.index_le⟩
  inj' _ _ h := ext_index (congrArg Fin.val h)

instance finite (C : Word R) (x : Q) : Finite (C.PositionAt x) :=
  Finite.of_injective (indexEmbedding C x) (indexEmbedding C x).injective

end PositionAt

/-- A position anywhere along a word, retaining the displayed vertex over
which it lies. -/
def Position (C : Word R) :=
  Σ x : Q, C.PositionAt x

namespace Position

/-- The prefix index of a total word position. -/
def index {C : Word R} (i : C.Position) : ℕ :=
  i.2.index

/-- The prefix index determines a total position, including its displayed
vertex. -/
theorem ext_index {C : Word R} {i j : C.Position}
    (h : i.index = j.index) : i = j := by
  rcases i with ⟨x, p⟩
  rcases j with ⟨y, q⟩
  have hxy : x = y := by
    rcases p.2 with ⟨p', hp'⟩
    rcases q.2 with ⟨q', hq'⟩
    exact @midpoint_eq_of_comp_eq_of_left_length_eq
      (Quiver.Symmetrify Q) (Quiver.symmetrifyQuiver Q)
      C.source x y C.target p.1 p' q.1 q'
      (hp'.symm.trans hq') h
  subst y
  exact Sigma.ext rfl (heq_of_eq (PositionAt.ext_index h))

/-- Prefix index embeds all positions of a word into its finite index
interval. -/
def indexEmbedding (C : Word R) :
    C.Position ↪ Fin (C.length + 1) where
  toFun i := ⟨i.index, Nat.lt_succ_of_le i.2.index_le⟩
  inj' _ _ h := ext_index (congrArg Fin.val h)

instance finite (C : Word R) : Finite C.Position :=
  Finite.of_injective (Position.indexEmbedding C)
    (Position.indexEmbedding C).injective

end Position

/-- The position at the source endpoint of a string word. -/
def sourcePosition (C : Word R) : C.PositionAt C.source :=
  ⟨Quiver.Path.nil, C.path, by simp⟩

@[simp]
theorem sourcePosition_index (C : Word R) : C.sourcePosition.index = 0 :=
  rfl

/-- The position at the target endpoint of a string word. -/
def targetPosition (C : Word R) : C.PositionAt C.target :=
  ⟨C.path, Quiver.Path.nil, by simp⟩

@[simp]
theorem targetPosition_index (C : Word R) :
    C.targetPosition.index = C.length :=
  rfl

/-- Every index between zero and the word length is represented by a total
word position. -/
theorem exists_position_index_eq (C : Word R) (n : ℕ)
    (hn : n ≤ C.length) :
    ∃ i : C.Position, i.index = n := by
  obtain ⟨x, p, q, hpq, hpLength⟩ :=
    C.path.exists_eq_comp_of_le_length hn
  exact ⟨⟨x, p, q, hpq⟩, hpLength⟩

/-- Total word positions are canonically indexed by the finite interval from
zero through the word length. -/
noncomputable def Position.indexEquiv (C : Word R) :
    C.Position ≃ Fin (C.length + 1) :=
  Equiv.ofBijective (Position.indexEmbedding C)
    ⟨(Position.indexEmbedding C).injective, by
      intro n
      obtain ⟨i, hi⟩ := C.exists_position_index_eq n (by omega)
      refine ⟨i, Fin.ext ?_⟩
      exact hi⟩

@[simp]
theorem Position.card_eq_length_add_one (C : Word R) :
    Nat.card C.Position = C.length + 1 := by
  rw [Nat.card_congr (Position.indexEquiv C), Nat.card_fin]

private theorem exists_signedArrow_eq_of_path_length_one
    {x y : Quiver.Symmetrify Q}
    (p : @Quiver.Path (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y)
    (hp : p.length = 1) :
    ∃ e : @Quiver.Hom (Quiver.Symmetrify Q)
      (Quiver.symmetrifyQuiver Q) x y, p = e.toPath := by
  obtain ⟨z, e, q, hq, hpath⟩ :=
    Quiver.Path.eq_toPath_comp_of_length_eq_succ p hp
  have hzy : z = y := q.eq_of_length_zero hq
  subst z
  rw [q.eq_nil_of_length_zero hq, Quiver.Path.comp_nil] at hpath
  exact ⟨e, hpath⟩

/-- The vertex space of the canonical string representation. -/
abbrev Space (C : Word R) (x : Q) := C.PositionAt x →₀ k

/-- A positive occurrence of `a` moves a basis position one step forward;
an inverse occurrence moves it one step backward. -/
def ArrowStep (C : Word R) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y) : Prop :=
  j.1 = i.1.comp (positiveArrow a).toPath ∨
    i.1 = j.1.comp (negativeArrow a).toPath

/-- An arrow step changes the prefix index by one, forward or backward. -/
theorem ArrowStep.index (C : Word R) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    j.index = i.index + 1 ∨ i.index = j.index + 1 := by
  rcases hij with hforward | hbackward
  · left
    change j.1.length = i.1.length + 1
    rw [hforward, Quiver.Path.length_comp, Quiver.Path.length_toPath]
  · right
    change i.1.length = j.1.length + 1
    rw [hbackward, Quiver.Path.length_comp, Quiver.Path.length_toPath]

/-- Two total positions at consecutive indices are joined by the displayed
ordinary arrow, oriented according to the intervening signed letter. -/
theorem exists_arrowStep_of_position_index_succ
    (C : Word R) (i j : C.Position)
    (hindex : j.index = i.index + 1) :
    (∃ a : i.1 ⟶ j.1, C.ArrowStep a i.2 j.2) ∨
      (∃ a : j.1 ⟶ i.1, C.ArrowStep a j.2 i.2) := by
  rcases i with ⟨x, ⟨p, q, hpq⟩⟩
  rcases j with ⟨y, ⟨p', q', hpq'⟩⟩
  change p'.length = p.length + 1 at hindex
  obtain ⟨z, r, s, hrs, hrLength⟩ :=
    p'.exists_eq_comp_of_le_length (n := p.length) (by omega)
  have hcomp : p.comp q = r.comp (s.comp q') := by
    calc
      p.comp q = C.path := hpq.symm
      _ = p'.comp q' := hpq'
      _ = (r.comp s).comp q' := congrArg (fun t ↦ t.comp q') hrs
      _ = r.comp (s.comp q') := Quiver.Path.comp_assoc _ _ _
  have hxz : x = z :=
    @midpoint_eq_of_comp_eq_of_left_length_eq
      (Quiver.Symmetrify Q) (Quiver.symmetrifyQuiver Q)
      C.source x z C.target p q r (s.comp q') hcomp hrLength.symm
  subst z
  have hpr : p = r :=
    ((Quiver.Path.comp_inj' hrLength.symm).1 hcomp).1
  subst r
  have hsLength : s.length = 1 := by
    have hlength := congrArg Quiver.Path.length hrs
    simp only [Quiver.Path.length_comp] at hlength
    omega
  obtain ⟨e, he⟩ := exists_signedArrow_eq_of_path_length_one s hsLength
  have hp' : p' = p.comp e.toPath := by
    rw [hrs, he]
  rcases e with a | a
  · left
    exact ⟨a, Or.inl hp'⟩
  · right
    exact ⟨a, Or.inr hp'⟩

/-- A position before the final index has an adjacent next position and a
displayed arrow in one of the two ordinary orientations. -/
theorem exists_arrowStep_of_index_lt_length
    (C : Word R) (i : C.Position)
    (hindex : i.index < C.length) :
    (∃ (y : Q) (j : C.PositionAt y) (a : i.1 ⟶ y),
        j.index = i.index + 1 ∧ C.ArrowStep a i.2 j) ∨
      (∃ (y : Q) (j : C.PositionAt y) (a : y ⟶ i.1),
        j.index = i.index + 1 ∧ C.ArrowStep a j i.2) := by
  obtain ⟨j, hj⟩ := C.exists_position_index_eq (i.index + 1) (by omega)
  rcases j with ⟨y, j⟩
  rcases C.exists_arrowStep_of_position_index_succ i ⟨y, j⟩ hj with
    hstep | hstep
  · obtain ⟨a, ha⟩ := hstep
    exact Or.inl ⟨y, j, a, hj, ha⟩
  · obtain ⟨a, ha⟩ := hstep
    exact Or.inr ⟨y, j, a, hj, ha⟩

/-- A position after the initial index has an adjacent previous position and
a displayed arrow in one of the two ordinary orientations. -/
theorem exists_arrowStep_of_index_pos
    (C : Word R) (i : C.Position)
    (hindex : 0 < i.index) :
    (∃ (x : Q) (j : C.PositionAt x) (a : x ⟶ i.1),
        j.index + 1 = i.index ∧ C.ArrowStep a j i.2) ∨
      (∃ (x : Q) (j : C.PositionAt x) (a : i.1 ⟶ x),
        j.index + 1 = i.index ∧ C.ArrowStep a i.2 j) := by
  obtain ⟨j, hj⟩ := C.exists_position_index_eq (i.index - 1) (by
    exact (Nat.sub_le i.index 1).trans i.2.index_le)
  have hsucc : i.index = j.index + 1 := by omega
  rcases C.exists_arrowStep_of_position_index_succ j i hsucc with
    hstep | hstep
  · obtain ⟨a, ha⟩ := hstep
    exact Or.inl ⟨j.1, j.2, a, hsucc.symm, ha⟩
  · obtain ⟨a, ha⟩ := hstep
    exact Or.inr ⟨j.1, j.2, a, hsucc.symm, ha⟩

/-- A fixed pair of adjacent word positions determines the displayed arrow
between them. -/
theorem arrow_eq_of_arrowSteps (C : Word R) {x y : Q}
    {a b : x ⟶ y} {i : C.PositionAt x} {j : C.PositionAt y}
    (ha : C.ArrowStep a i j) (hb : C.ArrowStep b i j) : a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hsuffix :
        (positiveArrow a).toPath = (positiveArrow b).toPath :=
      Quiver.Path.comp_injective_right i.1 (ha.symm.trans hb)
    have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
    exact Sum.inl.inj (eq_of_heq harrows)
  · have hforward : j.index = i.index + 1 := by
      change j.1.length = i.1.length + 1
      rw [ha, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    have hbackward : i.index = j.index + 1 := by
      change i.1.length = j.1.length + 1
      rw [hb, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega
  · have hbackward : i.index = j.index + 1 := by
      change i.1.length = j.1.length + 1
      rw [ha, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    have hforward : j.index = i.index + 1 := by
      change j.1.length = i.1.length + 1
      rw [hb, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega
  · have hsuffix :
        (negativeArrow a).toPath = (negativeArrow b).toPath :=
      Quiver.Path.comp_injective_right j.1 (ha.symm.trans hb)
    have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
    exact Sum.inr.inj (eq_of_heq harrows)

/-- Two displayed-arrow steps cannot traverse the same word edge in opposite
displayed directions. -/
theorem not_arrowSteps_reverse_of_index_add_one (C : Word R) {x y : Q}
    {a : x ⟶ y} {b : y ⟶ x}
    {i : C.PositionAt x} {j : C.PositionAt y}
    (ha : C.ArrowStep a i j) (hb : C.ArrowStep b j i)
    (hindex : j.index = i.index + 1) : False := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · have hbackward : i.index = j.index + 1 := by
        change i.1.length = j.1.length + 1
        rw [hb, Quiver.Path.length_comp, Quiver.Path.length_toPath]
      omega
    · have hsuffix :
          (positiveArrow a).toPath = (negativeArrow b).toPath :=
        Quiver.Path.comp_injective_right i.1 (ha.symm.trans hb)
      have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
      exact positiveArrow_ne_negativeArrow a b (eq_of_heq harrows)
  · have hbackward : i.index = j.index + 1 := by
      change i.1.length = j.1.length + 1
      rw [ha, Quiver.Path.length_comp, Quiver.Path.length_toPath]
    omega

/-- A string word has at most one target position for a displayed arrow from
a fixed source position. -/
theorem arrowStep_subsingleton (C : Word R) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) :
    Subsingleton {j : C.PositionAt y // C.ArrowStep a i j} := by
  constructor
  rintro ⟨j, hj⟩ ⟨j', hj'⟩
  apply Subtype.ext
  rcases hj with hj | hj <;> rcases hj' with hj' | hj'
  · exact Subtype.ext (hj.trans hj'.symm)
  · exfalso
    let e := negativeArrow a
    apply C.isString.1 e
    rcases j.2 with ⟨r, hr⟩
    refine ⟨j'.1, r, hr.trans ?_⟩
    calc
      j.1.comp r =
          (i.1.comp (positiveArrow a).toPath).comp r :=
        congrArg (fun p ↦ p.comp r) hj
      _ = ((j'.1.comp (negativeArrow a).toPath).comp
          (positiveArrow a).toPath).comp r :=
        congrArg
          (fun p ↦ (p.comp (positiveArrow a).toPath).comp r) hj'
      _ = j'.1.comp ((e.toPath.comp (Quiver.reverse e).toPath).comp r) := by
        change
          ((j'.1.comp (negativeArrow a).toPath).comp
              (positiveArrow a).toPath).comp r =
            j'.1.comp (((negativeArrow a).toPath.comp
              (positiveArrow a).toPath).comp r)
        simp only [Quiver.Path.comp_assoc]
  · exfalso
    let e := negativeArrow a
    apply C.isString.1 e
    rcases j'.2 with ⟨r, hr⟩
    refine ⟨j.1, r, hr.trans ?_⟩
    calc
      j'.1.comp r =
          (i.1.comp (positiveArrow a).toPath).comp r :=
        congrArg (fun p ↦ p.comp r) hj'
      _ = ((j.1.comp (negativeArrow a).toPath).comp
          (positiveArrow a).toPath).comp r :=
        congrArg
          (fun p ↦ (p.comp (positiveArrow a).toPath).comp r) hj
      _ = j.1.comp ((e.toPath.comp (Quiver.reverse e).toPath).comp r) := by
        change
          ((j.1.comp (negativeArrow a).toPath).comp
              (positiveArrow a).toPath).comp r =
            j.1.comp (((negativeArrow a).toPath.comp
              (positiveArrow a).toPath).comp r)
        simp only [Quiver.Path.comp_assoc]
  · apply Subtype.ext
    exact Quiver.Path.comp_injective_left
      (negativeArrow a).toPath (hj.symm.trans hj')

/-- The image of one position-basis vector under a displayed arrow. -/
def arrowOnBasis (C : Word R) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) : C.Space y := by
  classical
  exact if h : ∃ j : C.PositionAt y, C.ArrowStep a i j then
      Finsupp.single (Classical.choose h) 1
    else
      0

/-- At a witnessed arrow step, the corresponding basis vector is sent to the
basis vector at that target position. -/
theorem arrowOnBasis_eq_single_of_step (C : Word R)
    {x y : Q} (a : x ⟶ y) (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    C.arrowOnBasis a i = Finsupp.single j 1 := by
  classical
  rw [arrowOnBasis, dif_pos ⟨j, hij⟩]
  have hchosen :
      (⟨Classical.choose (⟨j, hij⟩),
        Classical.choose_spec (⟨j, hij⟩)⟩ :
          {l : C.PositionAt y // C.ArrowStep a i l}) =
        ⟨j, hij⟩ :=
    @Subsingleton.elim _ (C.arrowStep_subsingleton a i) _ _
  exact congrArg (fun l ↦ Finsupp.single l.1 (1 : k)) hchosen

/-- If an arrow has no target occurrence from a basis position, that basis
vector is killed. -/
theorem arrowOnBasis_eq_zero_of_not_exists (C : Word R)
    {x y : Q} (a : x ⟶ y) (i : C.PositionAt x)
    (h : ¬ ∃ j : C.PositionAt y, C.ArrowStep a i j) :
    C.arrowOnBasis a i = 0 := by
  classical
  simp only [arrowOnBasis, dif_neg h]

/-- The linear map assigned to a displayed arrow by the canonical string
representation. -/
def arrowLinearMap (C : Word R) {x y : Q} (a : x ⟶ y) :
    C.Space x →ₗ[k] C.Space y :=
  Finsupp.linearCombination k (C.arrowOnBasis a)

@[simp]
theorem arrowLinearMap_single (C : Word R) {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (c : k) :
    C.arrowLinearMap a (Finsupp.single i c) =
      c • C.arrowOnBasis a i := by
  exact Finsupp.linearCombination_single k c i

@[simp]
theorem arrowLinearMap_single_one_of_step (C : Word R)
    {x y : Q} (a : x ⟶ y) (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    C.arrowLinearMap a (Finsupp.single i 1) = Finsupp.single j 1 := by
  rw [arrowLinearMap_single, one_smul, C.arrowOnBasis_eq_single_of_step a i j hij]

instance finiteDimensional_space (C : Word R) (x : Q) :
    FiniteDimensional k (C.Space x) := inferInstance

/-- Reachability of one word-position basis vector under an ordinary quiver
path.  Each arrow is allowed to use either its positive occurrence or the
matching inverse occurrence in the word. -/
def PathReach (C : Word R) {x : Q} :
    ∀ {y : Q}, Quiver.Path x y → C.PositionAt x → C.PositionAt y → Prop
  | _, .nil, i, j => i = j
  | _, .cons p a, i, l =>
      ∃ j : C.PositionAt _, C.PathReach p i j ∧ C.ArrowStep a j l

/-- A nonempty positive traversal cannot be followed by a backward arrow
step: their final signed arrows would have opposite signs. -/
theorem not_forward_cons_then_negative (C : Word R)
    {w x y z : Q} (p : Quiver.Path w x) (b : x ⟶ y) (a : y ⟶ z)
    (i : C.PositionAt w) (j : C.PositionAt y) (l : C.PositionAt z)
    (hforward : j.1 = i.1.comp (positivePath (p.cons b)))
    (hnegative : j.1 = l.1.comp (negativeArrow a).toPath) : False := by
  have hpaths :
      (i.1.comp (positivePath p)).comp (positiveArrow b).toPath =
        l.1.comp (negativeArrow a).toPath := by
    simpa only [positivePath_cons, positivePath_toPath,
      Quiver.Path.comp_assoc] using hforward.symm.trans hnegative
  have hprefLength :
      (i.1.comp (positivePath p)).length = l.1.length := by
    have hlength := congrArg Quiver.Path.length hpaths
    rw [Quiver.Path.length_comp (i.1.comp (positivePath p))
        (positiveArrow b).toPath,
      Quiver.Path.length_comp l.1 (negativeArrow a).toPath,
      Quiver.Path.length_toPath, Quiver.Path.length_toPath] at hlength
    exact Nat.add_right_cancel hlength
  have hxz := midpoint_eq_of_comp_eq_of_left_length_eq hpaths hprefLength
  have hxzQ : x = z := hxz
  subst z
  have hsuffix := ((Quiver.Path.comp_inj' hprefLength).1 hpaths).2
  have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hsuffix
  exact positiveArrow_ne_negativeArrow b a (eq_of_heq harrows)

/-- A nonempty backward traversal cannot be followed by a forward arrow
step.  Reversing the two competing suffixes reduces this to the preceding
positive-versus-negative final-arrow contradiction. -/
theorem not_backward_cons_then_positive (C : Word R)
    {w x y z : Q} (p : Quiver.Path w x) (b : x ⟶ y) (a : y ⟶ z)
    (i : C.PositionAt w) (j : C.PositionAt y) (l : C.PositionAt z)
    (hbackward : i.1 = j.1.comp (positivePath (p.cons b)).reverse)
    (hpositive : l.1 = j.1.comp (positiveArrow a).toPath) : False := by
  rcases i.2 with ⟨ri, hri⟩
  rcases l.2 with ⟨rl, hrl⟩
  have htotal :
      (j.1.comp (positivePath (p.cons b)).reverse).comp ri =
        (j.1.comp (positiveArrow a).toPath).comp rl := by
    calc
      (j.1.comp (positivePath (p.cons b)).reverse).comp ri =
          i.1.comp ri := congrArg (fun q ↦ q.comp ri) hbackward.symm
      _ = C.path := hri.symm
      _ = l.1.comp rl := hrl
      _ = (j.1.comp (positiveArrow a).toPath).comp rl :=
        congrArg (fun q ↦ q.comp rl) hpositive
  have hsuffix :
      (positivePath (p.cons b)).reverse.comp ri =
        (positiveArrow a).toPath.comp rl := by
    apply Quiver.Path.comp_injective_right j.1
    simpa only [Quiver.Path.comp_assoc] using htotal
  have hreversed := congrArg Quiver.Path.reverse hsuffix
  simp only [Quiver.Path.reverse_comp, Quiver.Path.reverse_reverse,
    positivePath_cons, positivePath_toPath,
    Quiver.Path.comp_toPath_eq_cons, Quiver.Path.reverse_toPath,
    Quiver.symmetrify_reverse] at hreversed
  have hxz := Quiver.Path.obj_eq_of_cons_eq_cons hreversed
  subst z
  have harrows := Quiver.Path.hom_heq_of_cons_eq_cons hreversed
  exact positiveArrow_ne_negativeArrow b a (eq_of_heq harrows)

/-- A reachable ordinary path moves monotonically along the word: it is
realized either by the positive copy of the whole path or by the reversed
positive copy in the opposite direction. -/
theorem pathReach_forward_or_backward (C : Word R) :
    ∀ {x y : Q} (p : Quiver.Path x y)
      (i : C.PositionAt x) (j : C.PositionAt y),
      C.PathReach p i j →
        j.1 = i.1.comp (positivePath p) ∨
          i.1 = j.1.comp (positivePath p).reverse := by
  intro x y p
  induction p with
  | nil =>
      intro i j hij
      exact Or.inl (congrArg Subtype.val hij).symm
  | @cons z y p a ih =>
      intro i l hil
      rcases hil with ⟨j, hij, hjl⟩
      rcases ih i j hij with hforward | hbackward
      · rcases hjl with hpositive | hnegative
        · left
          calc
            l.1 = j.1.comp (positiveArrow a).toPath := hpositive
            _ = (i.1.comp (positivePath p)).comp
                (positiveArrow a).toPath :=
              congrArg (fun q ↦ q.comp (positiveArrow a).toPath) hforward
            _ = i.1.comp (positivePath (p.cons a)) := by
              simp only [positivePath_cons, positivePath_toPath,
                Quiver.Path.comp_assoc]
        · cases p with
          | nil =>
              right
              simpa only [positivePath_cons, positivePath_nil,
                positivePath_toPath, Quiver.Path.nil_comp,
                Quiver.Path.comp_nil,
                Quiver.Path.reverse_toPath, reverse_positiveArrow] using
                hforward.symm.trans hnegative
          | @cons w z p b =>
              exact False.elim
                (C.not_forward_cons_then_negative p b a i j l
                  hforward hnegative)
      · rcases hjl with hpositive | hnegative
        · cases p with
          | nil =>
              left
              have hji : j.1 = i.1 := by
                simpa only [positivePath_nil, Quiver.Path.reverse,
                  Quiver.Path.comp_nil] using hbackward.symm
              calc
                l.1 = j.1.comp (positiveArrow a).toPath := hpositive
                _ = i.1.comp (positiveArrow a).toPath :=
                  congrArg (fun q ↦ q.comp (positiveArrow a).toPath) hji
                _ = i.1.comp (positivePath (Quiver.Path.nil.cons a)) := by
                  simp only [positivePath_cons, positivePath_nil,
                    positivePath_toPath, Quiver.Path.nil_comp]
          | @cons w z p b =>
              exact False.elim
                (C.not_backward_cons_then_positive p b a i j l
                  hbackward hpositive)
        · right
          calc
            i.1 = j.1.comp (positivePath p).reverse := hbackward
            _ = (l.1.comp (negativeArrow a).toPath).comp
                (positivePath p).reverse :=
              congrArg (fun q ↦ q.comp (positivePath p).reverse) hnegative
            _ = l.1.comp (positivePath (p.cons a)).reverse := by
              simp only [positivePath_cons, positivePath_toPath,
                Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
                reverse_positiveArrow, Quiver.Path.comp_assoc]

/-- A reachable path occurs as one contiguous positive segment of the word
or of its reverse. -/
theorem pathReach_contiguous_forward_or_reverse (C : Word R)
    {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.PathReach p i j) :
    IsContiguousSubpath (positivePath p) C.path ∨
      IsContiguousSubpath (positivePath p) C.path.reverse := by
  rcases C.pathReach_forward_or_backward p i j hij with
    hforward | hbackward
  · left
    rcases j.2 with ⟨r, hr⟩
    refine ⟨i.1, r, ?_⟩
    calc
      C.path = j.1.comp r := hr
      _ = (i.1.comp (positivePath p)).comp r :=
        congrArg (fun q ↦ q.comp r) hforward
      _ = i.1.comp ((positivePath p).comp r) :=
        Quiver.Path.comp_assoc _ _ _
  · right
    rcases i.2 with ⟨r, hr⟩
    have hsub :
        IsContiguousSubpath (positivePath p).reverse C.path := by
      refine ⟨j.1, r, ?_⟩
      calc
        C.path = i.1.comp r := hr
        _ = (j.1.comp (positivePath p).reverse).comp r :=
          congrArg (fun q ↦ q.comp r) hbackward
        _ = j.1.comp ((positivePath p).reverse.comp r) :=
          Quiver.Path.comp_assoc _ _ _
    apply (isContiguousSubpath_reverse_iff
      (positivePath p) C.path.reverse).1
    simpa only [Quiver.Path.reverse_reverse] using hsub

/-- Every ordinary path which acts nontrivially on a position basis survives
the string-algebra relation quotient. -/
theorem pathMap_ne_zero_of_pathReach (C : Word R)
    {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.PathReach p i j) : pathMap R p ≠ 0 := by
  rcases C.pathReach_contiguous_forward_or_reverse p i j hij with
    hforward | hreverse
  · exact C.isString.2.1 p hforward
  · exact C.isString.2.2 p hreverse

/-- Reduction makes the endpoint of a reachable path unique. -/
theorem pathReach_subsingleton (C : Word R) {x y : Q}
    (p : Quiver.Path x y) (i : C.PositionAt x) :
    Subsingleton {j : C.PositionAt y // C.PathReach p i j} := by
  induction p with
  | nil =>
      constructor
      rintro ⟨j, hj⟩ ⟨l, hl⟩
      apply Subtype.ext
      exact hj.symm.trans hl
  | @cons z y p a ih =>
      constructor
      rintro ⟨l, j, hj, hjl⟩ ⟨l', j', hj', hjl'⟩
      have hmiddle :
          (⟨j, hj⟩ : {t : C.PositionAt z // C.PathReach p i t}) =
            ⟨j', hj'⟩ :=
        @Subsingleton.elim _ ih _ _
      have hjj' : j = j' := congrArg Subtype.val hmiddle
      subst j'
      have htarget :
          (⟨l, hjl⟩ : {t : C.PositionAt y // C.ArrowStep a j t}) =
            ⟨l', hjl'⟩ :=
        @Subsingleton.elim _ (C.arrowStep_subsingleton a j) _ _
      have hll' : l = l' := congrArg
        (fun t : {s : C.PositionAt y // C.ArrowStep a j s} ↦ t.1) htarget
      exact Subtype.ext hll'

/-- The image of a position-basis vector under a quiver path, expressed as
the unique reachable basis vector when it exists. -/
def pathOnBasis (C : Word R) {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) : C.Space y := by
  classical
  exact if h : ∃ j : C.PositionAt y, C.PathReach p i j then
      Finsupp.single (Classical.choose h) 1
    else
      0

theorem pathOnBasis_eq_single_of_reach (C : Word R)
    {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.PathReach p i j) :
    C.pathOnBasis p i = Finsupp.single j 1 := by
  classical
  rw [pathOnBasis, dif_pos ⟨j, hij⟩]
  have hchosen :
      (⟨Classical.choose (⟨j, hij⟩),
        Classical.choose_spec (⟨j, hij⟩)⟩ :
          {l : C.PositionAt y // C.PathReach p i l}) =
        ⟨j, hij⟩ :=
    @Subsingleton.elim _ (C.pathReach_subsingleton p i) _ _
  exact congrArg (fun l ↦ Finsupp.single l.1 (1 : k)) hchosen

theorem pathOnBasis_eq_zero_of_not_exists (C : Word R)
    {x y : Q} (p : Quiver.Path x y) (i : C.PositionAt x)
    (h : ¬ ∃ j : C.PositionAt y, C.PathReach p i j) :
    C.pathOnBasis p i = 0 := by
  classical
  simp only [pathOnBasis, dif_neg h]

/-- The canonical quiver representation of a string word before descending
through the relation quotient. -/
def quiverRepresentation (C : Word R) :
    LinearPathCategory.QuiverRep k Q :=
  Paths.lift
    { obj := fun x ↦ ModuleCat.of k (C.Space x)
      map := fun a ↦ ModuleCat.ofHom (C.arrowLinearMap a) }

/-- Evaluation of the canonical representation with the original displayed
vertices pinned explicitly. -/
def quiverMap (C : Word R) {x y : Q} (p : Quiver.Path x y) :
    ModuleCat.of k (C.Space x) ⟶ ModuleCat.of k (C.Space y) :=
  C.quiverRepresentation.map p

@[simp]
theorem quiverMap_nil (C : Word R) (x : Q) :
    C.quiverMap (Quiver.Path.nil : Quiver.Path x x) = 𝟙 _ :=
  C.quiverRepresentation.map_id x

theorem quiverMap_comp (C : Word R) {x y z : Q}
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    C.quiverMap (p.comp q) = C.quiverMap p ≫ C.quiverMap q :=
  C.quiverRepresentation.map_comp p q

@[simp]
theorem quiverRepresentation_obj (C : Word R) (x : Q) :
    C.quiverRepresentation.obj x = ModuleCat.of k (C.Space x) :=
  rfl

@[simp]
theorem quiverRepresentation_map_toPath (C : Word R)
    {x y : Q} (a : x ⟶ y) :
    C.quiverRepresentation.map a.toPath =
      ModuleCat.ofHom (C.arrowLinearMap a) := by
  exact Paths.lift_toPath _ a

@[simp]
theorem quiverMap_toPath (C : Word R) {x y : Q} (a : x ⟶ y) :
    C.quiverMap a.toPath = ModuleCat.ofHom (C.arrowLinearMap a) :=
  C.quiverRepresentation_map_toPath a

/-- Applying one more displayed arrow to the path image of a basis position
agrees with extending position reachability by that arrow. -/
theorem arrowLinearMap_pathOnBasis (C : Word R)
    {x y z : Q} (p : Quiver.Path x y) (a : y ⟶ z)
    (i : C.PositionAt x) :
    C.arrowLinearMap a (C.pathOnBasis p i) =
      C.pathOnBasis (p.cons a) i := by
  classical
  by_cases hp : ∃ j : C.PositionAt y, C.PathReach p i j
  · let j := Classical.choose hp
    have hj : C.PathReach p i j := Classical.choose_spec hp
    rw [C.pathOnBasis_eq_single_of_reach p i j hj]
    by_cases ha : ∃ l : C.PositionAt z, C.ArrowStep a j l
    · let l := Classical.choose ha
      have hl : C.ArrowStep a j l := Classical.choose_spec ha
      rw [C.arrowLinearMap_single_one_of_step a j l hl]
      exact C.pathOnBasis_eq_single_of_reach (p.cons a) i l ⟨j, hj, hl⟩ |>.symm
    · rw [arrowLinearMap_single, one_smul,
        C.arrowOnBasis_eq_zero_of_not_exists a j ha]
      symm
      apply (C.pathOnBasis_eq_zero_of_not_exists (p.cons a) i)
      rintro ⟨l, j', hj', hj'l⟩
      have hmiddle :
          (⟨j, hj⟩ : {t : C.PositionAt y // C.PathReach p i t}) =
            ⟨j', hj'⟩ :=
        @Subsingleton.elim _ (C.pathReach_subsingleton p i) _ _
      have : j = j' := congrArg
        (fun t : {s : C.PositionAt y // C.PathReach p i s} ↦ t.1) hmiddle
      subst j'
      exact ha ⟨l, hj'l⟩
  · rw [C.pathOnBasis_eq_zero_of_not_exists p i hp, map_zero]
    symm
    apply (C.pathOnBasis_eq_zero_of_not_exists (p.cons a) i)
    rintro ⟨l, j, hj, _⟩
    exact hp ⟨j, hj⟩

/-- Evaluation of an ordinary quiver path on a position-basis vector is the
unique reachable basis vector, or zero when no such position exists. -/
theorem quiverRepresentation_map_single (C : Word R)
    {x y : Q} (p : Quiver.Path x y)
    (i : C.PositionAt x) (c : k) :
    C.quiverRepresentation.map p (Finsupp.single i c) =
      c • C.pathOnBasis p i := by
  induction p with
  | nil =>
      rw [LinearPathCategory.QuiverRep.map_nil, ModuleCat.id_apply]
      have hi : C.PathReach (Quiver.Path.nil : Quiver.Path x x) i i := rfl
      rw [C.pathOnBasis_eq_single_of_reach Quiver.Path.nil i i hi]
      exact (Finsupp.smul_single_one i c).symm
  | @cons z y p a ih =>
      rw [show C.quiverRepresentation.map (p.cons a) =
          C.quiverRepresentation.map p ≫
            C.quiverRepresentation.map a.toPath by
        exact C.quiverRepresentation.map_comp p a.toPath]
      rw [ModuleCat.comp_apply, ih,
        C.quiverRepresentation_map_toPath a]
      change C.arrowLinearMap a (c • C.pathOnBasis p i) = _
      rw [map_smul, C.arrowLinearMap_pathOnBasis p a i]

/-- Every ordinary path killed by the relation quotient acts as zero on the
canonical string representation. -/
theorem quiverRepresentation_map_eq_zero_of_pathMap_eq_zero (C : Word R)
    {x y : Q} (p : Quiver.Path x y) (hp : pathMap R p = 0) :
    C.quiverRepresentation.map p = 0 := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro i c
  change C.quiverRepresentation.map p (Finsupp.single i c) = 0
  rw [C.quiverRepresentation_map_single p i c]
  have hnone : ¬ ∃ j : C.PositionAt y, C.PathReach p i j := by
    rintro ⟨j, hij⟩
    exact C.pathMap_ne_zero_of_pathReach p i j hij hp
  rw [C.pathOnBasis_eq_zero_of_not_exists p i hnone, smul_zero]
  rfl

/-- The reversed linear realization of the canonical quiver representation as
a right module over the free linear path category. -/
def freeRightModuleAux (C : Word R) :
    LinearPathCategory.Category k Q ⥤ (ModuleCat.{u} k)ᵒᵖ :=
  LinearPathCategory.lift
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun a ↦ (ModuleCat.ofHom (C.arrowLinearMap a)).op)

/-- Reversed path evaluation agrees with the opposite of evaluation in the
canonical quiver representation. -/
theorem freeRightModuleAux_pathMap (C : Word R) {x y : Q}
    (p : Quiver.Path x y) :
    LinearPathCategory.pathMap
        (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
        (fun a ↦ (ModuleCat.ofHom (C.arrowLinearMap a)).op) p =
      (C.quiverMap p).op := by
  induction p with
  | nil => simp
  | cons p a ih =>
      rw [LinearPathCategory.pathMap_cons, ih]
      rw [← C.quiverMap_toPath a, ← op_comp]
      exact congrArg Quiver.Hom.op (C.quiverMap_comp p a.toPath).symm

/-- On a path-basis morphism, the free right-module realization is the
opposite of the corresponding quiver-representation map. -/
@[simp]
theorem freeRightModuleAux_map_pathHom (C : Word R)
    {x y : LinearPathCategory.Category k Q}
    (p : Quiver.Path (LinearPathCategory.vertex y)
      (LinearPathCategory.vertex x)) :
    C.freeRightModuleAux.map (LinearPathCategory.pathHom p) =
      (C.quiverMap p).op := by
  unfold freeRightModuleAux
  exact (LinearPathCategory.lift_map_pathHom
    (fun x ↦ Opposite.op (ModuleCat.of k (C.Space x)))
    (fun a ↦ (ModuleCat.ofHom (C.arrowLinearMap a)).op) p).trans
      (C.freeRightModuleAux_pathMap p)

instance freeRightModuleAux_additive (C : Word R) :
    C.freeRightModuleAux.Additive := by
  unfold freeRightModuleAux
  infer_instance

instance freeRightModuleAux_linear (C : Word R) :
    C.freeRightModuleAux.Linear k := by
  unfold freeRightModuleAux
  infer_instance

/-- For a monomial presentation, the free realization of a string word kills
the complete generated relation ideal. -/
theorem relationIdeal_isKilledBy (C : Word R) (hmono : IsMonomial R) :
    (LinearPathCategory.HomogeneousQuotient.relationIdeal R).IsKilledBy
      C.freeRightModuleAux := by
  intro X Y f hf
  change f ∈ HomIdeal.generatedHomSubmodule k R X Y at hf
  have hspan :
      HomIdeal.generatedHomSubmodule k R X Y =
        Submodule.span k
          ((fun p : Quiver.Path
              (LinearPathCategory.vertex Y)
              (LinearPathCategory.vertex X) ↦
                LinearPathCategory.pathHom p) ''
            {p : Quiver.Path
              (LinearPathCategory.vertex Y)
              (LinearPathCategory.vertex X) | pathMap R p = 0}) := by
    exact hmono (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)
  rw [hspan] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨p, hp, rfl⟩
      rw [C.freeRightModuleAux_map_pathHom p,
        show C.quiverMap p = 0 from
          C.quiverRepresentation_map_eq_zero_of_pathMap_eq_zero p hp]
      rfl
  | zero => simp
  | add g h _ _ hg hh =>
      rw [C.freeRightModuleAux.map_add, hg, hh, add_zero]
  | smul c g _ hg =>
      rw [C.freeRightModuleAux.map_smul, hg, smul_zero]

/-- The string-word realization descended through a monomial relation
quotient, still written covariantly with values in the opposite module
category. -/
def quotientRightModuleAux (C : Word R) (hmono : IsMonomial R) :
    Category R ⥤ (ModuleCat.{u} k)ᵒᵖ :=
  (LinearPathCategory.HomogeneousQuotient.relationIdeal R).quotientLift
    C.freeRightModuleAux (C.relationIdeal_isKilledBy hmono)

instance quotientRightModuleAux_additive (C : Word R)
    (hmono : IsMonomial R) :
    (C.quotientRightModuleAux hmono).Additive := by
  unfold quotientRightModuleAux
  infer_instance

instance quotientRightModuleAux_linear (C : Word R)
    (hmono : IsMonomial R) :
    (C.quotientRightModuleAux hmono).Linear k := by
  unfold quotientRightModuleAux
  infer_instance

/-- The canonical finite-dimensional right module represented by a string
word. -/
def rightModule (C : Word R) (hmono : IsMonomial R) :
    (Category R)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj X := (C.quotientRightModuleAux hmono |>.obj X.unop).unop
  map f := (C.quotientRightModuleAux hmono |>.map f.unop).unop
  map_id X := by
    apply Quiver.Hom.op_inj
    simp
  map_comp f g := by
    apply Quiver.Hom.op_inj
    rw [unop_comp, Functor.map_comp]
    rfl

@[simp]
theorem rightModule_obj (C : Word R) (hmono : IsMonomial R) (x : Q) :
    (C.rightModule hmono).obj (Opposite.op (obj R x)) =
      ModuleCat.of k (C.Space x) :=
  rfl

/-- The descended right module evaluates a quotient path by the canonical
position-basis path map. -/
@[simp]
theorem rightModule_map_pathMap (C : Word R) (hmono : IsMonomial R)
    {x y : Q} (p : Quiver.Path x y) :
    (C.rightModule hmono).map (pathMap R p).op = C.quiverMap p := by
  change ((C.quotientRightModuleAux hmono).map (pathMap R p)).unop = _
  change
    ((C.quotientRightModuleAux hmono).map
      ((LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map
        (LinearPathCategory.pathHom p))).unop = _
  unfold quotientRightModuleAux
  rw [HomIdeal.quotientLift_map_functor_map,
    C.freeRightModuleAux_map_pathHom p]
  rfl

end Word

end StringWord

end MagnitudeConjecture.BoundQuiver
