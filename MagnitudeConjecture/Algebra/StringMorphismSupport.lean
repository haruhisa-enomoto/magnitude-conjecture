import MagnitudeConjecture.Algebra.StringMorphismCoefficient
import Mathlib.Logic.Relation

/-!
# Coefficient-support components of string morphisms

Naturality presents the matrix coefficients of a morphism between two string
modules by equality constraints along matched word steps and zero constraints
at unmatched boundaries.  This file packages that presentation as a graph on
pairs of word positions.  Its connected components are the ambient objects
from which graph-map overlaps will be extracted.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A possible matrix-coefficient position for a morphism from `C` to `D`:
two word positions lying over the same displayed vertex. -/
def MorphismCoefficientPosition (C D : Word R) :=
  Σ x : Q, C.PositionAt x × D.PositionAt x

/-- The source-word index of a coefficient position. -/
def MorphismCoefficientPosition.inputIndex {C D : Word R}
    (p : C.MorphismCoefficientPosition D) : ℕ :=
  p.2.1.index

/-- The target-word index of a coefficient position. -/
def MorphismCoefficientPosition.outputIndex {C D : Word R}
    (p : C.MorphismCoefficientPosition D) : ℕ :=
  p.2.2.index

/-- The source-word position underlying a coefficient position. -/
def MorphismCoefficientPosition.inputPosition {C D : Word R}
    (p : C.MorphismCoefficientPosition D) : C.Position :=
  ⟨p.1, p.2.1⟩

/-- The target-word position underlying a coefficient position. -/
def MorphismCoefficientPosition.outputPosition {C D : Word R}
    (p : C.MorphismCoefficientPosition D) : D.Position :=
  ⟨p.1, p.2.2⟩

@[simp]
theorem MorphismCoefficientPosition.inputPosition_index {C D : Word R}
    (p : C.MorphismCoefficientPosition D) :
    p.inputPosition.index = p.inputIndex :=
  rfl

@[simp]
theorem MorphismCoefficientPosition.outputPosition_index {C D : Word R}
    (p : C.MorphismCoefficientPosition D) :
    p.outputPosition.index = p.outputIndex :=
  rfl

/-- The two word indices determine a coefficient position. -/
def morphismCoefficientPositionIndexEmbedding (C D : Word R) :
    C.MorphismCoefficientPosition D ↪
      Fin (C.length + 1) × Fin (D.length + 1) where
  toFun p :=
    (⟨p.inputIndex, Nat.lt_succ_of_le p.2.1.index_le⟩,
      ⟨p.outputIndex, Nat.lt_succ_of_le p.2.2.index_le⟩)
  inj' := by
    intro p q h
    have hinput : p.inputPosition = q.inputPosition :=
      Position.ext_index (congrArg (fun t => t.1.1) h)
    have houtput : p.outputPosition = q.outputPosition :=
      Position.ext_index (congrArg (fun t => t.2.1) h)
    rcases p with ⟨x, i, i'⟩
    rcases q with ⟨y, j, j'⟩
    cases hinput
    cases houtput
    rfl

instance morphismCoefficientPosition_finite (C D : Word R) :
    Finite (C.MorphismCoefficientPosition D) :=
  Finite.of_injective (C.morphismCoefficientPositionIndexEmbedding D)
    (C.morphismCoefficientPositionIndexEmbedding D).injective

/-- A coefficient position on the diagonal of an endomorphism matrix. -/
def diagonalMorphismCoefficientPosition (C : Word R) {x : Q}
    (i : C.PositionAt x) : C.MorphismCoefficientPosition C :=
  ⟨x, i, i⟩

/-- The value of a string-module morphism at one coefficient position. -/
def morphismCoefficientAt
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (p : C.MorphismCoefficientPosition D) : k :=
  match p with
  | ⟨_, i, j⟩ => C.morphismCoefficient D hC hD f i j

@[simp]
theorem morphismCoefficientAt_zero
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD
        (0 : C.rightModule hC ⟶ D.rightModule hD) p = 0 := by
  rcases p with ⟨x, i, j⟩
  rfl

@[simp]
theorem morphismCoefficientAt_add
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f g : C.rightModule hC ⟶ D.rightModule hD)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD (f + g) p =
      C.morphismCoefficientAt D hC hD f p +
        C.morphismCoefficientAt D hC hD g p := by
  rcases p with ⟨x, i, j⟩
  rfl

@[simp]
theorem morphismCoefficientAt_neg
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD (-f) p =
      -C.morphismCoefficientAt D hC hD f p := by
  rcases p with ⟨x, i, j⟩
  rfl

@[simp]
theorem morphismCoefficientAt_sub
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f g : C.rightModule hC ⟶ D.rightModule hD)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD (f - g) p =
      C.morphismCoefficientAt D hC hD f p -
        C.morphismCoefficientAt D hC hD g p := by
  rcases p with ⟨x, i, j⟩
  rfl

@[simp]
theorem morphismCoefficientAt_smul
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (c : k) (f : C.rightModule hC ⟶ D.rightModule hD)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD (c • f) p =
      c * C.morphismCoefficientAt D hC hD f p := by
  rcases p with ⟨x, i, j⟩
  rfl

theorem morphismCoefficientAt_sum
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    {ι : Type*} (s : Finset ι)
    (f : ι → (C.rightModule hC ⟶ D.rightModule hD))
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD (∑ i ∈ s, f i) p =
      ∑ i ∈ s, C.morphismCoefficientAt D hC hD (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih]

/-- A morphism between position-basis string modules is determined by all of
its position coefficients. -/
theorem rightModuleHom_ext_morphismCoefficientAt
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    {f g : C.rightModule hC ⟶ D.rightModule hD}
    (hcoeff : ∀ p : C.MorphismCoefficientPosition D,
      C.morphismCoefficientAt D hC hD f p =
        C.morphismCoefficientAt D hC hD g p) :
    f = g := by
  apply NatTrans.ext
  funext X
  rcases X with ⟨⟨x⟩⟩
  let xQ : Q := LinearPathCategory.vertex x
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro i c
  apply Finsupp.ext
  intro j
  have hij := hcoeff
    (⟨xQ, (i, j)⟩ : C.MorphismCoefficientPosition D)
  change
    (show D.Space xQ from
      (f.app (Opposite.op (obj R xQ))).hom (Finsupp.single i 1)) j =
    (show D.Space xQ from
      (g.app (Opposite.op (obj R xQ))).hom (Finsupp.single i 1)) j at hij
  have hs : Finsupp.single i c = c • Finsupp.single i 1 := by simp
  rw [hs, map_smul, map_smul]
  change
    (c • (show D.Space xQ from
      (f.app (Opposite.op (obj R xQ))).hom (Finsupp.single i 1))) j =
    (c • (show D.Space xQ from
      (g.app (Opposite.op (obj R xQ))).hom (Finsupp.single i 1))) j
  rw [Finsupp.smul_apply, Finsupp.smul_apply, hij]

/-- An equality edge between coefficient positions.  Both words cross the
same displayed arrow, so naturality identifies the two coefficients. -/
inductive MorphismCoefficientStep (C D : Word R) :
    C.MorphismCoefficientPosition D →
      C.MorphismCoefficientPosition D → Prop
  | ofArrow {x y : Q} (a : x ⟶ y)
      (i : C.PositionAt x) (j : C.PositionAt y)
      (i' : D.PositionAt x) (j' : D.PositionAt y)
      (hij : C.ArrowStep a i j) (hij' : D.ArrowStep a i' j') :
      MorphismCoefficientStep C D ⟨x, i, i'⟩ ⟨y, j, j'⟩

/-- A matched-step edge moves one index in each of the two words. -/
theorem MorphismCoefficientStep.index
    (C D : Word R) {p q : C.MorphismCoefficientPosition D}
    (hpq : C.MorphismCoefficientStep D p q) :
    (q.inputIndex = p.inputIndex + 1 ∨
        p.inputIndex = q.inputIndex + 1) ∧
      (q.outputIndex = p.outputIndex + 1 ∨
        p.outputIndex = q.outputIndex + 1) := by
  cases hpq with
  | ofArrow a i j i' j' hij hij' =>
      exact ⟨hij.index, hij'.index⟩

/-- A zero boundary in the coefficient constraint graph.  The first
constructor records a source-word step with no matching incoming target-word
step; the second records a target-word step with no matching outgoing
source-word step. -/
inductive IsMorphismCoefficientBoundary (C D : Word R) :
    C.MorphismCoefficientPosition D → Prop
  | source {x y : Q} (a : x ⟶ y)
      (i : C.PositionAt x) (j : C.PositionAt y)
      (j' : D.PositionAt y)
      (hij : C.ArrowStep a i j)
      (hj' : ¬ ∃ i' : D.PositionAt x, D.ArrowStep a i' j') :
      IsMorphismCoefficientBoundary C D ⟨y, j, j'⟩
  | target {x y : Q} (a : x ⟶ y)
      (i : C.PositionAt x) (i' : D.PositionAt x)
      (j' : D.PositionAt y)
      (hi : ¬ ∃ j : C.PositionAt y, C.ArrowStep a i j)
      (hij' : D.ArrowStep a i' j') :
      IsMorphismCoefficientBoundary C D ⟨x, i, i'⟩

/-- A generated coefficient component contains no naturality boundary marked
as zero. -/
def IsBoundaryFreeMorphismCoefficientComponent
    (C D : Word R) (root : C.MorphismCoefficientPosition D) : Prop :=
  ∀ q, Relation.EqvGen (C.MorphismCoefficientStep D) root q →
    ¬ C.IsMorphismCoefficientBoundary D q

private theorem diagonalMorphismCoefficientPosition_eqvGen_source_of_prefix
    (C : Word R) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) C.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x C.target)
      (hpq : C.path = p.comp q),
      Relation.EqvGen (C.MorphismCoefficientStep C)
        (C.diagonalMorphismCoefficientPosition
          (⟨p, ⟨q, hpq⟩⟩ : C.PositionAt x))
        (C.diagonalMorphismCoefficientPosition C.sourcePosition) := by
  intro x p
  induction p with
  | nil =>
      intro q hpq
      have hi :
          (⟨Quiver.Path.nil, ⟨q, hpq⟩⟩ :
              C.PositionAt C.source) = C.sourcePosition := by
        apply PositionAt.ext_index
        rfl
      rw [hi]
      exact Relation.EqvGen.refl _
  | @cons y z p e ih =>
      intro q hpq
      have hprefix : C.path = p.comp (e.toPath.comp q) := by
        calc
          C.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : C.PositionAt y :=
        ⟨p, ⟨e.toPath.comp q, hprefix⟩⟩
      have hprev : Relation.EqvGen (C.MorphismCoefficientStep C)
          (C.diagonalMorphismCoefficientPosition iprev)
          (C.diagonalMorphismCoefficientPosition C.sourcePosition) :=
        ih (e.toPath.comp q) hprefix
      rcases e with a | a
      · let icurr : C.PositionAt z :=
          ⟨p.cons (Sum.inl a), ⟨q, hpq⟩⟩
        have hstep : C.ArrowStep a iprev icurr := Or.inl rfl
        have hedge : C.MorphismCoefficientStep C
            (C.diagonalMorphismCoefficientPosition iprev)
            (C.diagonalMorphismCoefficientPosition icurr) :=
          MorphismCoefficientStep.ofArrow a iprev icurr iprev icurr
            hstep hstep
        change Relation.EqvGen (C.MorphismCoefficientStep C)
          (C.diagonalMorphismCoefficientPosition icurr) _
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hedge)) hprev
      · let icurr : C.PositionAt z :=
          ⟨p.cons (Sum.inr a), ⟨q, hpq⟩⟩
        have hstep : C.ArrowStep a icurr iprev := Or.inr rfl
        have hedge : C.MorphismCoefficientStep C
            (C.diagonalMorphismCoefficientPosition icurr)
            (C.diagonalMorphismCoefficientPosition iprev) :=
          MorphismCoefficientStep.ofArrow a icurr iprev icurr iprev
            hstep hstep
        change Relation.EqvGen (C.MorphismCoefficientStep C)
          (C.diagonalMorphismCoefficientPosition icurr) _
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ hedge) hprev

/-- All diagonal coefficient positions of one word lie in the component of
the source position. -/
theorem diagonalMorphismCoefficientPosition_eqvGen_source
    (C : Word R) {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep C)
      (C.diagonalMorphismCoefficientPosition i)
      (C.diagonalMorphismCoefficientPosition C.sourcePosition) := by
  rcases i with ⟨p, q, hpq⟩
  exact C.diagonalMorphismCoefficientPosition_eqvGen_source_of_prefix
    p q hpq

/-- Coefficients agree across one matched-step edge. -/
theorem morphismCoefficientAt_eq_of_step
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : C.MorphismCoefficientStep D p q) :
    C.morphismCoefficientAt D hC hD f p =
      C.morphismCoefficientAt D hC hD f q := by
  cases hpq with
  | ofArrow a i j i' j' hij hij' =>
      exact C.morphismCoefficient_eq_of_arrowSteps D hC hD f
        a i j i' j' hij hij'

/-- Every coefficient marked by an unmatched boundary is zero. -/
theorem morphismCoefficientAt_eq_zero_of_boundary
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {p : C.MorphismCoefficientPosition D}
    (hp : C.IsMorphismCoefficientBoundary D p) :
    C.morphismCoefficientAt D hC hD f p = 0 := by
  cases hp with
  | source a i j j' hij hj' =>
      exact C.morphismCoefficient_eq_zero_of_source_step_of_no_target_source
        D hC hD f a i j j' hij hj'
  | target a i i' j' hi hij' =>
      exact C.morphismCoefficient_eq_zero_of_no_source_target_of_target_step
        D hC hD f a i i' j' hi hij'

/-- Coefficients are constant on every equivalence component generated by
matched-step edges. -/
theorem morphismCoefficientAt_eq_of_eqvGen
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    C.morphismCoefficientAt D hC hD f p =
      C.morphismCoefficientAt D hC hD f q := by
  induction hpq with
  | rel p q hpq =>
      exact C.morphismCoefficientAt_eq_of_step D hC hD f hpq
  | refl => rfl
  | symm p q _ hpq => exact hpq.symm
  | trans p q r _ _ hpq hqr => exact hpq.trans hqr

/-- If a coefficient component reaches an unmatched boundary, every
coefficient in that component vanishes. -/
theorem morphismCoefficientAt_eq_zero_of_eqvGen_boundary
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q)
    (hq : C.IsMorphismCoefficientBoundary D q) :
    C.morphismCoefficientAt D hC hD f p = 0 :=
  (C.morphismCoefficientAt_eq_of_eqvGen D hC hD f hpq).trans
    (C.morphismCoefficientAt_eq_zero_of_boundary D hC hD f hq)

/-- Nonvanishing is constant on a coefficient component. -/
theorem morphismCoefficientAt_ne_zero_iff_of_eqvGen
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    C.morphismCoefficientAt D hC hD f p ≠ 0 ↔
      C.morphismCoefficientAt D hC hD f q ≠ 0 := by
  rw [C.morphismCoefficientAt_eq_of_eqvGen D hC hD f hpq]

/-- A nonzero coefficient component contains no unmatched boundary. -/
theorem not_boundary_of_morphismCoefficientAt_ne_zero_of_eqvGen
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    {p q : C.MorphismCoefficientPosition D}
    (hp : C.morphismCoefficientAt D hC hD f p ≠ 0)
    (hpq : Relation.EqvGen (C.MorphismCoefficientStep D) p q) :
    ¬ C.IsMorphismCoefficientBoundary D q := by
  intro hq
  exact hp (C.morphismCoefficientAt_eq_zero_of_eqvGen_boundary
    D hC hD f hpq hq)

/-- The component of every nonzero coefficient of an actual morphism is
boundary-free. -/
theorem isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (root : C.MorphismCoefficientPosition D)
    (hroot : C.morphismCoefficientAt D hC hD f root ≠ 0) :
    C.IsBoundaryFreeMorphismCoefficientComponent D root := by
  intro q hq
  exact C.not_boundary_of_morphismCoefficientAt_ne_zero_of_eqvGen
    D hC hD f hroot hq

end MagnitudeConjecture.BoundQuiver.StringWord.Word
