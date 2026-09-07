import MagnitudeConjecture.Algebra.StringMorphismSupport

/-!
# Module maps carried by boundary-free coefficient components

Every boundary-free equality component in the coefficient constraint graph
defines a morphism between the corresponding string modules: put coefficient
one on the component and zero elsewhere.  Naturality is exactly the statement
that matched-step edges carry equal coefficients and unmatched boundaries
carry coefficient zero.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The scalar indicator of one generated coefficient component. -/
def coefficientComponentIndicator (C D : Word R)
    (root p : C.MorphismCoefficientPosition D) : k := by
  classical
  exact if Relation.EqvGen (C.MorphismCoefficientStep D) root p
    then 1 else 0

theorem coefficientComponentIndicator_eq_one (C D : Word R)
    (root p : C.MorphismCoefficientPosition D)
    (hp : Relation.EqvGen (C.MorphismCoefficientStep D) root p) :
    C.coefficientComponentIndicator D root p = 1 := by
  classical
  simp [coefficientComponentIndicator, hp]

theorem coefficientComponentIndicator_eq_zero (C D : Word R)
    (root p : C.MorphismCoefficientPosition D)
    (hp : ¬ Relation.EqvGen (C.MorphismCoefficientStep D) root p) :
    C.coefficientComponentIndicator D root p = 0 := by
  classical
  simp [coefficientComponentIndicator, hp]

/-- The position-basis vector whose coordinates are the indicator of one
coefficient component above a fixed source position. -/
def coefficientComponentOnBasis (C D : Word R)
    (root : C.MorphismCoefficientPosition D)
    {x : Q} (i : C.PositionAt x) : D.Space x := by
  classical
  exact Finsupp.equivFunOnFinite.symm fun j =>
    C.coefficientComponentIndicator D root ⟨x, i, j⟩

@[simp]
theorem coefficientComponentOnBasis_apply (C D : Word R)
    (root : C.MorphismCoefficientPosition D)
    {x : Q} (i : C.PositionAt x) (j : D.PositionAt x) :
    C.coefficientComponentOnBasis D root i j =
      C.coefficientComponentIndicator D root
        (⟨x, (i, j)⟩ : C.MorphismCoefficientPosition D) := by
  classical
  simp [coefficientComponentOnBasis]

/-- Extend a component indicator linearly from the source position basis. -/
def coefficientComponentLinearMap (C D : Word R)
    (root : C.MorphismCoefficientPosition D) (x : Q) :
    C.Space x →ₗ[k] D.Space x :=
  Finsupp.linearCombination k (C.coefficientComponentOnBasis D root)

@[simp]
theorem coefficientComponentLinearMap_single (C D : Word R)
    (root : C.MorphismCoefficientPosition D)
    {x : Q} (i : C.PositionAt x) (c : k) :
    C.coefficientComponentLinearMap D root x (Finsupp.single i c) =
      c • C.coefficientComponentOnBasis D root i := by
  exact Finsupp.linearCombination_single k c i

/-- Adjoining one equality edge does not change membership in the generated
coefficient component. -/
theorem eqvGen_morphismCoefficientStep_iff
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    {p q : C.MorphismCoefficientPosition D}
    (hpq : C.MorphismCoefficientStep D p q) :
    Relation.EqvGen (C.MorphismCoefficientStep D) root p ↔
      Relation.EqvGen (C.MorphismCoefficientStep D) root q := by
  constructor
  · intro hp
    exact Relation.EqvGen.trans _ _ _ hp
      (Relation.EqvGen.rel _ _ hpq)
  · intro hq
    exact Relation.EqvGen.trans _ _ _ hq
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hpq))

/-- The component indicator commutes with one displayed arrow on a source
basis vector. -/
theorem arrowLinearMap_coefficientComponentOnBasis
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    {x y : Q} (a : x ⟶ y) (i : C.PositionAt x) :
    D.arrowLinearMap a (C.coefficientComponentOnBasis D root i) =
      C.coefficientComponentLinearMap D root y (C.arrowOnBasis a i) := by
  classical
  apply Finsupp.ext
  intro j'
  by_cases hCstep : ∃ j : C.PositionAt y, C.ArrowStep a i j
  · let j := Classical.choose hCstep
    have hij : C.ArrowStep a i j := Classical.choose_spec hCstep
    rw [C.arrowOnBasis_eq_single_of_step a i j hij,
      C.coefficientComponentLinearMap_single, one_smul]
    by_cases hDstep : ∃ i' : D.PositionAt x, D.ArrowStep a i' j'
    · let i' := Classical.choose hDstep
      have hij' : D.ArrowStep a i' j' := Classical.choose_spec hDstep
      rw [D.arrowLinearMap_apply_of_step a _ i' j' hij',
        C.coefficientComponentOnBasis_apply,
        C.coefficientComponentOnBasis_apply]
      let p : C.MorphismCoefficientPosition D := ⟨x, i, i'⟩
      let q : C.MorphismCoefficientPosition D := ⟨y, j, j'⟩
      have hpq : C.MorphismCoefficientStep D p q :=
        MorphismCoefficientStep.ofArrow a i j i' j' hij hij'
      have hconn := C.eqvGen_morphismCoefficientStep_iff D root hpq
      classical
      unfold coefficientComponentIndicator
      rw [if_congr hconn rfl]
      rfl
    · rw [D.arrowLinearMap_apply_eq_zero_of_not_exists_source a _ j'
        hDstep,
      C.coefficientComponentOnBasis_apply]
      let q : C.MorphismCoefficientPosition D := ⟨y, j, j'⟩
      have hboundary : C.IsMorphismCoefficientBoundary D q :=
        IsMorphismCoefficientBoundary.source a i j j' hij hDstep
      have hnot : ¬ Relation.EqvGen (C.MorphismCoefficientStep D) root q := by
        intro hq
        exact hfree q hq hboundary
      rw [C.coefficientComponentIndicator_eq_zero D root q hnot]
  · rw [C.arrowOnBasis_eq_zero_of_not_exists a i hCstep, map_zero]
    by_cases hDstep : ∃ i' : D.PositionAt x, D.ArrowStep a i' j'
    · let i' := Classical.choose hDstep
      have hij' : D.ArrowStep a i' j' := Classical.choose_spec hDstep
      rw [D.arrowLinearMap_apply_of_step a _ i' j' hij',
        C.coefficientComponentOnBasis_apply]
      let p : C.MorphismCoefficientPosition D := ⟨x, i, i'⟩
      have hboundary : C.IsMorphismCoefficientBoundary D p :=
        IsMorphismCoefficientBoundary.target a i i' j' hCstep hij'
      have hnot : ¬ Relation.EqvGen (C.MorphismCoefficientStep D) root p := by
        intro hp
        exact hfree p hp hboundary
      rw [C.coefficientComponentIndicator_eq_zero D root p hnot]
      simp
    · rw [D.arrowLinearMap_apply_eq_zero_of_not_exists_source a _ j'
        hDstep]
      rfl

/-- The component-indicator linear maps commute with every displayed arrow. -/
theorem coefficientComponentLinearMap_arrowLinearMap
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    {x y : Q} (a : x ⟶ y) (v : C.Space x) :
    C.coefficientComponentLinearMap D root y (C.arrowLinearMap a v) =
      D.arrowLinearMap a
        (C.coefficientComponentLinearMap D root x v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i c =>
      calc
        C.coefficientComponentLinearMap D root y
            (C.arrowLinearMap a (Finsupp.single i c)) =
            c • C.coefficientComponentLinearMap D root y
              (C.arrowOnBasis a i) := by
          rw [C.arrowLinearMap_single, map_smul]
        _ = c • D.arrowLinearMap a
              (C.coefficientComponentOnBasis D root i) :=
          congrArg (c • ·)
            (C.arrowLinearMap_coefficientComponentOnBasis
              D root hfree a i).symm
        _ = D.arrowLinearMap a
              (c • C.coefficientComponentOnBasis D root i) := by
          rw [map_smul]
        _ = D.arrowLinearMap a
              (C.coefficientComponentLinearMap D root x
                (Finsupp.single i c)) := by
          rw [C.coefficientComponentLinearMap_single]

/-- A boundary-free component indicator is a morphism of the underlying
quiver representations. -/
def coefficientComponentQuiverRepresentationMap
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root) :
    C.quiverRepresentation ⟶ D.quiverRepresentation :=
  Paths.liftNatTrans
    (fun x => ModuleCat.ofHom (C.coefficientComponentLinearMap D root x))
    (fun {x y} a => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact C.coefficientComponentLinearMap_arrowLinearMap
        D root hfree a v)

/-- In the opposite-module realization, a component indicator has the
reversed natural-transformation direction. -/
def coefficientComponentFreeRightModuleAuxMap
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root) :
    D.freeRightModuleAux ⟶ C.freeRightModuleAux :=
  LinearPathCategory.liftNatTrans
    (fun x => Opposite.op (ModuleCat.of k (D.Space x)))
    (fun x => Opposite.op (ModuleCat.of k (C.Space x)))
    (fun a => (ModuleCat.ofHom (D.arrowLinearMap a)).op)
    (fun a => (ModuleCat.ofHom (C.arrowLinearMap a)).op)
    (fun x => (ModuleCat.ofHom
      (C.coefficientComponentLinearMap D root x)).op)
    (fun {x y} a => by
      rw [← op_comp, ← op_comp]
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change D.arrowLinearMap a
          (C.coefficientComponentLinearMap D root x v) =
        C.coefficientComponentLinearMap D root y (C.arrowLinearMap a v)
      exact (C.coefficientComponentLinearMap_arrowLinearMap
        D root hfree a v).symm)

/-- Descend a component indicator through the monomial relation quotient. -/
def coefficientComponentQuotientRightModuleAuxMap
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    (hC : IsMonomial R) (hD : IsMonomial R) :
    D.quotientRightModuleAux hD ⟶ C.quotientRightModuleAux hC :=
  HomIdeal.quotientLiftNatTrans
    (k := k)
    (I := LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (F := D.freeRightModuleAux)
    (D.relationIdeal_isKilledBy hD)
    (C.relationIdeal_isKilledBy hC)
    (C.coefficientComponentFreeRightModuleAuxMap D root hfree)

/-- The right-module morphism whose matrix is the indicator of a
boundary-free coefficient component. -/
def coefficientComponentRightModuleMap
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    (hC : IsMonomial R) (hD : IsMonomial R) :
    C.rightModule hC ⟶ D.rightModule hD where
  app X := ((C.coefficientComponentQuotientRightModuleAuxMap
    D root hfree hC hD).app X.unop).unop
  naturality {X Y} f := by
    apply Quiver.Hom.op_inj
    exact ((C.coefficientComponentQuotientRightModuleAuxMap
      D root hfree hC hD).naturality f.unop).symm

@[simp]
theorem coefficientComponentRightModuleMap_app_obj
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    (hC : IsMonomial R) (hD : IsMonomial R) (x : Q) :
    (C.coefficientComponentRightModuleMap D root hfree hC hD).app
        (Opposite.op (obj R x)) =
      ModuleCat.ofHom (C.coefficientComponentLinearMap D root x) :=
  rfl

/-- The coefficient matrix of the component map is exactly the indicator of
the selected component. -/
theorem morphismCoefficientAt_coefficientComponentRightModuleMap
    (C D : Word R) (root p : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    (hC : IsMonomial R) (hD : IsMonomial R) :
    C.morphismCoefficientAt D hC hD
        (C.coefficientComponentRightModuleMap D root hfree hC hD) p =
      C.coefficientComponentIndicator D root p := by
  rcases p with ⟨x, i, j⟩
  change C.coefficientComponentLinearMap D root x
      (Finsupp.single i 1) j = _
  rw [C.coefficientComponentLinearMap_single, one_smul,
    C.coefficientComponentOnBasis_apply]

/-- The selected component map has coefficient one at its root. -/
theorem morphismCoefficientAt_coefficientComponentRightModuleMap_root
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    (hC : IsMonomial R) (hD : IsMonomial R) :
    C.morphismCoefficientAt D hC hD
        (C.coefficientComponentRightModuleMap D root hfree hC hD) root = 1 := by
  rw [C.morphismCoefficientAt_coefficientComponentRightModuleMap
    D root root hfree hC hD,
    C.coefficientComponentIndicator_eq_one D root root
      (Relation.EqvGen.refl _)]

end MagnitudeConjecture.BoundQuiver.StringWord.Word
