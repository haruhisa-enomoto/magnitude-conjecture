import MagnitudeConjecture.Algebra.StringGraphComponentMap
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Spanning string morphisms by coefficient-component maps

The finite coefficient constraint graph partitions all possible matrix
coefficients into equality components.  This file chooses one representative
per component and decomposes every actual string-module morphism as the sum of
its component coefficient times the corresponding component-indicator map.
Components meeting a zero boundary contribute zero automatically.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Equality components of the matched-step coefficient graph. -/
def MorphismCoefficientComponent (C D : Word R) :=
  Quotient (Relation.EqvGen.setoid (C.MorphismCoefficientStep D))

/-- The component containing a coefficient position. -/
def morphismCoefficientComponentOf (C D : Word R)
    (p : C.MorphismCoefficientPosition D) :
    C.MorphismCoefficientComponent D :=
  Quotient.mk _ p

instance morphismCoefficientComponent_finite (C D : Word R) :
    Finite (C.MorphismCoefficientComponent D) :=
  Finite.of_surjective (C.morphismCoefficientComponentOf D)
    Quotient.mk_surjective

noncomputable instance morphismCoefficientComponent_fintype (C D : Word R) :
    Fintype (C.MorphismCoefficientComponent D) := Fintype.ofFinite _

/-- A chosen coefficient position in a component. -/
def MorphismCoefficientComponent.representative
    {C D : Word R} (component : C.MorphismCoefficientComponent D) :
    C.MorphismCoefficientPosition D :=
  Quotient.out component

@[simp]
theorem morphismCoefficientComponentOf_representative
    (C D : Word R) (component : C.MorphismCoefficientComponent D) :
    C.morphismCoefficientComponentOf D component.representative =
      component :=
  Quotient.out_eq component

/-- Equality of component classes is precisely generated matched-step
equivalence. -/
theorem morphismCoefficientComponentOf_eq_iff
    (C D : Word R) (p q : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientComponentOf D p =
        C.morphismCoefficientComponentOf D q ↔
      Relation.EqvGen (C.MorphismCoefficientStep D) p q := by
  exact Quotient.eq

/-- The coefficient components which carry no unmatched zero boundary. -/
def BoundaryFreeMorphismCoefficientComponent (C D : Word R) :=
  {component : C.MorphismCoefficientComponent D //
    C.IsBoundaryFreeMorphismCoefficientComponent D
      component.representative}

instance boundaryFreeMorphismCoefficientComponent_finite
    (C D : Word R) :
    Finite (C.BoundaryFreeMorphismCoefficientComponent D) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance boundaryFreeMorphismCoefficientComponent_fintype
    (C D : Word R) :
    Fintype (C.BoundaryFreeMorphismCoefficientComponent D) :=
  Fintype.ofFinite _

/-- Two chosen component representatives are matched-step equivalent exactly
when their components are equal. -/
theorem representative_eqv_iff
    (C D : Word R) (first second : C.MorphismCoefficientComponent D) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
        first.representative second.representative ↔
      first = second := by
  constructor
  · intro h
    have heq := (C.morphismCoefficientComponentOf_eq_iff D
      first.representative second.representative).mpr h
    simpa only [C.morphismCoefficientComponentOf_representative] using heq
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- The module map indexed by a boundary-free coefficient component. -/
def boundaryFreeMorphismCoefficientComponentMap
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (component : C.BoundaryFreeMorphismCoefficientComponent D) :
    C.rightModule hC ⟶ D.rightModule hD :=
  C.coefficientComponentRightModuleMap D component.1.representative
    component.2 hC hD

/-- The coefficient matrix of a boundary-free component map is its component
indicator. -/
theorem morphismCoefficientAt_boundaryFreeComponentMap
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD
        (C.boundaryFreeMorphismCoefficientComponentMap
          D hC hD component) p =
      C.coefficientComponentIndicator D component.1.representative p :=
  C.morphismCoefficientAt_coefficientComponentRightModuleMap
    D component.1.representative p component.2 hC hD

/-- The contribution of one coefficient component to an actual morphism.
Boundary components have zero coefficient and contribute the zero map;
otherwise the chosen coefficient scales the component-indicator map. -/
def morphismCoefficientComponentSummand
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (component : C.MorphismCoefficientComponent D) :
    C.rightModule hC ⟶ D.rightModule hD := by
  let root := component.representative
  by_cases hroot : C.morphismCoefficientAt D hC hD f root = 0
  · exact 0
  · exact C.morphismCoefficientAt D hC hD f root •
      C.coefficientComponentRightModuleMap D root
        (C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
          D hC hD f root hroot) hC hD

private theorem representative_eqv_of_componentOf_eq
    (C D : Word R) (component : C.MorphismCoefficientComponent D)
    (p : C.MorphismCoefficientPosition D)
    (hp : C.morphismCoefficientComponentOf D p = component) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      component.representative p := by
  apply (C.morphismCoefficientComponentOf_eq_iff D _ _).mp
  rw [C.morphismCoefficientComponentOf_representative D component, hp]

/-- On its own component, a summand recovers the coefficient of the original
morphism. -/
theorem morphismCoefficientAt_componentSummand_eq
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (component : C.MorphismCoefficientComponent D)
    (p : C.MorphismCoefficientPosition D)
    (hp : C.morphismCoefficientComponentOf D p = component) :
    C.morphismCoefficientAt D hC hD
        (C.morphismCoefficientComponentSummand D hC hD f component) p =
      C.morphismCoefficientAt D hC hD f p := by
  let root := component.representative
  have hrp : Relation.EqvGen (C.MorphismCoefficientStep D) root p :=
    C.representative_eqv_of_componentOf_eq D component p hp
  have hcoeff := C.morphismCoefficientAt_eq_of_eqvGen D hC hD f hrp
  unfold morphismCoefficientComponentSummand
  dsimp only
  split_ifs with hroot
  · rw [C.morphismCoefficientAt_zero]
    exact hroot.symm.trans hcoeff
  · rw [C.morphismCoefficientAt_smul,
      C.morphismCoefficientAt_coefficientComponentRightModuleMap,
      C.coefficientComponentIndicator_eq_one D root p hrp,
      mul_one]
    exact hcoeff

/-- Away from its own component, a summand has zero coefficient. -/
theorem morphismCoefficientAt_componentSummand_eq_zero
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (component : C.MorphismCoefficientComponent D)
    (p : C.MorphismCoefficientPosition D)
    (hp : C.morphismCoefficientComponentOf D p ≠ component) :
    C.morphismCoefficientAt D hC hD
        (C.morphismCoefficientComponentSummand D hC hD f component) p = 0 := by
  let root := component.representative
  have hnot : ¬ Relation.EqvGen (C.MorphismCoefficientStep D) root p := by
    intro hrp
    apply hp
    have heq := (C.morphismCoefficientComponentOf_eq_iff D root p).mpr hrp
    rw [C.morphismCoefficientComponentOf_representative D component] at heq
    exact heq.symm
  unfold morphismCoefficientComponentSummand
  dsimp only
  split_ifs with hroot
  · exact C.morphismCoefficientAt_zero D hC hD p
  · rw [C.morphismCoefficientAt_smul,
      C.morphismCoefficientAt_coefficientComponentRightModuleMap,
      C.coefficientComponentIndicator_eq_zero D root p hnot,
      mul_zero]

/-- Sum the contributions of all coefficient components of a morphism. -/
def morphismCoefficientComponentSum
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD) :
    C.rightModule hC ⟶ D.rightModule hD :=
  ∑ component : C.MorphismCoefficientComponent D,
    C.morphismCoefficientComponentSummand D hC hD f component

/-- The component sum has the same coefficient matrix as the original
morphism. -/
theorem morphismCoefficientAt_componentSum
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (p : C.MorphismCoefficientPosition D) :
    C.morphismCoefficientAt D hC hD
        (C.morphismCoefficientComponentSum D hC hD f) p =
      C.morphismCoefficientAt D hC hD f p := by
  classical
  rw [morphismCoefficientComponentSum,
    C.morphismCoefficientAt_sum D hC hD Finset.univ
      (fun component =>
        C.morphismCoefficientComponentSummand D hC hD f component) p]
  rw [Finset.sum_eq_single (C.morphismCoefficientComponentOf D p)]
  · exact C.morphismCoefficientAt_componentSummand_eq D hC hD f
      (C.morphismCoefficientComponentOf D p) p rfl
  · intro component _ hcomponent
    exact C.morphismCoefficientAt_componentSummand_eq_zero D hC hD f
      component p (Ne.symm hcomponent)
  · simp

/-- Every morphism between two string modules is the sum of its nonzero
boundary-free coefficient-component maps. -/
theorem morphismCoefficientComponentSum_eq
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD) :
    C.morphismCoefficientComponentSum D hC hD f = f := by
  apply C.rightModuleHom_ext_morphismCoefficientAt D hC hD
  exact C.morphismCoefficientAt_componentSum D hC hD f

/-- Boundary-free component maps are linearly independent. -/
theorem boundaryFreeMorphismCoefficientComponentMap_linearIndependent
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R) :
    LinearIndependent k
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hsum component
  let p : C.MorphismCoefficientPosition D :=
    component.1.representative
  have hzero :
      (∑ item : C.BoundaryFreeMorphismCoefficientComponent D,
        C.morphismCoefficientAt D hC hD
          (g item • C.boundaryFreeMorphismCoefficientComponentMap
            D hC hD item) p) = 0 := by
    calc
      _ = C.morphismCoefficientAt D hC hD
          (∑ item : C.BoundaryFreeMorphismCoefficientComponent D,
            g item • C.boundaryFreeMorphismCoefficientComponentMap
              D hC hD item) p := by
          symm
          exact C.morphismCoefficientAt_sum D hC hD Finset.univ
            (fun item => g item •
              C.boundaryFreeMorphismCoefficientComponentMap
                D hC hD item) p
      _ = C.morphismCoefficientAt D hC hD 0 p :=
        congrArg (fun f => C.morphismCoefficientAt D hC hD f p) hsum
      _ = 0 := C.morphismCoefficientAt_zero D hC hD p
  have heval :
      (∑ item : C.BoundaryFreeMorphismCoefficientComponent D,
        C.morphismCoefficientAt D hC hD
          (g item • C.boundaryFreeMorphismCoefficientComponentMap
            D hC hD item) p) = g component := by
    rw [Finset.sum_eq_single component]
    · rw [C.morphismCoefficientAt_smul,
        C.morphismCoefficientAt_boundaryFreeComponentMap,
        C.coefficientComponentIndicator_eq_one D
          component.1.representative p]
      · simp
      · exact Relation.EqvGen.refl _
    · intro item _ hitem
      rw [C.morphismCoefficientAt_smul,
        C.morphismCoefficientAt_boundaryFreeComponentMap,
        C.coefficientComponentIndicator_eq_zero D
          item.1.representative p]
      · simp
      · intro heqv
        apply hitem
        apply Subtype.ext
        exact (C.representative_eqv_iff D item.1 component.1).mp heqv
    · simp
  exact heval ▸ hzero

/-- Every string-module morphism lies in the span of the boundary-free
component maps. -/
theorem mem_span_boundaryFreeMorphismCoefficientComponentMap
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD) :
    f ∈ Submodule.span k
      (Set.range (C.boundaryFreeMorphismCoefficientComponentMap
        D hC hD)) := by
  rw [← C.morphismCoefficientComponentSum_eq D hC hD f]
  unfold morphismCoefficientComponentSum
  apply Submodule.sum_mem
  intro component _
  unfold morphismCoefficientComponentSummand
  dsimp only
  split_ifs with hroot
  · exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    let hfree :=
      C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
        D hC hD f component.representative hroot
    refine ⟨(⟨component, hfree⟩ :
      C.BoundaryFreeMorphismCoefficientComponent D), ?_⟩
    rfl

/-- Boundary-free coefficient-component maps span the whole Hom-space. -/
theorem span_boundaryFreeMorphismCoefficientComponentMap
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R) :
    Submodule.span k
        (Set.range (C.boundaryFreeMorphismCoefficientComponentMap
          D hC hD)) = ⊤ := by
  apply top_unique
  intro f _
  exact C.mem_span_boundaryFreeMorphismCoefficientComponentMap
    D hC hD f

/-- The boundary-free equality components give a basis of the Hom-space
between two string modules. -/
noncomputable def boundaryFreeMorphismCoefficientBasis
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R) :
    Module.Basis (C.BoundaryFreeMorphismCoefficientComponent D) k
      (C.rightModule hC ⟶ D.rightModule hD) :=
  Module.Basis.mk
    (C.boundaryFreeMorphismCoefficientComponentMap_linearIndependent
      D hC hD)
    (by rw [C.span_boundaryFreeMorphismCoefficientComponentMap D hC hD])

/-- The coordinate of a morphism in the graph-component basis is its matrix
coefficient at the chosen representative of that component. -/
theorem boundaryFreeMorphismCoefficientBasis_repr_apply
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (component : C.BoundaryFreeMorphismCoefficientComponent D) :
    (C.boundaryFreeMorphismCoefficientBasis D hC hD).repr f component =
      C.morphismCoefficientAt D hC hD f
        component.1.representative := by
  classical
  let b := C.boundaryFreeMorphismCoefficientBasis D hC hD
  let p := component.1.representative
  have hsum :
      (∑ item, b.repr f item •
        C.boundaryFreeMorphismCoefficientComponentMap D hC hD item) = f := by
    simpa only [b, boundaryFreeMorphismCoefficientBasis,
      Module.Basis.coe_mk] using b.sum_repr f
  have hcoeff := congrArg
    (fun g : C.rightModule hC ⟶ D.rightModule hD =>
      C.morphismCoefficientAt D hC hD g p) hsum
  change C.morphismCoefficientAt D hC hD
      (∑ item, b.repr f item •
        C.boundaryFreeMorphismCoefficientComponentMap D hC hD item) p =
    C.morphismCoefficientAt D hC hD f p at hcoeff
  rw [C.morphismCoefficientAt_sum D hC hD Finset.univ
    (fun item => b.repr f item •
      C.boundaryFreeMorphismCoefficientComponentMap D hC hD item) p] at hcoeff
  rw [Finset.sum_eq_single component] at hcoeff
  · rw [C.morphismCoefficientAt_smul,
      C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_one D
        component.1.representative p (Relation.EqvGen.refl _), mul_one]
        at hcoeff
    simpa only [b, p] using hcoeff
  · intro item _ hitem
    rw [C.morphismCoefficientAt_smul,
      C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_zero D]
    · simp
    · intro heqv
      apply hitem
      apply Subtype.ext
      exact (C.representative_eqv_iff D item.1 component.1).mp heqv
  · simp

end MagnitudeConjecture.BoundQuiver.StringWord.Word
