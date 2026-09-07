import MagnitudeConjecture.Statement
import MagnitudeConjecture.Algebra.BoundQuiverPresentation
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-!
# The independent and production bound-quiver presentations agree

The free path categories, generated ideals, and quotient linear structures
agree definitionally. Evaluating at a stationary path identifies the path
coordinates. Uniqueness of a finite direct sum identifies the category
algebras, giving explicit translations in both directions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.Statement.QuiverPresentation
universe u
variable {k Q B : Type u} [Field k] [Quiver.{u} Q] [Ring B] [Algebra k B]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
theorem coefficients_eq {X Y : FreeCategory k Q} (f : X ⟶ Y) :
    coefficients k Q f = LinearPathCategory.homPathLinearEquiv X Y f := rfl

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
theorem pathHom_eq {x y : Q} (p : Quiver.Path x y) :
    pathHom k Q p = LinearPathCategory.pathHom p := by
  apply (LinearPathCategory.homPathLinearEquiv _ _).injective
  rw [LinearPathCategory.homPathLinearEquiv_pathHom]
  change coefficients k Q (pathHom k Q p) = _
  change Finsupp.mapDomain (fun q : Quiver.Path y y ↦ p.comp q)
    (Finsupp.single Quiver.Path.nil (1 : k)) = _
  rw [Finsupp.mapDomain_single, Quiver.Path.comp_nil]

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
theorem pathMap_eq (R : BoundQuiver.RelationFamily k Q) {x y : Q} (p : Quiver.Path x y) :
    pathMap R p = BoundQuiver.pathMap R p := by
  unfold pathMap
  rw [pathHom_eq]
  rfl

/-- The independent ideal conditions are exactly production admissibility. -/
theorem Presentation.admissible (P : Presentation (k := k) (Q := Q) B) :
    BoundQuiver.IsAdmissible P.relations where
  relationIdeal_le_lengthTail_two X Y := by
    intro f hf
    rw [LinearPathCategory.mem_lengthTail_iff]
    intro p hp
    change 2 ≤ p.length
    by_contra h
    have hz := P.no_short_relations X Y f hf p (by omega)
    rw [coefficients_eq] at hz
    exact Finsupp.mem_support_iff.mp hp hz
  long_paths_mem := by
    obtain ⟨N, hN, hlong⟩ := P.long_paths_vanish
    refine ⟨N, hN, ?_⟩
    intro x y p hp
    change LinearPathCategory.pathHom (k := k) (Q := Q) p ∈ ideal P.relations y x
    rw [← pathHom_eq (k := k) (Q := Q) p]
    exact hlong p hp

/-- Recover the production presentation using uniqueness of finite direct sums. -/
def Presentation.toProduction (P : Presentation (k := k) (Q := Q) B) :
    BoundQuiver.SpecialBiserialPresentation k B Q where
  relations := P.relations
  admissible := P.admissible
  algebraEquiv := by
    letI : Fintype (QuotientCategory P.relations) := Fintype.ofEquiv Q
      (CategoryTheory.Quotient.equiv (rel P.relations)).symm
    let hP := BoundQuiver.finiteRepresentablesOfAdmissible P.admissible
    let C := BoundQuiver.Category P.relations
    let R := fun X : C ↦
      (CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Opposite.op X)
    let e : P.algebra.generator.pt ≅ CoveringHom.finiteCategoryProjectiveGenerator hP :=
      biproduct.uniqueUpToIso R P.algebra.isBilimit
    exact P.algebra.algebraEquiv.trans (MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv (k := k) e)
  arrows_starting_le_two := P.outgoing_le_two
  arrows_ending_le_two := P.incoming_le_two
  continuation_right_le_one := by
    intro x y a
    simpa only [pathMap_eq, BoundQuiver.arrowMap] using P.successor_le_one a
  continuation_left_le_one := by
    intro x y a
    simpa only [pathMap_eq, BoundQuiver.arrowMap] using P.predecessor_le_one a

/-- Express a production bound-quiver presentation in the independent vocabulary. -/
def ofProduction (P : BoundQuiver.SpecialBiserialPresentation k B Q) :
    Presentation (k := k) (Q := Q) B where
  relations := P.relations
  no_short_relations X Y f hf p hp := by
    rw [coefficients_eq]
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have htail := P.admissible.relationIdeal_le_lengthTail_two X Y hf
    have hlen := (LinearPathCategory.mem_lengthTail_iff X Y 2 f).mp htail hmem
    change 2 ≤ p.length at hlen
    omega
  long_paths_vanish := by
    obtain ⟨N, hN, hlong⟩ := P.admissible.long_paths_mem
    refine ⟨N, hN, ?_⟩
    intro x y p hp
    rw [pathHom_eq (k := k) (Q := Q) p]
    exact hlong p hp
  finiteHom := by
    rintro ⟨X⟩ ⟨Y⟩
    exact BoundQuiver.quotientHom_finiteDimensional P.admissible X Y
  algebra := by
    letI : Fintype (QuotientCategory P.relations) := Fintype.ofEquiv Q
      (CategoryTheory.Quotient.equiv (rel P.relations)).symm
    let hP := BoundQuiver.finiteRepresentablesOfAdmissible P.admissible
    let C := BoundQuiver.Category P.relations
    let R := fun X : C ↦
      (CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj (Opposite.op X)
    exact {
      generator := biproduct.bicone R
      isBilimit := biproduct.isBilimit R
      algebraEquiv := P.algebraEquiv }
  outgoing_le_two := P.arrows_starting_le_two
  incoming_le_two := P.arrows_ending_le_two
  successor_le_one := by
    intro x y a
    simpa only [pathMap_eq, BoundQuiver.arrowMap] using P.continuation_right_le_one a
  predecessor_le_one := by
    intro x y a
    simpa only [pathMap_eq, BoundQuiver.arrowMap] using P.continuation_left_le_one a

end MagnitudeConjecture.Statement.QuiverPresentation
