import MagnitudeConjecture.Algebra.BoundQuiverPathGenerated
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraFunctor
import MagnitudeConjecture.CategoryTheory.HomIdealComap
import MagnitudeConjecture.CategoryTheory.LinearIdealQuotientLift
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Quotients between bound-quiver category algebras

An inclusion between two generated relation ideals gives a full linear
functor between the corresponding quotient path categories.  Since this
functor is bijective on objects, it induces a surjective homomorphism between
their finite category algebras.  This is the algebraic quotient map used by
the path-support-hull construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- The first isomorphism theorem, stated for Mathlib's noncommutative
two-sided kernel ideal rather than directly for `RingCon.ker`. -/
def quotientKerAlgEquivOfSurjective
    {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) :
    (TwoSidedIdeal.ker f).ringCon.Quotient ≃ₐ[k] B :=
  AlgEquiv.ofBijective (RingCon.kerLiftₐ f)
    ⟨RingCon.kerLiftₐ_injective f, by
      intro b
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨⟦a⟧, rfl⟩⟩

private theorem relationIdeal_isKilledBy
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    (LinearPathCategory.HomogeneousQuotient.relationIdeal R).IsKilledBy
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor S) := by
  intro X Y f hf
  apply (LinearPathCategory.HomogeneousQuotient.relationIdeal S
    ).map_eq_zero_iff f |>.2
  exact hRS X Y hf

/-- The linear functor between relation quotients induced by inclusion of
their generated two-sided Hom ideals. -/
def relationQuotientFunctor
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    CategoryTheory.Functor (Category R) (Category S) := by
  let I := LinearPathCategory.HomogeneousQuotient.relationIdeal R
  let G := LinearPathCategory.HomogeneousQuotient.quotientFunctor S
  exact I.quotientLift G (relationIdeal_isKilledBy hRS)

/-- The relation-quotient functor is additive. -/
instance relationQuotientFunctor_additive
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    (relationQuotientFunctor hRS).Additive := by
  exact HomIdeal.quotientLift_additive
    (LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor S)
    (relationIdeal_isKilledBy hRS)

/-- The relation-quotient functor is linear. -/
instance relationQuotientFunctor_linear
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    (relationQuotientFunctor hRS).Linear k := by
  exact HomIdeal.quotientLift_linear
    (LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor S)
    (relationIdeal_isKilledBy hRS)

/-- The relation-quotient functor is full. -/
instance relationQuotientFunctor_full
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    (relationQuotientFunctor hRS).Full := by
  exact HomIdeal.quotientLift_full
    (LinearPathCategory.HomogeneousQuotient.relationIdeal R)
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor S)
    (relationIdeal_isKilledBy hRS)

/-- The relative relation Hom ideal: morphisms in the first quotient which
become zero after enlarging the relation ideal. -/
def relativeRelationHomIdeal
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    HomIdeal (Category R) :=
  HomIdeal.functorKernel (k := k) (relationQuotientFunctor hRS)

@[simp]
theorem mem_relativeRelationHomIdeal_iff
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y)
    {X Y : Category R} (f : X ⟶ Y) :
    f ∈ (relativeRelationHomIdeal hRS).hom X Y ↔
      (relationQuotientFunctor hRS).map f = 0 :=
  Iff.rfl

/-- A morphism belongs to the relative relation Hom ideal exactly when one
(equivalently every) free-path-category lift belongs to the larger generated
relation ideal. -/
theorem mem_relativeRelationHomIdeal_iff_exists_lift
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y)
    {X Y : Category R} (f : X ⟶ Y) :
    f ∈ (relativeRelationHomIdeal hRS).hom X Y ↔
      ∃ g : X.as ⟶ Y.as,
        (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map g = f ∧
          g ∈ HomIdeal.generatedHomSubmodule k S X.as Y.as := by
  constructor
  · intro hf
    obtain ⟨g, rfl⟩ :=
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor R
        ).map_surjective f
    refine ⟨g, rfl, ?_⟩
    apply (LinearPathCategory.HomogeneousQuotient.relationIdeal S
      ).map_eq_zero_iff g |>.1
    exact hf
  · rintro ⟨g, rfl, hg⟩
    exact (LinearPathCategory.HomogeneousQuotient.relationIdeal S
      ).map_eq_zero_iff g |>.2 hg

/-- If the larger relation ideal is monomial, the relative kernel between
the two relation quotients is spanned by the old-quotient images of the paths
killed by the larger quotient. -/
theorem relativeRelationHomIdeal_eq_span_killedPathMap
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y)
    (hS : IsMonomial S) (x y : Q) :
    HomIdeal.homSubmodule (k := k) (relativeRelationHomIdeal hRS)
        (obj R y) (obj R x) =
      Submodule.span k
        (Set.range fun p : {p : Quiver.Path x y // pathMap S p = 0} ↦
          pathMap R p.1) := by
  apply le_antisymm
  · intro f hf
    let qmap :
        (LinearPathCategory.obj k Q y ⟶ LinearPathCategory.obj k Q x) →ₗ[k]
          (obj R y ⟶ obj R x) :=
      LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
        (LinearPathCategory.obj k Q y) (LinearPathCategory.obj k Q x)
    obtain ⟨g, hgMap, hgIdeal⟩ :=
      (mem_relativeRelationHomIdeal_iff_exists_lift hRS f).1 hf
    have hgSpan : g ∈ Submodule.span k
        ((fun p : Quiver.Path x y ↦ LinearPathCategory.pathHom p) ''
          {p : Quiver.Path x y | pathMap S p = 0}) := by
      change g ∈ HomIdeal.generatedHomSubmodule k S
        (LinearPathCategory.obj k Q y)
        (LinearPathCategory.obj k Q x) at hgIdeal
      rw [hS x y] at hgIdeal
      exact hgIdeal
    have hmapSpan : ∀ g : LinearPathCategory.obj k Q y ⟶
          LinearPathCategory.obj k Q x,
        g ∈ Submodule.span k
            ((fun p : Quiver.Path x y ↦ LinearPathCategory.pathHom p) ''
              {p : Quiver.Path x y | pathMap S p = 0}) →
          qmap g ∈
            Submodule.span k
              (Set.range fun p : {p : Quiver.Path x y // pathMap S p = 0} ↦
                pathMap R p.1) := by
      intro q hq
      induction hq using Submodule.span_induction with
      | mem q hq =>
          rcases hq with ⟨p, hp, rfl⟩
          apply Submodule.subset_span
          exact ⟨⟨p, hp⟩, rfl⟩
      | zero => simpa only [map_zero] using
          (Submodule.zero_mem (Submodule.span k
            (Set.range fun p : {p : Quiver.Path x y // pathMap S p = 0} ↦
              pathMap R p.1)))
      | add g h _ _ hg hh =>
          simpa only [map_add]
            using Submodule.add_mem _ hg hh
      | smul c g _ hg =>
          simpa only [map_smul]
            using Submodule.smul_mem _ c hg
    have hgMap' : qmap g = f := hgMap
    rw [← hgMap']
    exact hmapSpan g hgSpan
  · apply Submodule.span_le.2
    rintro f ⟨p, rfl⟩
    apply (mem_relativeRelationHomIdeal_iff_exists_lift hRS
      (pathMap R p.1)).2
    refine ⟨LinearPathCategory.pathHom p.1, rfl, ?_⟩
    exact (pathMap_eq_zero_iff_mem_relationIdeal S p.1).1 p.2

/-- Passing from one relation ideal to a larger one does not change the
object set. -/
theorem relationQuotientFunctor_obj_bijective
    {R S : RelationFamily k Q}
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    Function.Bijective (relationQuotientFunctor hRS).obj := by
  constructor
  · rintro ⟨X⟩ ⟨Y⟩ hXY
    change (⟨X⟩ : Category S) = ⟨Y⟩ at hXY
    have h : X = Y := congrArg (fun Z : Category S ↦ Z.as) hXY
    subst Y
    apply CategoryTheory.Quotient.ext
    rfl
  · rintro ⟨Y⟩
    exact ⟨⟨Y⟩, rfl⟩

/-- The surjective finite-category-algebra map induced by inclusion of
admissible bound-quiver relation ideals. -/
def relationQuotientAlgebraHom
    {R S : RelationFamily k Q}
    (hR : IsAdmissible R) (hS : IsAdmissible S)
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (finiteRepresentablesOfAdmissible hR) →ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (finiteRepresentablesOfAdmissible hS) :=
  CoveringHom.finiteCategoryProjectiveGenerator.mapAlgebraHomOfBijective
    (k := k) (C := Category R) (D := Category S)
    (finiteRepresentablesOfAdmissible hR)
    (finiteRepresentablesOfAdmissible hS)
    (relationQuotientFunctor hRS)
    (relationQuotientFunctor_obj_bijective hRS)

/-- The algebra map attached to an inclusion of admissible relation ideals
is surjective. -/
theorem relationQuotientAlgebraHom_surjective
    {R S : RelationFamily k Q}
    (hR : IsAdmissible R) (hS : IsAdmissible S)
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y) :
    Function.Surjective (relationQuotientAlgebraHom hR hS hRS) :=
  CoveringHom.finiteCategoryProjectiveGenerator.mapAlgebraHomOfBijective_surjective
    (k := k) (C := Category R) (D := Category S)
    (finiteRepresentablesOfAdmissible hR)
    (finiteRepresentablesOfAdmissible hS)
    (relationQuotientFunctor hRS)
    (relationQuotientFunctor_obj_bijective hRS)

/-- Membership in the kernel of a relation-quotient category-algebra map is
coordinatewise: every category-morphism matrix entry is killed by the
underlying quotient functor. -/
theorem relationQuotientAlgebraHom_eq_zero_iff_coordinate
    {R S : RelationFamily k Q}
    (hR : IsAdmissible R) (hS : IsAdmissible S)
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y)
    (a : CoveringHom.finiteCategoryProjectiveGenerator.algebra
      (finiteRepresentablesOfAdmissible hR)) :
    relationQuotientAlgebraHom hR hS hRS a = 0 ↔
      ∀ i j : CoveringHom.finiteCategoryProjectiveGenerator.SmallIndex
          (C := Category.{u, u, u} R),
        (relationQuotientFunctor (k := k) (Q := Q)
          (R := R) (S := S) hRS).map
          (CoveringHom.finiteCategoryProjectiveGenerator.smallAlgebraCategoryCoordinate
              (finiteRepresentablesOfAdmissible.{u, u, u} hR) a i j) = 0 := by
  exact CoveringHom.finiteCategoryProjectiveGenerator.mapAlgebraHomOfBijective_eq_zero_iff_smallAlgebraCategoryCoordinate
      (finiteRepresentablesOfAdmissible.{u, u, u} hR)
      (finiteRepresentablesOfAdmissible.{u, u, u} hS)
      (relationQuotientFunctor (k := k) (Q := Q)
        (R := R) (S := S) hRS)
      (relationQuotientFunctor_obj_bijective (k := k) (Q := Q)
        (R := R) (S := S) hRS) a

/-- Object-indexed form of the coordinatewise kernel criterion for a
relation-quotient category-algebra map. -/
theorem relationQuotientAlgebraHom_eq_zero_iff_objectCoordinate
    {R S : RelationFamily k Q}
    (hR : IsAdmissible R) (hS : IsAdmissible S)
    (hRS : ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        HomIdeal.generatedHomSubmodule k S X Y)
    (a : CoveringHom.finiteCategoryProjectiveGenerator.algebra
      (finiteRepresentablesOfAdmissible hR)) :
    relationQuotientAlgebraHom hR hS hRS a = 0 ↔
      ∀ X Y : Category.{u, u, u} R,
        (relationQuotientFunctor (k := k) (Q := Q)
          (R := R) (S := S) hRS).map
          (CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
            (finiteRepresentablesOfAdmissible.{u, u, u} hR) a X Y) = 0 := by
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.mapAlgebraHomOfBijective_eq_zero_iff_algebraCategoryCoordinate
      (finiteRepresentablesOfAdmissible.{u, u, u} hR)
      (finiteRepresentablesOfAdmissible.{u, u, u} hS)
      (relationQuotientFunctor (k := k) (Q := Q)
        (R := R) (S := S) hRS)
      (relationQuotientFunctor_obj_bijective (k := k) (Q := Q)
        (R := R) (S := S) hRS) a

/-- The canonical quotient homomorphism from a special-biserial category
algebra to its path-support-hull string category algebra. -/
def SpecialBiserialPresentation.pathSupportHullAlgebraHom
    {A : Type u} [Ring A] [Algebra k A]
    (P : SpecialBiserialPresentation k A Q) :
    let hR := pathSupportHull_isAdmissible P.toPresentation.admissible
    A →ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (finiteRepresentablesOfAdmissible hR) := by
  let R := pathSupportHull P.toPresentation.relations
  let hR : IsAdmissible R :=
    pathSupportHull_isAdmissible P.toPresentation.admissible
  exact
    (relationQuotientAlgebraHom (k := k) (Q := Q)
        (R := P.toPresentation.relations) (S := R)
        P.toPresentation.admissible hR
        (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
          P.toPresentation.relations)).comp
      P.toPresentation.algebraEquiv.toAlgHom

/-- The path-support-hull algebra homomorphism is surjective. -/
theorem SpecialBiserialPresentation.pathSupportHullAlgebraHom_surjective
    {A : Type u} [Ring A] [Algebra k A]
    (P : SpecialBiserialPresentation k A Q) :
    Function.Surjective P.pathSupportHullAlgebraHom :=
  (relationQuotientAlgebraHom_surjective (k := k) (Q := Q)
      (R := P.toPresentation.relations)
      (S := pathSupportHull P.toPresentation.relations)
      P.toPresentation.admissible
      (pathSupportHull_isAdmissible P.toPresentation.admissible)
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)).comp
    P.toPresentation.algebraEquiv.surjective

/-- The path-support-hull map kills an ambient algebra element exactly when
the hull quotient kills every category-morphism coordinate of that element
in the supplied bound-quiver presentation. -/
theorem SpecialBiserialPresentation.pathSupportHullAlgebraHom_eq_zero_iff_coordinate
    {A : Type u} [Ring A] [Algebra k A]
    (P : SpecialBiserialPresentation k A Q) (a : A) :
    P.pathSupportHullAlgebraHom a = 0 ↔
      ∀ i j : CoveringHom.finiteCategoryProjectiveGenerator.SmallIndex
          (C := Category.{u, u, u} P.toPresentation.relations),
        (relationQuotientFunctor (k := k) (Q := Q)
          (R := P.toPresentation.relations)
          (S := pathSupportHull P.toPresentation.relations)
          (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
            P.toPresentation.relations)).map
          (CoveringHom.finiteCategoryProjectiveGenerator.smallAlgebraCategoryCoordinate
              (finiteRepresentablesOfAdmissible.{u, u, u}
                P.toPresentation.admissible)
              (P.toPresentation.algebraEquiv a) i j) = 0 := by
  exact relationQuotientAlgebraHom_eq_zero_iff_coordinate
    P.toPresentation.admissible
    (pathSupportHull_isAdmissible P.toPresentation.admissible)
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations)
    (P.toPresentation.algebraEquiv a)

/-- Object-indexed form of the coordinatewise kernel criterion for the
path-support-hull map. -/
theorem SpecialBiserialPresentation.pathSupportHullAlgebraHom_eq_zero_iff_objectCoordinate
    {A : Type u} [Ring A] [Algebra k A]
    (P : SpecialBiserialPresentation k A Q) (a : A) :
    P.pathSupportHullAlgebraHom a = 0 ↔
      ∀ X Y : Category.{u, u, u} P.toPresentation.relations,
        (relationQuotientFunctor (k := k) (Q := Q)
          (R := P.toPresentation.relations)
          (S := pathSupportHull P.toPresentation.relations)
          (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
            P.toPresentation.relations)).map
          (CoveringHom.finiteCategoryProjectiveGenerator.algebraCategoryCoordinate
            (finiteRepresentablesOfAdmissible.{u, u, u}
              P.toPresentation.admissible)
            (P.toPresentation.algebraEquiv a) X Y) = 0 := by
  exact relationQuotientAlgebraHom_eq_zero_iff_objectCoordinate
    P.toPresentation.admissible
    (pathSupportHull_isAdmissible P.toPresentation.admissible)
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations)
    (P.toPresentation.algebraEquiv a)

/-- The quotient by the kernel of the path-support-hull map is canonically
the resulting string category algebra. -/
def SpecialBiserialPresentation.pathSupportHullQuotientAlgEquiv
    {A : Type u} [Ring A] [Algebra k A]
    (P : SpecialBiserialPresentation k A Q) :
    (TwoSidedIdeal.ker P.pathSupportHullAlgebraHom).ringCon.Quotient ≃ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (finiteRepresentablesOfAdmissible.{u, u, u}
          (pathSupportHull_isAdmissible P.toPresentation.admissible)) :=
  quotientKerAlgEquivOfSurjective P.pathSupportHullAlgebraHom
    P.pathSupportHullAlgebraHom_surjective

/-- Once a specified two-sided ideal has been identified as the kernel of
the path-support-hull map, its literal quotient admits a string
presentation.  Thus the remaining structural content of socle reduction is
exactly the kernel identification. -/
theorem SpecialBiserialPresentation.quotient_admitsStringPresentation_of_ker_eq
    {A : Type u} [Ring A] [Algebra k A]
    (P : SpecialBiserialPresentation k A Q) (J : TwoSidedIdeal A)
    (hker : TwoSidedIdeal.ker P.pathSupportHullAlgebraHom = J) :
    AdmitsStringPresentation k J.ringCon.Quotient := by
  subst J
  apply (admitsStringPresentation_iff_of_algEquiv
    P.pathSupportHullQuotientAlgEquiv).2
  exact ⟨{
    Vertex := Q
    vertexFintype := inferInstance
    quiver := inferInstance
    arrowFintype := fun _ _ ↦ inferInstance
    presentation := P.pathSupportHullStringPresentation }⟩

end MagnitudeConjecture.BoundQuiver
