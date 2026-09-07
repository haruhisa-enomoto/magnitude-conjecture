import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator
import MagnitudeConjecture.CategoryTheory.HomogeneousRelationQuotient
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Bound-quiver and special-biserial presentations

This file records the literal bound-quiver convention used in the frozen
manuscript.  A relation family is admissible when its generated two-sided
ideal contains no terms of path length below two and contains every
sufficiently long path.  A bound-quiver presentation identifies an algebra
with the finite category algebra of that quotient.  The special-biserial
conditions are then imposed on the displayed arrows and their nonzero
two-arrow compositions in the quotient.

The free linear category uses the reversed categorical orientation:
`pathMap p` is a morphism from the endpoint of `p` to its source.  The quiver
itself, and hence the degree and continuation conditions below, retain the
usual path-algebra orientation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.BoundQuiver

universe u v w

variable {k A B : Type u} {Q : Type v}
variable [Field k] [Ring A] [Algebra k A]
variable [Ring B] [Algebra k B]
variable [Fintype Q] [Quiver.{w} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- Bounded paths in a finite quiver form a finite type, even when the
unbounded path type is infinite because the quiver has oriented cycles. -/
noncomputable instance boundedPathsFinite (n : ℕ) (x y : Q) :
    Finite (Quiver.Path.BoundedPaths x y n) := by
  induction n generalizing x y with
  | zero => exact Finite.of_subsingleton
  | succ n ih =>
      letI (a b : Q) : Finite (Quiver.Path.BoundedPaths a b n) := ih a b
      let source :=
        Quiver.Path.BoundedPaths x y 0 ⊕
          (Σ z : Q, Quiver.Path.BoundedPaths x z n × (z ⟶ y))
      let assemble : source → Quiver.Path.BoundedPaths x y (n + 1) :=
        fun s ↦ match s with
          | Sum.inl p => ⟨p.1, p.2.trans (Nat.zero_le _)⟩
          | Sum.inr q =>
              ⟨q.2.1.1.cons q.2.2, by
                simpa using Nat.succ_le_succ q.2.1.2⟩
      apply @Finite.of_surjective source _ inferInstance assemble
      rintro ⟨p, hp⟩
      cases p with
      | nil =>
          exact ⟨Sum.inl ⟨Quiver.Path.nil, by simp⟩, rfl⟩
      | @cons z _ p a =>
          have hp' : p.length ≤ n := by
            simpa using hp
          exact ⟨Sum.inr ⟨z, ⟨⟨p, hp'⟩, a⟩⟩, rfl⟩

/-- A family of relations in the free linear category on `Q`. -/
abbrev RelationFamily (k : Type u) (Q : Type v)
    [Field k] [Quiver.{w} Q] :=
  ∀ X Y : LinearPathCategory.Category k Q, Set (X ⟶ Y)

/-- The quotient of the free linear path category by a relation family. -/
abbrev Category (R : RelationFamily k Q) :=
  LinearPathCategory.HomogeneousQuotient.RawCategory R

/-- A quotient path category has the same finite object set as its displayed
quiver. -/
noncomputable instance categoryFintype (R : RelationFamily k Q) :
    Fintype (Category R) :=
  Fintype.ofEquiv Q
    (CategoryTheory.Quotient.equiv
      (LinearPathCategory.HomogeneousQuotient.relationIdeal R).rel).symm

/-- A quiver vertex as an object of the relation quotient. -/
abbrev obj (R : RelationFamily k Q) (x : Q) : Category R :=
  LinearPathCategory.HomogeneousQuotient.obj R
    (LinearPathCategory.obj k Q x)

/-- The image in the quotient category of a path in the displayed quiver. -/
def pathMap (R : RelationFamily k Q) {x y : Q} (p : Quiver.Path x y) :
    obj R y ⟶ obj R x :=
  (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map
    (LinearPathCategory.pathHom p)

/-- The image in the quotient category of one displayed quiver arrow. -/
def arrowMap (R : RelationFamily k Q) {x y : Q} (a : x ⟶ y) :
    obj R y ⟶ obj R x :=
  pathMap R a.toPath

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
@[simp]
theorem pathMap_comp (R : RelationFamily k Q) {x y z : Q}
    (p : Quiver.Path x y) (q : Quiver.Path y z) :
    pathMap R q ≫ pathMap R p = pathMap R (p.comp q) := by
  change
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map
        (LinearPathCategory.pathHom q) ≫
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map
        (LinearPathCategory.pathHom p) = _
  rw [← (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map_comp,
    LinearPathCategory.pathHom_comp]
  rfl

/-- The usual admissibility condition `J^N ⊆ I ⊆ J²` for a relation
ideal in a path algebra, expressed in the free linear path category. -/
structure IsAdmissible (R : RelationFamily k Q) : Prop where
  relationIdeal_le_lengthTail_two :
    ∀ X Y,
      HomIdeal.generatedHomSubmodule k R X Y ≤
        LinearPathCategory.lengthTail X Y 2
  long_paths_mem :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ {x y : Q} (p : Quiver.Path x y), N ≤ p.length →
        LinearPathCategory.pathHom p ∈
          HomIdeal.generatedHomSubmodule k R
            (LinearPathCategory.obj k Q y)
            (LinearPathCategory.obj k Q x)

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- Degree one and the tail of degree at least two meet only in zero. -/
theorem eq_zero_of_mem_lengthComponent_one_of_mem_lengthTail_two
    {X Y : LinearPathCategory.Category k Q} {f : X ⟶ Y}
    (hone : f ∈ LinearPathCategory.lengthComponent X Y 1)
    (htwo : f ∈ LinearPathCategory.lengthTail X Y 2) :
    f = 0 := by
  apply (LinearPathCategory.homPathLinearEquiv X Y).injective
  rw [map_zero]
  apply Finsupp.ext
  intro p
  by_cases hp : p ∈
      (LinearPathCategory.homPathLinearEquiv X Y f).support
  · have hpone :=
      (LinearPathCategory.mem_lengthComponent_iff X Y 1 f).1 hone hp
    have hptwo :=
      (LinearPathCategory.mem_lengthTail_iff X Y 2 f).1 htwo hp
    change p.length = 1 at hpone
    change 2 ≤ p.length at hptwo
    omega
  · rw [Finsupp.notMem_support_iff.mp hp]
    rfl

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- Admissibility makes the quotient map injective on the entire degree-one
subspace. -/
theorem quotientHomLinearMap_injOn_lengthComponent_one
    {R : RelationFamily k Q} (hR : IsAdmissible R)
    (X Y : LinearPathCategory.Category k Q) :
    Set.InjOn
      (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X Y)
      (LinearPathCategory.lengthComponent X Y 1) := by
  intro f hf g hg hfg
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_lengthComponent_one_of_mem_lengthTail_two
    (Submodule.sub_mem _ hf hg)
  apply hR.relationIdeal_le_lengthTail_two X Y
  rw [← LinearPathCategory.HomogeneousQuotient.ker_quotientHomLinearMap,
    LinearMap.mem_ker]
  simpa using congrArg (fun q ↦ q -
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R X Y g) hfg

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- A path of length below two survives every admissible quotient. -/
theorem pathMap_ne_zero_of_length_lt_two
    {R : RelationFamily k Q} (hR : IsAdmissible R)
    {x y : Q} (p : Quiver.Path x y) (hp : p.length < 2) :
    pathMap R p ≠ 0 := by
  intro hzero
  have hmem : LinearPathCategory.pathHom p ∈
      HomIdeal.generatedHomSubmodule k R
        (LinearPathCategory.obj k Q y)
        (LinearPathCategory.obj k Q x) := by
    rw [← LinearPathCategory.HomogeneousQuotient.ker_quotientHomLinearMap]
    change
      LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
          (LinearPathCategory.obj k Q y)
          (LinearPathCategory.obj k Q x)
          (LinearPathCategory.pathHom p) = 0
    exact hzero
  have htail := hR.relationIdeal_le_lengthTail_two _ _ hmem
  have hlength :=
    (LinearPathCategory.pathHom_mem_lengthTail_iff p 2).1 htail
  change 2 ≤ p.length at hlength
  omega

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- In particular, every displayed arrow survives an admissible quotient. -/
theorem arrowMap_ne_zero {R : RelationFamily k Q} (hR : IsAdmissible R)
    {x y : Q} (a : x ⟶ y) :
    arrowMap R a ≠ 0 :=
  pathMap_ne_zero_of_length_lt_two hR a.toPath (by simp)

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- The images of parallel displayed arrows remain linearly independent in
an admissible quotient. -/
theorem arrowMap_linearIndependent
    {R : RelationFamily k Q} (hR : IsAdmissible R) (x y : Q) :
    LinearIndependent k (fun a : x ⟶ y ↦ arrowMap R a) := by
  let sourceFamily : (x ⟶ y) →
      (LinearPathCategory.obj k Q y ⟶ LinearPathCategory.obj k Q x) :=
    fun a ↦ LinearPathCategory.pathHom a.toPath
  have htoPath : Function.Injective (fun a : x ⟶ y ↦ a.toPath) := by
    intro a b hab
    injection hab
  have hsource : LinearIndependent k sourceFamily := by
    exact
      (LinearPathCategory.homPathBasis
        (LinearPathCategory.obj k Q y)
        (LinearPathCategory.obj k Q x)).linearIndependent.comp
          (fun a : x ⟶ y ↦ a.toPath) htoPath
  let q :=
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
      (LinearPathCategory.obj k Q y)
      (LinearPathCategory.obj k Q x)
  have hspan : Submodule.span k (Set.range sourceFamily) ≤
      LinearPathCategory.lengthComponent
        (LinearPathCategory.obj k Q y)
        (LinearPathCategory.obj k Q x) 1 := by
    apply Submodule.span_le.2
    rintro f ⟨a, rfl⟩
    exact (LinearPathCategory.pathHom_mem_lengthComponent_iff a.toPath 1).2 rfl
  have hinj : Set.InjOn q (Submodule.span k (Set.range sourceFamily)) :=
    (quotientHomLinearMap_injOn_lengthComponent_one hR _ _).mono hspan
  have hmapped := hsource.map_injOn q hinj
  change LinearIndependent k (q ∘ sourceFamily)
  exact hmapped

omit [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] in
/-- The images of paths shorter than an admissibility cutoff span every Hom
space in the quotient. -/
theorem span_boundedPathMap_eq_top
    {R : RelationFamily k Q} {N : ℕ}
    (hlong : ∀ {x y : Q} (p : Quiver.Path x y), N ≤ p.length →
      LinearPathCategory.pathHom p ∈
        HomIdeal.generatedHomSubmodule k R
          (LinearPathCategory.obj k Q y)
          (LinearPathCategory.obj k Q x))
    (x y : Q) :
    Submodule.span k
      (Set.range fun p : Quiver.Path.BoundedPaths y x (N - 1) ↦
        pathMap R p.1) = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨g, rfl⟩ :=
    LinearPathCategory.HomogeneousQuotient.quotientHom_surjective R
      (LinearPathCategory.obj k Q x)
      (LinearPathCategory.obj k Q y) f
  have hg :=
    (LinearPathCategory.homPathBasis
      (LinearPathCategory.obj k Q x)
      (LinearPathCategory.obj k Q y)).mem_span g
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨p, rfl⟩
      rw [LinearPathCategory.homPathBasis_apply]
      by_cases hp : p.length < N
      · apply Submodule.subset_span
        exact ⟨⟨p, Nat.le_sub_one_of_lt hp⟩, rfl⟩
      · have hpIdeal := hlong p (by omega)
        have hpKer : LinearPathCategory.pathHom p ∈
            LinearMap.ker
              (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
                (LinearPathCategory.obj k Q x)
                (LinearPathCategory.obj k Q y)) := by
          rw [LinearPathCategory.HomogeneousQuotient.ker_quotientHomLinearMap]
          exact hpIdeal
        change
          LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
              (LinearPathCategory.obj k Q x)
              (LinearPathCategory.obj k Q y)
              (LinearPathCategory.pathHom p) ∈ _
        rw [LinearMap.mem_ker.mp hpKer]
        exact Submodule.zero_mem _
  | zero => simp
  | add g h _ _ hg hh =>
      simpa using Submodule.add_mem _ hg hh
  | smul c g _ hg =>
      simpa using Submodule.smul_mem _ c hg

/-- Every Hom space of a finite admissible bound-quiver quotient is
finite-dimensional. -/
theorem quotientHom_finiteDimensional
    {R : RelationFamily k Q} (hR : IsAdmissible R) (x y : Q) :
    FiniteDimensional k (obj R x ⟶ obj R y) := by
  obtain ⟨N, _, hlong⟩ := hR.long_paths_mem
  let family := fun p : Quiver.Path.BoundedPaths y x (N - 1) ↦ pathMap R p.1
  have hspan : Submodule.span k (Set.range family) = ⊤ :=
    span_boundedPathMap_eq_top hlong x y
  letI : FiniteDimensional k (Submodule.span k (Set.range family)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range family)
  apply Module.Finite.of_surjective
    (Submodule.subtype (Submodule.span k (Set.range family)))
  intro f
  refine ⟨⟨f, ?_⟩, rfl⟩
  rw [hspan]
  exact Submodule.mem_top

/-- Admissibility over a finite quiver supplies the finite-dimensional
representables needed by the finite category-algebra construction. -/
theorem finiteRepresentablesOfAdmissible
    {R : RelationFamily k Q} (hR : IsAdmissible R) :
    ∀ X : Category R,
      CoveringHom.IsFiniteDimensionalModule (C := Category R) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  rintro ⟨X⟩
  constructor
  · rintro ⟨Y⟩
    exact quotientHom_finiteDimensional hR X Y
  · exact Set.toFinite _

/-- Admissibility also supplies finite-dimensional representables on the
opposite quotient category.  These are the literal projective right modules
for the displayed bound quiver. -/
theorem finiteOppositeRepresentablesOfAdmissible
    {R : RelationFamily k Q} (hR : IsAdmissible R) :
    ∀ X : (Category R)ᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule (C := (Category R)ᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  rintro ⟨⟨X⟩⟩
  constructor
  · rintro ⟨⟨Y⟩⟩
    letI : FiniteDimensional k (obj R Y ⟶ obj R X) :=
      quotientHom_finiteDimensional hR Y X
    exact Module.Finite.equiv
      (CoveringHom.oppositeHomLinearEquiv (k := k)
        (Opposite.op (obj R X)) (Opposite.op (obj R Y))).symm
  · letI : Fintype ((Category R)ᵒᵖ) :=
      Fintype.ofEquiv (Category R) Opposite.equivToOpposite
    exact Set.toFinite _

/-- A literal finite bound-quiver presentation of `A`.  Finite-dimensionality
of the quotient category algebra is derived from admissibility. -/
structure Presentation (k A Q : Type u)
    [Field k] [Ring A] [Algebra k A]
    [Fintype Q] [Quiver.{u} Q] [∀ x y : Q, Fintype (x ⟶ y)] where
  relations : RelationFamily k Q
  admissible : IsAdmissible relations
  algebraEquiv :
    A ≃ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (finiteRepresentablesOfAdmissible admissible)

/-- A bound-quiver presentation satisfying the two degree bounds and the
two unique-nonzero-continuation conditions of the manuscript. -/
structure SpecialBiserialPresentation (k A Q : Type u)
    [Field k] [Ring A] [Algebra k A]
    [Fintype Q] [Quiver.{u} Q] [∀ x y : Q, Fintype (x ⟶ y)]
    extends Presentation k A Q where
  arrows_starting_le_two :
    ∀ x : Q, Nat.card (Quiver.Star x) ≤ 2
  arrows_ending_le_two :
    ∀ x : Q, Nat.card (Quiver.Costar x) ≤ 2
  continuation_right_le_one :
    ∀ {x y : Q} (a : x ⟶ y),
      Nat.card
        {b : Quiver.Star y //
          arrowMap toPresentation.relations b.2 ≫
              arrowMap toPresentation.relations a ≠ 0} ≤ 1
  continuation_left_le_one :
    ∀ {x y : Q} (a : x ⟶ y),
      Nat.card
        {c : Quiver.Costar x //
          arrowMap toPresentation.relations a ≫
              arrowMap toPresentation.relations c.2 ≠ 0} ≤ 1

namespace SpecialBiserialPresentation

/-- Transport a special-biserial presentation across an algebra
equivalence. -/
def mapAlgEquiv
    {Q' : Type u} [Fintype Q'] [Quiver.{u} Q']
    [∀ x y : Q', Fintype (x ⟶ y)]
    (P : SpecialBiserialPresentation k A Q') (e : B ≃ₐ[k] A) :
    SpecialBiserialPresentation k B Q' where
  relations := P.toPresentation.relations
  admissible := P.toPresentation.admissible
  algebraEquiv := e.trans P.toPresentation.algebraEquiv
  arrows_starting_le_two := P.arrows_starting_le_two
  arrows_ending_le_two := P.arrows_ending_le_two
  continuation_right_le_one := P.continuation_right_le_one
  continuation_left_le_one := P.continuation_left_le_one

end SpecialBiserialPresentation

/-- A universe-local bundle of a finite quiver and a special-biserial
presentation.  Bundling the instances makes the existence predicate below a
literal proposition rather than an interface with a hidden chosen quiver. -/
structure SpecialBiserialModel (k A : Type u)
    [Field k] [Ring A] [Algebra k A] where
  Vertex : Type u
  vertexFintype : Fintype Vertex
  quiver : Quiver.{u} Vertex
  arrowFintype :
    letI : Quiver.{u} Vertex := quiver
    ∀ x y : Vertex, Fintype (x ⟶ y)
  presentation :
    letI : Fintype Vertex := vertexFintype
    letI : Quiver.{u} Vertex := quiver
    letI (x y : Vertex) : Fintype (x ⟶ y) := arrowFintype x y
    SpecialBiserialPresentation k A Vertex

/-- A basic algebra admits the manuscript's special-biserial bound-quiver
presentation.  The final theorem will apply this predicate to a chosen basic
algebra of the original algebra. -/
def AdmitsSpecialBiserialPresentation (k A : Type u)
    [Field k] [Ring A] [Algebra k A] : Prop :=
  Nonempty (SpecialBiserialModel k A)

namespace SpecialBiserialModel

/-- Transport a bundled special-biserial model across an algebra
equivalence. -/
def mapAlgEquiv
    (M : SpecialBiserialModel k A) (e : B ≃ₐ[k] A) :
    SpecialBiserialModel k B where
  Vertex := M.Vertex
  vertexFintype := M.vertexFintype
  quiver := M.quiver
  arrowFintype := M.arrowFintype
  presentation := by
    letI : Fintype M.Vertex := M.vertexFintype
    letI : Quiver.{u} M.Vertex := M.quiver
    letI (x y : M.Vertex) : Fintype (x ⟶ y) := M.arrowFintype x y
    exact M.presentation.mapAlgEquiv e

end SpecialBiserialModel

/-- Admitting a special-biserial bound-quiver presentation is invariant under
algebra equivalence. -/
theorem admitsSpecialBiserialPresentation_iff_of_algEquiv
    (e : A ≃ₐ[k] B) :
    AdmitsSpecialBiserialPresentation k A ↔
      AdmitsSpecialBiserialPresentation k B := by
  constructor
  · rintro ⟨M⟩
    exact ⟨M.mapAlgEquiv e.symm⟩
  · rintro ⟨M⟩
    exact ⟨M.mapAlgEquiv e⟩

end MagnitudeConjecture.BoundQuiver
