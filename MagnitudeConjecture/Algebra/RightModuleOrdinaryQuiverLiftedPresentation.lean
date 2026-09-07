import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverUniverseLift
import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiverFullness
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-!
# A universe-local ordinary-quiver presentation

The ordinary quiver is naturally indexed by a small finite type, whereas the
public bound-quiver presentation bundle places its coefficient field, algebra,
and vertex type in one universe.  We therefore transport the exact ordinary
kernel attached to any ordinary-arrow representative system to `ULift` of the
projective labels.  Path reindexing preserves length, so admissibility and the
quotient realization are unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Realize the lifted ordinary quiver by first forgetting the universe lift. -/
def ordinaryLiftedRealization (D : S.OrdinaryArrowRepresentatives) :
    LinearPathCategory.Category k S.OrdinaryLiftedVertex ⥤
      S.ProjectiveCategory :=
  S.ordinaryLiftedToOrdinary ⋙ D.realization

noncomputable instance ordinaryLiftedRealization_additive
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedRealization D).Additive := by
  dsimp only [ordinaryLiftedRealization]
  infer_instance

noncomputable instance ordinaryLiftedRealization_linear
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedRealization D).Linear k := by
  dsimp only [ordinaryLiftedRealization]
  infer_instance

/-- A wrapper separating the lifted projective objects from the quiver vertex
type, so their distinct categorical and quiver structures never compete in
typeclass inference. -/
@[ext]
structure LiftedProjectiveLabel where
  vertex : S.OrdinaryLiftedVertex

noncomputable instance liftedProjectiveLabelFintype :
    Fintype S.LiftedProjectiveLabel :=
  Fintype.ofEquiv S.OrdinaryLiftedVertex
    { toFun := LiftedProjectiveLabel.mk
      invFun := LiftedProjectiveLabel.vertex
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The selected-projective category reindexed by wrapped lifted labels. -/
abbrev LiftedProjectiveCategory :=
  InducedCategory S.ProjectiveCategory
    (fun x : S.LiftedProjectiveLabel ↦
      (x.vertex.down : S.ProjectiveCategory))

noncomputable instance liftedProjectiveCategoryCategory :
    CategoryTheory.Category S.LiftedProjectiveCategory := by
  letI : CategoryTheory.Category S.ProjectiveCategory :=
    S.projectiveCategoryCategory
  exact inferInstanceAs (CategoryTheory.Category
    (InducedCategory S.ProjectiveCategory
      (fun x : S.LiftedProjectiveLabel ↦
        (x.vertex.down : S.ProjectiveCategory))))

noncomputable instance liftedProjectiveCategoryPreadditive :
    Preadditive S.LiftedProjectiveCategory := by
  letI : CategoryTheory.Category S.ProjectiveCategory :=
    S.projectiveCategoryCategory
  letI : Preadditive S.ProjectiveCategory :=
    S.projectiveCategoryPreadditive
  exact inferInstanceAs (Preadditive
    (InducedCategory S.ProjectiveCategory
      (fun x : S.LiftedProjectiveLabel ↦
        (x.vertex.down : S.ProjectiveCategory))))

noncomputable instance liftedProjectiveCategoryLinear :
    Linear k S.LiftedProjectiveCategory := by
  letI : CategoryTheory.Category S.ProjectiveCategory :=
    S.projectiveCategoryCategory
  letI : Preadditive S.ProjectiveCategory :=
    S.projectiveCategoryPreadditive
  letI : Linear k S.ProjectiveCategory :=
    S.projectiveCategoryLinear
  exact inferInstanceAs (Linear k
    (InducedCategory S.ProjectiveCategory
      (fun x : S.LiftedProjectiveLabel ↦
        (x.vertex.down : S.ProjectiveCategory))))

noncomputable instance liftedProjectiveCategoryFintype :
    Fintype S.LiftedProjectiveCategory :=
  inferInstanceAs (Fintype S.LiftedProjectiveLabel)

/-- Realize the lifted ordinary quiver in the universe-local copy of the
selected-projective category. -/
def ordinaryLiftedProjectiveRealization
    (D : S.OrdinaryArrowRepresentatives) :
    LinearPathCategory.Category k S.OrdinaryLiftedVertex ⥤
      S.LiftedProjectiveCategory where
  obj X := ⟨LinearPathCategory.vertex X⟩
  map f := InducedCategory.homMk ((S.ordinaryLiftedRealization D).map f)
  map_id X := by
    apply InducedCategory.hom_ext
    exact (S.ordinaryLiftedRealization D).map_id X
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (S.ordinaryLiftedRealization D).map_comp f g

noncomputable instance ordinaryLiftedProjectiveRealization_additive
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedProjectiveRealization D).Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    change (S.ordinaryLiftedRealization D).map (f + g) =
      (S.ordinaryLiftedRealization D).map f +
        (S.ordinaryLiftedRealization D).map g
    exact (S.ordinaryLiftedRealization D).map_add

noncomputable instance ordinaryLiftedProjectiveRealization_linear
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedProjectiveRealization D).Linear k where
  map_smul := by
    intro X Y f r
    apply InducedCategory.hom_ext
    change (S.ordinaryLiftedRealization D).map (r • f) =
      r • (S.ordinaryLiftedRealization D).map f
    exact (S.ordinaryLiftedRealization D).map_smul r f

@[simp]
theorem ordinaryLiftedProjectiveRealization_map_hom
    (D : S.OrdinaryArrowRepresentatives)
    {X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex}
    (f : X ⟶ Y) :
    ((S.ordinaryLiftedProjectiveRealization D).map f).hom =
      (S.ordinaryLiftedRealization D).map f :=
  rfl

/-- The full kernel of the lifted ordinary-quiver realization. -/
def ordinaryLiftedRelations (D : S.OrdinaryArrowRepresentatives) :
    BoundQuiver.RelationFamily k S.OrdinaryLiftedVertex :=
  fun _ _ ↦ {f | (S.ordinaryLiftedRealization D).map f = 0}

@[simp]
theorem mem_ordinaryLiftedRelations_iff
    (D : S.OrdinaryArrowRepresentatives)
    {X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex}
    (f : X ⟶ Y) :
    f ∈ S.ordinaryLiftedRelations D X Y ↔
      (S.ordinaryLiftedRealization D).map f = 0 :=
  Iff.rfl

/-- The relation family is already a two-sided linear kernel. -/
theorem ordinaryLiftedRelations_generatedHomSubmodule_eq_ker
    (D : S.OrdinaryArrowRepresentatives)
    (X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex) :
    HomIdeal.generatedHomSubmodule k (S.ordinaryLiftedRelations D) X Y =
      LinearMap.ker ((S.ordinaryLiftedRealization D).mapLinearMap k) := by
  ext f
  constructor
  · intro hf
    have hf' : f ∈
        (HomIdeal.linearSpan k (S.ordinaryLiftedRelations D)).hom X Y := hf
    have hk := HomIdeal.linearSpan_le (S.ordinaryLiftedRelations D)
      (HomIdeal.functorKernel (k := k) (S.ordinaryLiftedRealization D))
      (fun hr ↦ hr) hf'
    exact hk
  · intro hf
    apply HomIdeal.relation_mem_linearSpan (S.ordinaryLiftedRelations D)
    exact hf

/-- Forgetting the universe lift preserves path length. -/
@[simp]
theorem ordinaryLiftedPathEquiv_length
    {x y : S.OrdinaryLiftedVertex} (p : Quiver.Path x y) :
    (S.ordinaryLiftedPathEquiv x y p).length = p.length := by
  change (S.ordinaryQuiverDownPrefunctor.mapPath p).length = p.length
  induction p with
  | nil => rfl
  | cons p a ih =>
      simp only [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih]

/-- The endpoint-exact path equivalence used by the free-category functor also
preserves length. -/
@[simp]
theorem ordinaryLiftedFunctorPathEquiv_length
    {X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex}
    (p : Quiver.Path (LinearPathCategory.vertex Y)
      (LinearPathCategory.vertex X)) :
    (S.ordinaryLiftedFunctorPathEquiv X Y p).length = p.length := by
  change (S.ordinaryLiftedPathEquiv
    (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X) p).length =
      p.length
  exact S.ordinaryLiftedPathEquiv_length p

/-- The path-coordinate map of the Hom equivalence is literal domain
reindexing. -/
theorem homPathLinearEquiv_ordinaryLiftedHomLinearEquiv
    (X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex)
    (f : X ⟶ Y) :
    LinearPathCategory.homPathLinearEquiv
        (S.ordinaryLiftedToOrdinary.obj X)
        (S.ordinaryLiftedToOrdinary.obj Y)
        (S.ordinaryLiftedHomLinearEquiv X Y f) =
      Finsupp.equivMapDomain
        (S.ordinaryLiftedFunctorPathEquiv X Y)
        (LinearPathCategory.homPathLinearEquiv X Y f) := by
  rw [ordinaryLiftedHomLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- The lifted kernel has no path terms below length two. -/
theorem ordinaryLiftedRelations_generatedHomSubmodule_le_lengthTail_two
    (D : S.OrdinaryArrowRepresentatives)
    (X Y : LinearPathCategory.Category k S.OrdinaryLiftedVertex) :
    HomIdeal.generatedHomSubmodule k (S.ordinaryLiftedRelations D) X Y ≤
      LinearPathCategory.lengthTail X Y 2 := by
  intro f hf
  rw [S.ordinaryLiftedRelations_generatedHomSubmodule_eq_ker D] at hf
  have hmap : S.ordinaryLiftedToOrdinary.map f =
      S.ordinaryLiftedHomLinearEquiv X Y f := by
    exact LinearMap.congr_fun
      (S.ordinaryLiftedToOrdinary_map_eq_homLinearEquiv X Y) f
  have hsmallKernel :
      D.realization.map
        (S.ordinaryLiftedHomLinearEquiv X Y f) = 0 := by
    rw [← hmap]
    exact hf
  have hsmallTail :
      S.ordinaryLiftedHomLinearEquiv X Y f ∈
        LinearPathCategory.lengthTail
          (S.ordinaryLiftedToOrdinary.obj X)
          (S.ordinaryLiftedToOrdinary.obj Y) 2 := by
    apply D.relations_generatedHomSubmodule_le_lengthTail_two
    rw [D.relations_generatedHomSubmodule_eq_ker]
    exact hsmallKernel
  rw [LinearPathCategory.mem_lengthTail_iff] at hsmallTail ⊢
  intro p hp
  let e := S.ordinaryLiftedFunctorPathEquiv X Y
  have hpCoeff :
      LinearPathCategory.homPathLinearEquiv X Y f p ≠ 0 :=
    Finsupp.mem_support_iff.mp hp
  have hpImageCoeff :
      LinearPathCategory.homPathLinearEquiv
          (S.ordinaryLiftedToOrdinary.obj X)
          (S.ordinaryLiftedToOrdinary.obj Y)
          (S.ordinaryLiftedHomLinearEquiv X Y f) (e p) ≠ 0 := by
    rw [S.homPathLinearEquiv_ordinaryLiftedHomLinearEquiv,
      Finsupp.equivMapDomain_apply, e.symm_apply_apply]
    exact hpCoeff
  have hpImage : e p ∈
      (LinearPathCategory.homPathLinearEquiv
        (S.ordinaryLiftedToOrdinary.obj X)
        (S.ordinaryLiftedToOrdinary.obj Y)
        (S.ordinaryLiftedHomLinearEquiv X Y f)).support :=
    Finsupp.mem_support_iff.mpr hpImageCoeff
  have hlength := hsmallTail hpImage
  simpa [e] using hlength

/-- The same radical-nilpotence cutoff kills every sufficiently long lifted
ordinary path. -/
theorem ordinaryLiftedRelations_long_paths_mem :
    ∀ D : S.OrdinaryArrowRepresentatives,
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ {x y : S.OrdinaryLiftedVertex} (p : Quiver.Path x y),
        N ≤ p.length →
          LinearPathCategory.pathHom p ∈
            HomIdeal.generatedHomSubmodule k (S.ordinaryLiftedRelations D)
              (LinearPathCategory.obj k S.OrdinaryLiftedVertex y)
              (LinearPathCategory.obj k S.OrdinaryLiftedVertex x) := by
  intro D
  obtain ⟨N, hN, hpath⟩ := D.exists_realization_pathHom_eq_zero
  refine ⟨N, hN, ?_⟩
  intro x y p hp
  rw [S.ordinaryLiftedRelations_generatedHomSubmodule_eq_ker D]
  change (S.ordinaryLiftedRealization D).map
      (LinearPathCategory.pathHom p) = 0
  change D.realization.map
      (S.ordinaryLiftedToOrdinary.map
        (LinearPathCategory.pathHom p)) = 0
  rw [S.ordinaryLiftedToOrdinary_map_pathHom]
  apply hpath
  simpa using hp

/-- The lifted full kernel is an admissible relation ideal. -/
theorem ordinaryLiftedRelations_isAdmissible :
    ∀ D : S.OrdinaryArrowRepresentatives,
      BoundQuiver.IsAdmissible (S.ordinaryLiftedRelations D) := fun D ↦ {
  relationIdeal_le_lengthTail_two :=
    S.ordinaryLiftedRelations_generatedHomSubmodule_le_lengthTail_two D
  long_paths_mem := S.ordinaryLiftedRelations_long_paths_mem D
  }

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Covariant representables of the lifted selected-projective category are
pointwise finite-dimensional and finitely supported. -/
theorem liftedProjectiveCategory_finiteRepresentables :
    ∀ X : S.LiftedProjectiveCategory,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.LiftedProjectiveCategory) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    let inclusion : (X ⟶ Y) →ₗ[k]
        (S.fgObj X.vertex.down.label ⟶
          S.fgObj Y.vertex.down.label) :=
      { toFun := fun f ↦ f.hom.hom
        map_add' := by
          intro f g
          rfl
        map_smul' := by
          intro r f
          rfl }
    apply Module.Finite.of_injective inclusion
    intro f g hfg
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    exact hfg
  · exact Set.toFinite _

/-- The chosen basic algebra, formed from one lifted copy of every selected
indecomposable projective. -/
abbrev basicAlgebra :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    S.liftedProjectiveCategory_finiteRepresentables

noncomputable instance basicAlgebra_finiteDimensional :
    FiniteDimensional k S.basicAlgebra :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    S.liftedProjectiveCategory_finiteRepresentables

/-- The lifted realization kills the ideal generated by its full kernel. -/
theorem ordinaryLiftedRelationIdeal_isKilledBy :
    ∀ D : S.OrdinaryArrowRepresentatives,
    (LinearPathCategory.HomogeneousQuotient.relationIdeal
      (S.ordinaryLiftedRelations D)).IsKilledBy
        (S.ordinaryLiftedProjectiveRealization D) := by
  intro D X Y f hf
  have hf' : f ∈ HomIdeal.generatedHomSubmodule k
      (S.ordinaryLiftedRelations D) X Y := hf
  rw [S.ordinaryLiftedRelations_generatedHomSubmodule_eq_ker D] at hf'
  apply InducedCategory.hom_ext
  change (S.ordinaryLiftedRealization D).map f = 0
  exact hf'

/-- Realization of the lifted ordinary bound-quiver category. -/
def ordinaryLiftedQuiverQuotientRealization
    (D : S.OrdinaryArrowRepresentatives) :
    BoundQuiver.Category (S.ordinaryLiftedRelations D) ⥤
      S.LiftedProjectiveCategory :=
  (LinearPathCategory.HomogeneousQuotient.relationIdeal
      (S.ordinaryLiftedRelations D)).quotientLift
    (S.ordinaryLiftedProjectiveRealization D)
      (S.ordinaryLiftedRelationIdeal_isKilledBy D)

/-- Under the quotient realization, a displayed lifted arrow is the selected
ordinary-arrow representative with the same underlying endpoints. -/
@[simp]
theorem ordinaryLiftedQuiverQuotientRealization_map_arrowMap_hom
    (D : S.OrdinaryArrowRepresentatives)
    {x y : S.OrdinaryLiftedVertex} (a : x ⟶ y) :
    ((S.ordinaryLiftedQuiverQuotientRealization D).map
      (BoundQuiver.arrowMap (S.ordinaryLiftedRelations D) a)).hom =
        D.hom a := by
  change (S.ordinaryLiftedRealization D).map
      (LinearPathCategory.pathHom a.toPath) = D.hom a
  change D.realization.map
      (S.ordinaryLiftedToOrdinary.map
        (LinearPathCategory.pathHom a.toPath)) = D.hom a
  rw [S.ordinaryLiftedToOrdinary_map_pathHom,
    D.realization_map_pathHom]
  rw [show S.ordinaryLiftedPathEquiv x y a.toPath =
      (show Quiver.Path x.down y.down from Quiver.Path.nil.cons a) by rfl,
    OrdinaryArrowRepresentatives.pathMap,
    LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil]
  exact Category.comp_id _

noncomputable instance ordinaryLiftedQuiverQuotientRealization_additive
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientRealization D).Additive := by
  dsimp only [ordinaryLiftedQuiverQuotientRealization]
  infer_instance

noncomputable instance ordinaryLiftedQuiverQuotientRealization_linear
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientRealization D).Linear k := by
  dsimp only [ordinaryLiftedQuiverQuotientRealization]
  infer_instance

noncomputable instance ordinaryLiftedQuiverQuotientRealization_faithful
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientRealization D).Faithful := by
  apply HomIdeal.quotientLift_faithful
  intro X Y f hf
  change f ∈ HomIdeal.generatedHomSubmodule k
    (S.ordinaryLiftedRelations D) X Y
  rw [S.ordinaryLiftedRelations_generatedHomSubmodule_eq_ker D]
  have hhom := congrArg InducedCategory.Hom.hom hf
  change (S.ordinaryLiftedRealization D).map f = 0 at hhom
  exact hhom

/-- The lifted quotient still has exactly one object for each selected
indecomposable projective. -/
theorem ordinaryLiftedQuiverQuotientRealization_obj_bijective :
    ∀ D : S.OrdinaryArrowRepresentatives,
      Function.Bijective (S.ordinaryLiftedQuiverQuotientRealization D).obj := by
  intro D
  constructor
  · rintro ⟨X⟩ ⟨Y⟩ hXY
    congr
    exact congrArg LiftedProjectiveLabel.vertex hXY
  · intro Y
    exact ⟨⟨LinearPathCategory.obj k S.OrdinaryLiftedVertex
      Y.vertex⟩, rfl⟩

noncomputable instance ordinaryLiftedQuiverQuotientRealization_essSurj
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientRealization D).EssSurj := by
  constructor
  intro Y
  obtain ⟨X, hX⟩ :=
    (S.ordinaryLiftedQuiverQuotientRealization_obj_bijective D).2 Y
  exact ⟨X, ⟨eqToIso hX⟩⟩

variable [IsAlgClosed k]

noncomputable instance ordinaryLiftedRealization_full
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedRealization D).Full := by
  dsimp only [ordinaryLiftedRealization]
  infer_instance

noncomputable instance ordinaryLiftedProjectiveRealization_full
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedProjectiveRealization D).Full where
  map_surjective {X Y} f := by
    refine ⟨(S.ordinaryLiftedRealization D).preimage f.hom, ?_⟩
    apply InducedCategory.hom_ext
    exact (S.ordinaryLiftedRealization D).map_preimage f.hom

noncomputable instance ordinaryLiftedQuiverQuotientRealization_full
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientRealization D).Full := by
  dsimp only [ordinaryLiftedQuiverQuotientRealization]
  infer_instance

/-- The lifted ordinary bound-quiver category is linearly equivalent to the
selected-projective category. -/
noncomputable def ordinaryLiftedQuiverQuotientEquivalence
    (D : S.OrdinaryArrowRepresentatives) :
    BoundQuiver.Category (S.ordinaryLiftedRelations D) ≌
      S.LiftedProjectiveCategory := by
  let F := S.ordinaryLiftedQuiverQuotientRealization D
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

noncomputable instance
    ordinaryLiftedQuiverQuotientEquivalence_functor_additive
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientEquivalence D).functor.Additive := by
  change (S.ordinaryLiftedQuiverQuotientRealization D).Additive
  infer_instance

noncomputable instance
    ordinaryLiftedQuiverQuotientEquivalence_functor_linear
    (D : S.OrdinaryArrowRepresentatives) :
    (S.ordinaryLiftedQuiverQuotientEquivalence D).functor.Linear k := by
  change (S.ordinaryLiftedQuiverQuotientRealization D).Linear k
  infer_instance

/-- The chosen basic algebra has a literal universe-local bound-quiver
presentation by the lifted ordinary quiver and its exact kernel. -/
noncomputable def ordinaryLiftedPresentation
    (D : S.OrdinaryArrowRepresentatives) :
    BoundQuiver.Presentation k S.basicAlgebra S.OrdinaryLiftedVertex where
  relations := S.ordinaryLiftedRelations D
  admissible := S.ordinaryLiftedRelations_isAdmissible D
  algebraEquiv :=
    (CoveringHom.finiteCategoryAlgebraEquiv
      (BoundQuiver.finiteRepresentablesOfAdmissible
        (S.ordinaryLiftedRelations_isAdmissible D))
      S.liftedProjectiveCategory_finiteRepresentables
      (S.ordinaryLiftedQuiverQuotientEquivalence D)
      (S.ordinaryLiftedQuiverQuotientRealization_obj_bijective D)).symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
