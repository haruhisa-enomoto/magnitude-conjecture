import MagnitudeConjecture.Algebra.SpecialBiserialBranchIndependence
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaInjective

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- Admissibility over a finite quiver also makes every coefficient-dual
corepresentable finite-dimensional with finite support. -/
theorem finiteDualCorepresentablesOfAdmissible
    {R : RelationFamily k Q} (hR : IsAdmissible R) :
    ∀ X : Category R,
      CoveringHom.IsFiniteDimensionalModule (C := Category R) k
        (CoveringHom.dualLinearYonedaLinearModule (k := k) X) := by
  rintro ⟨X⟩
  constructor
  · rintro ⟨Y⟩
    change FiniteDimensional k (Module.Dual k (obj R Y ⟶ obj R X))
    letI : FiniteDimensional k (obj R Y ⟶ obj R X) :=
      quotientHom_finiteDimensional hR Y X
    infer_instance
  · exact Set.toFinite _

/-- A normalized functional detecting one nonzero surviving relation path
class. -/
noncomputable def relationSurvivingSupportFunctional
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (_hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    Module.Dual k
      (obj P.toPresentation.relations z ⟶
        obj P.toPresentation.relations x) :=
  Classical.choose
    (Module.Projective.exists_dual_eq_one k p.2.2)

@[simp]
theorem relationSurvivingSupportFunctional_pathMap
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    P.relationSurvivingSupportFunctional r hr p
        (pathMap P.toPresentation.relations p.1) = 1 :=
  Classical.choose_spec
    (Module.Projective.exists_dual_eq_one k p.2.2)

/-- The finite covariant representable whose path basis consists of paths
ending at `z`. -/
abbrev relationSourceRepresentable
    (P : SpecialBiserialPresentation k A Q) (z : Q) :=
  CoveringHom.finiteDimensionalLinearCoyoneda (k := k)
    (obj P.toPresentation.relations z)
    (finiteRepresentablesOfAdmissible P.toPresentation.admissible
      (obj P.toPresentation.relations z))

/-- The finite dual corepresentable whose dual path coordinates consist of
paths beginning at `x`. -/
abbrev relationTargetDualCorepresentable
    (P : SpecialBiserialPresentation k A Q) (x : Q) :=
  CoveringHom.finiteDimensionalDualLinearYoneda (k := k)
    (obj P.toPresentation.relations x)
    (finiteDualCorepresentablesOfAdmissible P.toPresentation.admissible
      (obj P.toPresentation.relations x))

/-- A surviving relation path class induces the composition-pairing map from
the representable at its terminal vertex to the dual corepresentable at its
initial vertex. -/
noncomputable def relationSurvivingSupportNakayamaHom
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    P.relationSourceRepresentable z ⟶
      P.relationTargetDualCorepresentable x :=
  (CoveringHom.finiteDualLinearYonedaHomEquiv
    (P.relationSourceRepresentable z)
    (obj P.toPresentation.relations x)
    (finiteDualCorepresentablesOfAdmissible
      P.toPresentation.admissible
      (obj P.toPresentation.relations x))).symm
        (P.relationSurvivingSupportFunctional r hr p)

/-- The induced module map is literally composition followed by the chosen
path-detecting functional. -/
theorem relationSurvivingSupportNakayamaHom_app_apply_apply
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    (Y : Category P.toPresentation.relations)
    (f : obj P.toPresentation.relations z ⟶ Y)
    (g : Y ⟶ obj P.toPresentation.relations x) :
    (show Module.Dual k
        (Y ⟶ obj P.toPresentation.relations x) from
      (P.relationSurvivingSupportNakayamaHom r hr p).hom.hom.app Y f) g =
      P.relationSurvivingSupportFunctional r hr p (f ≫ g) := by
  rfl

/-- The exact remaining combinatorial property needed to identify the two
endpoint modules attached to a paired maximal relation path. -/
def HasPerfectRelationPairing
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) : Prop :=
  ∀ Y : Category P.toPresentation.relations,
    Function.Bijective
      ((P.relationSurvivingSupportNakayamaHom r hr p).hom.hom.app Y)

/-- A perfect composition pairing makes the relation-induced module map an
isomorphism. -/
theorem relationSurvivingSupportNakayamaHom_isIso
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    (hperfect : P.HasPerfectRelationPairing r hr p) :
    IsIso (P.relationSurvivingSupportNakayamaHom r hr p) := by
  let f := P.relationSurvivingSupportNakayamaHom r hr p
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := Category P.toPresentation.relations) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := Category P.toPresentation.relations) k).ι
  letI appIso (Y : Category P.toPresentation.relations) :
      IsIso (f.hom.hom.app Y) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.hom.hom.app Y)).mpr
    exact hperfect Y
  haveI : IsIso f.hom.hom := NatIso.isIso_of_isIso_app f.hom.hom
  haveI : IsIso (I.map f.hom) := by
    change IsIso f.hom.hom
    infer_instance
  haveI : IsIso f.hom := isIso_of_reflects_iso f.hom I
  haveI : IsIso (J.map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f J

/-- The representable ending at a paired maximal relation path is injective
once its composition pairing is perfect. -/
theorem relationSourceRepresentable_injective_of_perfect
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    (hperfect : P.HasPerfectRelationPairing r hr p) :
    Injective (P.relationSourceRepresentable z) := by
  let hI := finiteDualCorepresentablesOfAdmissible
    P.toPresentation.admissible
    (obj P.toPresentation.relations x)
  let target := P.relationTargetDualCorepresentable x
  letI : Injective target :=
    CoveringHom.finiteDimensionalDualLinearYoneda_injective
      (obj P.toPresentation.relations x) hI
  letI : IsIso (P.relationSurvivingSupportNakayamaHom r hr p) :=
    P.relationSurvivingSupportNakayamaHom_isIso r hr p hperfect
  exact Injective.of_iso
    (asIso (P.relationSurvivingSupportNakayamaHom r hr p)).symm
      (inferInstance : Injective target)

/-- Every surviving path ending at the terminal vertex of a paired maximal
relation path is a suffix of one of the two relation-support paths. -/
theorem survivingPath_ending_relationSupport_factor
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations y z) :
    ∃ t : P.RelationSurvivingSupport r,
      ∃ g : Quiver.Path x y, t.1 = g.comp s.1 := by
  by_cases hsLength : s.1.length = 0
  · have hyz : y = z := s.1.eq_of_length_zero hsLength
    subst y
    refine ⟨p, p.1, ?_⟩
    rw [s.1.eq_nil_of_length_zero hsLength]
    simp
  · obtain ⟨m, shead, a, hsPath⟩ :=
      (Quiver.Path.length_ne_zero_iff_eq_cons s.1).1 hsLength
    have hsPath' : s.1 = shead.comp a.toPath := by
      simpa only [Quiver.Path.comp_toPath_eq_cons] using hsPath
    obtain ⟨t, htArrow⟩ :=
      (P.relationSurvivingSupportFinalArrow_bijective r hr p).2
        (⟨m, a⟩ : Quiver.Costar z)
    let dt := P.relationSurvivingSupportFinalDecomposition r hr t
    change (⟨dt.middle, dt.arrow⟩ : Quiver.Costar z) = ⟨m, a⟩ at htArrow
    cases htArrow
    let ss : P.LeftContinuationPath dt.arrow := by
      refine ⟨⟨y, shead⟩, ?_⟩
      change pathMap P.toPresentation.relations dt.arrow.toPath ≫
        pathMap P.toPresentation.relations shead ≠ 0
      rw [pathMap_comp, ← hsPath']
      exact s.2
    let tt : P.LeftContinuationPath dt.arrow := by
      refine ⟨⟨x, dt.head⟩, ?_⟩
      change pathMap P.toPresentation.relations dt.arrow.toPath ≫
        pathMap P.toPresentation.relations dt.head ≠ 0
      rw [pathMap_comp, ← dt.path_eq]
      exact t.2.2
    have hlength : shead.length ≤ dt.head.length := by
      by_contra hnot
      have hlt : dt.head.length < shead.length := Nat.lt_of_not_ge hnot
      obtain ⟨u, hu, huLength⟩ :=
        P.leftContinuationPath_factor_of_length_lt dt.arrow tt ss hlt
      have hu' : shead = u.comp dt.head := by
        simpa only [ss, tt] using hu
      have htHull : LinearPathCategory.pathHom t.1 ∈
          pathSupportHull P.toPresentation.relations
            (LinearPathCategory.obj k Q z)
            (LinearPathCategory.obj k Q x) :=
        ⟨t.1, rfl, r, hr, t.2.1⟩
      have hzero := P.pathSupportHullGenerator_comp_pathMap_eq_zero
        htHull u huLength
      apply s.2
      rw [hsPath', hu', Quiver.Path.comp_assoc, ← dt.path_eq,
        ← pathMap_comp]
      exact hzero
    obtain ⟨g, hg⟩ :=
      P.leftContinuationPath_factor_of_length_le dt.arrow ss tt hlength
    have hg' : dt.head = g.comp shead := by
      simpa only [ss, tt] using hg
    refine ⟨t, g, ?_⟩
    rw [dt.path_eq, hg', hsPath', Quiver.Path.comp_assoc]

/-- Every surviving path beginning at the initial vertex of a paired maximal
relation path is a prefix of one of the two relation-support paths. -/
theorem survivingPath_starting_relationSupport_factor
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations x y) :
    ∃ t : P.RelationSurvivingSupport r,
      ∃ h : Quiver.Path y z, t.1 = s.1.comp h := by
  by_cases hsLength : s.1.length = 0
  · have hxy : x = y := s.1.eq_of_length_zero hsLength
    subst y
    refine ⟨p, p.1, ?_⟩
    rw [s.1.eq_nil_of_length_zero hsLength]
    simp
  · obtain ⟨m, a, stail, hsPath, _⟩ :=
      (Quiver.Path.length_ne_zero_iff_eq_comp s.1).1 hsLength
    obtain ⟨t, htArrow⟩ :=
      (P.relationSurvivingSupportInitialArrow_bijective r hr p).2
        (⟨m, a⟩ : Quiver.Star x)
    let dt := P.relationSurvivingSupportInitialDecomposition r hr t
    change (⟨dt.middle, dt.arrow⟩ : Quiver.Star x) = ⟨m, a⟩ at htArrow
    cases htArrow
    let ss : P.RightContinuationPath dt.arrow := by
      refine ⟨⟨y, stail⟩, ?_⟩
      change pathMap P.toPresentation.relations stail ≫
        pathMap P.toPresentation.relations dt.arrow.toPath ≠ 0
      rw [pathMap_comp, ← hsPath]
      exact s.2
    let tt : P.RightContinuationPath dt.arrow := by
      refine ⟨⟨z, dt.tail⟩, ?_⟩
      change pathMap P.toPresentation.relations dt.tail ≫
        pathMap P.toPresentation.relations dt.arrow.toPath ≠ 0
      rw [pathMap_comp, ← dt.path_eq]
      exact t.2.2
    have hlength : stail.length ≤ dt.tail.length := by
      by_contra hnot
      have hlt : dt.tail.length < stail.length := Nat.lt_of_not_ge hnot
      obtain ⟨u, hu⟩ :=
        P.rightContinuationPath_factor_of_length_le dt.arrow tt ss hlt.le
      have hu' : stail = dt.tail.comp u := by
        simpa only [ss, tt] using hu
      have huLength : u.length ≠ 0 := by
        intro huZero
        have hlen := congrArg Quiver.Path.length hu'
        simp only [Quiver.Path.length_comp, huZero, add_zero] at hlen
        omega
      have htHull : LinearPathCategory.pathHom t.1 ∈
          pathSupportHull P.toPresentation.relations
            (LinearPathCategory.obj k Q z)
            (LinearPathCategory.obj k Q x) :=
        ⟨t.1, rfl, r, hr, t.2.1⟩
      have hzero := P.pathMap_comp_pathSupportHullGenerator_eq_zero
        htHull u huLength
      apply s.2
      rw [hsPath, hu', ← Quiver.Path.comp_assoc, ← dt.path_eq,
        ← pathMap_comp]
      exact hzero
    obtain ⟨h, hh⟩ :=
      P.rightContinuationPath_factor_of_length_le dt.arrow ss tt hlength
    have hh' : dt.tail = stail.comp h := by
      simpa only [ss, tt] using hh
    refine ⟨t, h, ?_⟩
    rw [dt.path_eq, hh', hsPath, ← Quiver.Path.comp_assoc]

/-- If a surviving path into the paired terminal vertex is killed by the
path-support-hull quotient, then it is itself one of the two maximal relation
paths: its complementary prefix has length zero. -/
theorem survivingPath_ending_hullKernel_relationSupport
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations y z)
    (hsHull : pathMap (pathSupportHull P.toPresentation.relations) s.1 = 0) :
    ∃ (t : P.RelationSurvivingSupport r) (g : Quiver.Path x y),
      t.1 = g.comp s.1 ∧ g.length = 0 := by
  obtain ⟨t, g, ht⟩ := P.survivingPath_ending_relationSupport_factor r hr p s
  refine ⟨t, g, ht, ?_⟩
  by_contra hgLength
  have hsRelative : pathMap P.toPresentation.relations s.1 ∈
      (MagnitudeConjecture.BoundQuiver.relativeRelationHomIdeal
        (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
          P.toPresentation.relations)).hom
        (obj P.toPresentation.relations z)
        (obj P.toPresentation.relations y) := by
    apply (MagnitudeConjecture.BoundQuiver.mem_relativeRelationHomIdeal_iff_exists_lift
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)
      (pathMap P.toPresentation.relations s.1)).2
    refine ⟨LinearPathCategory.pathHom s.1, rfl, ?_⟩
    exact (pathMap_eq_zero_iff_mem_relationIdeal
      (pathSupportHull P.toPresentation.relations) s.1).1 hsHull
  obtain ⟨w, ghead, a, hg⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons g).1 hgLength
  have hzero := P.relativePathSupportHull_leftExtension_eq_zero
    (pathMap P.toPresentation.relations s.1) hsRelative a
  change pathMap P.toPresentation.relations s.1 ≫
    pathMap P.toPresentation.relations a.toPath = 0 at hzero
  apply t.2.2
  rw [ht, ← pathMap_comp, hg,
    ← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp,
    ← Category.assoc, hzero, CategoryTheory.Limits.zero_comp]

/-- If a surviving path out of the paired initial vertex is killed by the
path-support-hull quotient, then it is itself one of the two maximal relation
paths: its complementary suffix has length zero. -/
theorem survivingPath_starting_hullKernel_relationSupport
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations x y)
    (hsHull : pathMap (pathSupportHull P.toPresentation.relations) s.1 = 0) :
    ∃ (t : P.RelationSurvivingSupport r) (h : Quiver.Path y z),
      t.1 = s.1.comp h ∧ h.length = 0 := by
  obtain ⟨t, h, ht⟩ := P.survivingPath_starting_relationSupport_factor r hr p s
  refine ⟨t, h, ht, ?_⟩
  by_contra hhLength
  have hsRelative : pathMap P.toPresentation.relations s.1 ∈
      (MagnitudeConjecture.BoundQuiver.relativeRelationHomIdeal
        (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
          P.toPresentation.relations)).hom
        (obj P.toPresentation.relations y)
        (obj P.toPresentation.relations x) := by
    apply (MagnitudeConjecture.BoundQuiver.mem_relativeRelationHomIdeal_iff_exists_lift
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)
      (pathMap P.toPresentation.relations s.1)).2
    refine ⟨LinearPathCategory.pathHom s.1, rfl, ?_⟩
    exact (pathMap_eq_zero_iff_mem_relationIdeal
      (pathSupportHull P.toPresentation.relations) s.1).1 hsHull
  obtain ⟨w, a, htail, hh, _⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp h).1 hhLength
  have hzero := P.relativePathSupportHull_rightExtension_eq_zero
    (pathMap P.toPresentation.relations s.1) hsRelative a
  change pathMap P.toPresentation.relations a.toPath ≫
    pathMap P.toPresentation.relations s.1 = 0 at hzero
  apply t.2.2
  rw [ht, ← pathMap_comp, hh, ← pathMap_comp, Category.assoc,
    hzero, CategoryTheory.Limits.comp_zero]

/-- At the two endpoints of a paired relation, the support-hull kernel is
spanned by precisely the surviving paths displayed in that relation. -/
theorem relativePathSupportHull_endpoint_eq_span_relationSupport
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    HomIdeal.homSubmodule (k := k)
        (relativeRelationHomIdeal
          (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
            P.toPresentation.relations))
        (obj P.toPresentation.relations z)
        (obj P.toPresentation.relations x) =
      Submodule.span k
        (Set.range fun t : P.RelationSurvivingSupport r ↦
          pathMap P.toPresentation.relations t.1) := by
  rw [relativeRelationHomIdeal_eq_span_killedPathMap
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations)
    (pathSupportHull_isMonomial P.toPresentation.relations) x z]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro f ⟨s, rfl⟩
    by_cases hs : pathMap P.toPresentation.relations s.1 = 0
    · change pathMap P.toPresentation.relations s.1 ∈ _
      rw [hs]
      exact Submodule.zero_mem _
    · let ss : SurvivingPath P.toPresentation.relations x z := ⟨s.1, hs⟩
      obtain ⟨t, g, ht, hg⟩ :=
        P.survivingPath_ending_hullKernel_relationSupport r hr p ss s.2
      have hgNil : g = Quiver.Path.nil := g.eq_nil_of_length_zero hg
      have htPath : t.1 = s.1 := by
        simpa only [hgNil, Quiver.Path.nil_comp] using ht
      apply Submodule.subset_span
      refine ⟨t, ?_⟩
      change pathMap P.toPresentation.relations t.1 =
        pathMap P.toPresentation.relations s.1
      exact congrArg (pathMap P.toPresentation.relations) htPath
  · apply Submodule.span_le.2
    rintro f ⟨t, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨t.1, ?_⟩, rfl⟩
    apply (pathMap_eq_zero_iff_mem_relationIdeal
      (pathSupportHull P.toPresentation.relations) t.1).2
    apply HomIdeal.relation_mem_linearSpan
      (pathSupportHull P.toPresentation.relations)
    exact ⟨t.1, rfl, r, hr, t.2.1⟩

/-- The endpoint kernel coordinate is the line generated by either one of
the two surviving relation-path classes. -/
theorem relativePathSupportHull_endpoint_eq_span_singleton
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    HomIdeal.homSubmodule (k := k)
        (relativeRelationHomIdeal
          (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
            P.toPresentation.relations))
        (obj P.toPresentation.relations z)
        (obj P.toPresentation.relations x) =
      Submodule.span k
        {pathMap P.toPresentation.relations p.1} := by
  rw [P.relativePathSupportHull_endpoint_eq_span_relationSupport r hr p]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro f ⟨t, rfl⟩
    by_cases htp : t = p
    · subst t
      exact Submodule.subset_span (Set.mem_singleton _)
    · obtain ⟨c, _, hc⟩ :=
        P.relationSurvivingSupport_pathMap_eq_smul r hr t p (Ne.symm htp)
      change pathMap P.toPresentation.relations t.1 ∈ _
      rw [hc]
      exact Submodule.smul_mem _ c
        (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_mono
    rintro f rfl
    exact ⟨p, rfl⟩

/-- Away from the initial endpoint, the terminal row of the support-hull
kernel vanishes. -/
theorem relativePathSupportHull_terminalCoordinate_eq_bot_of_ne
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (hyx : y ≠ x) :
    HomIdeal.homSubmodule (k := k)
        (relativeRelationHomIdeal
          (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
            P.toPresentation.relations))
        (obj P.toPresentation.relations z)
        (obj P.toPresentation.relations y) = ⊥ := by
  rw [relativeRelationHomIdeal_eq_span_killedPathMap
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations)
    (pathSupportHull_isMonomial P.toPresentation.relations) y z]
  rw [Submodule.span_eq_bot]
  intro f hf
  rcases hf with ⟨s, rfl⟩
  by_cases hs : pathMap P.toPresentation.relations s.1 = 0
  · exact hs
  · let ss : SurvivingPath P.toPresentation.relations y z := ⟨s.1, hs⟩
    obtain ⟨_, g, _, hg⟩ :=
      P.survivingPath_ending_hullKernel_relationSupport r hr p ss s.2
    exact (hyx (g.eq_of_length_zero hg).symm).elim

/-- Away from the terminal endpoint, the initial column of the support-hull
kernel vanishes. -/
theorem relativePathSupportHull_initialCoordinate_eq_bot_of_ne
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (hyz : y ≠ z) :
    HomIdeal.homSubmodule (k := k)
        (relativeRelationHomIdeal
          (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
            P.toPresentation.relations))
        (obj P.toPresentation.relations y)
        (obj P.toPresentation.relations x) = ⊥ := by
  rw [relativeRelationHomIdeal_eq_span_killedPathMap
    (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
      P.toPresentation.relations)
    (pathSupportHull_isMonomial P.toPresentation.relations) x y]
  rw [Submodule.span_eq_bot]
  intro f hf
  rcases hf with ⟨s, rfl⟩
  by_cases hs : pathMap P.toPresentation.relations s.1 = 0
  · exact hs
  · let ss : SurvivingPath P.toPresentation.relations x y := ⟨s.1, hs⟩
    obtain ⟨_, h, _, hh⟩ :=
      P.survivingPath_starting_hullKernel_relationSupport r hr p ss s.2
    exact (hyz (h.eq_of_length_zero hh)).elim

end MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation
