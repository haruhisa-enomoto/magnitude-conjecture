import MagnitudeConjecture.Algebra.SpecialBiserialSoclePairing

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

/-- Two surviving arms of one relation which have a common nonempty suffix
are the same arm. -/
theorem relationSurvivingSupport_eq_of_common_suffix
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (t u : P.RelationSurvivingSupport r)
    {y : Q} (s : Quiver.Path y z) (hs : s.length ≠ 0)
    (g h : Quiver.Path x y)
    (ht : t.1 = g.comp s) (hu : u.1 = h.comp s) :
    t = u := by
  obtain ⟨m, shead, a, hsPath⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons s).1 hs
  have hsPath' : s = shead.comp a.toPath := by
    simpa only [Quiver.Path.comp_toPath_eq_cons] using hsPath
  let dt := P.relationSurvivingSupportFinalDecomposition r hr t
  let du := P.relationSurvivingSupportFinalDecomposition r hr u
  have htLast : (⟨dt.middle, dt.arrow⟩ : Quiver.Costar z) = ⟨m, a⟩ := by
    have heq : dt.head.comp dt.arrow.toPath =
        (g.comp shead).comp a.toPath := by
      calc
        dt.head.comp dt.arrow.toPath = t.1 := dt.path_eq.symm
        _ = g.comp s := ht
        _ = g.comp (shead.comp a.toPath) := congrArg g.comp hsPath'
        _ = (g.comp shead).comp a.toPath :=
          (Quiver.Path.comp_assoc _ _ _).symm
    rw [Quiver.Path.comp_toPath_eq_cons,
      Quiver.Path.comp_toPath_eq_cons] at heq
    injection heq <;> simp_all
  have huLast : (⟨du.middle, du.arrow⟩ : Quiver.Costar z) = ⟨m, a⟩ := by
    have heq : du.head.comp du.arrow.toPath =
        (h.comp shead).comp a.toPath := by
      calc
        du.head.comp du.arrow.toPath = u.1 := du.path_eq.symm
        _ = h.comp s := hu
        _ = h.comp (shead.comp a.toPath) := congrArg h.comp hsPath'
        _ = (h.comp shead).comp a.toPath :=
          (Quiver.Path.comp_assoc _ _ _).symm
    rw [Quiver.Path.comp_toPath_eq_cons,
      Quiver.Path.comp_toPath_eq_cons] at heq
    injection heq <;> simp_all
  apply P.relationSurvivingSupportFinalArrow_injective r hr
  exact htLast.trans huLast.symm

/-- The first arrow of a nonempty path, packaged independently of its final
vertex. -/
private def pathInitialArrow? {x y : Q} :
    Quiver.Path x y → Option (Quiver.Star x)
  | .nil => none
  | .cons (.nil) a => some ⟨_, a⟩
  | .cons (.cons q a) b => pathInitialArrow? (q.cons a)

private theorem pathInitialArrow?_cons_of_length_ne_zero
    {x y z : Q} (q : Quiver.Path x y) (b : y ⟶ z)
    (hq : q.length ≠ 0) :
    pathInitialArrow? (q.cons b) = pathInitialArrow? q := by
  cases q with
  | nil => simp at hq
  | cons q a =>
      cases q <;> rfl

private theorem pathInitialArrow?_toPath_comp
    {x y z : Q} (a : x ⟶ y) (q : Quiver.Path y z) :
    pathInitialArrow? (a.toPath.comp q) = some ⟨y, a⟩ := by
  induction q with
  | nil => rfl
  | cons q b ih =>
      rw [Quiver.Path.comp_cons]
      rw [pathInitialArrow?_cons_of_length_ne_zero]
      · exact ih
      · simp

/-- Two surviving arms of one relation which have a common nonempty prefix
are the same arm. -/
theorem relationSurvivingSupport_eq_of_common_prefix
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (t u : P.RelationSurvivingSupport r)
    {y : Q} (s : Quiver.Path x y) (hs : s.length ≠ 0)
    (g h : Quiver.Path y z)
    (ht : t.1 = s.comp g) (hu : u.1 = s.comp h) :
    t = u := by
  obtain ⟨m, a, stail, hsPath, _⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp s).1 hs
  let dt := P.relationSurvivingSupportInitialDecomposition r hr t
  let du := P.relationSurvivingSupportInitialDecomposition r hr u
  have htFirst : (⟨dt.middle, dt.arrow⟩ : Quiver.Star x) = ⟨m, a⟩ := by
    have heq : dt.arrow.toPath.comp dt.tail =
        a.toPath.comp (stail.comp g) := by
      calc
        dt.arrow.toPath.comp dt.tail = t.1 := dt.path_eq.symm
        _ = s.comp g := ht
        _ = (a.toPath.comp stail).comp g := congrArg (·.comp g) hsPath
        _ = a.toPath.comp (stail.comp g) := Quiver.Path.comp_assoc _ _ _
    have hfirst := congrArg pathInitialArrow? heq
    exact Option.some.inj (by
      simpa only [pathInitialArrow?_toPath_comp] using hfirst)
  have huFirst : (⟨du.middle, du.arrow⟩ : Quiver.Star x) = ⟨m, a⟩ := by
    have heq : du.arrow.toPath.comp du.tail =
        a.toPath.comp (stail.comp h) := by
      calc
        du.arrow.toPath.comp du.tail = u.1 := du.path_eq.symm
        _ = s.comp h := hu
        _ = (a.toPath.comp stail).comp h := congrArg (·.comp h) hsPath
        _ = a.toPath.comp (stail.comp h) := Quiver.Path.comp_assoc _ _ _
    have hfirst := congrArg pathInitialArrow? heq
    exact Option.some.inj (by
      simpa only [pathInitialArrow?_toPath_comp] using hfirst)
  apply P.relationSurvivingSupportInitialArrow_injective r hr
  exact htFirst.trans huFirst.symm

/-- A free morphism with nonzero image in a relation quotient has a basis
path with both nonzero coefficient and nonzero quotient image. -/
theorem exists_path_coefficient_ne_zero_of_quotientMap_ne_zero
    (R : RelationFamily k Q) {x z : Q}
    (f : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hf : (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map f ≠ 0) :
    ∃ p : Quiver.Path x z,
      LinearPathCategory.homPathLinearEquiv
          (LinearPathCategory.obj k Q z)
          (LinearPathCategory.obj k Q x) f p ≠ 0 ∧
        pathMap R p ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  let b : Module.Basis (Quiver.Path x z) k
      (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x) :=
    LinearPathCategory.homPathBasis
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  let quotient :=
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  have hfExpansion :
      Finsupp.linearCombination k (fun q ↦ b q) (b.repr f) = f :=
    b.linearCombination_repr f
  have hquotient (q : Quiver.Path x z) :
      quotient (b q) = pathMap R q := by
    change quotient (LinearPathCategory.pathHom q) = pathMap R q
    rfl
  have hmapped := congrArg quotient hfExpansion
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at hmapped
  simp_rw [map_smul, hquotient] at hmapped
  change quotient f = 0
  rw [← hmapped]
  apply Finset.sum_eq_zero
  intro q hq
  have hcoeff : LinearPathCategory.homPathLinearEquiv
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x) f q ≠ 0 := by
    change b.repr f q ≠ 0
    exact Finsupp.mem_support_iff.mp hq
  change (b.repr f q) • pathMap R q = 0
  rw [h q hcoeff, smul_zero]

/-- Mapping a free morphism to the relation quotient is the finite sum of
its path coefficients times the corresponding path classes. -/
theorem quotientMap_eq_pathMap_sum
    (R : RelationFamily k Q) {x z : Q}
    (f : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x) :
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor R).map f =
      ∑ q ∈ (LinearPathCategory.homPathLinearEquiv
          (LinearPathCategory.obj k Q z)
          (LinearPathCategory.obj k Q x) f).support,
        LinearPathCategory.homPathLinearEquiv
            (LinearPathCategory.obj k Q z)
            (LinearPathCategory.obj k Q x) f q • pathMap R q := by
  let b : Module.Basis (Quiver.Path x z) k
      (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x) :=
    LinearPathCategory.homPathBasis
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  let quotient :=
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  have hfExpansion :
      Finsupp.linearCombination k (fun q ↦ b q) (b.repr f) = f :=
    b.linearCombination_repr f
  have hquotient (q : Quiver.Path x z) :
      quotient (b q) = pathMap R q := by
    change quotient (LinearPathCategory.pathHom q) = pathMap R q
    rfl
  have hmapped := congrArg quotient hfExpansion
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at hmapped
  simp_rw [map_smul, hquotient] at hmapped
  exact hmapped.symm

/-- Extend a free linear combination of paths on the initial side by an
arbitrary nonempty path and then pass to the special-biserial quotient. -/
def leftPathExtensionLinearMap
    (P : SpecialBiserialPresentation k A Q)
    {x y z : Q} (g : Quiver.Path x y) :
    (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q y) →ₗ[k]
      (obj P.toPresentation.relations z ⟶
        obj P.toPresentation.relations x) where
  toFun f :=
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map f ≫
        pathMap P.toPresentation.relations g
  map_add' f h := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_add, Preadditive.add_comp]
  map_smul' c f := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_smul,
      CategoryTheory.Linear.smul_comp]
    rfl

/-- If extension by a nonempty initial path kills a free linear combination,
then every coefficient whose extended path survives was already zero. -/
theorem homPathCoefficient_eq_zero_of_leftPathExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {x y z : Q} (g : Quiver.Path x y) (hg : g.length ≠ 0)
    (f : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q y)
    (hf : P.leftPathExtensionLinearMap g f = 0)
    (p : Quiver.Path y z)
    (hp : pathMap P.toPresentation.relations p ≫
        pathMap P.toPresentation.relations g ≠ 0) :
    LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q y) f p = 0 := by
  obtain ⟨m, a, tail, hgPath, _⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp g).1 hg
  have hpathMap_g : pathMap P.toPresentation.relations g =
      pathMap P.toPresentation.relations tail ≫
        arrowMap P.toPresentation.relations a := by
    calc
      pathMap P.toPresentation.relations g =
          pathMap P.toPresentation.relations (a.toPath.comp tail) :=
        congrArg (pathMap P.toPresentation.relations) hgPath
      _ = pathMap P.toPresentation.relations tail ≫
          pathMap P.toPresentation.relations a.toPath :=
        (pathMap_comp P.toPresentation.relations a.toPath tail).symm
      _ = pathMap P.toPresentation.relations tail ≫
          arrowMap P.toPresentation.relations a := rfl
  let B := LinearPathCategory.homPathBasis
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q y)
  let F :
      (LinearPathCategory.obj k Q z ⟶
          LinearPathCategory.obj k Q y) →ₗ[k]
        (obj P.toPresentation.relations z ⟶
          obj P.toPresentation.relations x) :=
    P.leftPathExtensionLinearMap g
  let toBranch : {q : Quiver.Path y z // F (B q) ≠ 0} →
      P.RightContinuationAt a z := fun q ↦ by
    refine ⟨tail.comp q.1, ?_⟩
    have hq := q.2
    change pathMap P.toPresentation.relations q.1 ≫
      pathMap P.toPresentation.relations g ≠ 0 at hq
    rw [hpathMap_g] at hq
    intro hzero
    apply hq
    rw [← Category.assoc,
      pathMap_comp P.toPresentation.relations tail q.1]
    exact hzero
  have toBranch_injective : Function.Injective toBranch := by
    intro q s hqs
    apply Subtype.ext
    apply Quiver.Path.comp_injective_right tail
    exact congrArg Subtype.val hqs
  have hfamily : (fun q : {q : Quiver.Path y z // F (B q) ≠ 0} ↦
      F (B q.1)) = P.rightBranchPathMap a z ∘ toBranch := by
    funext q
    change pathMap P.toPresentation.relations q.1 ≫
        pathMap P.toPresentation.relations g =
      pathMap P.toPresentation.relations (tail.comp q.1) ≫
        arrowMap P.toPresentation.relations a
    calc
      pathMap P.toPresentation.relations q.1 ≫
          pathMap P.toPresentation.relations g =
          pathMap P.toPresentation.relations q.1 ≫
            (pathMap P.toPresentation.relations tail ≫
              arrowMap P.toPresentation.relations a) := by
        rw [hpathMap_g]
      _ = (pathMap P.toPresentation.relations q.1 ≫
            pathMap P.toPresentation.relations tail) ≫
              arrowMap P.toPresentation.relations a :=
        (Category.assoc _ _ _).symm
      _ = pathMap P.toPresentation.relations (tail.comp q.1) ≫
          arrowMap P.toPresentation.relations a := by
        rw [pathMap_comp P.toPresentation.relations tail q.1]
  have hli : LinearIndependent k
      (fun q : {q : Quiver.Path y z // F (B q) ≠ 0} ↦ F (B q.1)) := by
    rw [hfamily]
    exact (P.rightBranchPathMap_linearIndependent a z).comp
      toBranch toBranch_injective
  have hp' : F (B p) ≠ 0 := by
    change pathMap P.toPresentation.relations p ≫
      pathMap P.toPresentation.relations g ≠ 0
    exact hp
  exact B.repr_eq_zero_of_map_eq_zero_of_image_ne_zero
    F hli f hf p hp'

/-- Extend a free linear combination of paths on the terminal side by an
arbitrary nonempty path and then pass to the special-biserial quotient. -/
def rightPathExtensionLinearMap
    (P : SpecialBiserialPresentation k A Q)
    {x y z : Q} (h : Quiver.Path y z) :
    (LinearPathCategory.obj k Q y ⟶
        LinearPathCategory.obj k Q x) →ₗ[k]
      (obj P.toPresentation.relations z ⟶
        obj P.toPresentation.relations x) where
  toFun g := pathMap P.toPresentation.relations h ≫
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map g
  map_add' g l := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_add, Preadditive.comp_add]
  map_smul' c g := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_smul,
      CategoryTheory.Linear.comp_smul]
    rfl

/-- If extension by a nonempty terminal path kills a free linear
combination, then every coefficient whose extended path survives was already
zero. -/
theorem homPathCoefficient_eq_zero_of_rightPathExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {x y z : Q} (h : Quiver.Path y z) (hh : h.length ≠ 0)
    (g : LinearPathCategory.obj k Q y ⟶
      LinearPathCategory.obj k Q x)
    (hg : P.rightPathExtensionLinearMap h g = 0)
    (q : Quiver.Path x y)
    (hq : pathMap P.toPresentation.relations h ≫
        pathMap P.toPresentation.relations q ≠ 0) :
    LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q y)
        (LinearPathCategory.obj k Q x) g q = 0 := by
  obtain ⟨m, head, a, hhPath⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons h).1 hh
  have hpathMap_h : pathMap P.toPresentation.relations h =
      arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations head := by
    calc
      pathMap P.toPresentation.relations h =
          pathMap P.toPresentation.relations (head.comp a.toPath) :=
        congrArg (pathMap P.toPresentation.relations)
          (by simpa only [Quiver.Path.comp_toPath_eq_cons] using hhPath)
      _ = pathMap P.toPresentation.relations a.toPath ≫
          pathMap P.toPresentation.relations head :=
        (pathMap_comp P.toPresentation.relations head a.toPath).symm
      _ = arrowMap P.toPresentation.relations a ≫
          pathMap P.toPresentation.relations head := rfl
  let B := LinearPathCategory.homPathBasis
    (LinearPathCategory.obj k Q y)
    (LinearPathCategory.obj k Q x)
  let F :
      (LinearPathCategory.obj k Q y ⟶
          LinearPathCategory.obj k Q x) →ₗ[k]
        (obj P.toPresentation.relations z ⟶
          obj P.toPresentation.relations x) :=
    P.rightPathExtensionLinearMap h
  let toBranch : {q : Quiver.Path x y // F (B q) ≠ 0} →
      P.LeftContinuationAt a x := fun q ↦ by
    refine ⟨q.1.comp head, ?_⟩
    have hq := q.2
    change pathMap P.toPresentation.relations h ≫
      pathMap P.toPresentation.relations q.1 ≠ 0 at hq
    rw [hpathMap_h] at hq
    intro hzero
    apply hq
    rw [Category.assoc,
      pathMap_comp P.toPresentation.relations q.1 head]
    exact hzero
  have toBranch_injective : Function.Injective toBranch := by
    intro q s hqs
    apply Subtype.ext
    apply Quiver.Path.comp_injective_left head
    exact congrArg Subtype.val hqs
  have hfamily : (fun q : {q : Quiver.Path x y // F (B q) ≠ 0} ↦
      F (B q.1)) = P.leftBranchPathMap a x ∘ toBranch := by
    funext q
    change pathMap P.toPresentation.relations h ≫
        pathMap P.toPresentation.relations q.1 =
      arrowMap P.toPresentation.relations a ≫
        pathMap P.toPresentation.relations (q.1.comp head)
    calc
      pathMap P.toPresentation.relations h ≫
          pathMap P.toPresentation.relations q.1 =
          (arrowMap P.toPresentation.relations a ≫
            pathMap P.toPresentation.relations head) ≫
              pathMap P.toPresentation.relations q.1 := by rw [hpathMap_h]
      _ = arrowMap P.toPresentation.relations a ≫
          (pathMap P.toPresentation.relations head ≫
            pathMap P.toPresentation.relations q.1) :=
        Category.assoc _ _ _
      _ = arrowMap P.toPresentation.relations a ≫
          pathMap P.toPresentation.relations (q.1.comp head) := by
        rw [pathMap_comp P.toPresentation.relations q.1 head]
  have hli : LinearIndependent k
      (fun q : {q : Quiver.Path x y // F (B q) ≠ 0} ↦ F (B q.1)) := by
    rw [hfamily]
    exact (P.leftBranchPathMap_linearIndependent a x).comp
      toBranch toBranch_injective
  have hq' : F (B q) ≠ 0 := by
    change pathMap P.toPresentation.relations h ≫
      pathMap P.toPresentation.relations q ≠ 0
    exact hq
  exact B.repr_eq_zero_of_map_eq_zero_of_image_ne_zero
    F hli g hg q hq'

/-- The chosen maximal relation arm containing a surviving suffix. -/
noncomputable def endingRelationSupportFactor
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations y z) :
    P.RelationSurvivingSupport r :=
  Classical.choose (P.survivingPath_ending_relationSupport_factor r hr p s)

/-- The chosen complementary prefix from `x` to the initial vertex of a
surviving suffix. -/
noncomputable def endingRelationComplement
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations y z) :
    Quiver.Path x y :=
  Classical.choose (Classical.choose_spec
    (P.survivingPath_ending_relationSupport_factor r hr p s))

theorem endingRelationSupportFactor_path_eq
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations y z) :
    (P.endingRelationSupportFactor r hr p s).1 =
      (P.endingRelationComplement r hr p s).comp s.1 :=
  Classical.choose_spec (Classical.choose_spec
    (P.survivingPath_ending_relationSupport_factor r hr p s))

/-- The chosen maximal relation arm containing a surviving prefix. -/
noncomputable def startingRelationSupportFactor
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations x y) :
    P.RelationSurvivingSupport r :=
  Classical.choose (P.survivingPath_starting_relationSupport_factor r hr p s)

/-- The chosen complementary suffix from the terminal vertex of a surviving
prefix to the terminal relation vertex. -/
noncomputable def startingRelationComplement
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations x y) :
    Quiver.Path y z :=
  Classical.choose (Classical.choose_spec
    (P.survivingPath_starting_relationSupport_factor r hr p s))

theorem startingRelationSupportFactor_path_eq
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (s : SurvivingPath P.toPresentation.relations x y) :
    (P.startingRelationSupportFactor r hr p s).1 =
      s.1.comp (P.startingRelationComplement r hr p s) :=
  Classical.choose_spec (Classical.choose_spec
    (P.survivingPath_starting_relationSupport_factor r hr p s))

/-- Every nonzero element of the terminal representable can be composed into
the nonzero endpoint line of the paired relation. -/
theorem exists_comp_mem_relationEndpointLine_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (f : obj P.toPresentation.relations z ⟶
      obj P.toPresentation.relations y) (hf : f ≠ 0) :
    ∃ g : obj P.toPresentation.relations y ⟶
        obj P.toPresentation.relations x,
      f ≫ g ∈ Submodule.span k
          {pathMap P.toPresentation.relations p.1} ∧
        f ≫ g ≠ 0 := by
  classical
  let R := P.toPresentation.relations
  let quotient :=
    LinearPathCategory.HomogeneousQuotient.quotientFunctor R
  obtain ⟨lift, hlift⟩ :=
    LinearPathCategory.HomogeneousQuotient.quotientHom_surjective R
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q y) f
  have hliftMap : quotient.map lift = f := by
    change (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q y)) lift = f
    exact hlift
  let coeff : Quiver.Path y z →₀ k :=
    LinearPathCategory.homPathLinearEquiv
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q y) lift
  have hliftNe : quotient.map lift ≠ 0 := by
    change (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q y)) lift ≠ 0
    rw [hlift]
    exact hf
  let T : Finset (Quiver.Path y z) :=
    coeff.support.filter fun q ↦ pathMap R q ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨q, hqCoeff, hqMap⟩ :=
      exists_path_coefficient_ne_zero_of_quotientMap_ne_zero R lift hliftNe
    refine ⟨q, ?_⟩
    simp only [T, Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨hqCoeff, hqMap⟩
  let toSurviving : {q // q ∈ T} → SurvivingPath R y z := fun q ↦
    ⟨q.1, (Finset.mem_filter.mp q.2).2⟩
  let score : {q // q ∈ T} → ℕ := fun q ↦
    (P.endingRelationComplement r hr p (toSurviving q)).length
  have hmain (hpositive : ∀ q, q ∈ T → q.length ≠ 0) :
      ∃ g : obj R y ⟶ obj R x,
        f ≫ g ∈ Submodule.span k {pathMap R p.1} ∧ f ≫ g ≠ 0 := by
    obtain ⟨q, _, hqMax⟩ :=
      Finset.exists_max_image T.attach score
        (by
          obtain ⟨q, hq⟩ := hT
          exact ⟨⟨q, hq⟩, by simp only [Finset.mem_attach]⟩)
    let s := toSurviving q
    let t := P.endingRelationSupportFactor r hr p s
    let g := P.endingRelationComplement r hr p s
    have ht : t.1 = g.comp s.1 :=
      P.endingRelationSupportFactor_path_eq r hr p s
    have hpathMem (q' : Quiver.Path y z) (hq'T : q' ∈ T) :
        pathMap R q' ≫ pathMap R g ∈
          Submodule.span k {pathMap R p.1} := by
      let qa : {q // q ∈ T} := ⟨q', hq'T⟩
      let s' := toSurviving qa
      let t' := P.endingRelationSupportFactor r hr p s'
      let a' := P.endingRelationComplement r hr p s'
      have ht' : t'.1 = a'.comp s'.1 :=
        P.endingRelationSupportFactor_path_eq r hr p s'
      by_cases hcomp : pathMap R q' ≫ pathMap R g = 0
      · rw [hcomp]
        exact Submodule.zero_mem _
      · let sg : SurvivingPath R x z :=
          ⟨g.comp q', by
            rw [← pathMap_comp]
            exact hcomp⟩
        obtain ⟨u, b, hu⟩ :=
          P.survivingPath_ending_relationSupport_factor r hr p sg
        have hu' : u.1 = (b.comp g).comp q' := by
          calc
            u.1 = b.comp sg.1 := hu
            _ = b.comp (g.comp q') := rfl
            _ = (b.comp g).comp q' :=
              (Quiver.Path.comp_assoc _ _ _).symm
        have ht'u : t' = u :=
          P.relationSurvivingSupport_eq_of_common_suffix r hr t' u q'
            (hpositive q' hq'T) a' (b.comp g) (by simpa [s'] using ht') hu'
        have ha' : a' = b.comp g := by
          apply Quiver.Path.comp_injective_left q'
          calc
            a'.comp q' = t'.1 := (by simpa [s'] using ht'.symm)
            _ = u.1 := congrArg Subtype.val ht'u
            _ = (b.comp g).comp q' := hu'
        have hscore : a'.length ≤ g.length := by
          have hmax := hqMax qa (by simp only [Finset.mem_attach])
          exact hmax
        have hbLength : b.length = 0 := by
          have hlength := congrArg Quiver.Path.length ha'
          simp only [Quiver.Path.length_comp] at hlength
          omega
        have hbNil : b = Quiver.Path.nil := b.eq_nil_of_length_zero hbLength
        have huPath : u.1 = g.comp q' := by
          simpa only [sg, hbNil, Quiver.Path.nil_comp] using hu
        have huLine : pathMap R u.1 ∈
            Submodule.span k {pathMap R p.1} := by
          by_cases hup : u = p
          · rw [hup]
            exact Submodule.subset_span (Set.mem_singleton _)
          · obtain ⟨c, _, hc⟩ :=
              P.relationSurvivingSupport_pathMap_eq_smul
                r hr u p (Ne.symm hup)
            rw [hc]
            exact Submodule.smul_mem _ c
              (Submodule.subset_span (Set.mem_singleton _))
        rw [pathMap_comp R g q', ← huPath]
        exact huLine
    have hfSum : f = ∑ q ∈ coeff.support,
        coeff q • pathMap R q := by
      rw [← hliftMap]
      exact quotientMap_eq_pathMap_sum R lift
    refine ⟨pathMap R g, ?_, ?_⟩
    · rw [hfSum]
      change (∑ q ∈ coeff.support,
          coeff q • pathMap P.toPresentation.relations q) ≫
        pathMap P.toPresentation.relations g ∈
          Submodule.span k {pathMap P.toPresentation.relations p.1}
      rw [Preadditive.sum_comp]
      apply Submodule.sum_mem
      intro q' hq'Support
      rw [CategoryTheory.Linear.smul_comp]
      apply Submodule.smul_mem
      by_cases hq'Map : pathMap R q' = 0
      · rw [hq'Map, CategoryTheory.Limits.zero_comp]
        exact Submodule.zero_mem _
      · exact hpathMem q'
          (Finset.mem_filter.mpr ⟨hq'Support, hq'Map⟩)
    · by_cases hgLength : g.length = 0
      · have hxy : x = y := g.eq_of_length_zero hgLength
        subst y
        have hgNil : g = Quiver.Path.nil := g.eq_nil_of_length_zero hgLength
        rw [hgNil]
        change f ≫ quotient.map
          (LinearPathCategory.pathHom Quiver.Path.nil) ≠ 0
        rw [LinearPathCategory.pathHom_nil, quotient.map_id,
          Category.comp_id]
        exact hf
      · intro hzero
        have hextension : P.leftPathExtensionLinearMap g lift = 0 := by
          change quotient.map lift ≫ pathMap R g = 0
          rw [hliftMap]
          exact hzero
        have hfull : pathMap R s.1 ≫ pathMap R g ≠ 0 := by
          rw [pathMap_comp R g s.1, ← ht]
          exact t.2.2
        have hcoeffZero :=
          P.homPathCoefficient_eq_zero_of_leftPathExtension_eq_zero
            g hgLength lift hextension s.1 hfull
        have hqSupport : q.1 ∈ coeff.support :=
          (Finset.mem_filter.mp q.2).1
        exact (Finsupp.mem_support_iff.mp hqSupport) hcoeffZero
  by_cases hyz : y = z
  · subst y
    by_cases hnil : coeff (Quiver.Path.nil : Quiver.Path z z) ≠ 0
    · let v : obj R z ⟶ obj R x := pathMap R p.1
      let hpHull : LinearPathCategory.pathHom p.1 ∈
          pathSupportHull R
            (LinearPathCategory.obj k Q z)
            (LinearPathCategory.obj k Q x) :=
        ⟨p.1, rfl, r, hr, p.2.1⟩
      have hfSum : f = ∑ q ∈ coeff.support,
          coeff q • pathMap R q := by
        rw [← hliftMap]
        exact quotientMap_eq_pathMap_sum R lift
      change f = ∑ q ∈ coeff.support,
        coeff q • pathMap P.toPresentation.relations q at hfSum
      have hcomp : f ≫ v = coeff Quiver.Path.nil • v := by
        rw [hfSum]
        rw [Preadditive.sum_comp,
          Finset.sum_eq_single (Quiver.Path.nil : Quiver.Path z z)]
        · rw [CategoryTheory.Linear.smul_comp]
          change coeff Quiver.Path.nil •
            (quotient.map (LinearPathCategory.pathHom Quiver.Path.nil) ≫ v) = _
          rw [LinearPathCategory.pathHom_nil, quotient.map_id,
            Category.id_comp]
        · intro q hq hqNil
          have hqLength : q.length ≠ 0 := by
            intro hzero
            exact hqNil (q.eq_nil_of_length_zero hzero)
          have hzero := P.pathMap_comp_pathSupportHullGenerator_eq_zero
            hpHull q hqLength
          rw [CategoryTheory.Linear.smul_comp]
          change pathMap P.toPresentation.relations q ≫ v = 0 at hzero
          rw [hzero, smul_zero]
        · intro hnot
          exact False.elim (hnot (Finsupp.mem_support_iff.mpr hnil))
      refine ⟨v, ?_, ?_⟩
      · rw [hcomp]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_singleton _))
      · rw [hcomp]
        apply smul_ne_zero hnil
        exact p.2.2
    · apply hmain
      intro q hqT hqLength
      have hqNil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hqLength
      subst q
      exact hnil (Finsupp.mem_support_iff.mp
        (Finset.mem_filter.mp hqT).1)
  · apply hmain
    intro q _ hqLength
    exact hyz (q.eq_of_length_zero hqLength)

/-- Every nonzero element of the initial representable can be composed into
the nonzero endpoint line of the paired relation. -/
theorem exists_left_comp_mem_relationEndpointLine_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    {y : Q} (g : obj P.toPresentation.relations y ⟶
      obj P.toPresentation.relations x) (hg : g ≠ 0) :
    ∃ f : obj P.toPresentation.relations z ⟶
        obj P.toPresentation.relations y,
      f ≫ g ∈ Submodule.span k
          {pathMap P.toPresentation.relations p.1} ∧
        f ≫ g ≠ 0 := by
  classical
  let R := P.toPresentation.relations
  let quotient :=
    LinearPathCategory.HomogeneousQuotient.quotientFunctor R
  obtain ⟨lift, hlift⟩ :=
    LinearPathCategory.HomogeneousQuotient.quotientHom_surjective R
      (LinearPathCategory.obj k Q y)
      (LinearPathCategory.obj k Q x) g
  have hliftMap : quotient.map lift = g := by
    change (LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap R
      (LinearPathCategory.obj k Q y)
      (LinearPathCategory.obj k Q x)) lift = g
    exact hlift
  let coeff : Quiver.Path x y →₀ k :=
    LinearPathCategory.homPathLinearEquiv
      (LinearPathCategory.obj k Q y)
      (LinearPathCategory.obj k Q x) lift
  have hliftNe : quotient.map lift ≠ 0 := by
    rw [hliftMap]
    exact hg
  let T : Finset (Quiver.Path x y) :=
    coeff.support.filter fun q ↦ pathMap R q ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨q, hqCoeff, hqMap⟩ :=
      exists_path_coefficient_ne_zero_of_quotientMap_ne_zero R lift hliftNe
    refine ⟨q, ?_⟩
    simp only [T, Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨hqCoeff, hqMap⟩
  let toSurviving : {q // q ∈ T} → SurvivingPath R x y := fun q ↦
    ⟨q.1, (Finset.mem_filter.mp q.2).2⟩
  let score : {q // q ∈ T} → ℕ := fun q ↦
    (P.startingRelationComplement r hr p (toSurviving q)).length
  have hmain (hpositive : ∀ q, q ∈ T → q.length ≠ 0) :
      ∃ f : obj R z ⟶ obj R y,
        f ≫ g ∈ Submodule.span k {pathMap R p.1} ∧ f ≫ g ≠ 0 := by
    obtain ⟨q, _, hqMax⟩ :=
      Finset.exists_max_image T.attach score
        (by
          obtain ⟨q, hq⟩ := hT
          exact ⟨⟨q, hq⟩, by simp only [Finset.mem_attach]⟩)
    let s := toSurviving q
    let t := P.startingRelationSupportFactor r hr p s
    let h := P.startingRelationComplement r hr p s
    have ht : t.1 = s.1.comp h :=
      P.startingRelationSupportFactor_path_eq r hr p s
    have hpathMem (q' : Quiver.Path x y) (hq'T : q' ∈ T) :
        pathMap R h ≫ pathMap R q' ∈
          Submodule.span k {pathMap R p.1} := by
      let qa : {q // q ∈ T} := ⟨q', hq'T⟩
      let s' := toSurviving qa
      let t' := P.startingRelationSupportFactor r hr p s'
      let a' := P.startingRelationComplement r hr p s'
      have ht' : t'.1 = s'.1.comp a' :=
        P.startingRelationSupportFactor_path_eq r hr p s'
      by_cases hcomp : pathMap R h ≫ pathMap R q' = 0
      · rw [hcomp]
        exact Submodule.zero_mem _
      · let sg : SurvivingPath R x z :=
          ⟨q'.comp h, by
            rw [← pathMap_comp]
            exact hcomp⟩
        obtain ⟨u, b, hu⟩ :=
          P.survivingPath_starting_relationSupport_factor r hr p sg
        have hu' : u.1 = q'.comp (h.comp b) := by
          calc
            u.1 = sg.1.comp b := hu
            _ = (q'.comp h).comp b := rfl
            _ = q'.comp (h.comp b) := Quiver.Path.comp_assoc _ _ _
        have ht'u : t' = u :=
          P.relationSurvivingSupport_eq_of_common_prefix r hr t' u q'
            (hpositive q' hq'T) a' (h.comp b)
              (by simpa [s'] using ht') hu'
        have ha' : a' = h.comp b := by
          apply Quiver.Path.comp_injective_right q'
          calc
            q'.comp a' = t'.1 := (by simpa [s'] using ht'.symm)
            _ = u.1 := congrArg Subtype.val ht'u
            _ = q'.comp (h.comp b) := hu'
        have hscore : a'.length ≤ h.length := by
          have hmax := hqMax qa (by simp only [Finset.mem_attach])
          exact hmax
        have hbLength : b.length = 0 := by
          have hlength := congrArg Quiver.Path.length ha'
          simp only [Quiver.Path.length_comp] at hlength
          omega
        have hbNil : b = Quiver.Path.nil := b.eq_nil_of_length_zero hbLength
        have huPath : u.1 = q'.comp h := by
          simpa only [sg, hbNil, Quiver.Path.comp_nil] using hu
        have huLine : pathMap R u.1 ∈
            Submodule.span k {pathMap R p.1} := by
          by_cases hup : u = p
          · rw [hup]
            exact Submodule.subset_span (Set.mem_singleton _)
          · obtain ⟨c, _, hc⟩ :=
              P.relationSurvivingSupport_pathMap_eq_smul
                r hr u p (Ne.symm hup)
            rw [hc]
            exact Submodule.smul_mem _ c
              (Submodule.subset_span (Set.mem_singleton _))
        rw [pathMap_comp R q' h, ← huPath]
        exact huLine
    have hgSum : g = ∑ q ∈ coeff.support,
        coeff q • pathMap R q := by
      rw [← hliftMap]
      exact quotientMap_eq_pathMap_sum R lift
    refine ⟨pathMap R h, ?_, ?_⟩
    · rw [hgSum]
      change pathMap P.toPresentation.relations h ≫
          (∑ q ∈ coeff.support,
            coeff q • pathMap P.toPresentation.relations q) ∈
        Submodule.span k {pathMap P.toPresentation.relations p.1}
      rw [Preadditive.comp_sum]
      apply Submodule.sum_mem
      intro q' hq'Support
      rw [CategoryTheory.Linear.comp_smul]
      apply Submodule.smul_mem
      by_cases hq'Map : pathMap R q' = 0
      · rw [hq'Map, CategoryTheory.Limits.comp_zero]
        exact Submodule.zero_mem _
      · exact hpathMem q'
          (Finset.mem_filter.mpr ⟨hq'Support, hq'Map⟩)
    · by_cases hhLength : h.length = 0
      · have hyz : y = z := h.eq_of_length_zero hhLength
        subst y
        have hhNil : h = Quiver.Path.nil := h.eq_nil_of_length_zero hhLength
        rw [hhNil]
        change quotient.map
          (LinearPathCategory.pathHom Quiver.Path.nil) ≫ g ≠ 0
        rw [LinearPathCategory.pathHom_nil, quotient.map_id,
          Category.id_comp]
        exact hg
      · intro hzero
        have hextension : P.rightPathExtensionLinearMap h lift = 0 := by
          change pathMap R h ≫ quotient.map lift = 0
          rw [hliftMap]
          exact hzero
        have hfull : pathMap R h ≫ pathMap R s.1 ≠ 0 := by
          rw [pathMap_comp R s.1 h, ← ht]
          exact t.2.2
        have hcoeffZero :=
          P.homPathCoefficient_eq_zero_of_rightPathExtension_eq_zero
            h hhLength lift hextension s.1 hfull
        have hqSupport : q.1 ∈ coeff.support :=
          (Finset.mem_filter.mp q.2).1
        exact (Finsupp.mem_support_iff.mp hqSupport) hcoeffZero
  by_cases hyx : y = x
  · subst y
    by_cases hnil : coeff (Quiver.Path.nil : Quiver.Path x x) ≠ 0
    · let v : obj R z ⟶ obj R x := pathMap R p.1
      let hpHull : LinearPathCategory.pathHom p.1 ∈
          pathSupportHull R
            (LinearPathCategory.obj k Q z)
            (LinearPathCategory.obj k Q x) :=
        ⟨p.1, rfl, r, hr, p.2.1⟩
      have hgSum : g = ∑ q ∈ coeff.support,
          coeff q • pathMap R q := by
        rw [← hliftMap]
        exact quotientMap_eq_pathMap_sum R lift
      change g = ∑ q ∈ coeff.support,
        coeff q • pathMap P.toPresentation.relations q at hgSum
      have hcomp : v ≫ g = coeff Quiver.Path.nil • v := by
        rw [hgSum]
        rw [Preadditive.comp_sum,
          Finset.sum_eq_single (Quiver.Path.nil : Quiver.Path x x)]
        · rw [CategoryTheory.Linear.comp_smul]
          change coeff Quiver.Path.nil •
            (v ≫ quotient.map
              (LinearPathCategory.pathHom Quiver.Path.nil)) = _
          rw [LinearPathCategory.pathHom_nil, quotient.map_id,
            Category.comp_id]
        · intro q hq hqNil
          have hqLength : q.length ≠ 0 := by
            intro hzero
            exact hqNil (q.eq_nil_of_length_zero hzero)
          have hzero := P.pathSupportHullGenerator_comp_pathMap_eq_zero
            hpHull q hqLength
          rw [CategoryTheory.Linear.comp_smul]
          change v ≫ pathMap P.toPresentation.relations q = 0 at hzero
          rw [hzero, smul_zero]
        · intro hnot
          exact False.elim (hnot (Finsupp.mem_support_iff.mpr hnil))
      refine ⟨v, ?_, ?_⟩
      · rw [hcomp]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_singleton _))
      · rw [hcomp]
        apply smul_ne_zero hnil
        exact p.2.2
    · apply hmain
      intro q hqT hqLength
      have hqNil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hqLength
      subst q
      exact hnil (Finsupp.mem_support_iff.mp
        (Finset.mem_filter.mp hqT).1)
  · apply hmain
    intro q _ hqLength
    exact hyx (q.eq_of_length_zero hqLength).symm

/-- The normalized endpoint functional is nonzero on every nonzero element
of the relation endpoint line. -/
theorem relationSurvivingSupportFunctional_ne_zero_of_mem_span
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    (h : obj P.toPresentation.relations z ⟶
      obj P.toPresentation.relations x)
    (hmem : h ∈ Submodule.span k
      {pathMap P.toPresentation.relations p.1})
    (hne : h ≠ 0) :
    P.relationSurvivingSupportFunctional r hr p h ≠ 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  intro hzero
  rw [map_smul, P.relationSurvivingSupportFunctional_pathMap r hr p,
    smul_eq_mul, mul_one] at hzero
  subst c
  exact hne (zero_smul k _)

/-- The transpose of the relation composition pairing at one displayed
vertex. -/
noncomputable def relationSurvivingSupportTransposeLinearMap
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    (Y : Category P.toPresentation.relations) :
    (Y ⟶ obj P.toPresentation.relations x) →ₗ[k]
      Module.Dual k (obj P.toPresentation.relations z ⟶ Y) where
  toFun g :=
    { toFun := fun f ↦
        P.relationSurvivingSupportFunctional r hr p (f ≫ g)
      map_add' := fun f l ↦ by
        rw [Preadditive.add_comp, map_add]
      map_smul' := fun c f ↦ by
        rw [CategoryTheory.Linear.smul_comp, map_smul]
        rfl }
  map_add' g h := by
    apply LinearMap.ext
    intro f
    simp only [Preadditive.comp_add, map_add, LinearMap.add_apply]
    rfl
  map_smul' c g := by
    apply LinearMap.ext
    intro f
    simp only [CategoryTheory.Linear.comp_smul, map_smul,
      LinearMap.smul_apply]
    rfl

theorem relationSurvivingSupportTransposeLinearMap_apply_apply
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r)
    (Y : Category P.toPresentation.relations)
    (g : Y ⟶ obj P.toPresentation.relations x)
    (f : obj P.toPresentation.relations z ⟶ Y) :
    P.relationSurvivingSupportTransposeLinearMap r hr p Y g f =
      P.relationSurvivingSupportFunctional r hr p (f ≫ g) :=
  rfl

/-- The composition pairing induced by a surviving relation arm is perfect. -/
theorem hasPerfectRelationPairing
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    P.HasPerfectRelationPairing r hr p := by
  rintro ⟨y⟩
  let L := ((P.relationSurvivingSupportNakayamaHom r hr p).hom.hom.app
    (obj P.toPresentation.relations y)).hom
  let T := P.relationSurvivingSupportTransposeLinearMap r hr p
    (obj P.toPresentation.relations y)
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro f hfzero
    by_contra hf
    obtain ⟨g, hmem, hne⟩ :=
      P.exists_comp_mem_relationEndpointLine_ne_zero r hr p f hf
    have hfunctional :=
      P.relationSurvivingSupportFunctional_ne_zero_of_mem_span
        r hr p (f ≫ g) hmem hne
    apply hfunctional
    rw [← P.relationSurvivingSupportNakayamaHom_app_apply_apply
      r hr p (obj P.toPresentation.relations y) f g]
    change (show Module.Dual k
        (obj P.toPresentation.relations y ⟶
          obj P.toPresentation.relations x) from
      (P.relationSurvivingSupportNakayamaHom r hr p).hom.hom.app
        (obj P.toPresentation.relations y) f) = 0 at hfzero
    simpa using DFunLike.congr_fun hfzero g
  have hT : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro g hgzero
    by_contra hg
    obtain ⟨f, hmem, hne⟩ :=
      P.exists_left_comp_mem_relationEndpointLine_ne_zero r hr p g hg
    have hfunctional :=
      P.relationSurvivingSupportFunctional_ne_zero_of_mem_span
        r hr p (f ≫ g) hmem hne
    apply hfunctional
    rw [← P.relationSurvivingSupportTransposeLinearMap_apply_apply
      r hr p (obj P.toPresentation.relations y) g f]
    simpa using DFunLike.congr_fun hgzero f
  letI : FiniteDimensional k
      (obj P.toPresentation.relations z ⟶
        obj P.toPresentation.relations y) :=
    quotientHom_finiteDimensional P.toPresentation.admissible z y
  letI : FiniteDimensional k
      (obj P.toPresentation.relations y ⟶
        obj P.toPresentation.relations x) :=
    quotientHom_finiteDimensional P.toPresentation.admissible y x
  have hle : Module.finrank k
      ↑((P.relationSourceRepresentable z).obj.obj.obj
        (obj P.toPresentation.relations y)) ≤
      Module.finrank k
        ↑((P.relationTargetDualCorepresentable x).obj.obj.obj
          (obj P.toPresentation.relations y)) :=
    LinearMap.finrank_le_finrank_of_injective hL
  have hgeExplicit : Module.finrank k
      (obj P.toPresentation.relations y ⟶
        obj P.toPresentation.relations x) ≤
      Module.finrank k
        (obj P.toPresentation.relations z ⟶
          obj P.toPresentation.relations y) := by
    have h := LinearMap.finrank_le_finrank_of_injective hT
    change Module.finrank k
        (obj P.toPresentation.relations y ⟶
          obj P.toPresentation.relations x) ≤
      Module.finrank k (Module.Dual k
        (obj P.toPresentation.relations z ⟶
          obj P.toPresentation.relations y)) at h
    simpa only [Subspace.dual_finrank_eq] using h
  have hge : Module.finrank k
      ↑((P.relationTargetDualCorepresentable x).obj.obj.obj
        (obj P.toPresentation.relations y)) ≤
      Module.finrank k
        ↑((P.relationSourceRepresentable z).obj.obj.obj
          (obj P.toPresentation.relations y)) := by
    change Module.finrank k (Module.Dual k
        (obj P.toPresentation.relations y ⟶
          obj P.toPresentation.relations x)) ≤
      Module.finrank k
        (obj P.toPresentation.relations z ⟶
          obj P.toPresentation.relations y)
    simpa only [Subspace.dual_finrank_eq] using hgeExplicit
  refine ⟨hL, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Nat.le_antisymm hle hge) (f := L)).mp hL

/-- The relation-induced Nakayama map is unconditionally an isomorphism for
a special-biserial presentation. -/
theorem relationSurvivingSupportNakayamaHom_isIso_of_specialBiserial
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    IsIso (P.relationSurvivingSupportNakayamaHom r hr p) :=
  P.relationSurvivingSupportNakayamaHom_isIso r hr p
    (P.hasPerfectRelationPairing r hr p)

/-- The representable ending at a surviving special-biserial relation arm is
injective. -/
theorem relationSourceRepresentable_injective
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    Injective (P.relationSourceRepresentable z) :=
  P.relationSourceRepresentable_injective_of_perfect r hr p
    (P.hasPerfectRelationPairing r hr p)

end MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation
