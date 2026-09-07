import MagnitudeConjecture.Algebra.BoundQuiverAdmissibleBasic
import MagnitudeConjecture.Algebra.BoundQuiverPathGenerated
import MagnitudeConjecture.Algebra.BoundQuiverRelationQuotient
import MagnitudeConjecture.Algebra.StringPathCombinatorics

/-!
# Linear independence along a special-biserial branch

The unique-continuation condition orders the surviving paths beginning with
one fixed arrow by length.  Even when the presentation is not monomial, the
images of those paths with a fixed endpoint are linearly independent.  The
key point is that a relation with a shortest nonzero coefficient factors as
a nonzero scalar plus a positive-tail endomorphism; admissibility makes the
positive part nilpotent, hence the factor is invertible.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace Module.Basis

universe u₁ u₂ u₃ u₄

/-- If the nonzero images of basis vectors are linearly independent, a
vector killed by the linear map has zero coefficient at every basis vector
whose image is nonzero. -/
theorem repr_eq_zero_of_map_eq_zero_of_image_ne_zero
    {k : Type u₁} [Field k]
    {I : Type u₂} {V : Type u₃} {W : Type u₄}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (b : Module.Basis I k V) (f : V →ₗ[k] W)
    (hli : LinearIndependent k
      (fun i : {i : I // f (b i) ≠ 0} ↦ f (b i.1)))
    (v : V) (hv : f v = 0) (i : I) (hi : f (b i) ≠ 0) :
    b.repr v i = 0 := by
  classical
  let survives : I → Prop := fun j ↦ f (b j) ≠ 0
  let l : I →₀ k := (b.repr v).filter survives
  let n : I →₀ k := (b.repr v).filter fun j ↦ ¬ survives j
  have hnzero : Finsupp.linearCombination k (fun j ↦ f (b j)) n = 0 := by
    rw [Finsupp.linearCombination_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hjData := Finset.mem_filter.mp
      (show j ∈ (b.repr v).support.filter (fun r ↦ ¬ survives r) by
        exact hj)
    have hfj : f (b j) = 0 := not_ne_iff.mp hjData.2
    change n j • f (b j) = 0
    rw [hfj, smul_zero]
  have hsplit : l + n = b.repr v := by
    exact Finsupp.filter_add_filter_not (b.repr v) survives
  have hlcomb :
      Finsupp.linearCombination k (fun j ↦ f (b j)) l = 0 := by
    have hfull :
        Finsupp.linearCombination k (fun j ↦ f (b j)) (b.repr v) =
          f v := by
      calc
        Finsupp.linearCombination k (fun j ↦ f (b j)) (b.repr v) =
            f (Finsupp.linearCombination k (fun j ↦ b j) (b.repr v)) := by
          rw [Finsupp.linearCombination_apply,
            Finsupp.linearCombination_apply, map_finsuppSum]
          simp only [map_smul]
        _ = f v := by rw [b.linearCombination_repr]
    have hsplitComb := congrArg
      (Finsupp.linearCombination k (fun j ↦ f (b j))) hsplit
    rw [map_add, hnzero, add_zero, hfull, hv] at hsplitComb
    exact hsplitComb
  let l' : {j : I // survives j} →₀ k :=
    Finsupp.subtypeDomain survives l
  have hlsupport : ∀ j ∈ l.support, survives j := by
    intro j hj
    exact (Finset.mem_filter.mp
      (show j ∈ (b.repr v).support.filter survives by exact hj)).2
  have hl'comb :
      Finsupp.linearCombination k
          (fun j : {j : I // survives j} ↦ f (b j.1)) l' = 0 := by
    rw [Finsupp.linearCombination_apply]
    change
      (Finsupp.subtypeDomain survives l).sum
          (fun j c ↦ c • f (b j.1)) = 0
    have hsub := Finsupp.sum_subtypeDomain_index
      (v := l) (h := fun j c ↦ c • f (b j)) hlsupport
    rw [Finsupp.linearCombination_apply] at hlcomb
    exact hsub.trans hlcomb
  have hl'zero : l' = 0 :=
    (linearIndependent_iff.mp hli) l' hl'comb
  have hvalue := DFunLike.congr_fun hl'zero (⟨i, hi⟩ : Subtype survives)
  change l i = 0 at hvalue
  simpa only [l, Finsupp.filter_apply, survives, if_pos hi] using hvalue

end Module.Basis

namespace MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- The quotient morphism represented by a surviving continuation followed
by its fixed initial arrow. -/
def rightBranchPathMap
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (q : P.RightContinuationAt a z) :
    obj P.toPresentation.relations z ⟶
      obj P.toPresentation.relations x :=
  pathMap P.toPresentation.relations q.1 ≫
    arrowMap P.toPresentation.relations a

@[simp]
theorem rightBranchPathMap_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (q : P.RightContinuationAt a z) :
    P.rightBranchPathMap a z q ≠ 0 :=
  q.2

/-- Factoring a continuation path factors the corresponding branch
morphism on the left. -/
theorem rightBranchPathMap_eq_factor_comp
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p q : P.RightContinuationAt a z)
    (r : Quiver.Path z z) (hr : q.1 = p.1.comp r) :
    P.rightBranchPathMap a z q =
      pathMap P.toPresentation.relations r ≫
        P.rightBranchPathMap a z p := by
  simp only [rightBranchPathMap, hr]
  rw [← pathMap_comp]
  simp only [Category.assoc]

/-- A positive-length loop maps into the positive part of the admissible
path filtration. -/
theorem pathMap_mem_quotientHomLengthTail_one_of_length_ne_zero
    (P : SpecialBiserialPresentation k A Q) (z : Q)
    (r : Quiver.Path z z) (hr : r.length ≠ 0) :
    pathMap P.toPresentation.relations r ∈
      P.toPresentation.admissible.quotientHomLengthTail
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q z) 1 := by
  refine ⟨LinearPathCategory.pathHom r, ?_, rfl⟩
  exact (LinearPathCategory.pathHom_mem_lengthTail_iff r 1).2
    (Nat.one_le_iff_ne_zero.2 hr)

/-- Distinct surviving paths in one fixed special-biserial branch remain
linearly independent in the original (possibly nonmonomial) quotient. -/
theorem rightBranchPathMap_linearIndependent
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    LinearIndependent k (P.rightBranchPathMap a z) := by
  classical
  let R := P.toPresentation.relations
  let Z := LinearPathCategory.obj k Q z
  let α := P.RightContinuationAt a z
  letI : Finite α := P.rightContinuationAt_finite a z
  letI : Fintype α := Fintype.ofFinite α
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum q
  by_contra hcq
  let T : Finset α := Finset.univ.filter fun p ↦ c p ≠ 0
  have hT : T.Nonempty := by
    refine ⟨q, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcq
  obtain ⟨p, hpT, hpmin⟩ :=
    Finset.exists_min_image T (fun r ↦ r.1.length) hT
  have hcp : c p ≠ 0 := by
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hpT
  have hmin : ∀ r : α, r ∈ T → p.1.length ≤ r.1.length := by
    intro r hr
    exact hpmin r hr
  let factor (r : α) : Quiver.Path z z :=
    if hr : r ∈ T then
      Classical.choose
        (P.rightContinuationAt_factor_of_length_le a z p r (hmin r hr))
    else Quiver.Path.nil
  have hfactor : ∀ r : α, r ∈ T →
      r.1 = p.1.comp (factor r) := by
    intro r hr
    rw [show factor r = Classical.choose
        (P.rightContinuationAt_factor_of_length_le a z p r
          (hmin r hr)) by simp [factor, hr]]
    exact Classical.choose_spec
      (P.rightContinuationAt_factor_of_length_le a z p r (hmin r hr))
  have hfactorPositive : ∀ r : α, r ∈ T.erase p →
      (factor r).length ≠ 0 := by
    intro r hr
    have hrData := Finset.mem_erase.mp hr
    have hlengthNe : p.1.length ≠ r.1.length := by
      intro hlength
      apply hrData.1
      exact (P.rightContinuationAtLengthEmbedding a z).injective
        hlength.symm
    have hlengthLt : p.1.length < r.1.length :=
      lt_of_le_of_ne (hmin r hrData.2) hlengthNe
    have hlength := congrArg Quiver.Path.length (hfactor r hrData.2)
    simp only [Quiver.Path.length_comp] at hlength
    omega
  let t : End (obj R z) := End.of
    (∑ r ∈ T.erase p,
      c r • pathMap R (factor r))
  have htPositive : End.asHom t ∈
      P.toPresentation.admissible.quotientHomLengthTail Z Z 1 := by
    dsimp only [t]
    apply Submodule.sum_mem
    intro r hr
    apply Submodule.smul_mem
    exact P.pathMap_mem_quotientHomLengthTail_one_of_length_ne_zero
      z (factor r) (hfactorPositive r hr)
  have htNilpotent : IsNilpotent t :=
    P.toPresentation.admissible.isNilpotent_of_mem_quotientHomLengthTail_one
      Z t htPositive
  have hscalarUnit : IsUnit (c p • (1 : End (obj R z))) := by
    rw [Algebra.smul_def]
    exact (isUnit_iff_ne_zero.mpr hcp).map
      (algebraMap k (End (obj R z)))
  have hcommute : Commute t (c p • (1 : End (obj R z))) := by
    rw [Algebra.smul_def]
    exact (Algebra.commutes (c p) t).symm
  have hunit : IsUnit (c p • (1 : End (obj R z)) + t) := by
    exact htNilpotent.isUnit_add_left_of_commute hscalarUnit hcommute
  have hsumT :
      ∑ r ∈ T, c r • P.rightBranchPathMap a z r = 0 := by
    calc
      ∑ r ∈ T, c r • P.rightBranchPathMap a z r =
          ∑ r ∈ Finset.univ, c r • P.rightBranchPathMap a z r := by
        apply Finset.sum_subset (Finset.subset_univ T)
        intro r _ hrT
        have hcr : c r = 0 := by
          by_contra hcr
          exact hrT (by simp [T, hcr])
        rw [hcr, zero_smul]
      _ = 0 := by simpa using hsum
  have htailFactor :
      (∑ r ∈ T.erase p,
          c r • P.rightBranchPathMap a z r) =
        End.asHom t ≫ P.rightBranchPathMap a z p := by
    dsimp only [t]
    simp only [Preadditive.sum_comp, Linear.smul_comp]
    apply Finset.sum_congr rfl
    intro r hr
    rw [P.rightBranchPathMap_eq_factor_comp a z p r
      (factor r) (hfactor r (Finset.mem_of_mem_erase hr))]
  have htotalFactor :
      (∑ r ∈ T, c r • P.rightBranchPathMap a z r) =
        End.asHom (c p • (1 : End (obj R z)) + t) ≫
          P.rightBranchPathMap a z p := by
    rw [← Finset.sum_erase_add T _ hpT, htailFactor]
    change
      End.asHom t ≫ P.rightBranchPathMap a z p +
          c p • P.rightBranchPathMap a z p =
        (c p • 𝟙 (obj R z) + End.asHom t) ≫
          P.rightBranchPathMap a z p
    rw [Preadditive.add_comp, Linear.smul_comp, Category.id_comp]
    exact add_comm _ _
  have hzero :
      End.asHom (c p • (1 : End (obj R z)) + t) ≫
          P.rightBranchPathMap a z p = 0 := by
    rw [← htotalFactor]
    exact hsumT
  letI : IsIso
      (End.asHom (c p • (1 : End (obj R z)) + t)) :=
    (CategoryTheory.isUnit_iff_isIso _).1 hunit
  have hpzero : P.rightBranchPathMap a z p = 0 := by
    apply (cancel_epi
      (End.asHom (c p • (1 : End (obj R z)) + t))).1
    simpa only [CategoryTheory.Limits.comp_zero] using hzero
  exact P.rightBranchPathMap_ne_zero a z p hpzero

/-- The quotient morphism represented by a fixed final arrow preceded by a
surviving left continuation. -/
def leftBranchPathMap
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p : P.LeftContinuationAt a z) :
    obj P.toPresentation.relations y ⟶
      obj P.toPresentation.relations z :=
  arrowMap P.toPresentation.relations a ≫
    pathMap P.toPresentation.relations p.1

@[simp]
theorem leftBranchPathMap_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p : P.LeftContinuationAt a z) :
    P.leftBranchPathMap a z p ≠ 0 :=
  p.2

/-- Factoring a left continuation path factors the corresponding branch
morphism on the right. -/
theorem leftBranchPathMap_eq_comp_factor
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q)
    (p q : P.LeftContinuationAt a z)
    (r : Quiver.Path z z) (hr : q.1 = r.comp p.1) :
    P.leftBranchPathMap a z q =
      P.leftBranchPathMap a z p ≫
        pathMap P.toPresentation.relations r := by
  simp only [leftBranchPathMap, hr]
  rw [← pathMap_comp]
  simp only [Category.assoc]

/-- Distinct surviving paths in one fixed left branch remain linearly
independent in the original (possibly nonmonomial) quotient. -/
theorem leftBranchPathMap_linearIndependent
    (P : SpecialBiserialPresentation k A Q)
    {x y : Q} (a : x ⟶ y) (z : Q) :
    LinearIndependent k (P.leftBranchPathMap a z) := by
  classical
  let R := P.toPresentation.relations
  let Z := LinearPathCategory.obj k Q z
  let α := P.LeftContinuationAt a z
  letI : Finite α := P.leftContinuationAt_finite a z
  letI : Fintype α := Fintype.ofFinite α
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum q
  by_contra hcq
  let T : Finset α := Finset.univ.filter fun p ↦ c p ≠ 0
  have hT : T.Nonempty := by
    refine ⟨q, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcq
  obtain ⟨p, hpT, hpmin⟩ :=
    Finset.exists_min_image T (fun r ↦ r.1.length) hT
  have hcp : c p ≠ 0 := by
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hpT
  have hmin : ∀ r : α, r ∈ T → p.1.length ≤ r.1.length := by
    intro r hr
    exact hpmin r hr
  let factor (r : α) : Quiver.Path z z :=
    if hr : r ∈ T then
      Classical.choose
        (P.leftContinuationAt_factor_of_length_le a z p r (hmin r hr))
    else Quiver.Path.nil
  have hfactor : ∀ r : α, r ∈ T →
      r.1 = (factor r).comp p.1 := by
    intro r hr
    rw [show factor r = Classical.choose
        (P.leftContinuationAt_factor_of_length_le a z p r
          (hmin r hr)) by simp [factor, hr]]
    exact Classical.choose_spec
      (P.leftContinuationAt_factor_of_length_le a z p r (hmin r hr))
  have hfactorPositive : ∀ r : α, r ∈ T.erase p →
      (factor r).length ≠ 0 := by
    intro r hr
    have hrData := Finset.mem_erase.mp hr
    have hlengthNe : p.1.length ≠ r.1.length := by
      intro hlength
      apply hrData.1
      exact (P.leftContinuationAtLengthEmbedding a z).injective
        hlength.symm
    have hlength := congrArg Quiver.Path.length (hfactor r hrData.2)
    simp only [Quiver.Path.length_comp] at hlength
    omega
  let t : End (obj R z) := End.of
    (∑ r ∈ T.erase p,
      c r • pathMap R (factor r))
  have htPositive : End.asHom t ∈
      P.toPresentation.admissible.quotientHomLengthTail Z Z 1 := by
    dsimp only [t]
    apply Submodule.sum_mem
    intro r hr
    apply Submodule.smul_mem
    exact P.pathMap_mem_quotientHomLengthTail_one_of_length_ne_zero
      z (factor r) (hfactorPositive r hr)
  have htNilpotent : IsNilpotent t :=
    P.toPresentation.admissible.isNilpotent_of_mem_quotientHomLengthTail_one
      Z t htPositive
  have hscalarUnit : IsUnit (c p • (1 : End (obj R z))) := by
    rw [Algebra.smul_def]
    exact (isUnit_iff_ne_zero.mpr hcp).map
      (algebraMap k (End (obj R z)))
  have hcommute : Commute t (c p • (1 : End (obj R z))) := by
    rw [Algebra.smul_def]
    exact (Algebra.commutes (c p) t).symm
  have hunit : IsUnit (c p • (1 : End (obj R z)) + t) := by
    exact htNilpotent.isUnit_add_left_of_commute hscalarUnit hcommute
  have hsumT :
      ∑ r ∈ T, c r • P.leftBranchPathMap a z r = 0 := by
    calc
      ∑ r ∈ T, c r • P.leftBranchPathMap a z r =
          ∑ r ∈ Finset.univ, c r • P.leftBranchPathMap a z r := by
        apply Finset.sum_subset (Finset.subset_univ T)
        intro r _ hrT
        have hcr : c r = 0 := by
          by_contra hcr
          exact hrT (by simp [T, hcr])
        rw [hcr, zero_smul]
      _ = 0 := by simpa using hsum
  have htailFactor :
      (∑ r ∈ T.erase p,
          c r • P.leftBranchPathMap a z r) =
        P.leftBranchPathMap a z p ≫ End.asHom t := by
    dsimp only [t]
    simp only [Preadditive.comp_sum, CategoryTheory.Linear.comp_smul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [P.leftBranchPathMap_eq_comp_factor a z p r
      (factor r) (hfactor r (Finset.mem_of_mem_erase hr))]
  have htotalFactor :
      (∑ r ∈ T, c r • P.leftBranchPathMap a z r) =
        P.leftBranchPathMap a z p ≫
          End.asHom (c p • (1 : End (obj R z)) + t) := by
    rw [← Finset.sum_erase_add T _ hpT, htailFactor]
    change
      P.leftBranchPathMap a z p ≫ End.asHom t +
          c p • P.leftBranchPathMap a z p =
        P.leftBranchPathMap a z p ≫
          (c p • 𝟙 (obj R z) + End.asHom t)
    rw [Preadditive.comp_add, CategoryTheory.Linear.comp_smul,
      Category.comp_id]
    exact add_comm _ _
  have hzero :
      P.leftBranchPathMap a z p ≫
          End.asHom (c p • (1 : End (obj R z)) + t) = 0 := by
    rw [← htotalFactor]
    exact hsumT
  letI : IsIso
      (End.asHom (c p • (1 : End (obj R z)) + t)) :=
    (CategoryTheory.isUnit_iff_isIso _).1 hunit
  have hpzero : P.leftBranchPathMap a z p = 0 := by
    apply (cancel_mono
      (End.asHom (c p • (1 : End (obj R z)) + t))).1
    simpa only [CategoryTheory.Limits.zero_comp] using hzero
  exact P.leftBranchPathMap_ne_zero a z p hpzero

/-- Extend a free linear combination of paths on the right by one displayed
arrow and then pass to the relation quotient. -/
def rightExtensionLinearMap
    (P : SpecialBiserialPresentation k A Q)
    {x z w : Q} (b : z ⟶ w) :
    (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x) →ₗ[k]
      (obj P.toPresentation.relations w ⟶
        obj P.toPresentation.relations x) where
  toFun r := arrowMap P.toPresentation.relations b ≫
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map r
  map_add' r s := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_add, Preadditive.comp_add]
  map_smul' c r := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_smul,
      CategoryTheory.Linear.comp_smul]
    rfl

/-- Extend a free linear combination of paths on the left by one displayed
arrow and then pass to the relation quotient. -/
def leftExtensionLinearMap
    (P : SpecialBiserialPresentation k A Q)
    {w x z : Q} (c : w ⟶ x) :
    (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x) →ₗ[k]
      (obj P.toPresentation.relations z ⟶
        obj P.toPresentation.relations w) where
  toFun r :=
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map r ≫
        arrowMap P.toPresentation.relations c
  map_add' r s := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_add, Preadditive.add_comp]
  map_smul' d r := by
    rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
      P.toPresentation.relations).map_smul,
      CategoryTheory.Linear.smul_comp]
    rfl

/-- If right extension of a linear relation vanishes, then every path which
survives that extension has zero coefficient. -/
theorem homPathCoefficient_eq_zero_of_rightExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z w : Q} (b : z ⟶ w)
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : P.rightExtensionLinearMap b r = 0)
    (p : Quiver.Path x z)
    (hp : arrowMap P.toPresentation.relations b ≫
        pathMap P.toPresentation.relations p ≠ 0) :
    LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r p = 0 := by
  let B := LinearPathCategory.homPathBasis
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q x)
  let f :
      (LinearPathCategory.obj k Q z ⟶
          LinearPathCategory.obj k Q x) →ₗ[k]
        (obj P.toPresentation.relations w ⟶
          obj P.toPresentation.relations x) :=
    P.rightExtensionLinearMap (x := x) b
  have hli : LinearIndependent k
      (fun q : {q : Quiver.Path x z // f (B q) ≠ 0} ↦ f (B q.1)) := by
    dsimp only [f, B, rightExtensionLinearMap]
    simp only [LinearPathCategory.homPathBasis_apply]
    change LinearIndependent k (P.leftBranchPathMap b x)
    exact P.leftBranchPathMap_linearIndependent b x
  have hp' : f (B p) ≠ 0 := by
    dsimp only [f, B, rightExtensionLinearMap]
    rw [LinearPathCategory.homPathBasis_apply]
    change arrowMap P.toPresentation.relations b ≫
      pathMap P.toPresentation.relations p ≠ 0
    exact hp
  exact B.repr_eq_zero_of_map_eq_zero_of_image_ne_zero
    f hli r hr p hp'

/-- If left extension of a linear relation vanishes, then every path which
survives that extension has zero coefficient. -/
theorem homPathCoefficient_eq_zero_of_leftExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {w x z : Q} (c : w ⟶ x)
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : P.leftExtensionLinearMap c r = 0)
    (p : Quiver.Path x z)
    (hp : pathMap P.toPresentation.relations p ≫
        arrowMap P.toPresentation.relations c ≠ 0) :
    LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r p = 0 := by
  let B := LinearPathCategory.homPathBasis
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q x)
  let f :
      (LinearPathCategory.obj k Q z ⟶
          LinearPathCategory.obj k Q x) →ₗ[k]
        (obj P.toPresentation.relations z ⟶
          obj P.toPresentation.relations w) :=
    P.leftExtensionLinearMap (z := z) c
  have hli : LinearIndependent k
      (fun q : {q : Quiver.Path x z // f (B q) ≠ 0} ↦ f (B q.1)) := by
    dsimp only [f, B, leftExtensionLinearMap]
    simp only [LinearPathCategory.homPathBasis_apply]
    change LinearIndependent k (P.rightBranchPathMap c z)
    exact P.rightBranchPathMap_linearIndependent c z
  have hp' : f (B p) ≠ 0 := by
    dsimp only [f, B, leftExtensionLinearMap]
    rw [LinearPathCategory.homPathBasis_apply]
    change pathMap P.toPresentation.relations p ≫
      arrowMap P.toPresentation.relations c ≠ 0
    exact hp
  exact B.repr_eq_zero_of_map_eq_zero_of_image_ne_zero
    f hli r hr p hp'

/-- Every surviving path occurring in a displayed special-biserial relation
is right-maximal: adjoining any arrow at its endpoint kills it. -/
theorem relationSupportPath_rightExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z w : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : Quiver.Path x z)
    (hp : LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r p ≠ 0)
    (b : z ⟶ w) :
    arrowMap P.toPresentation.relations b ≫
        pathMap P.toPresentation.relations p = 0 := by
  by_contra hpb
  have hrQuotient :
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map r = 0 := by
    apply (LinearPathCategory.HomogeneousQuotient.relationIdeal
      P.toPresentation.relations).map_eq_zero_iff r |>.2
    exact HomIdeal.relation_mem_linearSpan P.toPresentation.relations hr
  have hrExtension : P.rightExtensionLinearMap b r = 0 := by
    change arrowMap P.toPresentation.relations b ≫
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map r = 0
    rw [hrQuotient, CategoryTheory.Limits.comp_zero]
  exact hp (P.homPathCoefficient_eq_zero_of_rightExtension_eq_zero
    b r hrExtension p hpb)

/-- Every surviving path occurring in a displayed special-biserial relation
is left-maximal: adjoining any arrow at its source kills it. -/
theorem relationSupportPath_leftExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {w x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : Quiver.Path x z)
    (hp : LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r p ≠ 0)
    (c : w ⟶ x) :
    pathMap P.toPresentation.relations p ≫
        arrowMap P.toPresentation.relations c = 0 := by
  by_contra hcp
  have hrQuotient :
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map r = 0 := by
    apply (LinearPathCategory.HomogeneousQuotient.relationIdeal
      P.toPresentation.relations).map_eq_zero_iff r |>.2
    exact HomIdeal.relation_mem_linearSpan P.toPresentation.relations hr
  have hrExtension : P.leftExtensionLinearMap c r = 0 := by
    change
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map r ≫
          arrowMap P.toPresentation.relations c = 0
    rw [hrQuotient, CategoryTheory.Limits.zero_comp]
  exact hp (P.homPathCoefficient_eq_zero_of_leftExtension_eq_zero
    c r hrExtension p hcp)

/-- Every generator of the path-support hull is right-maximal already in
the original special-biserial quotient. -/
theorem pathSupportHullGenerator_rightExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : LinearPathCategory.Category k Q} {f : X ⟶ Y}
    (hf : f ∈ pathSupportHull P.toPresentation.relations X Y)
    {w : Q} (b : LinearPathCategory.vertex X ⟶ w) :
    arrowMap P.toPresentation.relations b ≫
        (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f = 0 := by
  rcases hf with ⟨p, rfl, r, hr, hp⟩
  change arrowMap P.toPresentation.relations b ≫
      pathMap P.toPresentation.relations p = 0
  exact P.relationSupportPath_rightExtension_eq_zero r hr p hp b

/-- Every generator of the path-support hull is left-maximal already in
the original special-biserial quotient. -/
theorem pathSupportHullGenerator_leftExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : LinearPathCategory.Category k Q} {f : X ⟶ Y}
    (hf : f ∈ pathSupportHull P.toPresentation.relations X Y)
    {w : Q} (c : w ⟶ LinearPathCategory.vertex Y) :
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f ≫
        arrowMap P.toPresentation.relations c = 0 := by
  rcases hf with ⟨p, rfl, r, hr, hp⟩
  change pathMap P.toPresentation.relations p ≫
      arrowMap P.toPresentation.relations c = 0
  exact P.relationSupportPath_leftExtension_eq_zero r hr p hp c

/-- A nonempty path on the right of a path-support-hull generator kills
that generator in the original quotient.  Here "right" refers to the
displayed quiver direction; it is precomposition categorically. -/
theorem pathMap_comp_pathSupportHullGenerator_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : LinearPathCategory.Category k Q} {f : X ⟶ Y}
    (hf : f ∈ pathSupportHull P.toPresentation.relations X Y)
    {w : Q}
    (q : Quiver.Path (LinearPathCategory.vertex X) w)
    (hq : q.length ≠ 0) :
    pathMap P.toPresentation.relations q ≫
        (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f = 0 := by
  obtain ⟨c, b, q', rfl, -⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp q).1 hq
  rw [← pathMap_comp]
  change
    (pathMap P.toPresentation.relations q' ≫
        arrowMap P.toPresentation.relations b) ≫
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map f = 0
  rw [Category.assoc,
    P.pathSupportHullGenerator_rightExtension_eq_zero hf b,
    CategoryTheory.Limits.comp_zero]

/-- A nonempty path on the left of a path-support-hull generator kills
that generator in the original quotient.  Here "left" refers to the
displayed quiver direction; it is postcomposition categorically. -/
theorem pathSupportHullGenerator_comp_pathMap_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : LinearPathCategory.Category k Q} {f : X ⟶ Y}
    (hf : f ∈ pathSupportHull P.toPresentation.relations X Y)
    {w : Q}
    (q : Quiver.Path w (LinearPathCategory.vertex Y))
    (hq : q.length ≠ 0) :
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f ≫
        pathMap P.toPresentation.relations q = 0 := by
  change Quiver.Path w Y at q
  obtain ⟨c, q', b, rfl⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons q).1 hq
  rw [← Quiver.Path.comp_toPath_eq_cons, ← pathMap_comp]
  change
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map f ≫
      (arrowMap P.toPresentation.relations b ≫
        pathMap P.toPresentation.relations q') = 0
  rw [← Category.assoc,
    P.pathSupportHullGenerator_leftExtension_eq_zero hf b,
    CategoryTheory.Limits.zero_comp]

/-- A positive free morphism precomposed with a path-support-hull generator
maps to zero in the original quotient. -/
theorem quotientMap_comp_pathSupportHullGenerator_eq_zero_of_mem_lengthTail_one
    (P : SpecialBiserialPresentation k A Q)
    {W X Y : LinearPathCategory.Category k Q}
    (g : W ⟶ X) (hg : g ∈ LinearPathCategory.lengthTail W X 1)
    {f : X ⟶ Y}
    (hf : f ∈ pathSupportHull P.toPresentation.relations X Y) :
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map g ≫
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f = 0 := by
  rw [LinearPathCategory.lengthTail_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨q, hq, rfl⟩
      change pathMap P.toPresentation.relations q ≫
          (LinearPathCategory.HomogeneousQuotient.quotientFunctor
            P.toPresentation.relations).map f = 0
      exact P.pathMap_comp_pathSupportHullGenerator_eq_zero hf q
        (Nat.one_le_iff_ne_zero.mp hq)
  | zero => simp
  | add g h _ _ hg hh =>
      rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map_add, Preadditive.add_comp, hg, hh,
        add_zero]
  | smul c g _ hg =>
      rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map_smul, CategoryTheory.Linear.smul_comp,
        hg, smul_zero]

/-- A path-support-hull generator postcomposed with a positive free
morphism maps to zero in the original quotient. -/
theorem pathSupportHullGenerator_comp_quotientMap_eq_zero_of_mem_lengthTail_one
    (P : SpecialBiserialPresentation k A Q)
    {X Y Z : LinearPathCategory.Category k Q}
    {f : X ⟶ Y}
    (hf : f ∈ pathSupportHull P.toPresentation.relations X Y)
    (g : Y ⟶ Z) (hg : g ∈ LinearPathCategory.lengthTail Y Z 1) :
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f ≫
      (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map g = 0 := by
  rw [LinearPathCategory.lengthTail_eq_span] at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨q, hq, rfl⟩
      change
        (LinearPathCategory.HomogeneousQuotient.quotientFunctor
            P.toPresentation.relations).map f ≫
          pathMap P.toPresentation.relations q = 0
      exact P.pathSupportHullGenerator_comp_pathMap_eq_zero hf q
        (Nat.one_le_iff_ne_zero.mp hq)
  | zero => simp
  | add g h _ _ hg hh =>
      rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map_add, Preadditive.comp_add, hg, hh,
        add_zero]
  | smul c g _ hg =>
      rw [(LinearPathCategory.HomogeneousQuotient.quotientFunctor
        P.toPresentation.relations).map_smul,
        CategoryTheory.Linear.comp_smul, hg, smul_zero]

/-- Every element of the two-sided ideal generated by the path-support
hull is killed by precomposition with a displayed arrow after mapping back
to the original special-biserial quotient. -/
theorem pathSupportHullIdeal_rightExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : LinearPathCategory.Category k Q} (f : X ⟶ Y)
    (hf : f ∈ HomIdeal.generatedHomSubmodule k
      (pathSupportHull P.toPresentation.relations) X Y)
    {w : Q} (b : LinearPathCategory.vertex X ⟶ w) :
    arrowMap P.toPresentation.relations b ≫
        (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f = 0 := by
  let F := LinearPathCategory.HomogeneousQuotient.quotientFunctor
    P.toPresentation.relations
  let q : Quiver.Path (LinearPathCategory.vertex X)
      (LinearPathCategory.vertex (LinearPathCategory.obj k Q w)) := b.toPath
  let d : LinearPathCategory.obj k Q w ⟶ X :=
    LinearPathCategory.pathHom q
  change F.map d ≫ F.map f = 0
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨U, V, r, hr, a, c, rfl⟩
      have hd : d ∈ LinearPathCategory.lengthTail
          (LinearPathCategory.obj k Q w) X 1 := by
        exact (LinearPathCategory.pathHom_mem_lengthTail_iff q 1).2
          (by rw [show q.length = 1 by exact Quiver.Path.length_toPath b])
      have ha : a ∈ LinearPathCategory.lengthTail X U 0 := by
        rw [LinearPathCategory.mem_lengthTail_iff]
        intro q hq
        exact Nat.zero_le q.length
      have hda : d ≫ a ∈ LinearPathCategory.lengthTail
          (LinearPathCategory.obj k Q w) U 1 := by
        simpa using LinearPathCategory.comp_mem_lengthTail hd ha
      have hzero :=
        P.quotientMap_comp_pathSupportHullGenerator_eq_zero_of_mem_lengthTail_one
          (d ≫ a) hda hr
      calc
        F.map d ≫ F.map (a ≫ r ≫ c) =
            (F.map (d ≫ a) ≫ F.map r) ≫ F.map c := by
              rw [F.map_comp, F.map_comp, F.map_comp]
              simp only [Category.assoc]
        _ = 0 := by rw [hzero, CategoryTheory.Limits.zero_comp]
  | zero => simp
  | add f g _ _ hf hg =>
      rw [F.map_add, Preadditive.comp_add, hf, hg, add_zero]
  | smul c f _ hf =>
      rw [F.map_smul, CategoryTheory.Linear.comp_smul, hf, smul_zero]

/-- Every element of the two-sided ideal generated by the path-support
hull is killed by postcomposition with a displayed arrow after mapping back
to the original special-biserial quotient. -/
theorem pathSupportHullIdeal_leftExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : LinearPathCategory.Category k Q} (f : X ⟶ Y)
    (hf : f ∈ HomIdeal.generatedHomSubmodule k
      (pathSupportHull P.toPresentation.relations) X Y)
    {w : Q} (b : w ⟶ LinearPathCategory.vertex Y) :
    (LinearPathCategory.HomogeneousQuotient.quotientFunctor
          P.toPresentation.relations).map f ≫
        arrowMap P.toPresentation.relations b = 0 := by
  let F := LinearPathCategory.HomogeneousQuotient.quotientFunctor
    P.toPresentation.relations
  let q : Quiver.Path
      (LinearPathCategory.vertex (LinearPathCategory.obj k Q w))
      (LinearPathCategory.vertex Y) := b.toPath
  let d : Y ⟶ LinearPathCategory.obj k Q w :=
    LinearPathCategory.pathHom q
  change F.map f ≫ F.map d = 0
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨U, V, r, hr, a, c, rfl⟩
      have hc : c ∈ LinearPathCategory.lengthTail V Y 0 := by
        rw [LinearPathCategory.mem_lengthTail_iff]
        intro q hq
        exact Nat.zero_le q.length
      have hd : d ∈ LinearPathCategory.lengthTail Y
          (LinearPathCategory.obj k Q w) 1 := by
        exact (LinearPathCategory.pathHom_mem_lengthTail_iff q 1).2
          (by rw [show q.length = 1 by exact Quiver.Path.length_toPath b])
      have hcd : c ≫ d ∈ LinearPathCategory.lengthTail V
          (LinearPathCategory.obj k Q w) 1 := by
        simpa using LinearPathCategory.comp_mem_lengthTail hc hd
      have hzero :=
        P.pathSupportHullGenerator_comp_quotientMap_eq_zero_of_mem_lengthTail_one
          hr (c ≫ d) hcd
      calc
        F.map (a ≫ r ≫ c) ≫ F.map d =
            F.map a ≫ (F.map r ≫ F.map (c ≫ d)) := by
              rw [F.map_comp, F.map_comp, F.map_comp]
              simp only [Category.assoc]
        _ = 0 := by rw [hzero, CategoryTheory.Limits.comp_zero]
  | zero => simp
  | add f g _ _ hf hg =>
      rw [F.map_add, Preadditive.add_comp, hf, hg, add_zero]
  | smul c f _ hf =>
      rw [F.map_smul, CategoryTheory.Linear.smul_comp, hf, smul_zero]

/-- A morphism in the relative path-support-hull kernel is annihilated on
the right by every displayed arrow in the original quotient category. -/
theorem relativePathSupportHull_rightExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : Category P.toPresentation.relations} (f : X ⟶ Y)
    (hf : f ∈ (MagnitudeConjecture.BoundQuiver.relativeRelationHomIdeal
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)).hom X Y)
    {w : Q} (b : LinearPathCategory.vertex X.as ⟶ w) :
    arrowMap P.toPresentation.relations b ≫ f = 0 := by
  obtain ⟨g, rfl, hg⟩ :=
    (MagnitudeConjecture.BoundQuiver.mem_relativeRelationHomIdeal_iff_exists_lift
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations) f).1 hf
  exact P.pathSupportHullIdeal_rightExtension_eq_zero g hg b

/-- A morphism in the relative path-support-hull kernel is annihilated on
the left by every displayed arrow in the original quotient category. -/
theorem relativePathSupportHull_leftExtension_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {X Y : Category P.toPresentation.relations} (f : X ⟶ Y)
    (hf : f ∈ (MagnitudeConjecture.BoundQuiver.relativeRelationHomIdeal
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations)).hom X Y)
    {w : Q} (b : w ⟶ LinearPathCategory.vertex Y.as) :
    f ≫ arrowMap P.toPresentation.relations b = 0 := by
  obtain ⟨g, rfl, hg⟩ :=
    (MagnitudeConjecture.BoundQuiver.mem_relativeRelationHomIdeal_iff_exists_lift
      (fun _ _ ↦ relationIdeal_le_pathSupportHullIdeal
        P.toPresentation.relations) f).1 hf
  exact P.pathSupportHullIdeal_leftExtension_eq_zero g hg b

/-- The paths in a displayed relation which still survive in the original
special-biserial quotient. -/
abbrev RelationSurvivingSupport
    (P : SpecialBiserialPresentation k A Q) {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x) :=
  {p : Quiver.Path x z //
    LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r p ≠ 0 ∧
      pathMap P.toPresentation.relations p ≠ 0}

/-- A nonempty path decomposed into its first arrow and remaining tail. -/
structure InitialDecomposition {x z : Q} (p : Quiver.Path x z) where
  middle : Q
  arrow : x ⟶ middle
  tail : Quiver.Path middle z
  path_eq : p = arrow.toPath.comp tail
  length_eq : p.length = tail.length + 1

/-- Every path in the surviving support of a displayed relation has length
at least two, hence in particular has a first arrow. -/
theorem relationSurvivingSupport_length_ne_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    p.1.length ≠ 0 := by
  have hrIdeal : r ∈ HomIdeal.generatedHomSubmodule k
      P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x) :=
    HomIdeal.relation_mem_linearSpan P.toPresentation.relations hr
  have hrTail : r ∈ LinearPathCategory.lengthTail
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x) 2 :=
    P.toPresentation.admissible.relationIdeal_le_lengthTail_two _ _ hrIdeal
  have hpSupport : p.1 ∈
      (LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r).support :=
    Finsupp.mem_support_iff.mpr p.2.1
  have hpLength : 2 ≤ p.1.length :=
    (LinearPathCategory.mem_lengthTail_iff _ _ 2 r).1 hrTail hpSupport
  omega

/-- A chosen first-arrow decomposition for a surviving relation-support
path. -/
noncomputable def relationSurvivingSupportInitialDecomposition
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) : InitialDecomposition p.1 := by
  have hnonempty : Nonempty (InitialDecomposition p.1) := by
    obtain ⟨y, a, q, hp, hlength⟩ :=
      (Quiver.Path.length_ne_zero_iff_eq_comp p.1).1
        (P.relationSurvivingSupport_length_ne_zero r hr p)
    exact ⟨⟨y, a, q, hp, hlength⟩⟩
  exact Classical.choice hnonempty

/-- The first arrow of a surviving relation-support path. -/
noncomputable def relationSurvivingSupportInitialArrow
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    P.RelationSurvivingSupport r → Quiver.Star x :=
  fun p ↦
    let d := P.relationSurvivingSupportInitialDecomposition r hr p
    ⟨d.middle, d.arrow⟩

/-- Surviving paths in one displayed relation have distinct first arrows. -/
theorem relationSurvivingSupportInitialArrow_injective
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    Function.Injective (P.relationSurvivingSupportInitialArrow r hr) := by
  intro p q hpq
  let dp := P.relationSurvivingSupportInitialDecomposition r hr p
  let dq := P.relationSurvivingSupportInitialDecomposition r hr q
  change (⟨dp.middle, dp.arrow⟩ : Quiver.Star x) =
    ⟨dq.middle, dq.arrow⟩ at hpq
  rcases hdp : dp with ⟨y, a, ptail, hpPath, hpLength⟩
  rcases hdq : dq with ⟨y', a', qtail, hqPath, hqLength⟩
  rw [hdp, hdq] at hpq
  cases hpq
  let pp : P.RightContinuationAt a z := by
    refine ⟨ptail, ?_⟩
    change pathMap P.toPresentation.relations ptail ≫
      pathMap P.toPresentation.relations a.toPath ≠ 0
    rw [pathMap_comp, ← hpPath]
    exact p.2.2
  let qq : P.RightContinuationAt a z := by
    refine ⟨qtail, ?_⟩
    change pathMap P.toPresentation.relations qtail ≫
      pathMap P.toPresentation.relations a.toPath ≠ 0
    rw [pathMap_comp, ← hqPath]
    exact q.2.2
  have htail : ptail = qtail := by
    have hppqq : pp = qq := by
      apply (P.rightContinuationAtLengthEmbedding a z).injective
      change ptail.length = qtail.length
      by_contra hlength
      rcases lt_or_gt_of_ne hlength with hlt | hgt
      · obtain ⟨s, hs⟩ :=
          P.rightContinuationAt_factor_of_length_le a z pp qq
            (Nat.le_of_lt hlt)
        have hsLength : s.length ≠ 0 := by
          intro hsZero
          have hlen := congrArg Quiver.Path.length hs
          simp only [Quiver.Path.length_comp, hsZero, add_zero] at hlen
          exact hlength hlen.symm
        have hpHull : LinearPathCategory.pathHom p.1 ∈
            pathSupportHull P.toPresentation.relations
              (LinearPathCategory.obj k Q z)
              (LinearPathCategory.obj k Q x) :=
          ⟨p.1, rfl, r, hr, p.2.1⟩
        have hzero := P.pathMap_comp_pathSupportHullGenerator_eq_zero
          hpHull s hsLength
        apply q.2.2
        rw [hqPath, show qtail = ptail.comp s from hs]
        calc
          pathMap P.toPresentation.relations
              (a.toPath.comp (ptail.comp s)) =
              pathMap P.toPresentation.relations
                ((a.toPath.comp ptail).comp s) := by
                  rw [Quiver.Path.comp_assoc]
          _ = pathMap P.toPresentation.relations s ≫
              pathMap P.toPresentation.relations
                (a.toPath.comp ptail) := by rw [pathMap_comp]
          _ = pathMap P.toPresentation.relations s ≫
              pathMap P.toPresentation.relations p.1 := by rw [hpPath]
          _ = 0 := hzero
      · obtain ⟨s, hs⟩ :=
          P.rightContinuationAt_factor_of_length_le a z qq pp
            (Nat.le_of_lt hgt)
        have hsLength : s.length ≠ 0 := by
          intro hsZero
          have hlen := congrArg Quiver.Path.length hs
          simp only [Quiver.Path.length_comp, hsZero, add_zero] at hlen
          exact hlength hlen
        have hqHull : LinearPathCategory.pathHom q.1 ∈
            pathSupportHull P.toPresentation.relations
              (LinearPathCategory.obj k Q z)
              (LinearPathCategory.obj k Q x) :=
          ⟨q.1, rfl, r, hr, q.2.1⟩
        have hzero := P.pathMap_comp_pathSupportHullGenerator_eq_zero
          hqHull s hsLength
        apply p.2.2
        rw [hpPath, show ptail = qtail.comp s from hs]
        calc
          pathMap P.toPresentation.relations
              (a.toPath.comp (qtail.comp s)) =
              pathMap P.toPresentation.relations
                ((a.toPath.comp qtail).comp s) := by
                  rw [Quiver.Path.comp_assoc]
          _ = pathMap P.toPresentation.relations s ≫
              pathMap P.toPresentation.relations
                (a.toPath.comp qtail) := by rw [pathMap_comp]
          _ = pathMap P.toPresentation.relations s ≫
              pathMap P.toPresentation.relations q.1 := by rw [hqPath]
          _ = 0 := hzero
    exact congrArg Subtype.val hppqq
  apply Subtype.ext
  rw [hpPath, hqPath, htail]

/-- At most two paths occurring in one displayed relation can survive in
the original special-biserial quotient. -/
theorem relationSurvivingSupport_natCard_le_two
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    Nat.card (P.RelationSurvivingSupport r) ≤ 2 :=
  (Nat.card_le_card_of_injective
      (P.relationSurvivingSupportInitialArrow r hr)
      (P.relationSurvivingSupportInitialArrow_injective r hr)).trans
    (P.arrows_starting_le_two x)

/-- A surviving path in a displayed relation is paired with a distinct
surviving path in that same relation. -/
theorem RelationSurvivingSupport.exists_ne
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    ∃ q : P.RelationSurvivingSupport r, q ≠ p := by
  by_contra hnot
  push Not at hnot
  let b : Module.Basis (Quiver.Path x z) k
      (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x) :=
    LinearPathCategory.homPathBasis
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  let quotient :=
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
      P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  have hrMap : quotient r = 0 := by
    apply (LinearPathCategory.HomogeneousQuotient.relationIdeal
      P.toPresentation.relations).map_eq_zero_iff r |>.2
    exact HomIdeal.relation_mem_linearSpan P.toPresentation.relations hr
  have hrExpansion :
      Finsupp.linearCombination k (fun q ↦ b q) (b.repr r) = r :=
    b.linearCombination_repr r
  have hquotient (q : Quiver.Path x z) :
      quotient (b q) = pathMap P.toPresentation.relations q := by
    change quotient (LinearPathCategory.pathHom q) =
      pathMap P.toPresentation.relations q
    rfl
  have hsum :
      ∑ q ∈ (b.repr r).support,
        b.repr r q • pathMap P.toPresentation.relations q = 0 := by
    have hmapped := congrArg quotient hrExpansion
    rw [Finsupp.linearCombination_apply, map_finsuppSum] at hmapped
    simp_rw [map_smul, hquotient] at hmapped
    rw [hrMap] at hmapped
    exact hmapped
  have hpMem : p.1 ∈ (b.repr r).support :=
    Finsupp.mem_support_iff.mpr p.2.1
  have hsumSingle :
      ∑ q ∈ (b.repr r).support,
          b.repr r q • pathMap P.toPresentation.relations q =
        b.repr r p.1 • pathMap P.toPresentation.relations p.1 := by
    apply Finset.sum_eq_single p.1
    · intro q hq hqp
      by_cases hqMap : pathMap P.toPresentation.relations q = 0
      · rw [hqMap, smul_zero]
      · have hqCoeff : b.repr r q ≠ 0 :=
          Finsupp.mem_support_iff.mp hq
        have hqp' := hnot (⟨q, hqCoeff, hqMap⟩ :
          P.RelationSurvivingSupport r)
        exact False.elim (hqp (congrArg Subtype.val hqp'))
    · exact fun hpNot ↦ False.elim (hpNot hpMem)
  have hpZero :
      b.repr r p.1 • pathMap P.toPresentation.relations p.1 = 0 := by
    rw [← hsumSingle]
    exact hsum
  exact (smul_ne_zero p.2.1 p.2.2) hpZero

/-- A nonempty path decomposed into an initial segment and final arrow. -/
structure FinalDecomposition {x z : Q} (p : Quiver.Path x z) where
  middle : Q
  head : Quiver.Path x middle
  arrow : middle ⟶ z
  path_eq : p = head.comp arrow.toPath
  length_eq : p.length = head.length + 1

/-- A chosen final-arrow decomposition for a surviving relation-support
path. -/
noncomputable def relationSurvivingSupportFinalDecomposition
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) : FinalDecomposition p.1 := by
  have hnonempty : Nonempty (FinalDecomposition p.1) := by
    obtain ⟨y, q, a, hp⟩ :=
      (Quiver.Path.length_ne_zero_iff_eq_cons p.1).1
        (P.relationSurvivingSupport_length_ne_zero r hr p)
    refine ⟨⟨y, q, a, ?_, ?_⟩⟩
    · simpa only [Quiver.Path.comp_toPath_eq_cons] using hp
    · rw [hp]
      simp
  exact Classical.choice hnonempty

/-- The final arrow of a surviving relation-support path. -/
noncomputable def relationSurvivingSupportFinalArrow
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    P.RelationSurvivingSupport r → Quiver.Costar z :=
  fun p ↦
    let d := P.relationSurvivingSupportFinalDecomposition r hr p
    ⟨d.middle, d.arrow⟩

/-- Surviving paths in one displayed relation have distinct final arrows. -/
theorem relationSurvivingSupportFinalArrow_injective
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    Function.Injective (P.relationSurvivingSupportFinalArrow r hr) := by
  intro p q hpq
  let dp := P.relationSurvivingSupportFinalDecomposition r hr p
  let dq := P.relationSurvivingSupportFinalDecomposition r hr q
  change (⟨dp.middle, dp.arrow⟩ : Quiver.Costar z) =
    ⟨dq.middle, dq.arrow⟩ at hpq
  rcases hdp : dp with ⟨y, phead, a, hpPath, hpLength⟩
  rcases hdq : dq with ⟨y', qhead, a', hqPath, hqLength⟩
  rw [hdp, hdq] at hpq
  cases hpq
  let pp : P.LeftContinuationAt a x := by
    refine ⟨phead, ?_⟩
    change pathMap P.toPresentation.relations a.toPath ≫
      pathMap P.toPresentation.relations phead ≠ 0
    rw [pathMap_comp, ← hpPath]
    exact p.2.2
  let qq : P.LeftContinuationAt a x := by
    refine ⟨qhead, ?_⟩
    change pathMap P.toPresentation.relations a.toPath ≫
      pathMap P.toPresentation.relations qhead ≠ 0
    rw [pathMap_comp, ← hqPath]
    exact q.2.2
  have hhead : phead = qhead := by
    have hppqq : pp = qq := by
      apply (P.leftContinuationAtLengthEmbedding a x).injective
      change phead.length = qhead.length
      by_contra hlength
      rcases lt_or_gt_of_ne hlength with hlt | hgt
      · obtain ⟨s, hs⟩ :=
          P.leftContinuationAt_factor_of_length_le a x pp qq
            (Nat.le_of_lt hlt)
        have hsLength : s.length ≠ 0 := by
          intro hsZero
          have hlen := congrArg Quiver.Path.length hs
          simp only [Quiver.Path.length_comp, hsZero, zero_add] at hlen
          exact hlength hlen.symm
        have hpHull : LinearPathCategory.pathHom p.1 ∈
            pathSupportHull P.toPresentation.relations
              (LinearPathCategory.obj k Q z)
              (LinearPathCategory.obj k Q x) :=
          ⟨p.1, rfl, r, hr, p.2.1⟩
        have hzero := P.pathSupportHullGenerator_comp_pathMap_eq_zero
          hpHull s hsLength
        apply q.2.2
        rw [hqPath, show qhead = s.comp phead from hs]
        calc
          pathMap P.toPresentation.relations
              ((s.comp phead).comp a.toPath) =
              pathMap P.toPresentation.relations
                (s.comp (phead.comp a.toPath)) := by
                  rw [Quiver.Path.comp_assoc]
          _ = pathMap P.toPresentation.relations
                (phead.comp a.toPath) ≫
              pathMap P.toPresentation.relations s := by rw [pathMap_comp]
          _ = pathMap P.toPresentation.relations p.1 ≫
              pathMap P.toPresentation.relations s := by rw [hpPath]
          _ = 0 := hzero
      · obtain ⟨s, hs⟩ :=
          P.leftContinuationAt_factor_of_length_le a x qq pp
            (Nat.le_of_lt hgt)
        have hsLength : s.length ≠ 0 := by
          intro hsZero
          have hlen := congrArg Quiver.Path.length hs
          simp only [Quiver.Path.length_comp, hsZero, zero_add] at hlen
          exact hlength hlen
        have hqHull : LinearPathCategory.pathHom q.1 ∈
            pathSupportHull P.toPresentation.relations
              (LinearPathCategory.obj k Q z)
              (LinearPathCategory.obj k Q x) :=
          ⟨q.1, rfl, r, hr, q.2.1⟩
        have hzero := P.pathSupportHullGenerator_comp_pathMap_eq_zero
          hqHull s hsLength
        apply p.2.2
        rw [hpPath, show phead = s.comp qhead from hs]
        calc
          pathMap P.toPresentation.relations
              ((s.comp qhead).comp a.toPath) =
              pathMap P.toPresentation.relations
                (s.comp (qhead.comp a.toPath)) := by
                  rw [Quiver.Path.comp_assoc]
          _ = pathMap P.toPresentation.relations
                (qhead.comp a.toPath) ≫
              pathMap P.toPresentation.relations s := by rw [pathMap_comp]
          _ = pathMap P.toPresentation.relations q.1 ≫
              pathMap P.toPresentation.relations s := by rw [hqPath]
          _ = 0 := hzero
    exact congrArg Subtype.val hppqq
  apply Subtype.ext
  rw [hpPath, hqPath, hhead]

/-- The surviving support of a displayed relation is finite. -/
theorem relationSurvivingSupport_finite
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    Finite (P.RelationSurvivingSupport r) :=
  Finite.of_injective (P.relationSurvivingSupportFinalArrow r hr)
    (P.relationSurvivingSupportFinalArrow_injective r hr)

/-- A displayed relation with one surviving path has exactly two surviving
path terms. -/
theorem relationSurvivingSupport_natCard_eq_two
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    Nat.card (P.RelationSurvivingSupport r) = 2 := by
  classical
  letI : Finite (P.RelationSurvivingSupport r) :=
    P.relationSurvivingSupport_finite r hr
  letI : Fintype (P.RelationSurvivingSupport r) := Fintype.ofFinite _
  obtain ⟨q, hqp⟩ := p.exists_ne P r hr
  have hsubset : ({p, q} : Finset (P.RelationSurvivingSupport r)) ⊆
      Finset.univ := by simp
  have hlower : 2 ≤ Fintype.card (P.RelationSurvivingSupport r) := by
    have hcard := Finset.card_le_card hsubset
    simp only [Finset.card_univ] at hcard
    have htwo : ({p, q} :
        Finset (P.RelationSurvivingSupport r)).card = 2 := by
      simp [Ne.symm hqp]
    omega
  have hupper : Fintype.card (P.RelationSurvivingSupport r) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      P.relationSurvivingSupport_natCard_le_two r hr
  rw [Nat.card_eq_fintype_card]
  omega

/-- Once a displayed relation has a surviving term, its two terms exhaust
the arrows leaving their common initial vertex. -/
theorem relationSurvivingSupportInitialArrow_bijective
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    Function.Bijective (P.relationSurvivingSupportInitialArrow r hr) := by
  letI : Finite (P.RelationSurvivingSupport r) :=
    P.relationSurvivingSupport_finite r hr
  letI : Fintype (P.RelationSurvivingSupport r) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card
    (P.relationSurvivingSupportInitialArrow r hr)).mpr
  refine ⟨P.relationSurvivingSupportInitialArrow_injective r hr, ?_⟩
  have hdomain : Fintype.card (P.RelationSurvivingSupport r) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      P.relationSurvivingSupport_natCard_eq_two r hr p
  have htargetUpper : Fintype.card (Quiver.Star x) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using P.arrows_starting_le_two x
  have htargetLower : Fintype.card (P.RelationSurvivingSupport r) ≤
      Fintype.card (Quiver.Star x) :=
    Fintype.card_le_of_injective
      (P.relationSurvivingSupportInitialArrow r hr)
      (P.relationSurvivingSupportInitialArrow_injective r hr)
  omega

/-- Once a displayed relation has a surviving term, its two terms exhaust
the arrows entering their common terminal vertex. -/
theorem relationSurvivingSupportFinalArrow_bijective
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    Function.Bijective (P.relationSurvivingSupportFinalArrow r hr) := by
  letI : Finite (P.RelationSurvivingSupport r) :=
    P.relationSurvivingSupport_finite r hr
  letI : Fintype (P.RelationSurvivingSupport r) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card
    (P.relationSurvivingSupportFinalArrow r hr)).mpr
  refine ⟨P.relationSurvivingSupportFinalArrow_injective r hr, ?_⟩
  have hdomain : Fintype.card (P.RelationSurvivingSupport r) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      P.relationSurvivingSupport_natCard_eq_two r hr p
  have htargetUpper : Fintype.card (Quiver.Costar z) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using P.arrows_ending_le_two z
  have htargetLower : Fintype.card (P.RelationSurvivingSupport r) ≤
      Fintype.card (Quiver.Costar z) :=
    Fintype.card_le_of_injective
      (P.relationSurvivingSupportFinalArrow r hr)
      (P.relationSurvivingSupportFinalArrow_injective r hr)
  omega

/-- Every surviving path has a unique distinct partner in its displayed
relation. -/
theorem RelationSurvivingSupport.existsUnique_ne
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p : P.RelationSurvivingSupport r) :
    ∃! q : P.RelationSurvivingSupport r, q ≠ p := by
  classical
  letI : Finite (P.RelationSurvivingSupport r) :=
    P.relationSurvivingSupport_finite r hr
  letI : Fintype (P.RelationSurvivingSupport r) := Fintype.ofFinite _
  obtain ⟨q, hqp⟩ := p.exists_ne P r hr
  refine ⟨q, hqp, ?_⟩
  intro s hsp
  by_contra hsq
  have hsmall : Fintype.card (P.RelationSurvivingSupport r) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      P.relationSurvivingSupport_natCard_le_two r hr
  have hsubset : ({p, q, s} : Finset (P.RelationSurvivingSupport r)) ⊆
      Finset.univ := by simp
  have hlarge : 3 ≤ Fintype.card (P.RelationSurvivingSupport r) := by
    have hcard := Finset.card_le_card hsubset
    simp only [Finset.card_univ] at hcard
    have hthree : ({p, q, s} :
        Finset (P.RelationSurvivingSupport r)).card = 3 := by
      simp [hqp, hsp, hsq, Ne.symm hqp, Ne.symm hsp, Ne.symm hsq]
    omega
  omega

/-- The displayed relation maps to the corresponding coefficient sum of
path classes, which vanishes in the original quotient. -/
theorem relation_pathMap_sum_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)) :
    ∑ q ∈ (LinearPathCategory.homPathLinearEquiv
        (LinearPathCategory.obj k Q z)
        (LinearPathCategory.obj k Q x) r).support,
      LinearPathCategory.homPathLinearEquiv
          (LinearPathCategory.obj k Q z)
          (LinearPathCategory.obj k Q x) r q •
        pathMap P.toPresentation.relations q = 0 := by
  let b : Module.Basis (Quiver.Path x z) k
      (LinearPathCategory.obj k Q z ⟶
        LinearPathCategory.obj k Q x) :=
    LinearPathCategory.homPathBasis
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  let quotient :=
    LinearPathCategory.HomogeneousQuotient.quotientHomLinearMap
      P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x)
  have hrMap : quotient r = 0 := by
    apply (LinearPathCategory.HomogeneousQuotient.relationIdeal
      P.toPresentation.relations).map_eq_zero_iff r |>.2
    exact HomIdeal.relation_mem_linearSpan P.toPresentation.relations hr
  have hrExpansion :
      Finsupp.linearCombination k (fun q ↦ b q) (b.repr r) = r :=
    b.linearCombination_repr r
  have hquotient (q : Quiver.Path x z) :
      quotient (b q) = pathMap P.toPresentation.relations q := by
    change quotient (LinearPathCategory.pathHom q) =
      pathMap P.toPresentation.relations q
    rfl
  have hmapped := congrArg quotient hrExpansion
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at hmapped
  simp_rw [map_smul, hquotient] at hmapped
  rw [hrMap] at hmapped
  exact hmapped

/-- The two surviving path classes in a displayed relation satisfy its
literal two-term linear relation. -/
theorem relationSurvivingSupport_pair_smul_add_eq_zero
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p q : P.RelationSurvivingSupport r)
    (hqp : q ≠ p) :
    LinearPathCategory.homPathLinearEquiv
          (LinearPathCategory.obj k Q z)
          (LinearPathCategory.obj k Q x) r p.1 •
        pathMap P.toPresentation.relations p.1 +
      LinearPathCategory.homPathLinearEquiv
          (LinearPathCategory.obj k Q z)
          (LinearPathCategory.obj k Q x) r q.1 •
        pathMap P.toPresentation.relations q.1 = 0 := by
  classical
  let coeff := LinearPathCategory.homPathLinearEquiv
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q x) r
  let term : Quiver.Path x z →
      (BoundQuiver.obj P.toPresentation.relations z ⟶
        BoundQuiver.obj P.toPresentation.relations x) :=
    fun t ↦ coeff t • pathMap P.toPresentation.relations t
  have hpMem : p.1 ∈ coeff.support :=
    Finsupp.mem_support_iff.mpr p.2.1
  have hqMem : q.1 ∈ coeff.support :=
    Finsupp.mem_support_iff.mpr q.2.1
  have hpqVal : p.1 ≠ q.1 := by
    intro hpq
    apply hqp
    apply Subtype.ext
    exact hpq.symm
  have hsubset : {p.1, q.1} ⊆ coeff.support := by
    exact Finset.insert_subset_iff.mpr
      ⟨hpMem, Finset.singleton_subset_iff.mpr hqMem⟩
  have houtside (t : Quiver.Path x z) (ht : t ∈ coeff.support)
      (htnot : t ∉ ({p.1, q.1} : Finset (Quiver.Path x z))) :
      term t = 0 := by
    have htCoeff : coeff t ≠ 0 := Finsupp.mem_support_iff.mp ht
    by_cases htMap : pathMap P.toPresentation.relations t = 0
    · simp [term, htMap]
    · let s : P.RelationSurvivingSupport r :=
        ⟨t, htCoeff, htMap⟩
      have hsp : s ≠ p := by
        intro hsp
        apply htnot
        simp [show t = p.1 from congrArg Subtype.val hsp]
      obtain ⟨partner, hpartner, hunique⟩ := p.existsUnique_ne P r hr
      have hsq : s = q :=
        (hunique s hsp).trans (hunique q hqp).symm
      apply False.elim
      apply htnot
      simp [show t = q.1 from congrArg Subtype.val hsq]
  have hsumSubset :
      ∑ t ∈ ({p.1, q.1} : Finset (Quiver.Path x z)), term t =
        ∑ t ∈ coeff.support, term t :=
    Finset.sum_subset hsubset houtside
  have hpair :
      ∑ t ∈ ({p.1, q.1} : Finset (Quiver.Path x z)), term t =
        term p.1 + term q.1 := by
    simp [hpqVal]
  change term p.1 + term q.1 = 0
  rw [← hpair, hsumSubset]
  exact P.relation_pathMap_sum_eq_zero r hr

/-- The two surviving path classes in one displayed relation are nonzero
scalar multiples of one another. -/
theorem relationSurvivingSupport_pathMap_eq_smul
    (P : SpecialBiserialPresentation k A Q)
    {x z : Q}
    (r : LinearPathCategory.obj k Q z ⟶
      LinearPathCategory.obj k Q x)
    (hr : r ∈ P.toPresentation.relations
      (LinearPathCategory.obj k Q z)
      (LinearPathCategory.obj k Q x))
    (p q : P.RelationSurvivingSupport r)
    (hqp : q ≠ p) :
    ∃ c : k, c ≠ 0 ∧
      pathMap P.toPresentation.relations p.1 =
        c • pathMap P.toPresentation.relations q.1 := by
  let a := LinearPathCategory.homPathLinearEquiv
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q x) r p.1
  let b := LinearPathCategory.homPathLinearEquiv
    (LinearPathCategory.obj k Q z)
    (LinearPathCategory.obj k Q x) r q.1
  have ha : a ≠ 0 := p.2.1
  have hb : b ≠ 0 := q.2.1
  refine ⟨-(a⁻¹ * b), ?_, ?_⟩
  · exact neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero ha) hb)
  · have hrelation :=
      P.relationSurvivingSupport_pair_smul_add_eq_zero r hr p q hqp
    have haPath :
        a • pathMap P.toPresentation.relations p.1 =
          -(b • pathMap P.toPresentation.relations q.1) :=
      eq_neg_of_add_eq_zero_left hrelation
    calc
      pathMap P.toPresentation.relations p.1 =
          a⁻¹ • (a • pathMap P.toPresentation.relations p.1) := by
        rw [← mul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • (-(b • pathMap P.toPresentation.relations q.1)) := by
        rw [haPath]
      _ = -(a⁻¹ * b) • pathMap P.toPresentation.relations q.1 := by
        simp [smul_smul]

end MagnitudeConjecture.BoundQuiver.SpecialBiserialPresentation
