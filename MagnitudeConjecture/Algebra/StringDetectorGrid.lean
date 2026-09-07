import MagnitudeConjecture.Algebra.StringDetectorWordCoverage
import MagnitudeConjecture.Algebra.StringDetectorPair
import MagnitudeConjecture.LinearAlgebra.FiniteFiltration
import Mathlib.Data.Prod.Lex

/-!
# Grid refinement of the two endpoint-word filtrations

For opposite endpoint polarizations, Ringel refines the left word interval
by the right word filtration.  This file first identifies one resulting grid
quotient with the already defined pair detector, by a canonical natural
linear equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- Lower endpoint of the grid interval obtained by refining `L` with `R`. -/
def pairGridLower
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  (lowerSubspace N R ⊔ lowerSubspace N L) ⊓ upperSubspace N L

/-- Upper endpoint of the grid interval obtained by refining `L` with `R`. -/
def pairGridUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  (upperSubspace N R ⊔ lowerSubspace N L) ⊓ upperSubspace N L

theorem pairGridLower_le_pairGridUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    pairGridLower N L R ≤ pairGridUpper N L R := by
  exact inf_le_inf
    (sup_le_sup_right (lowerSubspace_le_upperSubspace N R) _)
    le_rfl

/-- The lower grid endpoint as a subspace of its upper endpoint. -/
def pairGridLowerInUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Submodule k (pairGridUpper N L R) :=
  (pairGridLower N L R).comap (pairGridUpper N L R).subtype

/-- One successive quotient in Ringel's two-filtration grid. -/
abbrev PairGridSpace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :=
  pairGridUpper N L R ⧸ pairGridLowerInUpper N L R

/-- On the pair numerator, membership in the pair denominator is equivalent
to membership in the lower grid endpoint.  This is the elementwise modular
law underlying Ringel's quotient formula. -/
theorem mem_pairDetectorDenominator_iff_mem_pairGridLower
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (x : N.obj (Opposite.op (obj P.toPresentation.relations u₀)))
    (hx : x ∈ pairDetectorNumerator N L R) :
    x ∈ pairDetectorDenominator N L R ↔ x ∈ pairGridLower N L R := by
  constructor
  · intro hden
    rw [pairDetectorDenominator, Submodule.mem_sup] at hden
    rcases hden with ⟨y, hy, z, hz, rfl⟩
    constructor
    · exact (lowerSubspace N R ⊔ lowerSubspace N L).add_mem
        ((show lowerSubspace N R ≤
          lowerSubspace N R ⊔ lowerSubspace N L from le_sup_left) hy.2)
        ((show lowerSubspace N L ≤
          lowerSubspace N R ⊔ lowerSubspace N L from le_sup_right) hz.1)
    · exact (upperSubspace N L).add_mem hy.1
        ((lowerSubspace_le_upperSubspace N L) hz.1)
  · intro hgrid
    rcases (Submodule.mem_sup.mp hgrid.1) with ⟨y, hy, z, hz, hyz⟩
    have hzUpperL : z ∈ upperSubspace N L :=
      (lowerSubspace_le_upperSubspace N L) hz
    have hyUpperL : y ∈ upperSubspace N L := by
      have hyEq : y = x - z := by
        rw [← hyz]
        abel
      rw [hyEq]
      exact (upperSubspace N L).sub_mem hgrid.2 hzUpperL
    have hyUpperR : y ∈ upperSubspace N R :=
      (lowerSubspace_le_upperSubspace N R) hy
    have hzUpperR : z ∈ upperSubspace N R := by
      have hzEq : z = x - y := by
        rw [← hyz]
        abel
      rw [hzEq]
      exact (upperSubspace N R).sub_mem hx.2 hyUpperR
    rw [pairDetectorDenominator, Submodule.mem_sup]
    exact ⟨y, ⟨hyUpperL, hy⟩, z, ⟨hz, hzUpperR⟩, hyz⟩

/-- Inclusion of the pair numerator into the upper grid endpoint. -/
def pairNumeratorToGridUpperMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    pairDetectorNumerator N L R →ₗ[k] pairGridUpper N L R :=
  LinearMap.codRestrict (pairGridUpper N L R)
    (pairDetectorNumerator N L R).subtype (by
      rintro ⟨x, hx⟩
      exact ⟨(show upperSubspace N R ≤
        upperSubspace N R ⊔ lowerSubspace N L from le_sup_left) hx.2,
        hx.1⟩)

@[simp]
theorem pairNumeratorToGridUpperMap_coe
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (x : pairDetectorNumerator N L R) :
    (pairNumeratorToGridUpperMap N L R x :
      N.obj (Opposite.op (obj P.toPresentation.relations u₀))) = x :=
  rfl

/-- The pair denominator maps into the lower grid endpoint. -/
theorem pairDetectorDenominatorInNumerator_le_comap_pairGridLowerInUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    pairDetectorDenominatorInNumerator N L R ≤
      (pairGridLowerInUpper N L R).comap
        (pairNumeratorToGridUpperMap N L R) := by
  intro x hx
  exact (mem_pairDetectorDenominator_iff_mem_pairGridLower
    N L R x.1 x.2).mp hx

/-- Canonical map from the pair detector to its grid realization. -/
def pairDetectorToGridLinearMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    PairDetectorSpace N L R →ₗ[k] PairGridSpace N L R :=
  Submodule.mapQ
    (pairDetectorDenominatorInNumerator N L R)
    (pairGridLowerInUpper N L R)
    (pairNumeratorToGridUpperMap N L R)
    (pairDetectorDenominatorInNumerator_le_comap_pairGridLowerInUpper
      N L R)

@[simp]
theorem pairDetectorToGridLinearMap_mk
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (x : pairDetectorNumerator N L R) :
    pairDetectorToGridLinearMap N L R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (pairNumeratorToGridUpperMap N L R x) := by
  exact Submodule.mapQ_apply _ _ _ x

theorem pairDetectorToGridLinearMap_injective
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Function.Injective (pairDetectorToGridLinearMap N L R) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [pairDetectorToGridLinearMap_mk,
        Submodule.Quotient.mk_eq_zero] at hq
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (mem_pairDetectorDenominator_iff_mem_pairGridLower
        N L R x.1 x.2).mpr hq

theorem pairDetectorToGridLinearMap_surjective
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Function.Surjective (pairDetectorToGridLinearMap N L R) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
      rcases (Submodule.mem_sup.mp y.2.1) with ⟨x, hxR, z, hzL, hxz⟩
      have hzUpperL : z ∈ upperSubspace N L :=
        (lowerSubspace_le_upperSubspace N L) hzL
      have hxL : x ∈ upperSubspace N L := by
        have hxEq : x = y.1 - z := by
          rw [← hxz]
          abel
        rw [hxEq]
        exact (upperSubspace N L).sub_mem y.2.2 hzUpperL
      let xnum : pairDetectorNumerator N L R := ⟨x, hxL, hxR⟩
      refine ⟨Submodule.Quotient.mk xnum, ?_⟩
      rw [pairDetectorToGridLinearMap_mk]
      apply (Submodule.Quotient.eq (pairGridLowerInUpper N L R)).mpr
      change x - y.1 ∈ pairGridLower N L R
      have hzGrid : z ∈ pairGridLower N L R := by
        exact ⟨(show lowerSubspace N L ≤
          lowerSubspace N R ⊔ lowerSubspace N L from le_sup_right) hzL,
          hzUpperL⟩
      have hdiff : x - y.1 = -z := by
        rw [← hxz]
        abel
      rw [hdiff]
      exact (pairGridLower N L R).neg_mem hzGrid

/-- Canonical equivalence from a pair detector to its grid quotient. -/
noncomputable def pairDetectorGridEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    PairDetectorSpace N L R ≃ₗ[k] PairGridSpace N L R :=
  LinearEquiv.ofBijective (pairDetectorToGridLinearMap N L R)
    ⟨pairDetectorToGridLinearMap_injective N L R,
      pairDetectorToGridLinearMap_surjective N L R⟩

/-- Ringel's grid quotient, oriented toward the existing pair detector. -/
noncomputable def pairGridDetectorEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    PairGridSpace N L R ≃ₗ[k] PairDetectorSpace N L R :=
  (pairDetectorGridEquiv N L R).symm

@[simp]
theorem pairDetectorGridEquiv_apply
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (q : PairDetectorSpace N L R) :
    pairDetectorGridEquiv N L R q = pairDetectorToGridLinearMap N L R q :=
  rfl

/-- A module morphism preserves lower grid endpoints. -/
theorem pairGridLower_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    (pairGridLower M L R).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u₀))).hom ≤
      pairGridLower N L R := by
  apply (Submodule.map_inf_le _).trans
  apply inf_le_inf
  · rw [Submodule.map_sup]
    exact sup_le_sup (lowerSubspace_map_le f R)
      (lowerSubspace_map_le f L)
  · exact upperSubspace_map_le f L

/-- A module morphism preserves upper grid endpoints. -/
theorem pairGridUpper_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    (pairGridUpper M L R).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u₀))).hom ≤
      pairGridUpper N L R := by
  apply (Submodule.map_inf_le _).trans
  apply inf_le_inf
  · rw [Submodule.map_sup]
    exact sup_le_sup (upperSubspace_map_le f R)
      (lowerSubspace_map_le f L)
  · exact upperSubspace_map_le f L

/-- Map induced by a module morphism on one grid quotient. -/
def pairGridLinearMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    PairGridSpace M L R →ₗ[k] PairGridSpace N L R :=
  MagnitudeConjecture.LinearAlgebra.FiniteFiltration.layerMap
    (f.app (Opposite.op (obj P.toPresentation.relations u₀))).hom
    (pairGridLower M L R) (pairGridUpper M L R)
    (pairGridLower N L R) (pairGridUpper N L R)
    (pairGridLower_le_pairGridUpper M L R)
    (pairGridLower_le_pairGridUpper N L R)
    (pairGridUpper_map_le f L R) (pairGridLower_map_le f L R)

@[simp]
theorem pairGridLinearMap_mk
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (x : pairGridUpper M L R) :
    pairGridLinearMap f L R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (MagnitudeConjecture.LinearAlgebra.FiniteFiltration.restrictionMap
          (f.app (Opposite.op
            (obj P.toPresentation.relations u₀))).hom
          (pairGridUpper M L R) (pairGridUpper N L R)
          (pairGridUpper_map_le f L R) x) := by
  exact MagnitudeConjecture.LinearAlgebra.FiniteFiltration.layerMap_mk
    _ _ _ _ _ _ _ _ _ _

/-- The canonical pair-to-grid map commutes with module morphisms. -/
theorem pairDetectorToGridLinearMap_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (q : PairDetectorSpace M L R) :
    pairGridLinearMap f L R (pairDetectorToGridLinearMap M L R q) =
      pairDetectorToGridLinearMap N L R
        (pairDetectorLinearMap f L R q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [pairDetectorToGridLinearMap_mk, pairGridLinearMap_mk,
        pairDetectorLinearMap_mk, pairDetectorToGridLinearMap_mk]
      rfl

/-- The grid-to-pair equivalence is natural under module morphisms. -/
theorem pairGridDetectorEquiv_naturality
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (q : PairGridSpace M L R) :
    pairGridDetectorEquiv N L R (pairGridLinearMap f L R q) =
      pairDetectorLinearMap f L R (pairGridDetectorEquiv M L R q) := by
  apply (pairDetectorGridEquiv N L R).injective
  change (pairDetectorGridEquiv N L R)
      ((pairDetectorGridEquiv N L R).symm (pairGridLinearMap f L R q)) =
    (pairDetectorGridEquiv N L R)
      (pairDetectorLinearMap f L R
        ((pairDetectorGridEquiv M L R).symm q))
  rw [LinearEquiv.apply_symm_apply, pairDetectorGridEquiv_apply,
    ← pairDetectorToGridLinearMap_naturality,
    ← pairDetectorGridEquiv_apply, LinearEquiv.apply_symm_apply]

open Prod.Lex

/-- Pairs of oppositely polarized endpoint words, in lexicographic order. -/
abbrev GridWordIndex (S : P.ArrowPolarization) (u₀ : Q) (t : Bool) :=
  EndpointWord S u₀ (Bool.not t) ×ₗ EndpointWord S u₀ t

/-- The finite grid-word family in canonical lexicographic enumeration. -/
noncomputable def orderedGridWordOrderIso [Finite (DetectorIndex S)] :
    Fin (Nat.card (GridWordIndex S u₀ t)) ≃o GridWordIndex S u₀ t := by
  letI : Finite (EndpointWord S u₀ (Bool.not t)) :=
    DetectorIndex.finite_endpointWord_of_finite_detectorIndex
      (P := P) (S := S) u₀ (Bool.not t)
  letI : Finite (EndpointWord S u₀ t) :=
    DetectorIndex.finite_endpointWord_of_finite_detectorIndex
      (P := P) (S := S) u₀ t
  letI : Finite (GridWordIndex S u₀ t) :=
    Finite.of_injective ofLex (Equiv.injective ofLex)
  letI : Fintype (GridWordIndex S u₀ t) := Fintype.ofFinite _
  have hcard : (Finset.univ : Finset (GridWordIndex S u₀ t)).card =
      Nat.card (GridWordIndex S u₀ t) := by
    simp [Nat.card_eq_fintype_card]
  let e := (Finset.univ : Finset (GridWordIndex S u₀ t)).orderIsoOfFin hcard
  exact e.trans {
    toFun := fun C ↦ C.1
    invFun := fun C ↦ ⟨C, Finset.mem_univ C⟩
    left_inv := fun C ↦ Subtype.ext rfl
    right_inv := fun C ↦ rfl
    map_rel_iff' := by intro C D; rfl }

/-- The `i`th pair of endpoint words in lexicographic grid order. -/
noncomputable def orderedGridWord [Finite (DetectorIndex S)]
    (i : Fin (Nat.card (GridWordIndex S u₀ t))) :
    EndpointWord S u₀ (Bool.not t) × EndpointWord S u₀ t :=
  ofLex (orderedGridWordOrderIso
    (P := P) (S := S) (u₀ := u₀) (t := t) i)

theorem orderedGridWord_lt_iff [Finite (DetectorIndex S)]
    {i j : Fin (Nat.card (GridWordIndex S u₀ t))} :
    toLex (orderedGridWord (P := P) (S := S) i) <
        toLex (orderedGridWord (P := P) (S := S) j) ↔ i < j :=
  (orderedGridWordOrderIso
    (P := P) (S := S) (u₀ := u₀) (t := t)).lt_iff_lt

theorem orderedGridWord_surjective [Finite (DetectorIndex S)] :
    Function.Surjective
      (orderedGridWord (P := P) (S := S) (u₀ := u₀) (t := t)) := by
  intro LR
  obtain ⟨i, hi⟩ := (orderedGridWordOrderIso
    (P := P) (S := S) (u₀ := u₀) (t := t)).surjective (toLex LR)
  exact ⟨i, congrArg ofLex hi⟩

theorem lowerSubspace_le_pairGridLower
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    lowerSubspace N L ≤ pairGridLower N L R := by
  intro x hx
  exact ⟨(show lowerSubspace N L ≤
      lowerSubspace N R ⊔ lowerSubspace N L from le_sup_right) hx,
    (lowerSubspace_le_upperSubspace N L) hx⟩

/-- Grid intervals avoid one another in lexicographic pair order. -/
theorem pairGridUpper_le_pairGridLower_of_lex_lt
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {LR LR' : EndpointWord S u₀ (Bool.not t) ×
      EndpointWord S u₀ t}
    (h : toLex LR < toLex LR') :
    pairGridUpper N LR.1 LR.2 ≤ pairGridLower N LR'.1 LR'.2 := by
  rcases LR with ⟨L, R⟩
  rcases LR' with ⟨L', R'⟩
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with hL | ⟨hL, hR⟩
  · calc
      pairGridUpper N L R ≤ upperSubspace N L := inf_le_right
      _ ≤ lowerSubspace N L' :=
        upperSubspace_le_lowerSubspace_of_wordLT N L L'
          ((wordLT_iff_lt _ _).mpr hL)
      _ ≤ pairGridLower N L' R' :=
        lowerSubspace_le_pairGridLower N L' R'
  · have hLL' : L = L' := by simpa only using hL
    subst L'
    exact inf_le_inf
      (sup_le_sup_right
        (upperSubspace_le_lowerSubspace_of_wordLT N R R'
          ((wordLT_iff_lt _ _).mpr hR)) _)
      le_rfl

theorem orderedGridWord_upper_le_lower
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    {i j : Fin (Nat.card (GridWordIndex S u₀ t))} (hij : i < j) :
    pairGridUpper N (orderedGridWord (P := P) (S := S) i).1
        (orderedGridWord (P := P) (S := S) i).2 ≤
      pairGridLower N (orderedGridWord (P := P) (S := S) j).1
        (orderedGridWord (P := P) (S := S) j).2 := by
  apply pairGridUpper_le_pairGridLower_of_lex_lt N
  rw [orderedGridWord_lt_iff]
  exact hij

/-- Every nonzero vector belongs to one of the finite grid intervals. -/
theorem exists_pairGrid_interval_of_ne_zero
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (u₀ : Q) (t : Bool)
    (x : N.obj (Opposite.op (obj P.toPresentation.relations u₀)))
    (hx : x ≠ 0) :
    ∃ (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t),
      x ∈ pairGridUpper N L R ∧ x ∉ pairGridLower N L R := by
  classical
  obtain ⟨L, hxUpperL, hxNotLowerL⟩ :=
    exists_endpointWord_interval_of_ne_zero
      (P := P) (S := S) N u₀ (Bool.not t) x hx
  let n := Nat.card (EndpointWord S u₀ t)
  let cuts : Finset (Fin (n + 1)) := Finset.univ.filter fun j ↦
    x ∈ cumulativeWordSubspace (P := P) (S := S) (t := t) N j ⊔
      lowerSubspace N L
  have hcuts : cuts.Nonempty := by
    refine ⟨Fin.last n, ?_⟩
    simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cumulativeWordSubspace_last
      (P := P) (S := S) (u := u₀) (t := t)]
    simp
  let j₀ := cuts.min' hcuts
  have hj₀mem : j₀ ∈ cuts := Finset.min'_mem cuts hcuts
  have hj₀ne : j₀ ≠ 0 := by
    intro hj₀zero
    have hmem : x ∈
        cumulativeWordSubspace (P := P) (S := S) (t := t) N j₀ ⊔
          lowerSubspace N L := by
      simpa only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
        using hj₀mem
    rw [hj₀zero] at hmem
    rw [cumulativeWordSubspace_zero
      (P := P) (S := S) (u := u₀) (t := t), bot_sup_eq] at hmem
    exact hxNotLowerL hmem
  obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hj₀ne
  have hjmem : j.succ ∈ cuts := by
    rw [← hj]
    exact hj₀mem
  have hxUpperCut : x ∈
      cumulativeWordSubspace (P := P) (S := S) (t := t) N j.succ ⊔
        lowerSubspace N L :=
    (by
      simpa only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
        using hjmem)
  have hxNotLowerCut : x ∉
      cumulativeWordSubspace (P := P) (S := S) (t := t) N j.castSucc ⊔
        lowerSubspace N L := by
    intro hprev
    have hprevMem : j.castSucc ∈ cuts := by
      simpa only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
        using hprev
    have hle : j.succ ≤ j.castSucc := by
      rw [← hj]
      exact Finset.min'_le cuts _ hprevMem
    exact (not_le_of_gt Fin.castSucc_lt_succ) hle
  let R := orderedWord (P := P) (S := S) (u := u₀) (t := t) j
  refine ⟨L, R, ?_, ?_⟩
  · rw [pairGridUpper, ← cumulativeWordSubspace_succ
      (P := P) (S := S) N j]
    exact ⟨hxUpperCut, hxUpperL⟩
  · intro hgrid
    apply hxNotLowerCut
    rw [pairGridLower, ← cumulativeWordSubspace_castSucc
      (P := P) (S := S) N j] at hgrid
    exact hgrid.1

/-- Cumulative upper endpoints before a cut in lexicographic grid order. -/
noncomputable def cumulativeGridSubspace [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (j : Fin (Nat.card (GridWordIndex S u₀ t) + 1)) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  ⨆ (i : Fin (Nat.card (GridWordIndex S u₀ t))),
    ⨆ (_ : i.val < j.val),
      pairGridUpper N (orderedGridWord (P := P) (S := S) i).1
        (orderedGridWord (P := P) (S := S) i).2

theorem cumulativeGridSubspace_le_lower
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (GridWordIndex S u₀ t))) :
    cumulativeGridSubspace (P := P) (S := S) N j.castSucc ≤
      pairGridLower N (orderedGridWord (P := P) (S := S) j).1
        (orderedGridWord (P := P) (S := S) j).2 := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hij
  exact orderedGridWord_upper_le_lower N hij

theorem pairGridLower_le_cumulativeGridSubspace
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (GridWordIndex S u₀ t))) :
    pairGridLower N (orderedGridWord (P := P) (S := S) j).1
        (orderedGridWord (P := P) (S := S) j).2 ≤
      cumulativeGridSubspace (P := P) (S := S) N j.castSucc := by
  intro x hxLower
  by_cases hxZero : x = 0
  · subst x
    exact Submodule.zero_mem _
  obtain ⟨L, R, hxUpper, hxNotLower⟩ :=
    exists_pairGrid_interval_of_ne_zero
      (P := P) (S := S) N u₀ t x hxZero
  obtain ⟨d, hd⟩ := orderedGridWord_surjective
    (P := P) (S := S) (u₀ := u₀) (t := t) (L, R)
  have hxUpper' : x ∈ pairGridUpper N
      (orderedGridWord (P := P) (S := S) d).1
      (orderedGridWord (P := P) (S := S) d).2 := by
    simpa only [hd] using hxUpper
  have hxNotLower' : x ∉ pairGridLower N
      (orderedGridWord (P := P) (S := S) d).1
      (orderedGridWord (P := P) (S := S) d).2 := by
    simpa only [hd] using hxNotLower
  rcases lt_trichotomy d j with hdj | hdj | hjd
  · apply Submodule.mem_iSup_of_mem d
    exact Submodule.mem_iSup_of_mem hdj hxUpper'
  · subst d
    exact (hxNotLower' hxLower).elim
  · apply (hxNotLower' ?_).elim
    exact orderedGridWord_upper_le_lower N hjd
      ((pairGridLower_le_pairGridUpper N _ _) hxLower)

theorem cumulativeGridSubspace_castSucc
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (GridWordIndex S u₀ t))) :
    cumulativeGridSubspace (P := P) (S := S) N j.castSucc =
      pairGridLower N (orderedGridWord (P := P) (S := S) j).1
        (orderedGridWord (P := P) (S := S) j).2 :=
  le_antisymm (cumulativeGridSubspace_le_lower N j)
    (pairGridLower_le_cumulativeGridSubspace N j)

theorem cumulativeGridSubspace_succ
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (j : Fin (Nat.card (GridWordIndex S u₀ t))) :
    cumulativeGridSubspace (P := P) (S := S) N j.succ =
      pairGridUpper N (orderedGridWord (P := P) (S := S) j).1
        (orderedGridWord (P := P) (S := S) j).2 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hij
    have hijVal : i.val < j.val + 1 := by
      simpa only [Fin.val_succ] using hij
    have hij' : i ≤ j := by omega
    rcases hij'.lt_or_eq with hij' | rfl
    · exact (orderedGridWord_upper_le_lower N hij').trans
        (pairGridLower_le_pairGridUpper N _ _)
    · exact le_rfl
  · apply le_iSup_of_le j
    apply le_iSup_of_le (show j.val < j.succ.val by
      simpa only [Fin.val_succ] using Nat.lt_succ_self j.val)
    exact le_rfl

theorem cumulativeGridSubspace_zero
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k) :
    cumulativeGridSubspace (P := P) (S := S) (u₀ := u₀) (t := t) N 0 =
      (⊥ : Submodule k (N.obj (Opposite.op
        (obj P.toPresentation.relations u₀)))) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    have hi' : i.val < 0 := by simpa only [Fin.val_zero] using hi
    omega
  · exact bot_le

theorem cumulativeGridSubspace_last
    [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] :
    cumulativeGridSubspace (P := P) (S := S) N
        (Fin.last (Nat.card (GridWordIndex S u₀ t))) = ⊤ := by
  apply top_unique
  intro x hx
  by_cases hxZero : x = 0
  · subst x
    exact Submodule.zero_mem _
  obtain ⟨L, R, hxUpper, hxNotLower⟩ :=
    exists_pairGrid_interval_of_ne_zero
      (P := P) (S := S) N u₀ t x hxZero
  obtain ⟨d, hd⟩ := orderedGridWord_surjective
    (P := P) (S := S) (u₀ := u₀) (t := t) (L, R)
  have hxUpper' : x ∈ pairGridUpper N
      (orderedGridWord (P := P) (S := S) d).1
      (orderedGridWord (P := P) (S := S) d).2 := by
    simpa only [hd] using hxUpper
  apply Submodule.mem_iSup_of_mem d
  exact Submodule.mem_iSup_of_mem d.isLt hxUpper'

/-- The finite lexicographic grid filtration at one displayed vertex. -/
noncomputable def orderedGridFiltration [Finite (DetectorIndex S)]
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] :
    MagnitudeConjecture.LinearAlgebra.FiniteFiltration.Filtration k
      (N.obj (Opposite.op (obj P.toPresentation.relations u₀)))
      (Nat.card (GridWordIndex S u₀ t)) where
  subspace := cumulativeGridSubspace (P := P) (S := S) N
  monotone_subspace := by
    intro i j hij
    apply iSup_le
    intro w
    apply iSup_le
    intro hwi
    apply le_iSup_of_le w
    apply le_iSup_of_le (lt_of_lt_of_le hwi hij)
    exact le_rfl
  subspace_zero := cumulativeGridSubspace_zero
    (P := P) (S := S) (u₀ := u₀) (t := t) N
  subspace_last := cumulativeGridSubspace_last
    (P := P) (S := S) (u₀ := u₀) (t := t) N

/-- Every module morphism preserves the finite grid filtrations. -/
theorem orderedGridFiltration_compatible
    [Finite (DetectorIndex S)]
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N) :
    MagnitudeConjecture.LinearAlgebra.FiniteFiltration.Filtration.Compatible
      (f.app (Opposite.op (obj P.toPresentation.relations u₀))).hom
      (orderedGridFiltration (P := P) (S := S) (t := t) M)
      (orderedGridFiltration (P := P) (S := S) (t := t) N) := by
  intro j
  change (cumulativeGridSubspace (P := P) (S := S) (t := t) M j).map
      (f.app (Opposite.op (obj P.toPresentation.relations u₀))).hom ≤
    cumulativeGridSubspace (P := P) (S := S) (t := t) N j
  rw [cumulativeGridSubspace, Submodule.map_iSup]
  apply iSup_le
  intro i
  rw [Submodule.map_iSup]
  apply iSup_le
  intro hij
  apply le_iSup_of_le i
  apply le_iSup_of_le hij
  exact pairGridUpper_map_le f _ _

end MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord
