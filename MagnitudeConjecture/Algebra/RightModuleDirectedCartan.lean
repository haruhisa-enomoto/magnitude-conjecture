import MagnitudeConjecture.Algebra.RightModuleDirected
import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent
import MagnitudeConjecture.CategoryTheory.IrreducibleAbelian
import MagnitudeConjecture.LinearAlgebra.CartanCoordinateEstimate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Extension.Linear
import Mathlib.Order.Preorder.Finite

/-!
# The projective Cartan matrix of a directed module skeleton

This file constructs the integral Cartan matrix indexed by the chosen
indecomposable projective right modules.  A linear extension of the ambient
nonzero-nonisomorphism relation makes this matrix upper unitriangular, so its
inverse is again integral.  It also identifies the coordinate belonging to a
literal primitive idempotent with the already constructed multiplicity
`dim_k Xe`.

The application is local: Appendix A of the frozen manuscript first restricts
the algebra to the support of the middle term of each Auslander--Reiten
sequence.  Accordingly this file exposes a local-support root-pair interface
whose Cartan index may vary with the sequence.  It deliberately contains no
ambient weak-positivity compatibility route.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Reflexive transitive reachability through nonzero nonisomorphisms. -/
def NonzeroNonisomorphismReachability (i j : Fin S.n) : Prop :=
  Relation.ReflTransGen S.NonzeroNonisomorphism i j

/-- Cycle-freeness makes nonzero-nonisomorphism reachability a partial
order. -/
theorem nonzeroNonisomorphismReachability_isPartialOrder
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    IsPartialOrder (Fin S.n) S.NonzeroNonisomorphismReachability where
  refl _ := Relation.ReflTransGen.refl
  trans _ _ _ := Relation.ReflTransGen.trans
  antisymm := by
    intro i j hij hji
    by_contra hne
    have hij' : Relation.TransGen S.NonzeroNonisomorphism i j :=
      (Relation.reflTransGen_iff_eq_or_transGen.mp hij).resolve_left
        (fun hji' ↦ hne hji'.symm)
    exact H i (hij'.trans_left hji)

/-- A chosen linear extension of nonzero-nonisomorphism reachability. -/
@[reducible] noncomputable def directedLinearOrder
    (H : S.HasAcyclicNonzeroNonisomorphisms) : LinearOrder (Fin S.n) := by
  letI : IsPartialOrder (Fin S.n) S.NonzeroNonisomorphismReachability :=
    S.nonzeroNonisomorphismReachability_isPartialOrder H
  let r := (extend_partialOrder S.NonzeroNonisomorphismReachability).choose
  have hr : IsLinearOrder (Fin S.n) r :=
    (extend_partialOrder S.NonzeroNonisomorphismReachability).choose_spec.1
  letI hle : LE (Fin S.n) := ⟨r⟩
  letI hlt : LT (Fin S.n) := ⟨fun i j ↦ r i j ∧ ¬ r j i⟩
  letI hdecLE : DecidableLE (Fin S.n) := Classical.decRel r
  letI hdecEq : DecidableEq (Fin S.n) := Classical.decEq _
  letI hdecLT : DecidableLT (Fin S.n) := Classical.decRel _
  letI hmin : Min (Fin S.n) := minOfLe
  letI hmax : Max (Fin S.n) := maxOfLe
  letI hord : Ord (Fin S.n) := ⟨fun i j ↦ compareOfLessAndEq i j⟩
  exact
    { le := r
      lt := fun i j ↦ r i j ∧ ¬ r j i
      le_refl := hr.refl
      le_trans := hr.trans
      lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl
      le_antisymm := hr.antisymm
      min := minOfLe.min
      max := maxOfLe.max
      compare := fun i j ↦ compareOfLessAndEq i j
      le_total := hr.total
      toDecidableLE := hdecLE
      toDecidableEq := hdecEq
      toDecidableLT := hdecLT
      min_def := fun _ _ ↦ rfl
      max_def := fun _ _ ↦ rfl
      compare_eq_compareOfLessAndEq := fun _ _ ↦ rfl }

/-- The chosen linear order extends directed reachability. -/
theorem le_directedLinearOrder_of_reachable
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {i j : Fin S.n} (h : S.NonzeroNonisomorphismReachability i j) :
    (S.directedLinearOrder H).le i j := by
  letI : IsPartialOrder (Fin S.n) S.NonzeroNonisomorphismReachability :=
    S.nonzeroNonisomorphismReachability_isPartialOrder H
  exact (extend_partialOrder
    S.NonzeroNonisomorphismReachability).choose_spec.2 i j h

/-- In the chosen directed order, every nonzero off-diagonal map points
strictly forward. -/
theorem directedLinearOrder_hom_lt
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {i j : Fin S.n} (f : S.fgObj i ⟶ S.fgObj j)
    (hf : f ≠ 0) (hij : i ≠ j) :
    (S.directedLinearOrder H).lt i j := by
  have hfnot : ¬ IsIso f := by
    intro hfiso
    letI : IsIso f := hfiso
    exact hij (S.fgObj_skeletal ⟨asIso f⟩)
  let O := S.directedLinearOrder H
  have hle : O.le i j :=
    S.le_directedLinearOrder_of_reachable H
      (Relation.ReflTransGen.single ⟨f, hf, hfnot⟩)
  apply (O.lt_iff_le_not_ge i j).2
  refine ⟨hle, ?_⟩
  intro hji
  exact hij (O.le_antisymm i j hle hji)

/-- In the directed order there are no morphisms strictly backwards. -/
theorem hom_eq_zero_of_lt
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    ∀ {i j : Fin S.n}, (S.directedLinearOrder H).lt j i →
      ∀ f : S.fgObj i ⟶ S.fgObj j, f = 0 := by
  intro i j hji f
  by_contra hf
  have hne : i ≠ j := by
    intro hij
    subst j
    have hstrict := ((S.directedLinearOrder H).lt_iff_le_not_ge i i).1 hji
    exact hstrict.2 hstrict.1
  have hij := S.directedLinearOrder_hom_lt H f hf hne
  let O := S.directedLinearOrder H
  have hij' := (O.lt_iff_le_not_ge i j).1 hij
  have hji' := (O.lt_iff_le_not_ge j i).1 hji
  exact hij'.2 hji'.1

/-- Labels of the chosen indecomposable projective right modules.  This is a
structure, rather than a subtype abbreviation, so its proof-relevant directed
order cannot accidentally reuse the numerical order on `Fin S.n`. -/
structure ProjectiveLabel where
  label : Fin S.n
  projective : Projective (S.fgObj label)

/-- Labels of the chosen indecomposable injective right modules. -/
structure InjectiveLabel where
  label : Fin S.n
  injective : Injective (S.fgObj label)

/-- The structured projective labels are equivalent to the corresponding
subtype. -/
def projectiveLabelEquivSubtype :
    S.ProjectiveLabel ≃ {i : Fin S.n // Projective (S.fgObj i)} where
  toFun i := ⟨i.label, i.projective⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance projectiveLabelFintype : Fintype S.ProjectiveLabel := by
  letI : DecidablePred (fun i : Fin S.n ↦ Projective (S.fgObj i)) :=
    Classical.decPred _
  exact Fintype.ofEquiv _ S.projectiveLabelEquivSubtype.symm

/-- The simple-coordinate support of a finitely generated right module,
indexed by the chosen indecomposable projectives. -/
def projectiveSupport (X : RightModule.FinitelyGeneratedCategory A) :
    Set S.ProjectiveLabel :=
  {p | ∃ f : S.fgObj p.label ⟶ X, f ≠ 0}

/-- A monomorphism can only enlarge projective support. -/
theorem projectiveSupport_mono
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hf : Mono f) : S.projectiveSupport X ⊆ S.projectiveSupport Y := by
  letI : Mono f := hf
  rintro p ⟨g, hg⟩
  refine ⟨g ≫ f, ?_⟩
  intro hzero
  apply hg
  rw [← cancel_mono f]
  simpa using hzero

/-- An epimorphism can only shrink projective support. -/
theorem projectiveSupport_epi
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hf : Epi f) : S.projectiveSupport Y ⊆ S.projectiveSupport X := by
  letI : Epi f := hf
  rintro p ⟨g, hg⟩
  letI : Projective (S.fgObj p.label) := p.projective
  obtain ⟨h, hh⟩ := Projective.factors g f
  refine ⟨h, ?_⟩
  intro hzero
  apply hg
  rw [← hh, hzero, zero_comp]

/-- Isomorphic finitely generated modules have identical projective support. -/
theorem projectiveSupport_eq_of_iso
    {X Y : RightModule.FinitelyGeneratedCategory A} (e : X ≅ Y) :
    S.projectiveSupport X = S.projectiveSupport Y := by
  apply Set.Subset.antisymm
  · exact S.projectiveSupport_mono e.hom inferInstance
  · exact S.projectiveSupport_mono e.inv inferInstance

/-- Projective support of a finite biproduct is the union of the supports of
its summands. -/
theorem mem_projectiveSupport_biproduct_iff
    {J : Type} [Fintype J]
    (F : J → RightModule.FinitelyGeneratedCategory A)
    (p : S.ProjectiveLabel) :
    p ∈ S.projectiveSupport (⨁ F) ↔
      ∃ j : J, p ∈ S.projectiveSupport (F j) := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    by_contra hnone
    push Not at hnone
    apply hf
    apply biproduct.hom_ext
    intro j
    simp only [zero_comp]
    by_contra hcomponent
    exact hnone j ⟨f ≫ biproduct.π F j, hcomponent⟩
  · rintro ⟨j, f, hf⟩
    refine ⟨f ≫ biproduct.ι F j, ?_⟩
    intro hzero
    apply hf
    have hcomponent := congrArg
      (fun q ↦ q ≫ biproduct.π F j) hzero
    simpa [Category.assoc] using hcomponent

/-- Regard the kernel map of the chosen nonprojective right almost-split
sequence, with the same displayed middle decomposition, as a minimal left
almost-split decomposition. -/
def rightSequenceLeftDecomposition
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.almostSplitSkeleton.MinimalLeftAlmostSplitDecomposition
      (S.rightTranslationLabel z) :=
  let B := S.minimalRightAlmostSplitAt z.1
  { middle := B.middle
    finiteLength := B.finiteLength
    map := S.rightKernelMap z
    leftAlmostSplit := S.rightKernelMap_leftAlmostSplit z
    leftMinimal := S.rightKernelMap_leftMinimal z
    index := B.index
    label := B.label
    decomposition := B.decomposition }

/-- The chosen middle-term decomposition represents projective support as
the union of the supports of its indecomposable summands. -/
theorem mem_projectiveSupport_rightMiddle_iff
    (z : Fin S.n) (p : S.ProjectiveLabel) :
    p ∈ S.projectiveSupport (S.minimalRightAlmostSplitAt z).middle ↔
      ∃ t : (S.minimalRightAlmostSplitAt z).index,
        p ∈ S.projectiveSupport
          (S.fgObj ((S.minimalRightAlmostSplitAt z).label t)) := by
  let B := S.minimalRightAlmostSplitAt z
  letI : Fintype B.index := FintypeCat.fintype
  rw [S.projectiveSupport_eq_of_iso B.decomposition]
  exact S.mem_projectiveSupport_biproduct_iff
    (fun t : B.index ↦ S.fgObj (B.label t)) p

/-- Both endpoint supports of an almost-split sequence lie in the support of
its middle term. -/
theorem rightSequence_endpointSupport_subset_middle
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.projectiveSupport (S.fgObj (S.rightTranslationLabel z)) ⊆
        S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle ∧
      S.projectiveSupport (S.fgObj z.1) ⊆
        S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle := by
  let B := S.minimalRightAlmostSplitAt z.1
  constructor
  · rintro p ⟨g, hg⟩
    refine ⟨g ≫ S.rightKernelMap z, ?_⟩
    intro hzero
    apply hg
    haveI : Mono (S.rightKernelMap z) := by
      change Mono
        ((S.rightTranslationKernelIso z).inv ≫
          kernel.ι (S.minimalRightAlmostSplitAt z.1).map)
      infer_instance
    have hc : g ≫ S.rightKernelMap z =
        (0 : S.fgObj p.label ⟶
          S.fgObj (S.rightTranslation z).1) ≫ S.rightKernelMap z := by
      simpa only [zero_comp] using hzero
    exact (cancel_mono (S.rightKernelMap z)).mp hc
  · rintro p ⟨g, hg⟩
    letI : Projective (S.fgObj p.label) := p.projective
    let hepi : Epi B.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton B.map B.rightAlmostSplit z.2
    obtain ⟨h, hh⟩ := @Projective.factors
      (RightModule.FinitelyGeneratedCategory A) inferInstance
      (S.fgObj p.label) p.projective B.middle (S.fgObj z.1)
      g B.map hepi
    refine ⟨h, ?_⟩
    intro hzero
    apply hg
    rw [← hh, hzero, zero_comp]

/-- If one left component of an Auslander--Reiten sequence is monic, every
different right component is monic.  This is the exactness step in Ringel's
support argument. -/
theorem rightComponent_mono_of_ne_of_leftComponent_mono
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (i j : (S.minimalRightAlmostSplitAt z.1).index) (hji : j ≠ i)
    (hi : Mono ((S.rightSequenceLeftDecomposition z).component
      S.almostSplitSkeleton i)) :
    Mono ((S.minimalRightAlmostSplitAt z.1).component
      S.almostSplitSkeleton j) := by
  let B := S.minimalRightAlmostSplitAt z.1
  let F : B.index → FGModuleCat Aᵐᵒᵖ :=
    fun t ↦ S.almostSplitSkeleton.obj (B.label t)
  let p : B.middle ⟶ F i :=
    B.decomposition.hom ≫ biproduct.π F i
  let inc : F j ⟶ B.middle :=
    biproduct.ι F j ≫ B.decomposition.inv
  have hweak : ∀ (W : RightModule.FinitelyGeneratedCategory A)
      (q : W ⟶ B.middle), q ≫ B.map = 0 →
        ∃ l : W ⟶ S.fgObj (S.rightTranslationLabel z),
          l ≫ S.rightKernelMap z = q := by
    intro W q hq
    refine ⟨kernel.lift B.map q hq ≫
      (S.rightTranslationKernelIso z).hom, ?_⟩
    change (kernel.lift B.map q hq ≫
      (S.rightTranslationKernelIso z).hom) ≫
        ((S.rightTranslationKernelIso z).inv ≫
          kernel.ι B.map) = q
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact kernel.lift_ι B.map q hq
  have hfp : Mono (S.rightKernelMap z ≫ p) := by
    change Mono ((S.rightSequenceLeftDecomposition z).component
      S.almostSplitSkeleton i)
    exact hi
  have hinc : Mono inc := by
    dsimp only [inc]
    infer_instance
  have hincp : inc ≫ p = 0 := by
    calc
      inc ≫ p = biproduct.ι F j ≫
          (B.decomposition.inv ≫ B.decomposition.hom ≫
            biproduct.π F i) := by
        simp only [inc, p, Category.assoc]
      _ = biproduct.ι F j ≫ biproduct.π F i := by
        rw [← Category.assoc B.decomposition.inv
          B.decomposition.hom (biproduct.π F i),
          B.decomposition.inv_hom_id, Category.id_comp]
      _ = 0 := biproduct.ι_π_ne F hji
  change Mono (inc ≫ B.map)
  exact mono_comp_of_weakKernel_component hweak hfp hinc hincp

/-- Ringel's support lemma for the chosen Auslander--Reiten sequence: the
support of the source, the endpoint, or one displayed indecomposable middle
summand contains the supports of all the other terms. -/
theorem rightSequence_has_support_dominating_term
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    ((∀ t : (S.minimalRightAlmostSplitAt z.1).index,
        S.projectiveSupport
            (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label t)) ⊆
          S.projectiveSupport
            (S.fgObj (S.rightTranslationLabel z))) ∧
      S.projectiveSupport (S.fgObj z.1) ⊆
        S.projectiveSupport
          (S.fgObj (S.rightTranslationLabel z))) ∨
    ((∀ t : (S.minimalRightAlmostSplitAt z.1).index,
        S.projectiveSupport
            (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label t)) ⊆
          S.projectiveSupport (S.fgObj z.1)) ∧
      S.projectiveSupport
          (S.fgObj (S.rightTranslationLabel z)) ⊆
        S.projectiveSupport (S.fgObj z.1)) ∨
    ∃ i : (S.minimalRightAlmostSplitAt z.1).index,
      S.projectiveSupport
          (S.fgObj (S.rightTranslationLabel z)) ⊆
        S.projectiveSupport
          (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label i)) ∧
      S.projectiveSupport (S.fgObj z.1) ⊆
        S.projectiveSupport
          (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label i)) ∧
      ∀ t : (S.minimalRightAlmostSplitAt z.1).index,
        S.projectiveSupport
            (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label t)) ⊆
          S.projectiveSupport
            (S.fgObj ((S.minimalRightAlmostSplitAt z.1).label i)) := by
  classical
  let B := S.minimalRightAlmostSplitAt z.1
  let L := S.rightSequenceLeftDecomposition z
  let σ := S.almostSplitSkeleton
  have hendpoint := S.rightSequence_endpointSupport_subset_middle z
  by_cases hleft : ∀ t : B.index, Epi (L.component σ t)
  · left
    constructor
    · intro t
      exact S.projectiveSupport_epi (L.component σ t) (hleft t)
    · intro p hp
      have hpmiddle := hendpoint.2 hp
      rw [S.mem_projectiveSupport_rightMiddle_iff z.1 p] at hpmiddle
      obtain ⟨t, hpt⟩ := hpmiddle
      exact (S.projectiveSupport_epi (L.component σ t) (hleft t)) hpt
  · obtain ⟨i, hiNotEpi⟩ := not_forall.mp hleft
    have hiMono : Mono (L.component σ i) :=
      (L.component_mono_or_epi σ i).resolve_right hiNotEpi
    by_cases hright : ∀ t : B.index, Mono (B.component σ t)
    · right
      left
      constructor
      · intro t
        exact S.projectiveSupport_mono (B.component σ t) (hright t)
      · intro p hp
        have hpmiddle := hendpoint.1 hp
        rw [S.mem_projectiveSupport_rightMiddle_iff z.1 p] at hpmiddle
        obtain ⟨t, hpt⟩ := hpmiddle
        exact (S.projectiveSupport_mono (B.component σ t) (hright t)) hpt
    · obtain ⟨j, hjNotMono⟩ := not_forall.mp hright
      have hjEpi : Epi (B.component σ j) :=
        (B.component_mono_or_epi σ j).resolve_left hjNotMono
      have hji : j = i := by
        by_contra hne
        have hjMono : Mono (B.component σ j) :=
          S.rightComponent_mono_of_ne_of_leftComponent_mono
            z i j hne hiMono
        letI : Mono (B.component σ j) := hjMono
        letI : Epi (B.component σ j) := hjEpi
        letI : IsIso (B.component σ j) :=
          isIso_of_mono_of_epi (B.component σ j)
        exact (B.component_irreducible σ j).not_isSplitMono inferInstance
      subst j
      right
      right
      refine ⟨i,
        S.projectiveSupport_mono (L.component σ i) hiMono,
        S.projectiveSupport_epi (B.component σ i) hjEpi, ?_⟩
      intro t
      by_cases hti : t = i
      · subst t
        exact Set.Subset.rfl
      · exact
          (S.projectiveSupport_mono (B.component σ t)
            (S.rightComponent_mono_of_ne_of_leftComponent_mono
              z i t hti hiMono)).trans
            (S.projectiveSupport_epi (B.component σ i) hjEpi)

/-- Exactness identifies the support of the middle term with the union of the
two endpoint supports. -/
theorem rightSequence_middleSupport_eq_union_endpoints
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle =
      S.projectiveSupport (S.fgObj (S.rightTranslationLabel z)) ∪
        S.projectiveSupport (S.fgObj z.1) := by
  let B := S.minimalRightAlmostSplitAt z.1
  apply Set.Subset.antisymm
  · rintro p ⟨f, hf⟩
    by_cases hfg : f ≫ B.map = 0
    · left
      let l : S.fgObj p.label ⟶
          S.fgObj (S.rightTranslationLabel z) :=
        kernel.lift B.map f hfg ≫ (S.rightTranslationKernelIso z).hom
      refine ⟨l, ?_⟩
      have hfactor : l ≫ S.rightKernelMap z = f := by
        change (kernel.lift B.map f hfg ≫
          (S.rightTranslationKernelIso z).hom) ≫
            ((S.rightTranslationKernelIso z).inv ≫
              kernel.ι B.map) = f
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        exact kernel.lift_ι B.map f hfg
      intro hlzero
      apply hf
      rw [← hfactor, hlzero, zero_comp]
    · right
      exact ⟨f ≫ B.map, hfg⟩
  · rintro p (hp | hp)
    · exact (S.rightSequence_endpointSupport_subset_middle z).1 hp
    · exact (S.rightSequence_endpointSupport_subset_middle z).2 hp

/-- One actual skeleton label occurring as the source, endpoint, or a middle
summand is sincere on the support of the almost-split middle term. -/
theorem exists_rightSequence_supportSincere_label
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    ∃ w : Fin S.n,
      S.projectiveSupport (S.fgObj w) =
          S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle ∧
        (w = S.rightTranslationLabel z ∨ w = z.1 ∨
          ∃ i : (S.minimalRightAlmostSplitAt z.1).index,
            w = (S.minimalRightAlmostSplitAt z.1).label i) := by
  rcases S.rightSequence_has_support_dominating_term z with
    hsource | htarget | ⟨i, _hsource, _htarget, hmiddle⟩
  · refine ⟨S.rightTranslationLabel z,
      Set.Subset.antisymm
        (S.rightSequence_endpointSupport_subset_middle z).1 ?_, Or.inl rfl⟩
    intro p hp
    rw [S.mem_projectiveSupport_rightMiddle_iff z.1 p] at hp
    obtain ⟨t, hpt⟩ := hp
    exact hsource.1 t hpt
  · refine ⟨z.1,
      Set.Subset.antisymm
        (S.rightSequence_endpointSupport_subset_middle z).2 ?_,
      Or.inr (Or.inl rfl)⟩
    intro p hp
    rw [S.mem_projectiveSupport_rightMiddle_iff z.1 p] at hp
    obtain ⟨t, hpt⟩ := hp
    exact htarget.1 t hpt
  · refine ⟨(S.minimalRightAlmostSplitAt z.1).label i,
      Set.Subset.antisymm ?_ ?_, Or.inr (Or.inr ⟨i, rfl⟩)⟩
    · intro p hp
      exact (S.mem_projectiveSupport_rightMiddle_iff z.1 p).2 ⟨i, hp⟩
    · intro p hp
      rw [S.mem_projectiveSupport_rightMiddle_iff z.1 p] at hp
      obtain ⟨t, hpt⟩ := hp
      exact hmiddle t hpt

noncomputable instance projectiveLabelDecidableEq :
    DecidableEq S.ProjectiveLabel := Classical.decEq _

/-- The directed order restricted to the indecomposable projective labels. -/
@[reducible] noncomputable def projectiveDirectedLinearOrder
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    LinearOrder S.ProjectiveLabel :=
  @LinearOrder.lift' S.ProjectiveLabel (Fin S.n)
    (S.directedLinearOrder H) ProjectiveLabel.label (by
      intro i j hij
      cases i
      cases j
      cases hij
      rfl)

/-- The integral Cartan matrix, with entry `dim_k Hom(P_i,P_j)`. -/
def projectiveCartanMatrix :
    Matrix S.ProjectiveLabel S.ProjectiveLabel ℤ :=
  fun i j ↦ Module.finrank k (S.fgObj i.label ⟶ S.fgObj j.label)

/-- The projective Cartan matrix is entrywise nonnegative. -/
theorem projectiveCartanMatrix_nonnegative (i j : S.ProjectiveLabel) :
    0 ≤ S.projectiveCartanMatrix i j := by
  simp [projectiveCartanMatrix]

/-- In the directed linear extension, the projective Cartan matrix is upper
triangular. -/
theorem projectiveCartanMatrix_blockTriangular
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    letI := S.projectiveDirectedLinearOrder H
    S.projectiveCartanMatrix.BlockTriangular id := by
  letI := S.projectiveDirectedLinearOrder H
  intro i j hji
  have hji' : (S.directedLinearOrder H).lt j.label i.label := hji
  change (Module.finrank k
    (S.fgObj i.label ⟶ S.fgObj j.label) : ℤ) = 0
  have hzero : ∀ f : S.fgObj i.label ⟶ S.fgObj j.label, f = 0 :=
    S.hom_eq_zero_of_lt H hji'
  haveI : Subsingleton (S.fgObj i.label ⟶ S.fgObj j.label) :=
    ⟨fun f g ↦ (hzero f).trans (hzero g).symm⟩
  exact_mod_cast (Module.finrank_zero_of_subsingleton :
    Module.finrank k (S.fgObj i.label ⟶ S.fgObj j.label) = 0)

/-- Directedness and algebraic closedness give unit diagonal. -/
theorem projectiveCartanMatrix_diagonal [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) (i : S.ProjectiveLabel) :
    S.projectiveCartanMatrix i i = 1 := by
  change (Module.finrank k
    (S.fgObj i.label ⟶ S.fgObj i.label) : ℤ) = 1
  exact_mod_cast H.finrank_endomorphism_eq_one S i.label

/-- The projective Cartan determinant is one. -/
theorem projectiveCartanMatrix_det [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.projectiveCartanMatrix.det = 1 := by
  letI := S.projectiveDirectedLinearOrder H
  classical
  rw [Matrix.det_of_upperTriangular
    (S.projectiveCartanMatrix_blockTriangular H)]
  simp [S.projectiveCartanMatrix_diagonal H]

/-- The integral inverse of the projective Cartan matrix. -/
def projectiveCartanInverse :
    Matrix S.ProjectiveLabel S.ProjectiveLabel ℤ :=
  S.projectiveCartanMatrix⁻¹

/-- The displayed integral inverse is a left inverse. -/
theorem projectiveCartanInverse_mul [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.projectiveCartanInverse * S.projectiveCartanMatrix = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [S.projectiveCartanMatrix_det H]
  exact isUnit_one

/-- The displayed integral inverse is a right inverse. -/
theorem projectiveCartan_mul_inverse [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.projectiveCartanMatrix * S.projectiveCartanInverse = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [S.projectiveCartanMatrix_det H]
  exact isUnit_one

/-- The projective-Hom dimension vector of a chosen indecomposable module. -/
def projectiveHomVector (x : Fin S.n) : S.ProjectiveLabel → ℤ :=
  fun p ↦ Module.finrank k (S.fgObj p.label ⟶ S.fgObj x)

/-- Projective-Hom dimension vectors are coordinatewise nonnegative. -/
theorem projectiveHomVector_nonnegative (x : Fin S.n) (p : S.ProjectiveLabel) :
    0 ≤ S.projectiveHomVector x p := by
  simp [projectiveHomVector]

/-- A retract of a projective object is projective. -/
theorem projective_of_retract_of_projective
    {P Q : RightModule.FinitelyGeneratedCategory A}
    (hP : Projective P) (i : Q ⟶ P) (r : P ⟶ Q)
    (hir : i ≫ r = 𝟙 Q) : Projective Q := by
  letI : Projective P := hP
  constructor
  intro X E f e hepi
  letI : Epi e := hepi
  obtain ⟨l, hl⟩ := Projective.factors (r ≫ f) e
  refine ⟨i ≫ l, ?_⟩
  rw [Category.assoc, hl, ← Category.assoc, hir, Category.id_comp]

/-- Every chosen indecomposable receives a nonzero map from a chosen
indecomposable projective. -/
theorem exists_projectiveLabel_hom_ne_zero (x : Fin S.n) :
    ∃ p : S.ProjectiveLabel,
      ∃ f : S.fgObj p.label ⟶ S.fgObj x, f ≠ 0 := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let P := Projective.over (S.fgObj x)
  let q := Projective.π (S.fgObj x)
  have hq : q ≠ 0 := by
    intro hqzero
    have hid : 𝟙 (S.fgObj x) = 0 := by
      apply (cancel_epi q).1
      rw [hqzero]
      simp
    exact (S.fgObj_indecomposable x).1 ((IsZero.iff_id_eq_zero _).2 hid)
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition P
  have hcomponent : ∃ t : Fin n,
      biproduct.ι (fun s ↦ S.fgObj (label s)) t ≫ e.inv ≫ q ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hq
    apply (cancel_epi e.inv).1
    apply biproduct.hom_ext'
    intro t
    simpa [Category.assoc] using hnone t
  obtain ⟨t, ht⟩ := hcomponent
  let i : S.fgObj (label t) ⟶ P :=
    biproduct.ι (fun s ↦ S.fgObj (label s)) t ≫ e.inv
  let r : P ⟶ S.fgObj (label t) :=
    e.hom ≫ biproduct.π (fun s ↦ S.fgObj (label s)) t
  have hir : i ≫ r = 𝟙 (S.fgObj (label t)) := by
    simp [i, r]
  have hp : Projective (S.fgObj (label t)) :=
    projective_of_retract_of_projective
      (inferInstance : Projective P) i r hir
  exact ⟨⟨label t, hp⟩, ⟨i ≫ q, by simpa [i, Category.assoc] using ht⟩⟩

/-- Every projective-Hom dimension vector is a positive integral vector. -/
theorem projectiveHomVector_positive (x : Fin S.n) :
    MagnitudeConjecture.CartanCoordinate.IsPositive
      (S.projectiveHomVector x) := by
  constructor
  · exact S.projectiveHomVector_nonnegative x
  · obtain ⟨p, f, hf⟩ := S.exists_projectiveLabel_hom_ne_zero x
    intro hzero
    have hcoord := congrFun hzero p
    haveI : Nontrivial (S.fgObj p.label ⟶ S.fgObj x) :=
      ⟨⟨f, 0, hf⟩⟩
    have hpos : 0 < S.projectiveHomVector x p := by
      change 0 < (Module.finrank k
        (S.fgObj p.label ⟶ S.fgObj x) : ℤ)
      exact_mod_cast (Module.finrank_pos (R := k)
        (M := S.fgObj p.label ⟶ S.fgObj x))
    rw [Pi.zero_apply] at hcoord
    omega

/-- An irreducible morphism points strictly forward in the chosen directed
linear order. -/
theorem directedLinearOrder_lt_of_irreducible
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {i j : Fin S.n}
    (hij : HasIrreducibleMorphism (S.fgObj i) (S.fgObj j)) :
    (S.directedLinearOrder H).lt i j := by
  obtain ⟨f, hf⟩ := hij
  have hlabels : i ≠ j := by
    intro hEq
    subst j
    exact S.almostSplitSkeleton.hasNoIrreducibleEndomorphism_obj i ⟨f, hf⟩
  have hf0 : f ≠ 0 := by
    intro hzero
    have hnotSquare :=
      ((S.almostSplitSkeleton
        |>.isIrreducibleMorphism_iff_mem_radical_not_mem_radicalSquare f).1 hf).2
    apply hnotSquare
    rw [hzero]
    exact AddSubgroup.zero_mem _
  exact S.directedLinearOrder_hom_lt H f hf0 hlabels

/-- Every nonzero morphism points weakly forward in the chosen directed
order.  This version intentionally permits coincident labels, which is what
the support-algebra cycle argument in Appendix A needs. -/
theorem directedLinearOrder_le_of_hom_ne_zero
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {i j : Fin S.n} (f : S.fgObj i ⟶ S.fgObj j) (hf : f ≠ 0) :
    (S.directedLinearOrder H).le i j := by
  let O := S.directedLinearOrder H
  by_cases hij : i = j
  · subst j
    exact O.le_refl i
  · exact (O.lt_iff_le_not_ge i j).1
      (S.directedLinearOrder_hom_lt H f hf hij) |>.1

/-- A closed triangle of nonzero maps cannot contain an irreducible edge in
a directed skeleton.  The weak inequalities automatically absorb coincident
terms, formalizing the manuscript's instruction to omit isomorphism edges
from the displayed cycle. -/
theorem HasAcyclicNonzeroNonisomorphisms.no_nonzero_triangle_of_irreducible
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {i j l : Fin S.n}
    (hij : HasIrreducibleMorphism (S.fgObj i) (S.fgObj j))
    (g : S.fgObj j ⟶ S.fgObj l) (hg : g ≠ 0)
    (h : S.fgObj l ⟶ S.fgObj i) (hh : h ≠ 0) : False := by
  let O := S.directedLinearOrder H
  have hij' : O.lt i j := S.directedLinearOrder_lt_of_irreducible H hij
  have hjl : O.le j l := S.directedLinearOrder_le_of_hom_ne_zero H g hg
  have hli : O.le l i := S.directedLinearOrder_le_of_hom_ne_zero H h hh
  have hnotji : ¬ O.le j i := (O.lt_iff_le_not_ge i j).1 hij' |>.2
  exact hnotji (O.le_trans j l i hjl hli)

/-- A primitive idempotent determines its corresponding projective Cartan
index. -/
def primitiveSourceProjectiveLabel {e : A}
    (D : RightModule.PrimitiveIdempotentData e) : S.ProjectiveLabel :=
  ⟨S.primitiveSourceLabel D, S.primitiveSource_projective D⟩

/-- A primitive idempotent determines its corresponding injective label. -/
def primitiveSinkInjectiveLabel {e : A}
    (D : RightModule.PrimitiveIdempotentData e) : S.InjectiveLabel :=
  ⟨S.primitiveSinkLabel D, S.primitiveSink_injective D⟩

/-- The categorical form of the schurian corner bound used at both ambient
boundaries in Appendix A. -/
structure SchurianBoundaryData : Prop where
  projectiveHom_le_one : ∀ p q : S.ProjectiveLabel,
    Module.finrank k (S.fgObj p.label ⟶ S.fgObj q.label) ≤ 1
  injectiveHom_le_one : ∀ i j : S.InjectiveLabel,
    Module.finrank k (S.fgObj i.label ⟶ S.fgObj j.label) ≤ 1

/-- The distinguished projective-Hom coordinate is exactly the literal
primitive multiplicity `dim_k Xe`. -/
theorem projectiveHomVector_primitiveSource {e : A}
    (D : RightModule.PrimitiveIdempotentData e) (x : Fin S.n) :
    S.projectiveHomVector x (S.primitiveSourceProjectiveLabel D) =
      S.primitiveMultiplicity D x := by
  change (Module.finrank k
    (S.fgObj (S.primitiveSourceLabel D) ⟶ S.fgObj x) : ℤ) =
      (S.primitiveMultiplicity D x : ℤ)
  exact_mod_cast (S.primitiveMultiplicity_eq_sourceHom D x).symm

/-- The schurian projective Hom bound gives the projective clause of the
primitive coordinate estimate. -/
theorem SchurianBoundaryData.primitiveMultiplicity_projective_le_one
    (B : S.SchurianBoundaryData) {e : A}
    (D : RightModule.PrimitiveIdempotentData e) (x : Fin S.n)
    (hx : Projective (S.fgObj x)) :
    S.primitiveMultiplicity D x ≤ 1 := by
  rw [S.primitiveMultiplicity_eq_sourceHom D x]
  exact B.projectiveHom_le_one
    (S.primitiveSourceProjectiveLabel D) ⟨x, hx⟩

/-- The dual schurian injective Hom bound gives the injective clause of the
primitive coordinate estimate. -/
theorem SchurianBoundaryData.primitiveMultiplicity_injective_le_one
    (B : S.SchurianBoundaryData) {e : A}
    (D : RightModule.PrimitiveIdempotentData e) (x : Fin S.n)
    (hx : Injective (S.fgObj x)) :
    S.primitiveMultiplicity D x ≤ 1 := by
  rw [S.primitiveMultiplicity_eq_sinkHom D x]
  exact B.injectiveHom_le_one ⟨x, hx⟩
    (S.primitiveSinkInjectiveLabel D)

/-- The literal projective Cartan matrix of a directed support algebra,
together with weak positivity of its Euler form, gives the numerical Cartan
datum used in Appendix A. -/
def supportWeaklyPositiveCartanData [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hweak : ∀ x,
      MagnitudeConjecture.CartanCoordinate.IsPositive x →
        1 ≤ MagnitudeConjecture.CartanCoordinate.quadraticForm
          S.projectiveCartanInverse x) :
    MagnitudeConjecture.CartanCoordinate.WeaklyPositiveCartanData
      (ι := S.ProjectiveLabel) where
  C := S.projectiveCartanMatrix
  Cinv := S.projectiveCartanInverse
  inverse_mul := S.projectiveCartanInverse_mul H
  mul_inverse := S.projectiveCartan_mul_inverse H
  diagonal := S.projectiveCartanMatrix_diagonal H
  nonnegative := S.projectiveCartanMatrix_nonnegative
  weaklyPositive := hweak

/-- Concrete Cartan/root/Coxeter data for the two endpoints of one
Auslander--Reiten sequence after passage to its middle-term support algebra.

The skeleton `S` here is the skeleton of that support algebra.  In particular,
this is not an ambient compatibility interface: each sequence may instantiate
the structure with a different algebra and skeleton. -/
structure SupportCartanRootPairData [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) (z x : Fin S.n) : Prop where
  weaklyPositive : ∀ v,
    MagnitudeConjecture.CartanCoordinate.IsPositive v →
      1 ≤ MagnitudeConjecture.CartanCoordinate.quadraticForm
        S.projectiveCartanInverse v
  source_root : MagnitudeConjecture.CartanCoordinate.quadraticForm
    S.projectiveCartanInverse (S.projectiveHomVector z) = 1
  translated_root : MagnitudeConjecture.CartanCoordinate.quadraticForm
    S.projectiveCartanInverse (S.projectiveHomVector x) = 1
  coxeter_translate : S.projectiveHomVector x =
    Matrix.vecMul (S.projectiveHomVector z)
      (MagnitudeConjecture.CartanCoordinate.coxeterMatrix
        S.projectiveCartanMatrix S.projectiveCartanInverse)

/-- Actual support-algebra Cartan data produces the local numerical root-pair
package once the chosen simple coordinate has been identified at both
endpoints. -/
def SupportCartanRootPairData.coordinateData [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) {z x : Fin S.n}
    (R : S.SupportCartanRootPairData H z x) (p : S.ProjectiveLabel)
    {a b : ℤ} (ha : S.projectiveHomVector z p = a)
    (hb : S.projectiveHomVector x p = b) :
    MagnitudeConjecture.CartanCoordinate.LocalRootPairCoordinateData a b where
  index := S.ProjectiveLabel
  cartan := S.supportWeaklyPositiveCartanData H R.weaklyPositive
  root := S.projectiveHomVector z
  root_positive := S.projectiveHomVector_positive z
  root_quadraticForm := R.source_root
  transform_positive := by
    change MagnitudeConjecture.CartanCoordinate.IsPositive
      (Matrix.vecMul (S.projectiveHomVector z)
        (MagnitudeConjecture.CartanCoordinate.coxeterMatrix
          S.projectiveCartanMatrix S.projectiveCartanInverse))
    rw [← R.coxeter_translate]
    exact S.projectiveHomVector_positive x
  transform_quadraticForm := by
    change MagnitudeConjecture.CartanCoordinate.quadraticForm
      S.projectiveCartanInverse
        (Matrix.vecMul (S.projectiveHomVector z)
          (MagnitudeConjecture.CartanCoordinate.coxeterMatrix
            S.projectiveCartanMatrix S.projectiveCartanInverse)) = 1
    rw [← R.coxeter_translate]
    exact R.translated_root
  coordinate := p
  root_coordinate := ha
  transform_coordinate := by
    change Matrix.vecMul (S.projectiveHomVector z)
      (MagnitudeConjecture.CartanCoordinate.coxeterMatrix
        S.projectiveCartanMatrix S.projectiveCartanInverse) p = b
    rw [← R.coxeter_translate]
    exact hb

/-- The concrete middle-term support-algebra data used by Appendix A.

For each ambient nonprojective label it records the support algebra, its
duplicate-free finite indecomposable skeleton, the two restricted endpoint
labels, and the projective coordinate corresponding to the selected simple.
The Cartan/root/Coxeter field uses the actual projective Cartan matrix of that
support skeleton. -/
structure MiddleSupportCartanData [IsAlgClosed k]
    {e : A} (D : RightModule.PrimitiveIdempotentData e) where
  supportAlgebra : {x : Fin S.n // ¬ Projective (S.fgObj x)} → Type u
  [supportRing : ∀ z, Ring (supportAlgebra z)]
  [supportAlgebraMap : ∀ z, Algebra k (supportAlgebra z)]
  [supportFiniteDimensional : ∀ z, FiniteDimensional k (supportAlgebra z)]
  [supportNoetherian : ∀ z, IsNoetherianRing (supportAlgebra z)ᵐᵒᵖ]
  skeleton : ∀ z, RightModule.FiniteIndecomposableSkeleton k (supportAlgebra z)
  acyclic : ∀ z, (skeleton z).HasAcyclicNonzeroNonisomorphisms
  sourceLabel : ∀ z, Fin (skeleton z).n
  translatedLabel : ∀ z, Fin (skeleton z).n
  coordinate : ∀ z,
    S.primitiveSourceProjectiveLabel D ∈
        S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle →
      (skeleton z).ProjectiveLabel
  rootPair : ∀ z (_hsupport :
      S.primitiveSourceProjectiveLabel D ∈
        S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle),
    (skeleton z).SupportCartanRootPairData
    (acyclic z) (sourceLabel z) (translatedLabel z)
  source_coordinate : ∀ z (hsupport :
      S.primitiveSourceProjectiveLabel D ∈
        S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle),
    (skeleton z).projectiveHomVector (sourceLabel z)
        (coordinate z hsupport) =
      (S.primitiveMultiplicity D z.1 : ℤ)
  translated_coordinate : ∀ z (hsupport :
      S.primitiveSourceProjectiveLabel D ∈
        S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle),
    (skeleton z).projectiveHomVector (translatedLabel z)
        (coordinate z hsupport) =
      (S.primitiveMultiplicity D (S.rightTranslationLabel z) : ℤ)

/-- The sequence-local support Cartan calculation gives the literal primitive
coordinate estimate directly. -/
theorem MiddleSupportCartanData.primitiveMultiplicity_translation_difference_le_one
    [IsAlgClosed k]
    {e : A} {D : RightModule.PrimitiveIdempotentData e}
    (R : S.MiddleSupportCartanData D)
    (z : {x : Fin S.n // ¬ Projective (S.fgObj x)}) :
    abs ((S.primitiveMultiplicity D z.1 : ℤ) -
      (S.primitiveMultiplicity D (S.rightTranslationLabel z) : ℤ)) ≤ 1 := by
  by_cases hsupport : S.primitiveSourceProjectiveLabel D ∈
      S.projectiveSupport (S.minimalRightAlmostSplitAt z.1).middle
  · letI := R.supportRing z
    letI := R.supportAlgebraMap z
    letI := R.supportFiniteDimensional z
    letI := R.supportNoetherian z
    exact (SupportCartanRootPairData.coordinateData
        (S := R.skeleton z) (R.acyclic z) (R.rootPair z hsupport)
          (R.coordinate z hsupport) (R.source_coordinate z hsupport)
          (R.translated_coordinate z hsupport)).abs_sub_le_one
  · have hsourceSupport : S.primitiveSourceProjectiveLabel D ∉
        S.projectiveSupport (S.fgObj z.1) := fun h ↦
      hsupport ((S.rightSequence_endpointSupport_subset_middle z).2 h)
    have htranslatedSupport : S.primitiveSourceProjectiveLabel D ∉
        S.projectiveSupport
          (S.fgObj (S.rightTranslationLabel z)) := fun h ↦
      hsupport ((S.rightSequence_endpointSupport_subset_middle z).1 h)
    have hsource : S.primitiveMultiplicity D z.1 = 0 := by
      rw [S.primitiveMultiplicity_eq_sourceHom D z.1]
      exact finrank_zero_iff_forall_zero.mpr fun f ↦ by
        by_contra hf
        exact hsourceSupport ⟨f, hf⟩
    have htranslated :
        S.primitiveMultiplicity D (S.rightTranslationLabel z) = 0 := by
      rw [S.primitiveMultiplicity_eq_sourceHom D
        (S.rightTranslationLabel z)]
      exact finrank_zero_iff_forall_zero.mpr fun f ↦ by
        by_contra hf
        exact htranslatedSupport ⟨f, hf⟩
    simp [hsource, htranslated]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
