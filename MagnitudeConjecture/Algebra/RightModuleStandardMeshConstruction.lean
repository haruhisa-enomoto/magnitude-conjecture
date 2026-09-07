import MagnitudeConjecture.Algebra.RightModuleStandardMeshFullness
import MagnitudeConjecture.CategoryTheory.DirectedMeshFaithfulness
import MagnitudeConjecture.CategoryTheory.StandardMeshGrading
import Mathlib.Data.Finset.Sort

/-!
# Recursive construction of the standard mesh realization

The vertices are processed in an increasing enumeration of the chosen
directed order.  At one target, the incoming occurrence representatives are
replaced by the components of a right almost-split sink.  The nonprojective
sink is first normalized so that its paired source composite vanishes;
the projective sink is the transported radical inclusion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance : Quiver (Fin S.n) := S.meshQuiver
local instance (i j : Fin S.n) : Fintype (i ⟶ j) :=
  S.meshArrowFintype i j
local instance meshArrowFintype' (i j : Fin S.n) :
    Fintype (S.MeshArrow i j) :=
  S.meshArrowFintype i j

/-- A wrapper carrying the selected directed order without replacing the
ordinary numerical order on `Fin S.n`. -/
structure DirectedVertex
    (H : S.HasAcyclicNonzeroNonisomorphisms) where
  val : Fin S.n

/-- Forget the directed-order wrapper. -/
def directedVertexUnderlyingEquiv
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.DirectedVertex H ≃ Fin S.n where
  toFun := DirectedVertex.val
  invFun := fun z ↦ ⟨z⟩
  left_inv := by intro z; cases z; rfl
  right_inv _ := rfl

noncomputable instance directedVertexFintype
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    Fintype (S.DirectedVertex H) :=
  Fintype.ofEquiv (Fin S.n) (S.directedVertexUnderlyingEquiv H).symm

noncomputable instance directedVertexLinearOrder
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    LinearOrder (S.DirectedVertex H) := by
  letI : LinearOrder (Fin S.n) := S.directedLinearOrder H
  exact LinearOrder.lift' DirectedVertex.val (by
    intro x y h
    cases x
    cases y
    simp_all)

/-- The order isomorphism enumerating the wrapped directed vertices. -/
def directedVertexOrderIso
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    Fin S.n ≃o S.DirectedVertex H :=
  Fintype.orderIsoFinOfCardEq _ (by
    rw [Fintype.card_congr (S.directedVertexUnderlyingEquiv H)]
    simp)

/-- An increasing enumeration of the selected directed linear order, kept as
an equivalence so its type does not export a competing order instance. -/
def directedVertexEquiv
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    Fin S.n ≃ Fin S.n :=
  (S.directedVertexOrderIso H).toEquiv.trans
    (S.directedVertexUnderlyingEquiv H)

/-- The position of a vertex in the selected directed enumeration. -/
def directedVertexIndex
    (H : S.HasAcyclicNonzeroNonisomorphisms) (z : Fin S.n) : Fin S.n :=
  (S.directedVertexEquiv H).symm z

@[simp]
theorem directedVertexIndex_equiv
    (H : S.HasAcyclicNonzeroNonisomorphisms) (p : Fin S.n) :
    S.directedVertexIndex H (S.directedVertexEquiv H p) = p :=
  (S.directedVertexEquiv H).symm_apply_apply p

@[simp]
theorem directedVertexEquiv_index
    (H : S.HasAcyclicNonzeroNonisomorphisms) (z : Fin S.n) :
    S.directedVertexEquiv H (S.directedVertexIndex H z) = z :=
  (S.directedVertexEquiv H).apply_symm_apply z

theorem directedVertexEquiv_lt_iff
    (H : S.HasAcyclicNonzeroNonisomorphisms) (p q : Fin S.n) :
    (S.directedLinearOrder H).lt
        (S.directedVertexEquiv H p) (S.directedVertexEquiv H q) ↔
      p < q := by
  change (S.directedLinearOrder H).lt
    (S.directedVertexOrderIso H p).val
      (S.directedVertexOrderIso H q).val ↔ p < q
  have h : S.directedVertexOrderIso H p <
      S.directedVertexOrderIso H q ↔ p < q :=
    (S.directedVertexOrderIso H).lt_iff_lt
  change (S.directedLinearOrder H).lt
    (S.directedVertexOrderIso H p).val
      (S.directedVertexOrderIso H q).val ↔ p < q at h
  exact h

theorem directedVertexIndex_lt_iff
    (H : S.HasAcyclicNonzeroNonisomorphisms) (y z : Fin S.n) :
    (S.directedVertexIndex H y < S.directedVertexIndex H z) ↔
      (S.directedLinearOrder H).lt y z := by
  have h := S.directedVertexEquiv_lt_iff H
    (S.directedVertexIndex H y) (S.directedVertexIndex H z)
  simpa only [S.directedVertexEquiv_index H y,
    S.directedVertexEquiv_index H z] using h.symm

/-- A choice of module morphism for every concrete reversed mesh arrow. -/
abbrev MeshArrowAssignment :=
  ∀ {i j : Fin S.n}, S.MeshArrow i j →
    (S.almostSplitSkeleton.obj j ⟶ S.almostSplitSkeleton.obj i)

/-- Free-path fullness at one target vertex. -/
def FreePathFullAt (arrowMap : S.MeshArrowAssignment) (z : Fin S.n) : Prop :=
  ∀ (x : Fin S.n)
    (f : S.almostSplitSkeleton.obj x ⟶ S.almostSplitSkeleton.obj z),
    ∃ p : LinearPathCategory.obj k (Fin S.n) x ⟶
        LinearPathCategory.obj k (Fin S.n) z,
      (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj arrowMap).map p = f

/-- All local data produced while processing one target. -/
structure MeshStepData [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : S.MeshArrowAssignment) (z : Fin S.n) where
  sink : (S.meshRightAlmostSplitAt z).middle ⟶
    S.almostSplitSkeleton.obj z
  rightAlmostSplit : IsRightAlmostSplit sink
  projective_kernel_zero : Projective (S.fgObj z) →
    ∀ {X : FGModuleCat.{u} Aᵐᵒᵖ}
      (q : X ⟶ (S.meshRightAlmostSplitAt z).middle),
      q ≫ sink = 0 → q = 0
  nonprojective_kernel_factor :
    ∀ (hz : ¬ Projective (S.fgObj z))
      {X : FGModuleCat.{u} Aᵐᵒᵖ}
      (q : X ⟶ (S.meshRightAlmostSplitAt z).middle),
      q ≫ sink = 0 →
        ∃ t : X ⟶ S.fgObj
            (S.rightTranslationLabel ⟨z, hz⟩),
          t ≫ S.rightMeshSourceMap H
            (S.replaceArrowMapAt arrowMap z sink) ⟨z, hz⟩ = q
  meshRelation_zero :
    ∀ (hz : ¬ Projective (S.fgObj z)),
      (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj
          (S.replaceArrowMapAt arrowMap z sink)).map
          ((S.rightMeshData H).meshRelation (k := k)
            (S.rightMeshNonprojectiveVertex H ⟨z, hz⟩)) = 0

/-- The projective radical boundary or the normalized nonprojective AR sink
supplies all data needed at one recursive step. -/
theorem exists_meshStepData
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : S.MeshArrowAssignment) (z : Fin S.n)
    (hfull : ∀ y : Fin S.n,
      (S.directedLinearOrder H).lt y z → S.FreePathFullAt arrowMap y) :
    Nonempty (S.MeshStepData H arrowMap z) := by
  classical
  by_cases hz : Projective (S.fgObj z)
  · let g := S.meshProjectiveSink z hz
    letI : Mono g := S.meshProjectiveSink_mono z hz
    exact ⟨
      { sink := g
        rightAlmostSplit := S.meshProjectiveSink_rightAlmostSplit z hz
        projective_kernel_zero := by
          intro _ X q hq
          apply (cancel_mono g).1
          simpa only [zero_comp] using hq
        nonprojective_kernel_factor := by
          intro hn
          exact (hn hz).elim
        meshRelation_zero := by
          intro hn
          exact (hn hz).elim }⟩
  · let zn : {z : Fin S.n // ¬ Projective (S.fgObj z)} := ⟨z, hz⟩
    obtain ⟨e, he, hzero⟩ :=
      S.exists_rightMesh_normalization H arrowMap zn (by
        intro y hy f
        exact hfull y hy _ f)
    let g := e.inv ≫ S.meshRightSinkMap zn
    have hg : IsRightAlmostSplit g :=
      rightAlmostSplit_precomp_iso
        (S.meshRightSinkMap_rightAlmostSplit zn) e.symm
    exact ⟨
      { sink := g
        rightAlmostSplit := hg
        projective_kernel_zero := by
          intro hp
          exact (hz hp).elim
        nonprojective_kernel_factor := by
          intro hn X q hq
          have hproof : hn = hz := Subsingleton.elim _ _
          subst hn
          have hsource :=
            S.rightMeshSourceMap_replaceArrowMapAt_eq_of_le H arrowMap z g
              zn ((S.directedLinearOrder H).le_refl z)
          obtain ⟨t, ht⟩ :=
            S.exists_comp_rightMeshSourceMap_eq_of_normalization
              H arrowMap zn e he q (by
                change q ≫ g = 0
                exact hq)
          refine ⟨t, ?_⟩
          rw [hsource]
          exact ht
        meshRelation_zero := by
          intro hn
          have hproof : hn = hz := Subsingleton.elim _ _
          subst hn
          rw [S.lift_map_meshRelation_eq_source_comp_sink H
            (S.replaceArrowMapAt arrowMap z g) zn]
          rw [S.realizedRightMeshSink_replaceArrowMapAt]
          rw [S.rightMeshSourceMap_replaceArrowMapAt_eq_of_le H arrowMap z g
            zn ((S.directedLinearOrder H).le_refl z)]
          change S.rightMeshSourceMap H arrowMap zn ≫
            e.inv ≫ S.meshRightSinkMap zn = 0
          exact hzero }⟩

/-- A global arrow assignment together with all properties established on
the first `m` vertices of the directed enumeration. -/
structure StandardMeshStage [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms) (m : ℕ) where
  arrowMap : S.MeshArrowAssignment
  full : ∀ (z : Fin S.n), (S.directedVertexIndex H z).val < m →
    S.FreePathFullAt arrowMap z
  sink_rightAlmostSplit :
    ∀ (z : Fin S.n), (S.directedVertexIndex H z).val < m →
      IsRightAlmostSplit (S.realizedRightMeshSink arrowMap z)
  projective_kernel_zero :
    ∀ (z : Fin S.n), Projective (S.fgObj z) →
      (S.directedVertexIndex H z).val < m →
      ∀ {X : FGModuleCat.{u} Aᵐᵒᵖ}
        (q : X ⟶ (S.meshRightAlmostSplitAt z).middle),
        q ≫ S.realizedRightMeshSink arrowMap z = 0 → q = 0
  nonprojective_kernel_factor :
    ∀ (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}),
      (S.directedVertexIndex H z.1).val < m →
      ∀ {X : FGModuleCat.{u} Aᵐᵒᵖ}
        (q : X ⟶ (S.meshRightAlmostSplitAt z.1).middle),
        q ≫ S.realizedRightMeshSink arrowMap z.1 = 0 →
          ∃ t : X ⟶ S.fgObj (S.rightTranslationLabel z),
            t ≫ S.rightMeshSourceMap H arrowMap z = q
  meshRelation_zero :
    ∀ (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}),
      (S.directedVertexIndex H z.1).val < m →
      (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj arrowMap).map
          ((S.rightMeshData H).meshRelation (k := k)
            (S.rightMeshNonprojectiveVertex H z)) = 0

/-- Before the recursion starts, the properties on the empty prefix hold
vacuously. -/
def standardMeshStageZero
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.StandardMeshStage H 0 where
  arrowMap := S.meshArrowMap
  full := by intro z hz; omega
  sink_rightAlmostSplit := by intro z hz; omega
  projective_kernel_zero := by intro z hp hz; omega
  nonprojective_kernel_factor := by intro z hz; omega
  meshRelation_zero := by intro z hz; omega

/-- Extend a completed prefix by one vertex.  All earlier properties survive
because only arrows ending at the new, strictly later target are changed. -/
theorem StandardMeshStage.exists_succ
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    {m : ℕ} (D : S.StandardMeshStage H m) (hm : m < S.n) :
    Nonempty (S.StandardMeshStage H (m + 1)) := by
  classical
  let p : Fin S.n := ⟨m, hm⟩
  let z : Fin S.n := S.directedVertexEquiv H p
  have hzindex : S.directedVertexIndex H z = p := by
    simp only [z, S.directedVertexIndex_equiv H p]
  have hindex_lt_of_lt (y : Fin S.n)
      (hyz : (S.directedLinearOrder H).lt y z) :
      (S.directedVertexIndex H y).val < m := by
    have hfin : S.directedVertexIndex H y <
        S.directedVertexIndex H z :=
      (S.directedVertexIndex_lt_iff H y z).2 hyz
    rw [hzindex] at hfin
    exact hfin
  have hfullOld (y : Fin S.n)
      (hyz : (S.directedLinearOrder H).lt y z) :
      S.FreePathFullAt D.arrowMap y :=
    D.full y (hindex_lt_of_lt y hyz)
  let E : S.MeshStepData H D.arrowMap z :=
    Classical.choice (S.exists_meshStepData H D.arrowMap z hfullOld)
  let arrowMap : S.MeshArrowAssignment :=
    S.replaceArrowMapAt D.arrowMap z E.sink
  have hbefore (w : Fin S.n)
      (hw : (S.directedVertexIndex H w).val < m) :
      (S.directedLinearOrder H).lt w z := by
    apply (S.directedVertexIndex_lt_iff H w z).1
    rw [hzindex]
    exact hw
  have hne (w : Fin S.n)
      (hw : (S.directedVertexIndex H w).val < m) : w ≠ z := by
    intro hwz
    subst w
    rw [hzindex] at hw
    exact (Nat.lt_irrefl m) hw
  have hcurrent (w : Fin S.n)
      (hwnew : (S.directedVertexIndex H w).val < m + 1)
      (hwold : ¬ (S.directedVertexIndex H w).val < m) : w = z := by
    apply (S.directedVertexEquiv H).symm.injective
    change S.directedVertexIndex H w = S.directedVertexIndex H z
    calc
      S.directedVertexIndex H w = p := by
        apply Fin.ext
        change (S.directedVertexIndex H w).val = m
        omega
      _ = S.directedVertexIndex H z := hzindex.symm
  have hfullBeforeNew (w : Fin S.n)
      (hwz : (S.directedLinearOrder H).lt w z) :
      S.FreePathFullAt arrowMap w := by
    have hw : (S.directedVertexIndex H w).val < m :=
      hindex_lt_of_lt w hwz
    intro x f
    obtain ⟨q, hq⟩ := D.full w hw x f
    refine ⟨q, ?_⟩
    rw [show
      (LinearPathCategory.lift
        (k := k) S.almostSplitSkeleton.obj arrowMap).map q =
          (LinearPathCategory.lift
            (k := k) S.almostSplitSkeleton.obj D.arrowMap).map q from
      S.lift_map_replaceArrowMapAt_eq_of_lt
        H D.arrowMap z E.sink hwz q,
      hq]
  have hfullCurrent : S.FreePathFullAt arrowMap z := by
    intro x f
    exact S.exists_freePath_map_eq_of_rightAlmostSplit
      H arrowMap z x (by
        rw [show S.realizedRightMeshSink arrowMap z = E.sink from
          S.realizedRightMeshSink_replaceArrowMapAt D.arrowMap z E.sink]
        exact E.rightAlmostSplit)
      (by
        intro y hy q
        exact hfullBeforeNew y hy _ q) f
  exact ⟨
    { arrowMap := arrowMap
      full := by
        intro w hwnew
        by_cases hwold : (S.directedVertexIndex H w).val < m
        · exact hfullBeforeNew w (hbefore w hwold)
        · have hwz : w = z := hcurrent w hwnew hwold
          subst w
          exact hfullCurrent
      sink_rightAlmostSplit := by
        intro w hwnew
        by_cases hwold : (S.directedVertexIndex H w).val < m
        · rw [show S.realizedRightMeshSink arrowMap w =
              S.realizedRightMeshSink D.arrowMap w from
            S.realizedRightMeshSink_replaceArrowMapAt_of_ne
              D.arrowMap z E.sink w (hne w hwold)]
          exact D.sink_rightAlmostSplit w hwold
        · have hwz : w = z := hcurrent w hwnew hwold
          subst w
          rw [show S.realizedRightMeshSink arrowMap z = E.sink from
            S.realizedRightMeshSink_replaceArrowMapAt D.arrowMap z E.sink]
          exact E.rightAlmostSplit
      projective_kernel_zero := by
        intro w hwproj hwnew X q hq
        by_cases hwold : (S.directedVertexIndex H w).val < m
        · have hsink : S.realizedRightMeshSink arrowMap w =
              S.realizedRightMeshSink D.arrowMap w :=
            S.realizedRightMeshSink_replaceArrowMapAt_of_ne
              D.arrowMap z E.sink w (hne w hwold)
          rw [hsink] at hq
          exact D.projective_kernel_zero w hwproj hwold q hq
        · have hwz : w = z := hcurrent w hwnew hwold
          subst w
          rw [S.realizedRightMeshSink_replaceArrowMapAt] at hq
          exact E.projective_kernel_zero hwproj q hq
      nonprojective_kernel_factor := by
        intro w hwnew X q hq
        by_cases hwold : (S.directedVertexIndex H w.1).val < m
        · have hsink : S.realizedRightMeshSink arrowMap w.1 =
              S.realizedRightMeshSink D.arrowMap w.1 :=
            S.realizedRightMeshSink_replaceArrowMapAt_of_ne
              D.arrowMap z E.sink w.1 (hne w.1 hwold)
          rw [hsink] at hq
          obtain ⟨t, ht⟩ :=
            D.nonprojective_kernel_factor w hwold q hq
          refine ⟨t, ?_⟩
          have hwle : (S.directedLinearOrder H).le w.1 z :=
            ((S.directedLinearOrder H).lt_iff_le_not_ge w.1 z).1
              (hbefore w.1 hwold) |>.1
          rw [S.rightMeshSourceMap_replaceArrowMapAt_eq_of_le
            H D.arrowMap z E.sink w hwle]
          exact ht
        · have hwz : w.1 = z := hcurrent w.1 hwnew hwold
          have hznp : ¬ Projective (S.fgObj z) := by
            rw [← hwz]
            exact w.2
          let wz : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
            ⟨z, hznp⟩
          have hweq : w = wz := Subtype.ext hwz
          subst w
          dsimp only [arrowMap] at hq ⊢
          rw [S.realizedRightMeshSink_replaceArrowMapAt] at hq
          exact E.nonprojective_kernel_factor hznp q hq
      meshRelation_zero := by
        intro w hwnew
        by_cases hwold : (S.directedVertexIndex H w.1).val < m
        · rw [show
            (LinearPathCategory.lift
              (k := k) S.almostSplitSkeleton.obj arrowMap).map
                ((S.rightMeshData H).meshRelation (k := k)
                  (S.rightMeshNonprojectiveVertex H w)) =
              (LinearPathCategory.lift
                (k := k) S.almostSplitSkeleton.obj D.arrowMap).map
                ((S.rightMeshData H).meshRelation (k := k)
                  (S.rightMeshNonprojectiveVertex H w)) from
            S.lift_map_replaceArrowMapAt_eq_of_lt
              H D.arrowMap z E.sink (hbefore w.1 hwold)
                ((S.rightMeshData H).meshRelation (k := k)
                  (S.rightMeshNonprojectiveVertex H w))]
          exact D.meshRelation_zero w hwold
        · have hwz : w.1 = z := hcurrent w.1 hwnew hwold
          have hznp : ¬ Projective (S.fgObj z) := by
            rw [← hwz]
            exact w.2
          let wz : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
            ⟨z, hznp⟩
          have hweq : w = wz := Subtype.ext hwz
          subst w
          exact E.meshRelation_zero hznp }⟩

/-- The recursive construction reaches every prefix of the directed
enumeration. -/
theorem exists_standardMeshStage
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (m : ℕ) (hm : m ≤ S.n) :
    Nonempty (S.StandardMeshStage H m) := by
  induction m with
  | zero => exact ⟨S.standardMeshStageZero H⟩
  | succ m ih =>
      obtain ⟨D⟩ := ih (Nat.le_of_succ_le hm)
      simpa only [Nat.succ_eq_add_one] using
        StandardMeshStage.exists_succ S H D (Nat.lt_of_succ_le hm)

/-- The completed recursive stage. -/
def standardMeshFinalStage
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.StandardMeshStage H S.n :=
  Classical.choice (S.exists_standardMeshStage H S.n le_rfl)

/-- The globally normalized arrow assignment obtained after processing every
vertex in the directed order. -/
def standardMeshArrowMap
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.MeshArrowAssignment :=
  (S.standardMeshFinalStage H).arrowMap

/-- Every target has been processed in the final stage. -/
theorem standardMeshFinalStage_index_lt
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : Fin S.n) :
    (S.directedVertexIndex H z).val < S.n :=
  (S.directedVertexIndex H z).isLt

/-- The completed arrow assignment is full already on the free linear path
category. -/
theorem standardMeshArrowMap_full
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : Fin S.n) :
    S.FreePathFullAt (S.standardMeshArrowMap H) z :=
  (S.standardMeshFinalStage H).full z
    (S.standardMeshFinalStage_index_lt H z)

/-- The completed sinks are right almost split. -/
theorem standardMeshArrowMap_sink_rightAlmostSplit
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : Fin S.n) :
    IsRightAlmostSplit
      (S.realizedRightMeshSink (S.standardMeshArrowMap H) z) :=
  (S.standardMeshFinalStage H).sink_rightAlmostSplit z
    (S.standardMeshFinalStage_index_lt H z)

/-- At a projective target the completed incoming sink has zero kernel. -/
theorem standardMeshArrowMap_projective_kernel_zero
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : Fin S.n) (hz : Projective (S.fgObj z))
    {X : FGModuleCat.{u} Aᵐᵒᵖ}
    (q : X ⟶ (S.meshRightAlmostSplitAt z).middle)
    (hq : q ≫ S.realizedRightMeshSink
      (S.standardMeshArrowMap H) z = 0) : q = 0 :=
  (S.standardMeshFinalStage H).projective_kernel_zero z hz
    (S.standardMeshFinalStage_index_lt H z) q hq

/-- At a nonprojective target the completed incoming sink has kernel generated
by the paired source map from the translate. -/
theorem standardMeshArrowMap_nonprojective_kernel_factor
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    {X : FGModuleCat.{u} Aᵐᵒᵖ}
    (q : X ⟶ (S.meshRightAlmostSplitAt z.1).middle)
    (hq : q ≫ S.realizedRightMeshSink
      (S.standardMeshArrowMap H) z.1 = 0) :
    ∃ t : X ⟶ S.fgObj (S.rightTranslationLabel z),
      t ≫ S.rightMeshSourceMap H (S.standardMeshArrowMap H) z = q :=
  (S.standardMeshFinalStage H).nonprojective_kernel_factor z
    (S.standardMeshFinalStage_index_lt H z.1) q hq

/-- The component formula for `meshMiddleLift`, stated at an arbitrary
incoming arrow rather than at a displayed-middle index. -/
theorem meshMiddleLift_decomposition_incoming
    {X : FGModuleCat.{u} Aᵐᵒᵖ} (z : Fin S.n)
    (c : ∀ a : Σ y : Fin S.n, S.MeshArrow z y,
      X ⟶ S.almostSplitSkeleton.obj a.1)
    (a : Σ y : Fin S.n, S.MeshArrow z y) :
    S.meshMiddleLift z c ≫
        (S.meshRightAlmostSplitAt z).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.almostSplitSkeleton.obj
            ((S.meshRightAlmostSplitAt z).label j))
          a.2.1 ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          a.2.2) =
      c a := by
  rcases a with ⟨y, ⟨t, ht⟩⟩
  subst y
  change (S.meshMiddleLift z c ≫
      (S.meshRightAlmostSplitAt z).decomposition.hom ≫
      biproduct.π
        (fun j ↦ S.almostSplitSkeleton.obj
          ((S.meshRightAlmostSplitAt z).label j)) t) ≫
      𝟙 _ = c (S.meshMiddleIndexEquiv z t)
  rw [S.meshMiddleLift_decomposition_π z c t]
  simp

/-- The component formula for the paired source map, again indexed by an
arbitrary incoming arrow. -/
theorem rightMeshSourceMap_decomposition_incoming
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (arrowMap : S.MeshArrowAssignment)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (a : Σ y : Fin S.n, S.MeshArrow z.1 y) :
    S.rightMeshSourceMap H arrowMap z ≫
        (S.meshRightAlmostSplitAt z.1).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.almostSplitSkeleton.obj
            ((S.meshRightAlmostSplitAt z.1).label j))
          a.2.1 ≫
        eqToHom (congrArg S.almostSplitSkeleton.obj
          a.2.2) =
      arrowMap (S.meshArrowEquiv H z a.1 a.2) := by
  rcases a with ⟨y, ⟨t, ht⟩⟩
  subst y
  change (S.rightMeshSourceMap H arrowMap z ≫
      (S.meshRightAlmostSplitAt z.1).decomposition.hom ≫
      biproduct.π
        (fun j ↦ S.almostSplitSkeleton.obj
          ((S.meshRightAlmostSplitAt z.1).label j)) t) ≫
      𝟙 _ = arrowMap
        (S.meshArrowEquiv H z
          ((S.meshRightAlmostSplitAt z.1).label t) ⟨t, rfl⟩)
  rw [S.rightMeshSourceMap_decomposition_π H arrowMap z t]
  change arrowMap
      (S.meshArrowEquiv H z
        ((S.meshRightAlmostSplitAt z.1).label t) ⟨t, rfl⟩) ≫
      𝟙 _ = arrowMap
        (S.meshArrowEquiv H z
          ((S.meshRightAlmostSplitAt z.1).label t) ⟨t, rfl⟩)
  simp

/-- Composing a map assembled from incoming-arrow coefficients with the
assembled sink is the sum of the componentwise composites. -/
theorem meshMiddleLift_comp_realizedRightMeshSink
    (arrowMap : S.MeshArrowAssignment)
    {X : FGModuleCat.{u} Aᵐᵒᵖ} (z : Fin S.n)
    (c : ∀ a : Σ y : Fin S.n, S.MeshArrow z y,
      X ⟶ S.almostSplitSkeleton.obj a.1) :
    S.meshMiddleLift z c ≫ S.realizedRightMeshSink arrowMap z =
      ∑ a : Σ y : Fin S.n, S.MeshArrow z y,
        c a ≫ arrowMap a.2 := by
  classical
  let B := S.meshRightAlmostSplitAt z
  letI : Fintype B.index := FintypeCat.fintype
  letI (y : Fin S.n) : Fintype (S.MeshArrow z y) :=
    S.meshArrowFintype z y
  dsimp only [meshMiddleLift, realizedRightMeshSink]
  rw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_desc]
  let e : B.index ≃ Σ y : Fin S.n, S.MeshArrow z y :=
    S.meshMiddleIndexEquiv z
  have hreindex := e.sum_comp (fun a ↦ c a ≫ arrowMap a.2)
  rw [hreindex.symm]
  apply Finset.sum_congr rfl
  intro t _
  rfl

/-- The final assignment kills every ordinary mesh relation. -/
theorem standardMeshArrowMap_meshRelation_zero
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (LinearPathCategory.lift
      (k := k) S.almostSplitSkeleton.obj
        (S.standardMeshArrowMap H)).map
        ((S.rightMeshData H).meshRelation (k := k)
          (S.rightMeshNonprojectiveVertex H z)) = 0 :=
  (S.standardMeshFinalStage H).meshRelation_zero z
    (S.standardMeshFinalStage_index_lt H z.1)

/-- The recursively chosen arrows descend from the free path category to the
ordinary mesh quotient. -/
def standardMeshRealization
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    MeshCategory.Realization (k := k) (S.rightMeshData H)
      S.almostSplitSkeleton.obj where
  arrowMap := S.standardMeshArrowMap H
  map_meshRelation := by
    intro z
    let zn : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
      ⟨z.1, by
        have hz := z.2
        change ¬ Projective (S.fgObj z.1) at hz
        exact hz⟩
    have hz := S.standardMeshArrowMap_meshRelation_zero H zn
    have heq : S.rightMeshNonprojectiveVertex H zn = z := Subtype.ext rfl
    rw [← heq]
    exact hz

/-- Fullness constructed target by target is exactly fullness of the free
linear path realization. -/
noncomputable instance standardMeshRealization_freeFunctor_full
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    (S.standardMeshRealization H).freeFunctor.Full where
  map_surjective := by
    intro X Y f
    exact S.standardMeshArrowMap_full H
      (LinearPathCategory.vertex Y) (LinearPathCategory.vertex X) f

/-- The completed realization satisfies the local exactness hypotheses in
Ringel's directed faithfulness argument. -/
def standardMeshDirectedExactData
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    (S.standardMeshRealization H).DirectedExactData where
  order := S.directedLinearOrder H
  arrow_lt := by
    intro a b e
    exact S.meshArrow_lt H e
  target_id_ne_zero := by
    intro x hx
    apply (S.fgObj_indecomposable x).1
    exact (IsZero.iff_id_eq_zero (S.fgObj x)).2 hx
  projective_exact := by
    classical
    intro z hz x h hsum a
    let R := S.standardMeshRealization H
    let c : ∀ a : Σ y : Fin S.n, S.MeshArrow z y,
        S.almostSplitSkeleton.obj x ⟶
          S.almostSplitSkeleton.obj a.1 :=
      fun a ↦ R.functor.map (h a)
    let q : S.almostSplitSkeleton.obj x ⟶
        (S.meshRightAlmostSplitAt z).middle :=
      S.meshMiddleLift z c
    have hsum' :
        (∑ a : Σ y : Fin S.n, S.MeshArrow z y,
          c a ≫ S.standardMeshArrowMap H a.2) = 0 := by
      have hsum' := hsum
      simp only [(S.standardMeshRealization H).functor_map_incomingArrowHom]
        at hsum'
      change (∑ a : Σ y : Fin S.n, S.MeshArrow z y,
        c a ≫ S.standardMeshArrowMap H a.2) = 0 at hsum'
      exact hsum'
    have hq : q ≫ S.realizedRightMeshSink
        (S.standardMeshArrowMap H) z = 0 := by
      rw [show q = S.meshMiddleLift z c from rfl,
        S.meshMiddleLift_comp_realizedRightMeshSink]
      exact hsum'
    have hz' : Projective (S.fgObj z) := by
      change Projective (S.fgObj z) at hz
      exact hz
    have hqzero : q = 0 :=
      S.standardMeshArrowMap_projective_kernel_zero H z hz' q hq
    have hc := S.meshMiddleLift_decomposition_incoming z c a
    rw [show S.meshMiddleLift z c = q from rfl, hqzero] at hc
    change c a = 0
    simpa only [zero_comp] using hc.symm
  nonprojective_exact := by
    classical
    intro z x h hsum
    let zn : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
      ⟨z.1, by
        have hz := z.2
        change ¬ Projective (S.fgObj z.1) at hz
        exact hz⟩
    have hzeq : S.rightMeshNonprojectiveVertex H zn = z :=
      Subtype.ext rfl
    let R := S.standardMeshRealization H
    let c : ∀ a : Σ y : Fin S.n, S.MeshArrow zn.1 y,
        S.almostSplitSkeleton.obj x ⟶
          S.almostSplitSkeleton.obj a.1 :=
      fun a ↦ R.functor.map (h a)
    let q : S.almostSplitSkeleton.obj x ⟶
        (S.meshRightAlmostSplitAt zn.1).middle :=
      S.meshMiddleLift zn.1 c
    have hsum' :
        (∑ a : Σ y : Fin S.n, S.MeshArrow zn.1 y,
          c a ≫ S.standardMeshArrowMap H a.2) = 0 := by
      have hsum' := hsum
      simp only [(S.standardMeshRealization H).functor_map_incomingArrowHom]
        at hsum'
      change (∑ a : Σ y : Fin S.n, S.MeshArrow zn.1 y,
        c a ≫ S.standardMeshArrowMap H a.2) = 0 at hsum'
      exact hsum'
    have hq : q ≫ S.realizedRightMeshSink
        (S.standardMeshArrowMap H) zn.1 = 0 := by
      rw [show q = S.meshMiddleLift zn.1 c from rfl,
        S.meshMiddleLift_comp_realizedRightMeshSink]
      exact hsum'
    obtain ⟨t, ht⟩ :=
      S.standardMeshArrowMap_nonprojective_kernel_factor H zn q hq
    let t' : S.almostSplitSkeleton.obj x ⟶
        S.almostSplitSkeleton.obj (S.rightTranslationLabel zn) := t
    have ht' : t' ≫ S.rightMeshSourceMap H
        (S.standardMeshArrowMap H) zn = q := ht
    refine ⟨t', ?_⟩
    intro a
    have hc := S.meshMiddleLift_decomposition_incoming zn.1 c a
    have hs := S.rightMeshSourceMap_decomposition_incoming H
      (S.standardMeshArrowMap H) zn a
    rw [show S.meshMiddleLift zn.1 c = q from rfl, ← ht'] at hc
    simp only [Category.assoc] at hc hs
    have htc : t' ≫
        S.standardMeshArrowMap H (S.meshArrowEquiv H zn a.1 a.2) =
        c a := by
      rw [← hs]
      exact hc
    rw [(S.standardMeshRealization H).functor_map_incomingArrowHom]
    change c a = t' ≫
      S.standardMeshArrowMap H
        ((S.rightMeshData H).arrowEquiv z a.1 a.2)
    have hpaired : (S.rightMeshData H).arrowEquiv z a.1 a.2 =
        S.meshArrowEquiv H zn a.1 a.2 := by
      change S.meshArrowEquiv H
          ⟨z.1, by
            have hz := z.2
            change ¬ Projective (S.fgObj z.1) at hz
            exact hz⟩ a.1 a.2 = _
      congr 2
    rw [hpaired]
    exact htc.symm

/-- Morphisms between ambient selected points are literally morphisms between
their underlying finitely generated modules. -/
def ambientAddPointHomLinearEquiv (x y : Fin S.n) :
    (S.ambientAddPoint x ⟶ S.ambientAddPoint y) ≃ₗ[k]
      (S.fgObj x ⟶ S.fgObj y) :=
  InducedCategory.homLinearEquiv

/-- Ringel standardness for the concrete right Auslander--Reiten mesh of a
directed representation-finite algebra. -/
def standardMeshPresentation
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.StandardMeshPresentation (quiver := S.meshQuiver)
      (arrowFintype := S.meshArrowFintype) (S.rightMeshData H) := by
  let R := S.standardMeshRealization H
  let D := S.standardMeshDirectedExactData H
  exact
    { homEquiv := fun x y ↦
        (R.homLinearEquivOfInjective x y
          (MeshCategory.Realization.DirectedExactData.map_injective
            (R := R) D x y)).trans
          (S.ambientAddPointHomLinearEquiv x y).symm
      map_id := by
        intro x
        apply ObjectProperty.hom_ext
        change R.functor.map (𝟙 (MeshCategory.obj
          (k := k) (S.rightMeshData H) x)) = 𝟙 (S.fgObj x)
        exact R.functor.map_id _
      map_comp := by
        intro x y z f g
        apply ObjectProperty.hom_ext
        change R.functor.map (f ≫ g) =
          R.functor.map f ≫ R.functor.map g
        exact R.functor.map_comp f g }

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
