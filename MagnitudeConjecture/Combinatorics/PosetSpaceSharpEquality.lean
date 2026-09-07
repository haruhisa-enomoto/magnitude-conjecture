import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MagnitudeConjecture.Combinatorics.FiniteWidthTwo
import MagnitudeConjecture.Combinatorics.PosetSpaceSelectableAntichain

/-!
# Sharp realization length for Schur poset spaces

This file formalizes the final equality step in the manuscript's poset-space
argument.  Under the sharp numerical bound, the three-antichain detour forces
every Schur object to be one-dimensional.  A nonzero nonisomorphism between
one-dimensional poset spaces then strictly enlarges its support, so every
nonzero composable chain has at most one arrow per poset element.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

open CategoryTheory

universe u v

variable (k T : Type u) [Field k] [PartialOrder T]

section Support

variable [Fintype T]

/-- The support of a poset space: the indices whose distinguished subspace is
the whole ambient space.  For a one-dimensional space these are exactly its
nonzero distinguished subspaces. -/
def support (X : Obj k T) : Finset T :=
  Finset.univ.filter fun t ↦ X.subspace t = ⊤

@[simp]
theorem mem_support {X : Obj k T} {t : T} :
    t ∈ support k T X ↔ X.subspace t = ⊤ := by
  simp [support]

/-- Every subspace of a one-dimensional vector space is zero or the whole
space. -/
theorem submodule_eq_bot_or_eq_top_of_finrank_eq_one
    {V : Type u} [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 1) (S : Submodule k V) :
    S = ⊥ ∨ S = ⊤ := by
  letI : IsSimpleOrder (Submodule k V) :=
    is_simple_module_of_finrank_eq_one (K := k) hV
  exact IsSimpleOrder.eq_bot_or_eq_top S

/-- A nonzero map into a one-dimensional poset space can only enlarge
support. -/
theorem support_mono_of_ne_zero_of_finrank_eq_one
    {X Y : Obj k T} (f : X ⟶ Y) (hf : f ≠ 0)
    (hY : Module.finrank k Y = 1) :
    support k T X ⊆ support k T Y := by
  have hflinear : f.linear ≠ 0 := by
    intro hzero
    apply hf
    apply Hom.ext
    simpa using hzero
  have hsurj : Function.Surjective f.linear :=
    surjective_of_nonzero_of_finrank_eq_one hY hflinear
  intro t ht
  rw [mem_support] at ht ⊢
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hsurj y
  exact f.map_subspace t x (by rw [ht]; exact Submodule.mem_top)

/-- A nonzero map between one-dimensional poset spaces with equal support is
an isomorphism. -/
theorem isIso_of_ne_zero_of_finrank_eq_one_of_support_eq
    {X Y : Obj k T} (f : X ⟶ Y) (hf : f ≠ 0)
    (hX : Module.finrank k X = 1)
    (hY : Module.finrank k Y = 1)
    (hsupport : support k T X = support k T Y) :
    IsIso f := by
  have hflinear : f.linear ≠ 0 := by
    intro hzero
    apply hf
    apply Hom.ext
    simpa using hzero
  have hsurj : Function.Surjective f.linear :=
    surjective_of_nonzero_of_finrank_eq_one hY hflinear
  have hinj : Function.Injective f.linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hX.trans hY.symm)).mpr hsurj
  let e : X ≃ₗ[k] Y := LinearEquiv.ofBijective f.linear ⟨hinj, hsurj⟩
  let g : Y ⟶ X :=
    { linear := e.symm.toLinearMap
      map_subspace := by
        intro t y hy
        have htop : X.subspace t = ⊤ ↔ Y.subspace t = ⊤ := by
          have hmem : t ∈ support k T X ↔ t ∈ support k T Y := by
            rw [hsupport]
          simpa only [mem_support] using hmem
        rcases submodule_eq_bot_or_eq_top_of_finrank_eq_one
            k hX (X.subspace t) with hXbot | hXtop
        · haveI : Nontrivial X :=
            Module.nontrivial_of_finrank_eq_succ (n := 0) hX
          have hXnot : X.subspace t ≠ ⊤ := by
            rw [hXbot]
            exact bot_ne_top
          have hYnot : Y.subspace t ≠ ⊤ := fun h ↦ hXnot (htop.mpr h)
          have hYbot :=
            (submodule_eq_bot_or_eq_top_of_finrank_eq_one
              k hY (Y.subspace t)).resolve_right hYnot
          have hyzero : y = 0 := by
            rw [hYbot] at hy
            simpa using hy
          subst y
          simp
        · rw [hXtop]
          exact Submodule.mem_top }
  let E : X ≅ Y :=
    { hom := f
      inv := g
      hom_inv_id := by
        apply Hom.ext
        apply LinearMap.ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply Hom.ext
        apply LinearMap.ext
        intro y
        exact e.apply_symm_apply y }
  exact E.isIso_hom

/-- Thus a nonzero nonisomorphism between one-dimensional poset spaces
strictly enlarges support. -/
theorem support_ssubset_of_ne_zero_of_not_isIso_of_finrank_eq_one
    {X Y : Obj k T} (f : X ⟶ Y) (hf : f ≠ 0) (hnot : ¬IsIso f)
    (hX : Module.finrank k X = 1)
    (hY : Module.finrank k Y = 1) :
    support k T X ⊂ support k T Y := by
  refine (Finset.ssubset_iff_subset_ne).2 ⟨
    support_mono_of_ne_zero_of_finrank_eq_one k T f hf hY, ?_⟩
  intro heq
  exact hnot
    (isIso_of_ne_zero_of_finrank_eq_one_of_support_eq
      k T f hf hX hY heq)

end Support

section Sharp

variable [Fintype T]

/-- A family of Schur poset spaces together with the manuscript's numerical
multiplicity, identified with total-space dimension.  The primitive-factor
realization will instantiate this structure on its surviving labels. -/
structure SchurRealizationFamily (I : Type v) where
  obj : I → Obj k T
  schur : ∀ i, IsSchur k T (obj i)
  multiplicity : I → ℕ
  multiplicity_eq_finrank :
    ∀ i, multiplicity i = Module.finrank k (obj i)

omit [Fintype T] in
/-- Any theorem forcing every Schur poset space to be a line immediately
forces all multiplicities in a realized family to be one. -/
theorem SchurRealizationFamily.multiplicity_eq_one
    {I : Type v} (R : SchurRealizationFamily k T I)
    (hline : ∀ X : Obj k T, IsSchur k T X → Module.finrank k X = 1) :
    ∀ i, R.multiplicity i = 1 := by
  intro i
  rw [R.multiplicity_eq_finrank]
  exact hline (R.obj i) (R.schur i)

/-- If every admissible poset space is one-dimensional, strict support growth
bounds every nonzero chain of nonisomorphisms by the cardinality of the
indexing poset. -/
theorem hasNonzeroNonisomorphismLengthAtMost_card_of_finrank_eq_one
    {P : Obj k T → Prop}
    (hline : ∀ X, P X → Module.finrank k X = 1) :
    HasNonzeroNonisomorphismLengthAtMost
      (Obj k T) P (Fintype.card T) := by
  intro n F hF
  have hsupport : ∀ j : Fin n,
      support k T (F.obj j.castSucc) ⊂
        support k T (F.obj j.succ) := by
    intro j
    let f := F.map' j.val (j.val + 1)
      (Nat.le_succ _) (Nat.succ_le_of_lt j.isLt)
    exact support_ssubset_of_ne_zero_of_not_isIso_of_finrank_eq_one
      k T f (hF.2.1 j).1 (hF.2.1 j).2
      (hline _ (hF.1 j.castSucc)) (hline _ (hF.1 j.succ))
  have hcard : ∀ i : Fin (n + 1),
      i.val ≤ (support k T (F.obj i)).card := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
        have hlt := Finset.card_lt_card (hsupport i)
        change i.val + 1 ≤ (support k T (F.obj i.succ)).card
        calc
          i.val + 1 ≤
              (support k T (F.obj i.castSucc)).card + 1 :=
            Nat.add_le_add_right ih 1
          _ ≤ (support k T (F.obj i.succ)).card := hlt
  calc
    n = (Fin.last n).val := rfl
    _ ≤ (support k T (F.obj (Fin.last n))).card := hcard (Fin.last n)
    _ ≤ Fintype.card T := by
      simpa using Finset.card_le_card
        (Finset.subset_univ (support k T (F.obj (Fin.last n))))

/-- Under the sharp numerical bound `L ≤ |T|`, the three-antichain detour
rules out every higher-dimensional Schur object. -/
theorem finrank_eq_one_of_isSchur_of_positiveGrading_of_le_card
    {L : ℕ} (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    (hL : L ≤ Fintype.card T) (X : Obj k T) (hX : IsSchur k T X) :
    Module.finrank k X = 1 := by
  have hpos : 0 < Module.finrank k X :=
    Module.finrank_pos_iff_exists_ne_zero.mpr hX.1
  by_contra hne
  have hrank : 2 ≤ Module.finrank k X := by omega
  obtain ⟨a, b, c, H⟩ :=
    exists_threeAntichain_of_isSchur_of_two_le_finrank X hX hrank
  have hstrict := card_add_one_le_of_threeAntichain k H G
  omega

/-- The frozen manuscript's sharp equality conclusion for the realization
category: once `L ≤ |T|`, every nonzero composable chain of Schur
nonisomorphisms has at most `|T|` arrows. -/
theorem schurLengthAtMostCard_of_positiveGrading_of_le_card
    {L : ℕ} (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    (hL : L ≤ Fintype.card T) :
    HasNonzeroNonisomorphismLengthAtMost
      (Obj k T) (IsSchur k T) (Fintype.card T) :=
  hasNonzeroNonisomorphismLengthAtMost_card_of_finrank_eq_one k T
    (fun X hX ↦
      finrank_eq_one_of_isSchur_of_positiveGrading_of_le_card
        k T G hL X hX)

end Sharp

end MagnitudeConjecture.PosetSpace
