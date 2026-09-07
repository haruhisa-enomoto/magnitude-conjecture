import MagnitudeConjecture.Combinatorics.PosetSpaceRealization

/-!
# The three-antichain path in finite poset spaces

This file formalizes the characteristic-free five-object path through the
two-dimensional three-line configuration used in the equality argument of
the frozen manuscript.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

open CategoryTheory
open CategoryTheory.Limits

/-- The discrete three-element poset underlying the local antichain
obstruction.  The phantom parameter keeps it in the same universe as the
field, as required by the literal `T`-space category. -/
inductive Three (α : Type u) : Type u
  | first
  | second
  | third
  deriving DecidableEq

instance {α : Type u} : PartialOrder (Three α) where
  le := Eq
  lt := fun _ _ ↦ False
  le_refl _ := rfl
  le_trans := fun _ _ _ hab hbc ↦ Eq.trans hab hbc
  le_antisymm _ _ hab _ := hab
  lt_iff_le_not_ge := by simp

theorem three_isUpperSet {α : Type u} (U : Set (Three α)) : IsUpperSet U := by
  intro s t hst hs
  change s = t at hst
  simpa [hst] using hs

section Field

variable (k : Type u) [Field k]

/-- The first coordinate axis in `k²`. -/
def firstAxis : Submodule k (k × k) where
  carrier := {x | x.2 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.snd_add]
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Prod.smul_snd]
    rw [hx, smul_zero]

/-- The second coordinate axis in `k²`. -/
def secondAxis : Submodule k (k × k) where
  carrier := {x | x.1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.fst_add]
    rw [hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Prod.smul_fst]
    rw [hx, smul_zero]

/-- The diagonal line in `k²`. -/
def diagonal : Submodule k (k × k) where
  carrier := {x | x.1 = x.2}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add]
    rw [hx, hy]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd]
    rw [hx]

@[simp]
theorem mem_firstAxis_iff (x : k × k) :
    x ∈ firstAxis k ↔ x.2 = 0 :=
  Iff.rfl

@[simp]
theorem mem_secondAxis_iff (x : k × k) :
    x ∈ secondAxis k ↔ x.1 = 0 :=
  Iff.rfl

@[simp]
theorem mem_diagonal_iff (x : k × k) :
    x ∈ diagonal k ↔ x.1 = x.2 :=
  Iff.rfl

/-- The manuscript's indecomposable two-dimensional three-line space. -/
abbrev threeLinePlane : Obj k (Three k) where
  carrier := k × k
  subspace
    | Three.first => firstAxis k
    | Three.second => secondAxis k
    | Three.third => diagonal k
  monotone_subspace := by
    intro s t hst
    change s = t at hst
    subst t
    exact le_rfl

/-- Empty-support scalar space. -/
abbrev threePathObj0 : Obj k (Three k) :=
  line k (Three k) ∅ (three_isUpperSet ∅)

/-- Scalar space supported at the first antichain point. -/
abbrev threePathObj1 : Obj k (Three k) :=
  line k (Three k) {Three.first} (three_isUpperSet {Three.first})

/-- Scalar space supported at the first two antichain points. -/
abbrev threePathObj3 : Obj k (Three k) :=
  line k (Three k) {Three.first, Three.second}
    (three_isUpperSet {Three.first, Three.second})

/-- Full-support scalar space. -/
abbrev threePathObj4 : Obj k (Three k) :=
  line k (Three k) Set.univ (three_isUpperSet Set.univ)

/-- First strict support inclusion in the three-antichain path. -/
abbrev threePathMap01 : threePathObj0 k ⟶ threePathObj1 k :=
  lineHom k (Three k) (by simp)

/-- The map `1 ↦ e₁` into the three-line plane. -/
def threePathMap12 : threePathObj1 k ⟶ threeLinePlane k where
  linear :=
    { toFun := fun x ↦ (x, 0)
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
  map_subspace := by
    classical
    intro t x hx
    cases t with
    | first => simp [threeLinePlane, firstAxis]
    | second =>
        have hx0 : x = 0 := by
          simpa [threePathObj1] using hx
        subst x
        simp [threeLinePlane, secondAxis]
    | third =>
        have hx0 : x = 0 := by
          simpa [threePathObj1] using hx
        subst x
        simp [threeLinePlane, diagonal]

/-- The map `(x,y) ↦ x-y`; it kills the diagonal line even in
characteristic two. -/
def threePathMap23 : threeLinePlane k ⟶ threePathObj3 k where
  linear :=
    { toFun := fun x ↦ x.1 - x.2
      map_add' := by
        intros
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intros
        simp [mul_sub] }
  map_subspace := by
    classical
    intro t x hx
    cases t with
    | first => simp
    | second => simp
    | third =>
        change x.1 = x.2 at hx
        simp [threePathObj3, hx]

/-- Final strict support inclusion in the three-antichain path. -/
abbrev threePathMap34 : threePathObj3 k ⟶ threePathObj4 k :=
  lineHom k (Three k) (by simp)

@[simp]
theorem threePathMap12_apply (x : k) :
    (threePathMap12 k).linear x = (x, 0) :=
  rfl

@[simp]
theorem threePathMap23_apply (x : k × k) :
    (threePathMap23 k).linear x = x.1 - x.2 :=
  rfl

theorem threePathMap12_ne_zero : threePathMap12 k ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear (1 : k)) hzero
  change ((1 : k), 0) = (0, 0) at h
  exact one_ne_zero (congrArg Prod.fst h)

theorem threePathMap01_ne_zero : threePathMap01 k ≠ 0 :=
  lineHom_ne_zero k (Three k) (by simp)

theorem threePathMap34_ne_zero : threePathMap34 k ≠ 0 :=
  lineHom_ne_zero k (Three k) (by simp)

theorem threePathMap23_ne_zero : threePathMap23 k ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear ((1 : k), 0)) hzero
  have hcalc : (threePathMap23 k).linear ((1 : k), 0) = 1 := by
    simpa using threePathMap23_apply k ((1 : k), 0)
  rw [hcalc, zero_linear, LinearMap.zero_apply] at h
  exact one_ne_zero h

/-- An isomorphism of `T`-spaces induces a linear equivalence of total
spaces. -/
def linearEquivOfIsIso {S : Type u} [PartialOrder S]
    {X Y : Obj k S} (f : X ⟶ Y) [IsIso f] :
    X ≃ₗ[k] Y where
  toLinearMap := f.linear
  invFun := (inv f).linear
  left_inv x := by
    have h := congrArg (fun g : X ⟶ X ↦ g.linear x)
      (IsIso.hom_inv_id f)
    exact h
  right_inv y := by
    have h := congrArg (fun g : Y ⟶ Y ↦ g.linear y)
      (IsIso.inv_hom_id f)
    exact h

theorem not_isIso_of_finrank_ne {S : Type u} [PartialOrder S]
    {X Y : Obj k S} (f : X ⟶ Y)
    (hfinrank : Module.finrank k X ≠ Module.finrank k Y) :
    ¬ IsIso f := by
  intro hf
  letI : IsIso f := hf
  exact hfinrank (LinearEquiv.finrank_eq (linearEquivOfIsIso k f))

theorem threePathMap12_not_isIso : ¬ IsIso (threePathMap12 k) := by
  apply not_isIso_of_finrank_ne k
  simp only [Module.finrank_self, Module.finrank_prod]
  omega

theorem threePathMap01_not_isIso : ¬ IsIso (threePathMap01 k) := by
  apply lineHom_not_isIso k (Three k)
  simp

theorem threePathMap34_not_isIso : ¬ IsIso (threePathMap34 k) := by
  apply lineHom_not_isIso k (Three k)
  constructor
  · simp
  · intro hEq
    have hmem : Three.third ∈ (Set.univ : Set (Three k)) := Set.mem_univ _
    have hnot : Three.third ∉ ({Three.first, Three.second} : Set (Three k)) := by
      simp
    exact hnot (hEq hmem)

theorem threePathMap23_not_isIso : ¬ IsIso (threePathMap23 k) := by
  apply not_isIso_of_finrank_ne k
  simp only [Module.finrank_self, Module.finrank_prod]
  omega

/-- The four displayed arrows have nonzero total composite. -/
@[simp]
theorem threePathComposite_apply :
    (threePathMap01 k ≫ threePathMap12 k ≫
      threePathMap23 k ≫ threePathMap34 k).linear (1 : k) = 1 :=
  by
    simp only [comp_linear, LinearMap.comp_apply, lineHom_linear,
      LinearMap.id_apply]
    rw [threePathMap12_apply, threePathMap23_apply]
    simp

/-- The four displayed arrows have nonzero total composite. -/
theorem threePathComposite_ne_zero :
    threePathMap01 k ≫ threePathMap12 k ≫
      threePathMap23 k ≫ threePathMap34 k ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear (1 : k)) hzero
  rw [threePathComposite_apply, zero_linear, LinearMap.zero_apply] at h
  exact one_ne_zero h

/-- The two-dimensional three-line configuration is Schur.  Preserving the
two coordinate axes makes an endomorphism diagonal, and preserving the third
line forces the two diagonal entries to agree.  This is the manuscript's
indecomposability argument in a stronger endomorphism-ring form. -/
theorem threeLinePlane_isSchur :
    IsSchur k (Three k) (threeLinePlane k) := by
  constructor
  · refine ⟨((1 : k), 0), ?_⟩
    intro hzero
    exact one_ne_zero (congrArg Prod.fst hzero)
  · intro f
    let v₁ : k × k := f.linear ((1 : k), 0)
    let v₂ : k × k := f.linear (0, (1 : k))
    have hv₁₂ : v₁.2 = 0 := by
      have hmem := f.map_subspace Three.first ((1 : k), 0) (by
        simp [threeLinePlane, firstAxis])
      exact hmem
    have hv₂₁ : v₂.1 = 0 := by
      have hmem := f.map_subspace Three.second (0, (1 : k)) (by
        simp [threeLinePlane, secondAxis])
      exact hmem
    have hvdiag :
        (f.linear ((1 : k), 1)).1 = (f.linear ((1 : k), 1)).2 := by
      have hmem := f.map_subspace Three.third ((1 : k), 1) (by
        simp [threeLinePlane, diagonal])
      exact hmem
    have hsum : f.linear ((1 : k), 1) = v₁ + v₂ := by
      change f.linear ((1 : k), 1) =
        f.linear ((1 : k), 0) + f.linear (0, (1 : k))
      rw [← LinearMap.map_add]
      congr 1
      ext <;> simp
    have hv₁₁_eq_v₂₂ : v₁.1 = v₂.2 := by
      rw [hsum] at hvdiag
      simpa [hv₁₂, hv₂₁] using hvdiag
    refine ⟨v₁.1, ?_⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hdecomp : (x, y) =
        x • ((1 : k), 0) + y • (0, (1 : k)) := by
      ext <;> simp
    rw [hdecomp, LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul]
    apply Prod.ext
    · simp [v₁, v₂, hv₂₁, mul_comm]
    · simp [v₁, v₂, hv₁₂, hv₁₁_eq_v₂₂, mul_comm]

/-- A positive grading on the Schur objects of the discrete three-point
poset-space category has length at least four.  This is one more than the
three ordinary support additions. -/
theorem four_le_of_three_schurPositiveGrading {L : ℕ}
    (G : PositiveGrading (Obj k (Three k)) (IsSchur k (Three k)) L) :
    4 ≤ L := by
  have hschur0 : IsSchur k (Three k) (threePathObj0 k) :=
    line_isSchur k (Three k) ∅ (three_isUpperSet ∅)
  have hschur1 : IsSchur k (Three k) (threePathObj1 k) :=
    line_isSchur k (Three k) {Three.first} (three_isUpperSet {Three.first})
  have hschur3 : IsSchur k (Three k) (threePathObj3 k) :=
    line_isSchur k (Three k) {Three.first, Three.second}
      (three_isUpperSet {Three.first, Three.second})
  have hschur4 : IsSchur k (Three k) (threePathObj4 k) :=
    line_isSchur k (Three k) Set.univ (three_isUpperSet Set.univ)
  have h01 := G.lt_of_nonzero_not_isIso (threePathMap01 k)
    hschur0 hschur1 (threePathMap01_ne_zero k)
    (threePathMap01_not_isIso k)
  have h12 := G.lt_of_nonzero_not_isIso (threePathMap12 k)
    hschur1 (threeLinePlane_isSchur k) (threePathMap12_ne_zero k)
    (threePathMap12_not_isIso k)
  have h23 := G.lt_of_nonzero_not_isIso (threePathMap23 k)
    (threeLinePlane_isSchur k) hschur3 (threePathMap23_ne_zero k)
    (threePathMap23_not_isIso k)
  have h34 := G.lt_of_nonzero_not_isIso (threePathMap34 k)
    hschur3 hschur4 (threePathMap34_ne_zero k)
    (threePathMap34_not_isIso k)
  have htop := G.level_le (threePathObj4 k) hschur4
  omega

section GlobalBlock

variable {T : Type u} [PartialOrder T] [Fintype T]

/-- A consecutive three-element block in the chosen reverse linear extension
which is an antichain in the original poset. -/
structure ConsecutiveAntichainBlock (q : ℕ)
    (hq : q + 2 < Fintype.card T) : Prop where
  le_eq_of_mem_block : ∀ {s t : T},
    q ≤ (reverseIndex T s).val → (reverseIndex T s).val ≤ q + 2 →
    q ≤ (reverseIndex T t).val → (reverseIndex T t).val ≤ q + 2 →
    s ≤ t → s = t

/-- The global three-line subspace configuration: elements before the
antichain block receive the whole plane, the block receives the two axes and
diagonal, and later elements receive zero. -/
def blockPlaneSubspace (q : ℕ) (t : T) : Submodule k (k × k) :=
  if (reverseIndex T t).val < q then ⊤
  else if (reverseIndex T t).val = q then firstAxis k
  else if (reverseIndex T t).val = q + 1 then secondAxis k
  else if (reverseIndex T t).val = q + 2 then diagonal k
  else ⊥

/-- The global two-dimensional `T`-space attached to a consecutive
three-antichain block. -/
abbrev blockThreeLinePlane (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) : Obj k T where
  carrier := k × k
  subspace := blockPlaneSubspace (T := T) k q
  monotone_subspace := by
    intro s t hst
    have hindex : (reverseIndex T t).val ≤ (reverseIndex T s).val :=
      reverseIndex_anti T hst
    change blockPlaneSubspace (T := T) k q s ≤
      blockPlaneSubspace (T := T) k q t
    by_cases htpre : (reverseIndex T t).val < q
    · have httop : blockPlaneSubspace (T := T) k q t = ⊤ := by
        simp [blockPlaneSubspace, htpre]
      rw [httop]
      exact le_top
    by_cases hsafter : q + 2 < (reverseIndex T s).val
    · have hsnpre : ¬(reverseIndex T s).val < q := by omega
      have hs0 : (reverseIndex T s).val ≠ q := by omega
      have hs1 : (reverseIndex T s).val ≠ q + 1 := by omega
      have hs2 : (reverseIndex T s).val ≠ q + 2 := by omega
      have hsbot : blockPlaneSubspace (T := T) k q s = ⊥ := by
        simp [blockPlaneSubspace, hsnpre, hs0, hs1, hs2]
      rw [hsbot]
      exact bot_le
    · have hslo : q ≤ (reverseIndex T s).val := by omega
      have hshi : (reverseIndex T s).val ≤ q + 2 := by omega
      have htlo : q ≤ (reverseIndex T t).val := by omega
      have hthi : (reverseIndex T t).val ≤ q + 2 := by omega
      have heq : s = t :=
        D.le_eq_of_mem_block hslo hshi htlo hthi hst
      subst t
      exact le_rfl

/-- The first inserted map, with underlying linear map `1 ↦ e₁`. -/
def blockInMap (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    supportLine k T
        ⟨q + 1, Nat.lt_succ_iff.mpr (Nat.le_of_lt (by omega))⟩ ⟶
      blockThreeLinePlane k q hq D where
  linear :=
    { toFun := fun x ↦ (x, 0)
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
  map_subspace := by
    intro t x hx
    by_cases hpre : (reverseIndex T t).val < q
    · change (x, 0) ∈ blockPlaneSubspace (T := T) k q t
      simp [blockPlaneSubspace, hpre]
    by_cases heq : (reverseIndex T t).val = q
    · change (x, 0) ∈ blockPlaneSubspace (T := T) k q t
      simp [blockPlaneSubspace, hpre, heq, firstAxis]
    · have hx0 : x = 0 := by
        simpa [supportLine, supportAt, show
          ¬(reverseIndex T t).val ≤ q by omega] using hx
      subst x
      exact Submodule.zero_mem _

/-- The second inserted map, with underlying linear map `(x,y) ↦ x-y`. -/
def blockOutMap (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    blockThreeLinePlane k q hq D ⟶
      supportLine k T
        ⟨q + 2, Nat.lt_succ_iff.mpr (Nat.le_of_lt hq)⟩ where
  linear :=
    { toFun := fun x ↦ x.1 - x.2
      map_add' := by
        intros
        simp only [Prod.fst_add, Prod.snd_add]
        abel
      map_smul' := by intros; simp [mul_sub] }
  map_subspace := by
    intro t x hx
    change x.1 - x.2 ∈
      (supportLine k T
        ⟨q + 2, Nat.lt_succ_iff.mpr (Nat.le_of_lt hq)⟩).subspace t
    by_cases htarget : (reverseIndex T t).val < q + 2
    · simp [supportLine, supportAt, htarget]
    · have htargetle : ¬(reverseIndex T t).val ≤ q + 1 := by omega
      have hzero : x.1 - x.2 = 0 := by
        by_cases heq : (reverseIndex T t).val = q + 2
        · have hxdiag : x.1 = x.2 := by
            change x ∈ blockPlaneSubspace (T := T) k q t at hx
            simpa [blockPlaneSubspace, heq] using hx
          simpa [hxdiag]
        · have hx0 : x = 0 := by
            change x ∈ blockPlaneSubspace (T := T) k q t at hx
            have hpre : ¬(reverseIndex T t).val < q := by omega
            have h0 : (reverseIndex T t).val ≠ q := by omega
            have h1 : (reverseIndex T t).val ≠ q + 1 := by omega
            simpa [blockPlaneSubspace, hpre, h0, h1, heq] using hx
          subst x
          simp
      simpa [supportLine, supportAt, htargetle, hzero]

@[simp]
theorem blockInMap_apply (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) (x : k) :
    (blockInMap k q hq D).linear x = (x, 0) :=
  rfl

@[simp]
theorem blockOutMap_apply (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) (x : k × k) :
    (blockOutMap k q hq D).linear x = x.1 - x.2 :=
  rfl

theorem blockInMap_ne_zero (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    blockInMap k q hq D ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear (1 : k)) hzero
  have hcalc : (blockInMap k q hq D).linear (1 : k) = (1, 0) := rfl
  rw [hcalc, zero_linear, LinearMap.zero_apply] at h
  exact one_ne_zero (congrArg Prod.fst h)

theorem blockOutMap_ne_zero (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    blockOutMap k q hq D ≠ 0 := by
  intro hzero
  have h := congrArg (fun f ↦ f.linear ((1 : k), 0)) hzero
  have hcalc : (blockOutMap k q hq D).linear ((1 : k), 0) = 1 := by
    simpa using blockOutMap_apply k q hq D ((1 : k), 0)
  rw [hcalc, zero_linear, LinearMap.zero_apply] at h
  exact one_ne_zero h

theorem blockInMap_not_isIso (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    ¬ IsIso (blockInMap k q hq D) := by
  apply not_isIso_of_finrank_ne k
  simp only [Module.finrank_self, Module.finrank_prod]
  omega

theorem blockOutMap_not_isIso (q : ℕ) (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    ¬ IsIso (blockOutMap k q hq D) := by
  apply not_isIso_of_finrank_ne k
  simp only [Module.finrank_self, Module.finrank_prod]
  omega

/-- The global three-line plane remains Schur: the surrounding full and zero
subspaces add no endomorphism freedom, while the three block positions impose
the same axis/diagonal constraints as the local construction. -/
theorem blockThreeLinePlane_isSchur (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    IsSchur k T (blockThreeLinePlane k q hq D) := by
  let t₀ : T := reverseElement T ⟨q, by omega⟩
  let t₁ : T := reverseElement T ⟨q + 1, by omega⟩
  let t₂ : T := reverseElement T ⟨q + 2, hq⟩
  have hsub₀ : (blockThreeLinePlane k q hq D).subspace t₀ = firstAxis k := by
    change blockPlaneSubspace (T := T) k q t₀ = firstAxis k
    simp [blockPlaneSubspace, t₀, reverseIndex_reverseElement]
  have hsub₁ : (blockThreeLinePlane k q hq D).subspace t₁ = secondAxis k := by
    change blockPlaneSubspace (T := T) k q t₁ = secondAxis k
    simp [blockPlaneSubspace, t₁, reverseIndex_reverseElement]
  have hsub₂ : (blockThreeLinePlane k q hq D).subspace t₂ = diagonal k := by
    change blockPlaneSubspace (T := T) k q t₂ = diagonal k
    simp [blockPlaneSubspace, t₂, reverseIndex_reverseElement]
  constructor
  · refine ⟨((1 : k), 0), ?_⟩
    intro hzero
    exact one_ne_zero (congrArg Prod.fst hzero)
  · intro f
    let v₁ : k × k := f.linear ((1 : k), 0)
    let v₂ : k × k := f.linear (0, (1 : k))
    have hv₁₂ : v₁.2 = 0 := by
      have hmem := f.map_subspace t₀ ((1 : k), 0) (by
        rw [hsub₀]
        simp [firstAxis])
      rw [hsub₀] at hmem
      exact hmem
    have hv₂₁ : v₂.1 = 0 := by
      have hmem := f.map_subspace t₁ (0, (1 : k)) (by
        rw [hsub₁]
        simp [secondAxis])
      rw [hsub₁] at hmem
      exact hmem
    have hvdiag :
        (f.linear ((1 : k), 1)).1 = (f.linear ((1 : k), 1)).2 := by
      have hmem := f.map_subspace t₂ ((1 : k), 1) (by
        rw [hsub₂]
        simp [diagonal])
      rw [hsub₂] at hmem
      exact hmem
    have hsum : f.linear ((1 : k), 1) = v₁ + v₂ := by
      change f.linear ((1 : k), 1) =
        f.linear ((1 : k), 0) + f.linear (0, (1 : k))
      rw [← LinearMap.map_add]
      congr 1
      ext <;> simp
    have hv₁₁_eq_v₂₂ : v₁.1 = v₂.2 := by
      rw [hsum] at hvdiag
      simpa [hv₁₂, hv₂₁] using hvdiag
    refine ⟨v₁.1, ?_⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hdecomp : (x, y) =
        x • ((1 : k), 0) + y • (0, (1 : k)) := by
      ext <;> simp
    rw [hdecomp, LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul]
    apply Prod.ext
    · simp [v₁, v₂, hv₂₁, mul_comm]
    · simp [v₁, v₂, hv₁₂, hv₁₁_eq_v₂₂, mul_comm]

/-- A consecutive antichain block constructs the global Schur detour through
the three-line plane. -/
def ConsecutiveAntichainBlock.schurDetour (q : ℕ)
    (hq : q + 2 < Fintype.card T)
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    SchurDetour k T q hq where
  middle := blockThreeLinePlane k q hq D
  middle_schur := blockThreeLinePlane_isSchur k q hq D
  inMap := blockInMap k q hq D
  outMap := blockOutMap k q hq D
  inMap_ne_zero := blockInMap_ne_zero k q hq D
  outMap_ne_zero := blockOutMap_ne_zero k q hq D
  inMap_not_isIso := blockInMap_not_isIso k q hq D
  outMap_not_isIso := blockOutMap_not_isIso k q hq D

/-- The manuscript's strict equality obstruction for an antichain block in
the chosen reverse extension. -/
theorem card_add_one_le_of_consecutiveAntichainBlock
    {L q : ℕ}
    (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    {hq : q + 2 < Fintype.card T}
    (D : ConsecutiveAntichainBlock (T := T) q hq) :
    Fintype.card T + 1 ≤ L :=
  card_add_one_le_of_schurDetour k T G (D.schurDetour k q hq)

end GlobalBlock

end Field

end MagnitudeConjecture.PosetSpace
