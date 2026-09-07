import MagnitudeConjecture.CategoryTheory.MeshCategory
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

/-- The subspace spanned by all path-length components of degree at least `n`. -/
def lengthTail (T : RightMeshData Q) (x y : Q) (n : ℕ) :
    Submodule k (obj (k := k) T x ⟶ obj (k := k) T y) :=
  ⨆ d : {d : ℕ // n ≤ d}, lengthComponent (k := k) T x y d.1

theorem mem_lengthTail_of_mem_lengthComponent
    (T : RightMeshData Q) {x y : Q} {n d : ℕ}
    {f : obj (k := k) T x ⟶ obj (k := k) T y}
    (hnd : n ≤ d) (hf : f ∈ lengthComponent (k := k) T x y d) :
    f ∈ lengthTail (k := k) T x y n :=
  Submodule.mem_iSup_of_mem ⟨d, hnd⟩ hf

theorem lengthTail_zero_eq_top (T : RightMeshData Q) (x y : Q) :
    lengthTail (k := k) T x y 0 = ⊤ := by
  apply top_unique
  rw [← (lengthComponent_isInternal (k := k) T x y).submodule_iSup_eq_top]
  refine iSup_le fun d ↦ ?_
  exact le_iSup_of_le ⟨d, Nat.zero_le d⟩ (by rfl)

/-- Raising the path-length cutoff shrinks the corresponding tail. -/
theorem lengthTail_antitone (T : RightMeshData Q) (x y : Q)
    {m n : ℕ} (hmn : m ≤ n) :
    lengthTail (k := k) T x y n ≤ lengthTail (k := k) T x y m := by
  rw [lengthTail, lengthTail]
  refine iSup_le fun d ↦ ?_
  exact le_iSup_of_le ⟨d.1, hmn.trans d.2⟩ (by rfl)

/-- The path-length filtration of every mesh-category Hom space is
separated: a morphism in every tail is zero. -/
theorem eq_zero_of_mem_lengthTail_all
    (T : RightMeshData Q) {x y : Q}
    {f : obj (k := k) T x ⟶ obj (k := k) T y}
    (hf : ∀ n, f ∈ lengthTail (k := k) T x y n) :
    f = 0 := by
  classical
  letI : DirectSum.Decomposition (lengthComponent (k := k) T x y) :=
    (lengthComponent_isInternal (k := k) T x y).chooseDecomposition
  have hcomponent (d n : ℕ)
      (hfn : f ∈ lengthTail (k := k) T x y n) (hdn : d < n) :
      (DirectSum.decompose (lengthComponent (k := k) T x y) f d).1 = 0 := by
    rw [lengthTail] at hfn
    refine Submodule.iSup_induction
      (fun e : {e : ℕ // n ≤ e} ↦ lengthComponent (k := k) T x y e.1)
      (motive := fun g ↦
        (DirectSum.decompose (lengthComponent (k := k) T x y) g d).1 = 0)
      hfn ?_ (by simp) ?_
    · intro e g hg
      exact DirectSum.decompose_of_mem_ne
        (lengthComponent (k := k) T x y) hg
        (Nat.ne_of_lt (hdn.trans_le e.2)).symm
    · intro g h hg hh
      rw [DirectSum.decompose_add]
      change
        (DirectSum.decompose (lengthComponent (k := k) T x y) g d).1 +
          (DirectSum.decompose (lengthComponent (k := k) T x y) h d).1 = 0
      rw [hg, hh, add_zero]
  rw [← DirectSum.sum_support_decompose
    (lengthComponent (k := k) T x y) f]
  apply Finset.sum_eq_zero
  intro d hd
  exact hcomponent d (d + 1) (hf (d + 1)) (Nat.lt_succ_self d)

/-- Between distinct vertices every mesh morphism has positive path length. -/
theorem lengthTail_one_eq_top_of_ne (T : RightMeshData Q)
    {x y : Q} (hyx : y ≠ x) :
    lengthTail (k := k) T x y 1 = ⊤ := by
  apply top_unique
  rw [← (lengthComponent_isInternal (k := k) T x y).submodule_iSup_eq_top]
  refine iSup_le fun d ↦ ?_
  by_cases hd : d = 0
  · subst d
    rw [lengthComponent_zero_eq_bot_of_ne (k := k) T hyx]
    exact bot_le
  · exact le_iSup_of_le ⟨d, Nat.one_le_iff_ne_zero.2 hd⟩ (by rfl)

/-- The identity of a mesh vertex does not lie in the positive-degree tail. -/
theorem id_not_mem_lengthTail_one (T : RightMeshData Q) (x : Q) :
    𝟙 (obj (k := k) T x) ∉ lengthTail (k := k) T x x 1 := by
  classical
  letI : DirectSum.Decomposition (lengthComponent (k := k) T x x) :=
    (lengthComponent_isInternal (k := k) T x x).chooseDecomposition
  intro hid
  rw [lengthTail] at hid
  have hzero :
      (DirectSum.decompose (lengthComponent (k := k) T x x)
          (𝟙 (obj (k := k) T x)) 0).1 = 0 := by
    refine Submodule.iSup_induction
      (fun d : {d : ℕ // 1 ≤ d} ↦ lengthComponent (k := k) T x x d.1)
      (motive := fun f ↦
        (DirectSum.decompose (lengthComponent (k := k) T x x) f 0).1 = 0)
      hid ?_ (by simp) ?_
    · intro d f hf
      exact DirectSum.decompose_of_mem_ne
        (lengthComponent (k := k) T x x) hf
        (Nat.ne_of_gt d.2)
    · intro f g hf hg
      rw [DirectSum.decompose_add]
      change (DirectSum.decompose (lengthComponent (k := k) T x x) f 0).1 +
        (DirectSum.decompose (lengthComponent (k := k) T x x) g 0).1 = 0
      rw [hf, hg, add_zero]
  have hidComponent :
      (DirectSum.decompose (lengthComponent (k := k) T x x)
          (𝟙 (obj (k := k) T x)) 0).1 = 𝟙 (obj (k := k) T x) :=
    DirectSum.decompose_of_mem_same _
      (id_mem_lengthComponent_zero (k := k) T x)
  have hidZero : 𝟙 (obj (k := k) T x) = 0 := by
    exact hidComponent.symm.trans hzero
  exact id_ne_zero (k := k) T x hidZero

theorem lengthTail_eq_bot_of_components
    (T : RightMeshData Q) (x y : Q) (n : ℕ)
    (hzero : ∀ d, n ≤ d → lengthComponent (k := k) T x y d = ⊥) :
    lengthTail (k := k) T x y n = ⊥ := by
  rw [lengthTail, iSup_eq_bot]
  intro d
  exact hzero d.1 d.2

theorem comp_mem_lengthTail
    (T : RightMeshData Q) {x y z : Q} {i j : ℕ}
    {f : obj (k := k) T x ⟶ obj (k := k) T y}
    {g : obj (k := k) T y ⟶ obj (k := k) T z}
    (hf : f ∈ lengthTail (k := k) T x y i)
    (hg : g ∈ lengthTail (k := k) T y z j) :
    f ≫ g ∈ lengthTail (k := k) T x z (i + j) := by
  rw [lengthTail] at hf hg ⊢
  refine Submodule.iSup_induction
    (fun d : {d : ℕ // i ≤ d} ↦ lengthComponent (k := k) T x y d.1)
    (motive := fun f ↦ f ≫ g ∈
      ⨆ d : {d : ℕ // i + j ≤ d}, lengthComponent (k := k) T x z d.1)
    hf ?_ (by simp) ?_
  · intro di f hfi
    refine Submodule.iSup_induction
      (fun d : {d : ℕ // j ≤ d} ↦ lengthComponent (k := k) T y z d.1)
      (motive := fun g ↦ f ≫ g ∈
        ⨆ d : {d : ℕ // i + j ≤ d}, lengthComponent (k := k) T x z d.1)
      hg ?_ (by simp) ?_
    · intro dj g hgj
      exact Submodule.mem_iSup_of_mem
        ⟨di.1 + dj.1, Nat.add_le_add di.2 dj.2⟩
        (comp_mem_lengthComponent T hfi hgj)
    · intro g h ihg ihh
      simpa only [Preadditive.comp_add] using Submodule.add_mem _ ihg ihh
  · intro f h ihf ihh
    simpa only [Preadditive.add_comp] using Submodule.add_mem _ ihf ihh

/-- Distinct quiver vertices cannot become isomorphic in the raw mesh
category. -/
theorem eq_of_obj_iso (T : RightMeshData Q) {x y : Q}
    (e : obj (k := k) T x ≅ obj (k := k) T y) : x = y := by
  by_contra hxy
  have hhom : e.hom ∈ lengthTail (k := k) T x y 1 := by
    rw [lengthTail_one_eq_top_of_ne (k := k) T (Ne.symm hxy)]
    exact Submodule.mem_top
  have hinv : e.inv ∈ lengthTail (k := k) T y x 1 := by
    rw [lengthTail_one_eq_top_of_ne (k := k) T hxy]
    exact Submodule.mem_top
  have hcomp := comp_mem_lengthTail (k := k) T hhom hinv
  have hpositive : e.hom ≫ e.inv ∈ lengthTail (k := k) T x x 1 :=
    lengthTail_antitone (k := k) T x x (by omega) hcomp
  rw [e.hom_inv_id] at hpositive
  exact id_not_mem_lengthTail_one (k := k) T x hpositive

/-- The raw mesh category is skeletal. -/
theorem rawCategory_skeletal (T : RightMeshData Q) :
    Skeletal (RawCategory (k := k) T) := by
  intro x y hxy
  obtain ⟨e⟩ := hxy
  apply CategoryTheory.Quotient.ext
  exact eq_of_obj_iso (k := k) T e

theorem exists_lengthComponent_cutoff
    (T : RightMeshData Q) (x y : Q)
    [FiniteDimensional k (obj (k := k) T x ⟶ obj (k := k) T y)] :
    ∃ n, ∀ d, n ≤ d → lengthComponent (k := k) T x y d = ⊥ := by
  let h := lengthComponent_isInternal (k := k) T x y
  letI : Fintype {d : ℕ // lengthComponent (k := k) T x y d ≠ ⊥} :=
    h.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  refine ⟨1 + ∑ d : {d : ℕ // lengthComponent (k := k) T x y d ≠ ⊥}, d.1, ?_⟩
  intro d hd
  by_contra hne
  let e : {d : ℕ // lengthComponent (k := k) T x y d ≠ ⊥} := ⟨d, hne⟩
  have hle : d ≤ ∑ a : {d : ℕ // lengthComponent (k := k) T x y d ≠ ⊥}, a.1 := by
    exact Finset.single_le_sum
      (f := fun a : {d : ℕ // lengthComponent (k := k) T x y d ≠ ⊥} ↦ a.1)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e)
  omega

/-- On a finite vertex set, finite-dimensionality of every mesh Hom space
gives one path-length cutoff valid for all pairs of vertices. -/
theorem exists_uniform_lengthComponent_cutoff
    [Fintype Q] (T : RightMeshData Q)
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (obj (k := k) T x ⟶ obj (k := k) T y)) :
    ∃ n, ∀ x y d, n ≤ d →
      lengthComponent (k := k) T x y d = ⊥ := by
  classical
  let cutoff (p : Q × Q) : ℕ := by
    letI : FiniteDimensional k
        (obj (k := k) T p.1 ⟶ obj (k := k) T p.2) :=
      hfinite p.1 p.2
    exact (exists_lengthComponent_cutoff (k := k) T p.1 p.2).choose
  have hcutoff (p : Q × Q) :
      ∀ d, cutoff p ≤ d →
        lengthComponent (k := k) T p.1 p.2 d = ⊥ := by
    letI : FiniteDimensional k
        (obj (k := k) T p.1 ⟶ obj (k := k) T p.2) :=
      hfinite p.1 p.2
    simpa only [cutoff] using
      (exists_lengthComponent_cutoff (k := k) T p.1 p.2).choose_spec
  refine ⟨∑ p : Q × Q, cutoff p, ?_⟩
  intro x y d hnd
  apply hcutoff (x, y) d
  have hle : cutoff (x, y) ≤ ∑ p : Q × Q, cutoff p := by
    exact Finset.single_le_sum
      (f := cutoff) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (x, y))
  exact hle.trans hnd

/-- The path-length pieces of a vertex endomorphism ring, with the ambient
type presented as `End` so that ring operations are definitionally visible. -/
def homEndLinearEquiv (T : RightMeshData Q) (x : Q) :
    (obj (k := k) T x ⟶ obj (k := k) T x) ≃ₗ[k]
      End (obj (k := k) T x) where
  toFun := End.of
  invFun := End.asHom
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

def endLengthComponent (T : RightMeshData Q) (x : Q) (n : ℕ) :
    Submodule k (End (obj (k := k) T x)) :=
  (lengthComponent (k := k) T x x n).map (homEndLinearEquiv (k := k) T x).toLinearMap

theorem endLengthComponent_isInternal (T : RightMeshData Q) (x : Q) :
    DirectSum.IsInternal (endLengthComponent (k := k) T x) := by
  exact MagnitudeConjecture.Graded.image_isInternal_of_equiv
    (lengthComponent (k := k) T x x)
    (lengthComponent_isInternal (k := k) T x x)
    (homEndLinearEquiv (k := k) T x)

noncomputable local instance endLengthComponentDecomposition
    (T : RightMeshData Q) (x : Q) :
    DirectSum.Decomposition (endLengthComponent (k := k) T x) :=
  (endLengthComponent_isInternal (k := k) T x).chooseDecomposition

/-- The positive-degree filtration on a vertex endomorphism ring. -/
def endLengthTail (T : RightMeshData Q) (x : Q) (n : ℕ) :
    Submodule k (End (obj (k := k) T x)) :=
  (lengthTail (k := k) T x x n).map (homEndLinearEquiv (k := k) T x).toLinearMap

theorem mem_endLengthTail_of_mem_endLengthComponent
    (T : RightMeshData Q) (x : Q) {n d : ℕ}
    {f : End (obj (k := k) T x)}
    (hnd : n ≤ d) (hf : f ∈ endLengthComponent (k := k) T x d) :
    f ∈ endLengthTail (k := k) T x n := by
  rcases hf with ⟨f, hf, rfl⟩
  exact ⟨f, mem_lengthTail_of_mem_lengthComponent (k := k) T hnd hf, rfl⟩

theorem endLengthTail_zero_eq_top (T : RightMeshData Q) (x : Q) :
    endLengthTail (k := k) T x 0 = ⊤ := by
  rw [endLengthTail, lengthTail_zero_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (homEndLinearEquiv (k := k) T x).surjective

theorem endLengthTail_eq_bot_of_components
    (T : RightMeshData Q) (x : Q) (n : ℕ)
    (hzero : ∀ d, n ≤ d → endLengthComponent (k := k) T x d = ⊥) :
    endLengthTail (k := k) T x n = ⊥ := by
  have hsource : ∀ d, n ≤ d → lengthComponent (k := k) T x x d = ⊥ := by
    intro d hd
    apply bot_unique
    intro f hf
    have himage : (homEndLinearEquiv (k := k) T x) f ∈
        endLengthComponent (k := k) T x d :=
      ⟨f, hf, rfl⟩
    rw [hzero d hd] at himage
    exact (homEndLinearEquiv (k := k) T x).injective (by simpa using himage)
  rw [endLengthTail, lengthTail_eq_bot_of_components (k := k) T x x n hsource]
  exact Submodule.map_bot _

theorem mul_mem_endLengthTail
    (T : RightMeshData Q) (x : Q) {i j : ℕ}
    {f g : End (obj (k := k) T x)}
    (hf : f ∈ endLengthTail (k := k) T x i)
    (hg : g ∈ endLengthTail (k := k) T x j) :
    f * g ∈ endLengthTail (k := k) T x (i + j) := by
  rcases hf with ⟨f, hf, rfl⟩
  rcases hg with ⟨g, hg, rfl⟩
  refine ⟨g ≫ f, ?_, rfl⟩
  change g ≫ f ∈ lengthTail (k := k) T x x (i + j)
  simpa only [Nat.add_comm] using comp_mem_lengthTail (k := k) T hg hf

theorem exists_endLengthComponent_cutoff
    (T : RightMeshData Q) (x : Q)
    [FiniteDimensional k (End (obj (k := k) T x))] :
    ∃ n, ∀ d, n ≤ d → endLengthComponent (k := k) T x d = ⊥ := by
  letI : FiniteDimensional k (obj (k := k) T x ⟶ obj (k := k) T x) :=
    FiniteDimensional.of_injective
      (homEndLinearEquiv (k := k) T x).toLinearMap
      (homEndLinearEquiv (k := k) T x).injective
  obtain ⟨n, hn⟩ := exists_lengthComponent_cutoff (k := k) T x x
  refine ⟨n, fun d hd ↦ ?_⟩
  rw [endLengthComponent, hn d hd]
  exact Submodule.map_bot _

theorem one_mem_endLengthComponent_zero (T : RightMeshData Q) (x : Q) :
    (1 : End (obj (k := k) T x)) ∈ endLengthComponent (k := k) T x 0 := by
  exact ⟨𝟙 (obj (k := k) T x), id_mem_lengthComponent_zero (k := k) T x, rfl⟩

theorem endLengthComponent_zero_self (T : RightMeshData Q) (x : Q) :
    endLengthComponent (k := k) T x 0 =
      k ∙ (1 : End (obj (k := k) T x)) := by
  rw [endLengthComponent, lengthComponent_zero_self,
    Submodule.map_span, Set.image_singleton]
  rfl

theorem mem_endLengthTail_one_of_degreeZero_eq_zero
    (T : RightMeshData Q) (x : Q)
    (f : End (obj (k := k) T x))
    (hzero : (DirectSum.decompose (endLengthComponent (k := k) T x) f 0).1 = 0) :
    f ∈ endLengthTail (k := k) T x 1 := by
  classical
  rw [← DirectSum.sum_support_decompose (endLengthComponent (k := k) T x) f]
  apply Submodule.sum_mem
  intro d hd
  apply mem_endLengthTail_of_mem_endLengthComponent T x (n := 1) (d := d)
  · exact Nat.one_le_iff_ne_zero.2 fun hd0 ↦ by
      subst d
      exact (DFinsupp.mem_support_iff.mp hd) (Subtype.ext hzero)
  · exact (DirectSum.decompose (endLengthComponent (k := k) T x) f d).2

theorem isNilpotent_of_degreeZero_eq_zero
    (T : RightMeshData Q) (x : Q)
    [FiniteDimensional k (End (obj (k := k) T x))]
    (f : End (obj (k := k) T x))
    (hzero : (DirectSum.decompose (endLengthComponent (k := k) T x) f 0).1 = 0) :
    IsNilpotent f := by
  have hpowAll : ∀ n, f ^ n ∈ endLengthTail (k := k) T x n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, endLengthTail_zero_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        rw [pow_succ]
        exact mul_mem_endLengthTail T x ih
          (mem_endLengthTail_one_of_degreeZero_eq_zero T x f hzero)
  obtain ⟨n, hn⟩ := exists_endLengthComponent_cutoff (k := k) T x
  refine ⟨n, ?_⟩
  have hpow := hpowAll n
  rw [endLengthTail_eq_bot_of_components (k := k) T x n hn] at hpow
  simpa using hpow

/-- A nonzero scalar identity plus a positive-length endomorphism is an
isomorphism.  Finite-dimensionality makes the positive-length summand
nilpotent. -/
theorem isIso_smul_id_add_of_mem_lengthTail_one
    (T : RightMeshData Q) (x : Q)
    [FiniteDimensional k (End (obj (k := k) T x))]
    (c : k) (hc : c ≠ 0) (r : End (obj (k := k) T x))
    (hr : End.asHom r ∈ lengthTail (k := k) T x x 1) :
    IsIso (c • 𝟙 (obj (k := k) T x) + End.asHom r) := by
  have hrTail : r ∈ endLengthTail (k := k) T x 1 :=
    ⟨End.asHom r, hr, rfl⟩
  have hpowAll : ∀ n, r ^ n ∈ endLengthTail (k := k) T x n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, endLengthTail_zero_eq_top]
        exact Submodule.mem_top
    | succ n ih =>
        rw [pow_succ]
        exact mul_mem_endLengthTail T x ih hrTail
  obtain ⟨n, hn⟩ := exists_endLengthComponent_cutoff (k := k) T x
  have hrnil : IsNilpotent r := by
    refine ⟨n, ?_⟩
    have hpow := hpowAll n
    rw [endLengthTail_eq_bot_of_components (k := k) T x n hn] at hpow
    simpa using hpow
  have hu : IsUnit (c • (1 : End (obj (k := k) T x))) := by
    rw [Algebra.smul_def]
    exact (isUnit_iff_ne_zero.mpr hc).map
      (algebraMap k (End (obj (k := k) T x)))
  have hcomm : Commute r (c • (1 : End (obj (k := k) T x))) := by
    rw [Algebra.smul_def]
    exact (Algebra.commutes c r).symm
  apply (isUnit_iff_isIso _).1
  change IsUnit (c • (1 : End (obj (k := k) T x)) + r)
  simpa only [add_comm] using
    hrnil.isUnit_add_right_of_commute hu hcomm

/-- A finite-dimensional mesh-category vertex has a local endomorphism ring. -/
theorem end_isLocalRing_of_finiteDimensional
    (T : RightMeshData Q) (x : Q)
    [FiniteDimensional k (End (obj (k := k) T x))] :
    IsLocalRing (End (obj (k := k) T x)) := by
  classical
  letI : Nontrivial (End (obj (k := k) T x)) :=
    ⟨1, 0, id_ne_zero (k := k) T x⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  have hdegreeZero :
      (DirectSum.decompose (endLengthComponent (k := k) T x) f 0).1 ∈
        k ∙ (1 : End (obj (k := k) T x)) := by
    rw [← endLengthComponent_zero_self (k := k) T x]
    exact (DirectSum.decompose (endLengthComponent (k := k) T x) f 0).2
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hdegreeZero
  let r : End (obj (k := k) T x) := f - a • 1
  have hrzero :
      (DirectSum.decompose (endLengthComponent (k := k) T x) r 0).1 = 0 := by
    change (DirectSum.decompose (endLengthComponent (k := k) T x)
      (f - a • (1 : End (obj (k := k) T x))) 0).1 = 0
    rw [DirectSum.decompose_sub, DirectSum.decompose_smul]
    change (DirectSum.decompose (endLengthComponent (k := k) T x) f 0).1 -
      a • (DirectSum.decompose (endLengthComponent (k := k) T x)
        (1 : End (obj (k := k) T x)) 0).1 = 0
    rw [← ha, DirectSum.decompose_of_mem_same
      (endLengthComponent (k := k) T x) (one_mem_endLengthComponent_zero T x)]
    simp
  have hrnil : IsNilpotent r := isNilpotent_of_degreeZero_eq_zero T x r hrzero
  by_cases hne : a = 0
  · right
    subst a
    simpa [r] using hrnil.isUnit_one_sub
  · left
    have hu : IsUnit (a • (1 : End (obj (k := k) T x))) := by
      rw [Algebra.smul_def]
      exact (isUnit_iff_ne_zero.mpr hne).map (algebraMap k (End (obj (k := k) T x)))
    have hcomm : Commute r (a • (1 : End (obj (k := k) T x))) := by
      rw [Algebra.smul_def]
      exact (Algebra.commutes a r).symm
    simpa [r] using hrnil.isUnit_add_right_of_commute hu hcomm

end MagnitudeConjecture.MeshCategory
