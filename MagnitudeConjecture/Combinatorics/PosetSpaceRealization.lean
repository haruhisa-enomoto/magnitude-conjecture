import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Order.UpperLower.Basic

/-!
# Finite poset spaces and the support chain

This file begins the concrete realization layer used by the frozen
manuscript.  It defines finite-dimensional spaces equipped with a monotone
family of subspaces indexed by a finite poset.  It also constructs, from a
reverse linear extension, the canonical chain of one-dimensional poset spaces
from empty support to full support.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

variable (k T : Type u) [Field k] [PartialOrder T]

/-- A finite-dimensional `T`-space: a vector space with a monotone family of
subspaces indexed by the poset `T`. -/
structure Obj where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module k carrier]
  [finiteDimensional : FiniteDimensional k carrier]
  subspace : T → Submodule k carrier
  monotone_subspace : ∀ ⦃s t : T⦄, s ≤ t → subspace s ≤ subspace t

attribute [instance] Obj.addCommGroup Obj.module Obj.finiteDimensional

instance : CoeSort (Obj k T) (Type u) :=
  ⟨Obj.carrier⟩

/-- A morphism of `T`-spaces is a linear map preserving every distinguished
subspace. -/
structure Hom (X Y : Obj k T) where
  linear : X →ₗ[k] Y
  map_subspace : ∀ (t : T) (x : X),
    x ∈ X.subspace t → linear x ∈ Y.subspace t

@[ext]
theorem Hom.ext {X Y : Obj k T} {f g : Hom k T X Y}
    (h : f.linear = g.linear) : f = g := by
  cases f with
  | mk fl fp =>
      cases g with
      | mk gl gp =>
          cases h
          rfl

instance : CategoryTheory.Category (Obj k T) where
  Hom := Hom k T
  id X :=
    { linear := LinearMap.id
      map_subspace := fun _ _ hx ↦ hx }
  comp f g :=
    { linear := g.linear.comp f.linear
      map_subspace := fun t x hx ↦ g.map_subspace t _ (f.map_subspace t x hx) }
  assoc := by intros; ext; rfl
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl

open CategoryTheory
open CategoryTheory.Limits

instance {X Y : Obj k T} : Zero (X ⟶ Y) where
  zero :=
    { linear := 0
      map_subspace := by simp }

@[simp]
theorem zero_linear {X Y : Obj k T} :
    (0 : X ⟶ Y).linear = 0 :=
  rfl

instance {X Y : Obj k T} : Add (X ⟶ Y) where
  add f g :=
    { linear := f.linear + g.linear
      map_subspace := fun t x hx ↦
        (Y.subspace t).add_mem (f.map_subspace t x hx)
          (g.map_subspace t x hx) }

@[simp]
theorem add_linear {X Y : Obj k T} (f g : X ⟶ Y) :
    (f + g).linear = f.linear + g.linear :=
  rfl

instance {X Y : Obj k T} : Neg (X ⟶ Y) where
  neg f :=
    { linear := -f.linear
      map_subspace := fun t x hx ↦
        (Y.subspace t).neg_mem (f.map_subspace t x hx) }

@[simp]
theorem neg_linear {X Y : Obj k T} (f : X ⟶ Y) :
    (-f).linear = -f.linear :=
  rfl

instance {X Y : Obj k T} : Sub (X ⟶ Y) where
  sub f g :=
    { linear := f.linear - g.linear
      map_subspace := fun t x hx ↦
        (Y.subspace t).sub_mem (f.map_subspace t x hx)
          (g.map_subspace t x hx) }

@[simp]
theorem sub_linear {X Y : Obj k T} (f g : X ⟶ Y) :
    (f - g).linear = f.linear - g.linear :=
  rfl

instance {X Y : Obj k T} : SMul ℕ (X ⟶ Y) where
  smul n f :=
    { linear := n • f.linear
      map_subspace := fun t x hx ↦
        (Y.subspace t).nsmul_mem (f.map_subspace t x hx) n }

@[simp]
theorem nsmul_linear {X Y : Obj k T} (n : ℕ) (f : X ⟶ Y) :
    (n • f).linear = n • f.linear :=
  rfl

instance {X Y : Obj k T} : SMul ℤ (X ⟶ Y) where
  smul n f :=
    { linear := n • f.linear
      map_subspace := fun t x hx ↦
        (Y.subspace t).toAddSubgroup.zsmul_mem
          (f.map_subspace t x hx) n }

@[simp]
theorem zsmul_linear {X Y : Obj k T} (n : ℤ) (f : X ⟶ Y) :
    (n • f).linear = n • f.linear :=
  rfl

instance {X Y : Obj k T} : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup (fun f : X ⟶ Y ↦ f.linear)
    (fun _ _ h ↦ Hom.ext (k := k) (T := T) h) rfl
      (fun _ _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance {X Y : Obj k T} : SMul k (X ⟶ Y) where
  smul c f :=
    { linear := c • f.linear
      map_subspace := fun t x hx ↦
        (Y.subspace t).smul_mem c (f.map_subspace t x hx) }

@[simp]
theorem smul_linear {X Y : Obj k T} (c : k) (f : X ⟶ Y) :
    (c • f).linear = c • f.linear :=
  rfl

instance {X Y : Obj k T} : Module k (X ⟶ Y) :=
  Function.Injective.module k
    { toFun := fun f : X ⟶ Y ↦ f.linear
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ h ↦ Hom.ext (k := k) (T := T) h) (fun _ _ ↦ rfl)

instance : Preadditive (Obj k T) where
  add_comp := by
    intro P Q R f f' g
    apply Hom.ext
    apply LinearMap.ext
    intro x
    exact g.linear.map_add (f.linear x) (f'.linear x)
  comp_add := by
    intro P Q R f g g'
    apply Hom.ext
    rfl

instance : Linear k (Obj k T) where
  smul_comp := by
    intro X Y Z r f g
    apply Hom.ext
    apply LinearMap.ext
    intro x
    exact g.linear.map_smul r (f.linear x)
  comp_smul := by
    intro X Y Z f r g
    apply Hom.ext
    rfl

instance : HasZeroMorphisms (Obj k T) where
  comp_zero := by
    intros
    apply Hom.ext
    apply LinearMap.ext
    intro x
    rfl
  zero_comp := by
    intros
    apply Hom.ext
    apply LinearMap.ext
    intro x
    exact LinearMap.map_zero _

@[simp]
theorem id_linear (X : Obj k T) :
    (𝟙 X : X ⟶ X).linear = LinearMap.id :=
  rfl

@[simp]
theorem comp_linear {X Y Z : Obj k T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).linear = g.linear.comp f.linear :=
  rfl

/-- The one-dimensional `T`-space whose distinguished subspace is `k`
exactly on the upper set `U`. -/
abbrev line (U : Set T) (hU : IsUpperSet U) : Obj k T := by
  classical
  exact
    { carrier := k
      subspace := fun t ↦ if t ∈ U then ⊤ else ⊥
      monotone_subspace := by
        intro s t hst
        by_cases hs : s ∈ U
        · have ht : t ∈ U := hU hst hs
          simp [hs, ht]
        · simp [hs] }

@[simp]
theorem line_subspace_of_mem (U : Set T) (hU : IsUpperSet U) (t : T)
    (ht : t ∈ U) :
    (line k T U hU).subspace t = ⊤ := by
  classical
  change (if t ∈ U then ⊤ else ⊥) = ⊤
  rw [if_pos ht]

@[simp]
theorem line_subspace_of_not_mem (U : Set T) (hU : IsUpperSet U) (t : T)
    (ht : t ∉ U) :
    (line k T U hU).subspace t = ⊥ := by
  classical
  change (if t ∈ U then ⊤ else ⊥) = ⊥
  rw [if_neg ht]

/-- Inclusion of upper supports gives a morphism of one-dimensional
`T`-spaces with underlying identity map. -/
def lineHom {U V : Set T} {hU : IsUpperSet U} {hV : IsUpperSet V}
    (hUV : U ⊆ V) : line k T U hU ⟶ line k T V hV := by
  classical
  exact
    { linear := LinearMap.id
      map_subspace := by
        intro t x hx
        by_cases ht : t ∈ U
        · change LinearMap.id x ∈ if t ∈ V then ⊤ else ⊥
          rw [if_pos (hUV ht)]
          exact Submodule.mem_top
        · have hx0 : x = 0 := by
            change x ∈ if t ∈ U then ⊤ else ⊥ at hx
            rw [if_neg ht] at hx
            simpa using hx
          subst x
          simp }

@[simp]
theorem lineHom_linear {U V : Set T} {hU : IsUpperSet U}
    {hV : IsUpperSet V} (hUV : U ⊆ V) :
    (lineHom k T (hU := hU) (hV := hV) hUV).linear =
      (LinearMap.id : k →ₗ[k] k) :=
  rfl

/-- Every support-inclusion map is nonzero. -/
theorem lineHom_ne_zero {U V : Set T} {hU : IsUpperSet U}
    {hV : IsUpperSet V} (hUV : U ⊆ V) :
    lineHom k T (hU := hU) (hV := hV) hUV ≠ 0 := by
  intro hzero
  have hlinear := congrArg Hom.linear hzero
  have hidzero : (LinearMap.id : k →ₗ[k] k) = 0 := by
    simpa using hlinear
  have happ := LinearMap.congr_fun hidzero (1 : k)
  have hone : (1 : k) = 0 := by simpa using happ
  exact (one_ne_zero : (1 : k) ≠ 0) hone

/-- A strict inclusion of upper supports gives a nonisomorphism between the
corresponding one-dimensional `T`-spaces. -/
theorem lineHom_not_isIso {U V : Set T} {hU : IsUpperSet U}
    {hV : IsUpperSet V} (hUV : U ⊂ V) :
    ¬ IsIso (lineHom k T (hU := hU) (hV := hV) hUV.1) := by
  classical
  intro hIso
  let f := lineHom k T (hU := hU) (hV := hV) hUV.1
  letI : IsIso f := hIso
  obtain ⟨t, htV, htU⟩ := Set.exists_of_ssubset hUV
  have hinv_mem : (inv f).linear (1 : k) ∈
      (line k T U hU).subspace t := by
    apply (inv f).map_subspace
    change (1 : k) ∈ if t ∈ V then ⊤ else ⊥
    rw [if_pos htV]
    exact Submodule.mem_top
  have hinv_zero : (inv f).linear (1 : k) = 0 := by
    change (inv f).linear (1 : k) ∈ if t ∈ U then ⊤ else ⊥ at hinv_mem
    rw [if_neg htU] at hinv_mem
    simpa using hinv_mem
  have hone : (1 : k) = 0 := by
    have hcomp : inv f ≫ f = 𝟙 (line k T V hV) := by
      simpa using (IsIso.inv_hom_id_assoc f (𝟙 _))
    have happ : f.linear ((inv f).linear (1 : k)) = 1 := by
      have h := congrArg
        (fun g : line k T V hV ⟶ line k T V hV ↦ g.linear (1 : k)) hcomp
      exact h
    calc
      (1 : k) = f.linear ((inv f).linear 1) := happ.symm
      _ = f.linear 0 := by rw [hinv_zero]
      _ = 0 := LinearMap.map_zero f.linear
  exact one_ne_zero hone

/-- A `T`-space is Schur when its total space is nonzero and every
endomorphism is scalar.  In the directed realization this is the concrete
property enjoyed by every indecomposable object. -/
def IsSchur (X : Obj k T) : Prop :=
  (∃ x : X, x ≠ 0) ∧
    ∀ f : X ⟶ X, ∃ a : k,
      f.linear = a • (LinearMap.id : X →ₗ[k] X)

/-- Every one-dimensional support object is Schur. -/
theorem line_isSchur (U : Set T) (hU : IsUpperSet U) :
    IsSchur k T (line k T U hU) := by
  constructor
  · exact ⟨1, one_ne_zero⟩
  · intro f
    refine ⟨f.linear 1, ?_⟩
    apply LinearMap.ext
    intro x
    calc
      f.linear x = f.linear (x • (1 : k)) := by simp
      _ = x • f.linear 1 := by rw [LinearMap.map_smul]
      _ = (f.linear 1) • (LinearMap.id : k →ₗ[k] k) x := by
        simp [mul_comm]

section Finite

variable [Fintype T]

/-- The reverse linear extension used in the manuscript: an increasing
linear extension of the dual poset. -/
abbrev ReverseExtension := LinearExtension (OrderDual T)

instance : Fintype (ReverseExtension T) :=
  inferInstanceAs (Fintype (OrderDual T))

/-- Increasing enumeration of the chosen reverse linear extension. -/
def reverseOrderIso : Fin (Fintype.card T) ≃o ReverseExtension T :=
  Fintype.orderIsoFinOfCardEq (ReverseExtension T) rfl

/-- The position of a poset element in the chosen reverse linear extension. -/
def reverseIndex (t : T) : Fin (Fintype.card T) :=
  (reverseOrderIso T).symm
    (toLinearExtension (OrderDual.toDual t))

/-- The reverse-extension index reverses the original partial order. -/
theorem reverseIndex_anti {s t : T} (hst : s ≤ t) :
    reverseIndex T t ≤ reverseIndex T s := by
  have hdual : OrderDual.toDual t ≤ OrderDual.toDual s := hst
  have hext : toLinearExtension (OrderDual.toDual t) ≤
      toLinearExtension (OrderDual.toDual s) :=
    (toLinearExtension : OrderDual T →o ReverseExtension T).monotone hdual
  exact (reverseOrderIso T).symm.monotone hext

/-- The upper support consisting of the first `j` elements of the reverse
linear extension. -/
def supportAt (j : Fin (Fintype.card T + 1)) : Set T :=
  {t | (reverseIndex T t).val < j.val}

/-- Every prefix of the reverse linear extension is an upper set in the
original poset. -/
theorem supportAt_isUpperSet (j : Fin (Fintype.card T + 1)) :
    IsUpperSet (supportAt T j) := by
  intro s t hst hs
  have hindex : reverseIndex T t ≤ reverseIndex T s :=
    reverseIndex_anti T hst
  change (reverseIndex T s).val < j.val at hs
  have hindex_val : (reverseIndex T t).val ≤ (reverseIndex T s).val := hindex
  exact lt_of_le_of_lt hindex_val hs

/-- The support prefixes are monotone in the prefix length. -/
theorem supportAt_mono {i j : Fin (Fintype.card T + 1)} (hij : i ≤ j) :
    supportAt T i ⊆ supportAt T j := by
  intro t ht
  change (reverseIndex T t).val < i.val at ht
  have hij_val : i.val ≤ j.val := hij
  exact lt_of_lt_of_le ht hij_val

/-- The element occupying position `j` in the reverse linear extension. -/
def reverseElement (j : Fin (Fintype.card T)) : T :=
  OrderDual.ofDual (reverseOrderIso T j)

@[simp]
theorem reverseIndex_reverseElement (j : Fin (Fintype.card T)) :
    reverseIndex T (reverseElement T j) = j := by
  exact (reverseOrderIso T).symm_apply_apply j

/-- A selectable reverse linear enumeration of a finite poset.  Unlike the
canonical choice above, this interface can carry order extensions chosen to
put a specified antichain in consecutive positions. -/
structure ReverseEnumeration where
  equiv : Fin (Fintype.card T) ≃ T
  index_anti : ∀ {s t : T}, s ≤ t → equiv.symm t ≤ equiv.symm s

namespace ReverseEnumeration

/-- The position of an element in a selectable reverse enumeration. -/
def index (R : ReverseEnumeration T) (t : T) : Fin (Fintype.card T) :=
  R.equiv.symm t

@[simp]
theorem index_equiv (R : ReverseEnumeration T) (j : Fin (Fintype.card T)) :
    index T R (R.equiv j) = j :=
  R.equiv.symm_apply_apply j

theorem index_injective (R : ReverseEnumeration T) :
    Function.Injective (index T R) :=
  R.equiv.symm.injective

end ReverseEnumeration

/-- The support chain starts at the empty set. -/
theorem supportAt_zero : supportAt T 0 = ∅ := by
  ext t
  simp [supportAt]

/-- The support chain ends at the full set. -/
theorem supportAt_last : supportAt T (Fin.last (Fintype.card T)) = Set.univ := by
  ext t
  simp [supportAt, Fin.is_lt]

/-- Consecutive supports in the reverse-linear-extension chain are strictly
increasing. -/
theorem supportAt_strictMono (j : Fin (Fintype.card T)) :
    supportAt T j.castSucc ⊂ supportAt T j.succ := by
  constructor
  · intro t ht
    exact Nat.lt_trans ht (Nat.lt_succ_self j.val)
  · intro hEq
    have hmem : reverseElement T j ∈ supportAt T j.succ := by
      simp [supportAt]
    have hnot : reverseElement T j ∉ supportAt T j.castSucc := by
      simp [supportAt]
    exact hnot (hEq hmem)

/-- The manuscript's canonical chain of one-dimensional `T`-spaces has one
strict nonisomorphism for every element of `T`. -/
abbrev supportLine (j : Fin (Fintype.card T + 1)) : Obj k T :=
  line k T (supportAt T j) (supportAt_isUpperSet T j)

/-- The consecutive morphisms in the canonical support chain. -/
abbrev supportLineStep (j : Fin (Fintype.card T)) :
    supportLine k T j.castSucc ⟶ supportLine k T j.succ :=
  lineHom k T
    (hU := supportAt_isUpperSet T j.castSucc)
    (hV := supportAt_isUpperSet T j.succ)
    (supportAt_strictMono T j).1

/-- Every step in the canonical support chain is a nonisomorphism. -/
theorem supportLineStep_not_isIso (j : Fin (Fintype.card T)) :
    ¬ IsIso (supportLineStep k T j) :=
  lineHom_not_isIso k T
    (hU := supportAt_isUpperSet T j.castSucc)
    (hV := supportAt_isUpperSet T j.succ)
    (supportAt_strictMono T j)

/-- The full canonical support chain, viewed as a composable string of
`|T|` morphisms. -/
abbrev supportLineChain :
    ComposableArrows (Obj k T) (Fintype.card T) where
  obj j := supportLine k T j
  map {i j} f :=
    lineHom k T
      (hU := supportAt_isUpperSet T i)
      (hV := supportAt_isUpperSet T j)
      (supportAt_mono T (leOfHom f))
  map_id := by intros; apply Hom.ext; rfl
  map_comp := by intros; apply Hom.ext; rfl

/-- The total composite of the canonical support chain is the identity on
its one-dimensional underlying vector space. -/
@[simp]
theorem supportLineChain_hom_linear :
    (supportLineChain k T).hom.linear = (LinearMap.id : k →ₗ[k] k) :=
  rfl

/-- Hence the total composite of the support chain is nonzero. -/
theorem supportLineChain_hom_ne_zero :
    (supportLineChain k T).hom ≠ 0 := by
  intro hzero
  have hlinear := congrArg Hom.linear hzero
  have hidzero : (LinearMap.id : k →ₗ[k] k) = 0 := by
    simpa using hlinear
  have happ := LinearMap.congr_fun hidzero (1 : k)
  have hone : (1 : k) = 0 := by simpa using happ
  exact (one_ne_zero : (1 : k) ≠ 0) hone

/-- The adjacent arrow of the full support chain is the previously defined
strict support-inclusion morphism. -/
theorem supportLineChain_map_succ (j : Fin (Fintype.card T)) :
    (supportLineChain k T).map'
        j.val (j.val + 1) (Nat.le_succ _) (Nat.succ_le_of_lt j.isLt) =
      supportLineStep k T j := by
  apply Hom.ext
  rfl

/-- Every adjacent arrow in the full support chain is a nonisomorphism. -/
theorem supportLineChain_map_succ_not_isIso
    (j : Fin (Fintype.card T)) :
    ¬ IsIso ((supportLineChain k T).map'
      j.val (j.val + 1) (Nat.le_succ _) (Nat.succ_le_of_lt j.isLt)) := by
  rw [supportLineChain_map_succ]
  exact supportLineStep_not_isIso k T j

/-- Every adjacent arrow in the full support chain is nonzero. -/
theorem supportLineChain_map_succ_ne_zero
    (j : Fin (Fintype.card T)) :
    (supportLineChain k T).map'
      j.val (j.val + 1) (Nat.le_succ _) (Nat.succ_le_of_lt j.isLt) ≠ 0 := by
  rw [supportLineChain_map_succ]
  exact lineHom_ne_zero k T (supportAt_strictMono T j).1

end Finite

/-- A composable chain through objects satisfying `P` is a nonzero
nonisomorphism chain when every adjacent arrow is a nonzero nonisomorphism and
its total composite is nonzero.  In the manuscript, `P` selects the
indecomposable objects. -/
def IsNonzeroNonisomorphismChain {C : Type u} [Category C]
    [HasZeroMorphisms C] (P : C → Prop) {n : ℕ}
    (F : ComposableArrows C n) : Prop :=
  (∀ i : Fin (n + 1), P (F.obj i)) ∧
    (∀ j : Fin n,
      F.map' j.val (j.val + 1)
          (Nat.le_succ _) (Nat.succ_le_of_lt j.isLt) ≠ 0 ∧
        ¬ IsIso (F.map' j.val (j.val + 1)
          (Nat.le_succ _) (Nat.succ_le_of_lt j.isLt))) ∧
    F.hom ≠ 0

/-- A category has nonzero nonisomorphism paths of length at most `L` when
every such finite composable chain has at most `L` arrows.  This is the exact
categorical consequence of the manuscript's positive path-length grading. -/
def HasNonzeroNonisomorphismLengthAtMost
    (C : Type u) [Category C] [HasZeroMorphisms C]
    (P : C → Prop) (L : ℕ) : Prop :=
  ∀ (n : ℕ) (F : ComposableArrows C n),
    IsNonzeroNonisomorphismChain P F → n ≤ L

/-- A positive grading on the objects satisfying `P`: nonzero
nonisomorphisms between admissible objects strictly raise level, and every
admissible object has level at most `L`. -/
structure PositiveGrading
    (C : Type u) [Category C] [HasZeroMorphisms C]
    (P : C → Prop) (L : ℕ) where
  level : C → ℕ
  level_le : ∀ X, P X → level X ≤ L
  lt_of_nonzero_not_isIso : ∀ {X Y : C} (f : X ⟶ Y),
    P X → P Y → f ≠ 0 → ¬ IsIso f → level X < level Y

/-- A positive grading bounds the length of every nonzero chain of
nonisomorphisms. -/
theorem PositiveGrading.hasNonzeroNonisomorphismLengthAtMost
    {C : Type u} [Category C] [HasZeroMorphisms C]
    {P : C → Prop} {L : ℕ} (G : PositiveGrading C P L) :
    HasNonzeroNonisomorphismLengthAtMost C P L := by
  intro n F hF
  have hlevel : ∀ i : Fin (n + 1), i.val ≤ G.level (F.obj i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
        apply Nat.succ_le_of_lt
        exact lt_of_le_of_lt ih
          (G.lt_of_nonzero_not_isIso
            (F.map' i.val (i.val + 1)
              (Nat.le_succ _) (Nat.succ_le_of_lt i.isLt))
            (hF.1 i.castSucc) (hF.1 i.succ)
            (hF.2.1 i).1 (hF.2.1 i).2)
  exact le_trans (hlevel (Fin.last n)) (G.level_le _ (hF.1 (Fin.last n)))

section Finite

variable [Fintype T]

/-- The canonical support chain is a nonzero nonisomorphism chain of length
exactly `|T|`. -/
theorem supportLineChain_isNonzeroNonisomorphismChain :
    ∀ {P : Obj k T → Prop},
      (∀ j, P (supportLine k T j)) →
        IsNonzeroNonisomorphismChain P (supportLineChain k T) := by
  intro P hP
  constructor
  · exact hP
  constructor
  · intro j
    exact ⟨supportLineChain_map_succ_ne_zero k T j,
      supportLineChain_map_succ_not_isIso k T j⟩
  · exact supportLineChain_hom_ne_zero k T

/-- The path-length bound in the poset-space category forces the
manuscript's realization inequality `|T| ≤ L`. -/
theorem card_le_of_nonzeroNonisomorphismLengthAtMost {L : ℕ}
    {P : Obj k T → Prop}
    (support_admissible : ∀ j, P (supportLine k T j))
    (hLength : HasNonzeroNonisomorphismLengthAtMost (Obj k T) P L) :
    Fintype.card T ≤ L :=
  hLength (Fintype.card T) (supportLineChain k T)
    (supportLineChain_isNonzeroNonisomorphismChain k T support_admissible)

/-- In particular, a positive grading on the poset-space category gives the
realization-length inequality `|T| ≤ L`. -/
theorem card_le_of_positiveGrading {L : ℕ}
    {P : Obj k T → Prop}
    (support_admissible : ∀ j, P (supportLine k T j))
    (G : PositiveGrading (Obj k T) P L) :
    Fintype.card T ≤ L :=
  card_le_of_nonzeroNonisomorphismLengthAtMost k T support_admissible
    G.hasNonzeroNonisomorphismLengthAtMost

/-- The manuscript-shaped specialization: a positive grading on the Schur
`T`-spaces forces `|T| ≤ L`, since every canonical support object is Schur. -/
theorem card_le_of_schurPositiveGrading {L : ℕ}
    (G : PositiveGrading (Obj k T) (IsSchur k T) L) :
    Fintype.card T ≤ L :=
  card_le_of_positiveGrading k T
    (fun j ↦ line_isSchur k T (supportAt T j) (supportAt_isUpperSet T j)) G

/-- Along the canonical support chain, a Schur-positive grading grows by at
least the difference of the support indices.  The subtraction-free statement
is convenient for natural-number arithmetic. -/
theorem supportLine_level_add_index_le
    {L : ℕ}
    (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    {i j : Fin (Fintype.card T + 1)} (hij : i ≤ j) :
    G.level (supportLine k T i) + j.val ≤
      G.level (supportLine k T j) + i.val := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  change i ≤ j at hij
  simp only
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _ ih =>
      specialize ih (Nat.lt_of_succ_lt hj)
      let r : Fin (Fintype.card T) := ⟨j, by omega⟩
      have hstep :
          G.level (supportLine k T r.castSucc) <
            G.level (supportLine k T r.succ) :=
        G.lt_of_nonzero_not_isIso (supportLineStep k T r)
          (line_isSchur k T (supportAt T r.castSucc)
            (supportAt_isUpperSet T r.castSucc))
          (line_isSchur k T (supportAt T r.succ)
            (supportAt_isUpperSet T r.succ))
          (lineHom_ne_zero k T (supportAt_strictMono T r).1)
          (supportLineStep_not_isIso k T r)
      change G.level (supportLine k T ⟨j, by omega⟩) <
        G.level (supportLine k T ⟨j + 1, hj⟩) at hstep
      omega

/-- A two-step Schur detour replacing one ordinary support inclusion.  The
three-antichain construction supplies this data with the two-dimensional
three-line space as `middle`. -/
structure SchurDetour (q : ℕ) (hq : q + 2 < Fintype.card T) where
  middle : Obj k T
  middle_schur : IsSchur k T middle
  inMap :
    supportLine k T
      ⟨q + 1, Nat.lt_succ_iff.mpr (Nat.le_of_lt (lt_trans (by omega) hq))⟩ ⟶
      middle
  outMap : middle ⟶
    supportLine k T
      ⟨q + 2, Nat.lt_succ_iff.mpr (Nat.le_of_lt hq)⟩
  inMap_ne_zero : inMap ≠ 0
  outMap_ne_zero : outMap ≠ 0
  inMap_not_isIso : ¬ IsIso inMap
  outMap_not_isIso : ¬ IsIso outMap

/-- Splicing a two-step Schur detour into the `|T|`-step support chain forces
the strict equality obstruction `|T|+1 ≤ L`. -/
theorem card_add_one_le_of_schurDetour
    {L q : ℕ}
    (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    {hq : q + 2 < Fintype.card T} (D : SchurDetour k T q hq) :
    Fintype.card T + 1 ≤ L := by
  let iq1 : Fin (Fintype.card T + 1) :=
    ⟨q + 1, Nat.lt_succ_iff.mpr (by omega)⟩
  let iq2 : Fin (Fintype.card T + 1) :=
    ⟨q + 2, Nat.lt_succ_iff.mpr (by omega)⟩
  let ilast : Fin (Fintype.card T + 1) := Fin.last (Fintype.card T)
  have hprefix := supportLine_level_add_index_le k T G
    (i := (0 : Fin (Fintype.card T + 1))) (j := iq1) (Fin.zero_le _)
  have hin : G.level (supportLine k T iq1) < G.level D.middle :=
    G.lt_of_nonzero_not_isIso D.inMap
      (line_isSchur k T (supportAt T iq1) (supportAt_isUpperSet T iq1))
      D.middle_schur D.inMap_ne_zero D.inMap_not_isIso
  have hout : G.level D.middle < G.level (supportLine k T iq2) :=
    G.lt_of_nonzero_not_isIso D.outMap D.middle_schur
      (line_isSchur k T (supportAt T iq2) (supportAt_isUpperSet T iq2))
      D.outMap_ne_zero D.outMap_not_isIso
  change G.level (supportLine k T iq1) < G.level D.middle at hin
  change G.level D.middle < G.level (supportLine k T iq2) at hout
  have hsuffix := supportLine_level_add_index_le k T G
    (i := iq2) (j := ilast) (by
      change q + 2 ≤ Fintype.card T
      exact Nat.le_of_lt hq)
  have htop := G.level_le (supportLine k T ilast)
    (line_isSchur k T (supportAt T ilast) (supportAt_isUpperSet T ilast))
  have hprefix' : q + 1 ≤ G.level (supportLine k T iq1) := by
    dsimp [iq1] at hprefix ⊢
    omega
  have hdetour : G.level (supportLine k T iq1) + 2 ≤
      G.level (supportLine k T iq2) := by
    omega
  have hsuffix' : G.level (supportLine k T iq2) + Fintype.card T ≤
      G.level (supportLine k T ilast) + (q + 2) := by
    change G.level (supportLine k T iq2) + Fintype.card T ≤
      G.level (supportLine k T ilast) + (q + 2) at hsuffix
    exact hsuffix
  change G.level (supportLine k T ilast) ≤ L at htop
  dsimp [iq1, iq2, ilast] at hprefix' hdetour hsuffix' htop
  omega

end Finite

end MagnitudeConjecture.PosetSpace
