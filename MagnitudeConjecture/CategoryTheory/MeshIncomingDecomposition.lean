import MagnitudeConjecture.CategoryTheory.LinearPathDecomposition
import MagnitudeConjecture.CategoryTheory.MeshCategory
import Mathlib.Combinatorics.Quiver.Cast

/-!
# Decomposition by the final categorical arrow

Every morphism in a mesh category is a scalar diagonal term plus a finite sum
of morphisms followed by one arrow into its target.  This is the path-algebra
decomposition used in Ringel's induction for fullness and faithfulness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.MeshCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable [∀ z : Q, Fintype (Σ y : Q, z ⟶ y)]
variable (T : RightMeshData Q)

namespace RightMeshData

/-- The finite family of reversed quiver arrows whose represented
categorical maps end at `z`. -/
abbrev IncomingArrow (z : Q) := Σ y : Q, z ⟶ y

/-- The mesh-category morphism represented by one arrow into `z`. -/
def incomingArrowHom {z : Q} (a : IncomingArrow z) :
    obj (k := k) T a.1 ⟶ obj (k := k) T z :=
  (quotientFunctor (k := k) T).map
    (MagnitudeConjecture.LinearPathCategory.pathHom a.2.toPath)

/-- One coefficient morphism for each arrow into the target. -/
abbrev IncomingCoefficient (x z : Q) :=
  ∀ a : IncomingArrow z,
    obj (k := k) T x ⟶ obj (k := k) T a.1

/-- Compose a family of coefficients with all arrows into the target. -/
def incomingSum {x z : Q} (c : IncomingCoefficient (k := k) T x z) :
    obj (k := k) T x ⟶ obj (k := k) T z :=
  ∑ a : IncomingArrow z, c a ≫ T.incomingArrowHom a

/-- A coefficient family supported at one incoming arrow. -/
def singleIncomingCoefficient {x z : Q} (a₀ : IncomingArrow z)
    (f : obj (k := k) T x ⟶ obj (k := k) T a₀.1) :
    IncomingCoefficient (k := k) T x z := by
  classical
  exact fun a ↦ if h : a₀ = a then
      f ≫ eqToHom (congrArg (fun b : IncomingArrow z ↦
        obj (k := k) T b.1) h)
    else 0

/-- Summing a coefficient family supported at one arrow recovers the one
displayed composite. -/
@[simp]
theorem incomingSum_single {x z : Q} (a₀ : IncomingArrow z)
    (f : obj (k := k) T x ⟶ obj (k := k) T a₀.1) :
    T.incomingSum (T.singleIncomingCoefficient a₀ f) =
      f ≫ T.incomingArrowHom a₀ := by
  classical
  rw [incomingSum, Finset.sum_eq_single a₀]
  · simp [singleIncomingCoefficient]
  · intro a _ ha
    simp [singleIncomingCoefficient, Ne.symm ha]
  · simp

/-- The scalar identity term when the source and target labels coincide,
and zero otherwise. -/
def diagonalScalar (x z : Q) (c : k) :
    obj (k := k) T x ⟶ obj (k := k) T z := by
  classical
  exact if h : x = z then
      c • eqToHom (congrArg (fun q ↦ obj (k := k) T q) h)
    else 0

@[simp]
theorem diagonalScalar_self (x : Q) (c : k) :
    T.diagonalScalar x x c = c • 𝟙 (obj (k := k) T x) := by
  simp [diagonalScalar]

/-- Every mesh-category morphism is a scalar diagonal term plus a sum of
morphisms followed by one incoming arrow. -/
theorem exists_eq_diagonalScalar_add_incomingSum {x z : Q}
    (f : obj (k := k) T x ⟶ obj (k := k) T z) :
    ∃ (c : k) (h : IncomingCoefficient (k := k) T x z),
      f = T.diagonalScalar x z c + T.incomingSum h := by
  classical
  obtain ⟨g, rfl⟩ := (quotientFunctor (k := k) T).map_surjective f
  let g' := MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q z) g
  rw [← (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q z)).symm_apply_apply g]
  change ∃ (c : k) (h : IncomingCoefficient (k := k) T x z),
    (quotientFunctor (k := k) T).map
        ((MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
          (MagnitudeConjecture.LinearPathCategory.obj k Q x)
          (MagnitudeConjecture.LinearPathCategory.obj k Q z)).symm g') =
      T.diagonalScalar x z c + T.incomingSum h
  induction g' using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, 0, ?_⟩
      simp [diagonalScalar, incomingSum]
  | add g₁ g₂ hg₁ hg₂ =>
      obtain ⟨c₁, h₁, hh₁⟩ := hg₁
      obtain ⟨c₂, h₂, hh₂⟩ := hg₂
      refine ⟨c₁ + c₂, h₁ + h₂, ?_⟩
      rw [(MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
        (MagnitudeConjecture.LinearPathCategory.obj k Q x)
        (MagnitudeConjecture.LinearPathCategory.obj k Q z)).symm.map_add,
        (quotientFunctor (k := k) T).map_add, hh₁, hh₂]
      simp only [diagonalScalar, incomingSum, Pi.add_apply,
        Preadditive.add_comp, Finset.sum_add_distrib]
      split_ifs <;> module
  | single p r =>
      rw [MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv_symm_single]
      rw [(quotientFunctor (k := k) T).map_smul]
      by_cases hp : p.length = 0
      · have hzx : z = x := p.eq_of_length_zero hp
        subst x
        have hpnil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hp
        subst p
        refine ⟨r, 0, ?_⟩
        simp [diagonalScalar, incomingSum]
      · obtain ⟨y, a, q, hpq, _⟩ :=
          (Quiver.Path.length_ne_zero_iff_eq_comp p).mp hp
        subst p
        let a₀ : IncomingArrow z := ⟨y, a⟩
        let qHom : obj (k := k) T x ⟶ obj (k := k) T y :=
          (quotientFunctor (k := k) T).map
            (MagnitudeConjecture.LinearPathCategory.pathHom q)
        refine ⟨0, T.singleIncomingCoefficient a₀ (r • qHom), ?_⟩
        rw [T.incomingSum_single]
        have hdiag : T.diagonalScalar (k := k) x z (0 : k) = 0 := by
          simp [diagonalScalar]
        rw [hdiag, zero_add]
        dsimp only [a₀, qHom, incomingArrowHom]
        change r • (quotientFunctor (k := k) T).map
            (MagnitudeConjecture.LinearPathCategory.pathHom
              (a.toPath.comp q)) =
          (r • (quotientFunctor (k := k) T).map
              (MagnitudeConjecture.LinearPathCategory.pathHom q)) ≫
            (quotientFunctor (k := k) T).map
              (MagnitudeConjecture.LinearPathCategory.pathHom a.toPath)
        rw [CategoryTheory.Linear.smul_comp,
          ← (quotientFunctor (k := k) T).map_comp,
          MagnitudeConjecture.LinearPathCategory.pathHom_comp]
        rfl

/-- One coefficient morphism for each arrow into a target, with an arbitrary
raw mesh-category object as source. -/
abbrev RawIncomingCoefficient (X : RawCategory (k := k) T) (z : Q) :=
  ∀ a : IncomingArrow z, X ⟶ obj (k := k) T a.1

/-- Compose raw-source coefficients with all arrows into the target. -/
def rawIncomingSum {X : RawCategory (k := k) T} {z : Q}
    (c : RawIncomingCoefficient (k := k) T X z) :
    X ⟶ obj (k := k) T z :=
  ∑ a : IncomingArrow z, c a ≫ T.incomingArrowHom a

/-- The scalar identity term for an arbitrary raw source object, and zero
unless that source is the displayed target vertex. -/
def rawDiagonalScalar (X : RawCategory (k := k) T) (z : Q) (c : k) :
    X ⟶ obj (k := k) T z := by
  classical
  exact if h : X = obj (k := k) T z then c • eqToHom h else 0

/-- Decomposition by the final arrow for an arbitrary raw source object.
This wrapper internalizes the harmless object transport between a quotient
object and the vertex represented by its underlying path-category object. -/
theorem exists_eq_rawDiagonalScalar_add_rawIncomingSum
    {X : RawCategory (k := k) T} {z : Q}
    (f : X ⟶ obj (k := k) T z) :
    ∃ (c : k) (h : RawIncomingCoefficient (k := k) T X z),
      f = T.rawDiagonalScalar X z c + T.rawIncomingSum h := by
  classical
  rcases X with ⟨X⟩
  let x := MagnitudeConjecture.LinearPathCategory.vertex X
  have hobj :
      ({ as := X } : RawCategory (k := k) T) = obj (k := k) T x := rfl
  let f' : obj (k := k) T x ⟶ obj (k := k) T z :=
    eqToHom hobj.symm ≫ f
  obtain ⟨c, h, hf⟩ :=
    T.exists_eq_diagonalScalar_add_incomingSum (x := x) (z := z) f'
  let h' : RawIncomingCoefficient (k := k) T ({ as := X }) z :=
    fun a ↦ eqToHom hobj ≫ h a
  refine ⟨c, h', ?_⟩
  have hincoming :
      eqToHom hobj ≫ T.incomingSum h = T.rawIncomingSum h' := by
    unfold incomingSum rawIncomingSum
    rw [Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp [h', Category.assoc]
  have hdiag :
      eqToHom hobj ≫ T.diagonalScalar x z c =
        T.rawDiagonalScalar ({ as := X }) z c := by
    by_cases hx : x = z
    · subst z
      simp [rawDiagonalScalar, diagonalScalar, hobj]
    · have hraw :
          ({ as := X } : RawCategory (k := k) T) ≠ obj (k := k) T z := by
        intro hEq
        apply hx
        exact congrArg
          (fun Y : RawCategory (k := k) T ↦
            MagnitudeConjecture.LinearPathCategory.vertex Y.as) hEq
      simp [rawDiagonalScalar, diagonalScalar, hx, hraw]
  calc
    f = eqToHom hobj ≫ f' := by simp [f']
    _ = eqToHom hobj ≫
        (T.diagonalScalar x z c + T.incomingSum h) := by rw [← hf]
    _ = T.rawDiagonalScalar ({ as := X }) z c +
        T.rawIncomingSum h' := by rw [Preadditive.comp_add, hdiag, hincoming]

/-- The finite family of reversed quiver arrows whose represented
categorical maps start at `x`. -/
abbrev OutgoingArrow (x : Q) := Σ y : Q, y ⟶ x

variable [∀ x : Q, Fintype (OutgoingArrow x)]

/-- The mesh-category morphism represented by one arrow out of `x`. -/
def outgoingArrowHom {x : Q} (a : OutgoingArrow x) :
    obj (k := k) T x ⟶ obj (k := k) T a.1 :=
  (quotientFunctor (k := k) T).map
    (MagnitudeConjecture.LinearPathCategory.pathHom a.2.toPath)

set_option backward.isDefEq.respectTransparency false in
/-- Transporting the source of an outgoing arrow is realized by the
corresponding object equality before the original mesh morphism. -/
theorem outgoingArrowHom_cast_source
    {x x' : Q} (h : x = x') (a : OutgoingArrow x) :
    T.outgoingArrowHom (k := k)
        (⟨a.1, Quiver.Hom.cast rfl h a.2⟩ : OutgoingArrow x') =
      eqToHom (congrArg (obj (k := k) T) h).symm ≫
        T.outgoingArrowHom (k := k) a := by
  subst x'
  simp

/-- One coefficient morphism after each arrow out of the source. -/
abbrev OutgoingCoefficient (x z : Q) :=
  ∀ a : OutgoingArrow x,
    obj (k := k) T a.1 ⟶ obj (k := k) T z

/-- Compose all arrows out of a source with their coefficient family. -/
def outgoingSum {x z : Q} (c : OutgoingCoefficient (k := k) T x z) :
    obj (k := k) T x ⟶ obj (k := k) T z :=
  ∑ a : OutgoingArrow x, T.outgoingArrowHom a ≫ c a

/-- A coefficient family supported after one outgoing arrow. -/
def singleOutgoingCoefficient {x z : Q} (a₀ : OutgoingArrow x)
    (f : obj (k := k) T a₀.1 ⟶ obj (k := k) T z) :
    OutgoingCoefficient (k := k) T x z := by
  classical
  exact fun a ↦ if h : a₀ = a then
      eqToHom (congrArg (fun b : OutgoingArrow x ↦
        obj (k := k) T b.1) h.symm) ≫ f
    else 0

/-- Summing a coefficient family supported after one arrow recovers the
one displayed composite. -/
@[simp]
theorem outgoingSum_single {x z : Q} (a₀ : OutgoingArrow x)
    (f : obj (k := k) T a₀.1 ⟶ obj (k := k) T z) :
    T.outgoingSum (T.singleOutgoingCoefficient a₀ f) =
      T.outgoingArrowHom a₀ ≫ f := by
  classical
  rw [outgoingSum, Finset.sum_eq_single a₀]
  · simp [singleOutgoingCoefficient]
  · intro a _ ha
    simp [singleOutgoingCoefficient, Ne.symm ha]
  · simp

/-- Every mesh-category morphism is a scalar diagonal term plus a sum of
one outgoing arrow followed by a coefficient morphism. -/
theorem exists_eq_diagonalScalar_add_outgoingSum {x z : Q}
    (f : obj (k := k) T x ⟶ obj (k := k) T z) :
    ∃ (c : k) (h : OutgoingCoefficient (k := k) T x z),
      f = T.diagonalScalar x z c + T.outgoingSum h := by
  classical
  obtain ⟨g, rfl⟩ := (quotientFunctor (k := k) T).map_surjective f
  let g' := MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q z) g
  rw [← (MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
    (MagnitudeConjecture.LinearPathCategory.obj k Q x)
    (MagnitudeConjecture.LinearPathCategory.obj k Q z)).symm_apply_apply g]
  change ∃ (c : k) (h : OutgoingCoefficient (k := k) T x z),
    (quotientFunctor (k := k) T).map
        ((MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
          (MagnitudeConjecture.LinearPathCategory.obj k Q x)
          (MagnitudeConjecture.LinearPathCategory.obj k Q z)).symm g') =
      T.diagonalScalar x z c + T.outgoingSum h
  induction g' using Finsupp.induction_linear with
  | zero =>
      refine ⟨0, 0, ?_⟩
      simp [diagonalScalar, outgoingSum]
  | add g₁ g₂ hg₁ hg₂ =>
      obtain ⟨c₁, h₁, hh₁⟩ := hg₁
      obtain ⟨c₂, h₂, hh₂⟩ := hg₂
      refine ⟨c₁ + c₂, h₁ + h₂, ?_⟩
      rw [(MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv
        (MagnitudeConjecture.LinearPathCategory.obj k Q x)
        (MagnitudeConjecture.LinearPathCategory.obj k Q z)).symm.map_add,
        (quotientFunctor (k := k) T).map_add, hh₁, hh₂]
      simp only [diagonalScalar, outgoingSum, Pi.add_apply,
        Preadditive.comp_add, Finset.sum_add_distrib]
      split_ifs <;> module
  | single p r =>
      rw [MagnitudeConjecture.LinearPathCategory.homPathLinearEquiv_symm_single]
      rw [(quotientFunctor (k := k) T).map_smul]
      by_cases hp : p.length = 0
      · have hzx : z = x := p.eq_of_length_zero hp
        subst x
        have hpnil : p = Quiver.Path.nil := p.eq_nil_of_length_zero hp
        subst p
        refine ⟨r, 0, ?_⟩
        simp [diagonalScalar, outgoingSum]
      · obtain ⟨y, q, a, hpq⟩ :=
          (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hp
        subst p
        let a₀ : OutgoingArrow x := ⟨y, a⟩
        let qHom : obj (k := k) T y ⟶ obj (k := k) T z :=
          (quotientFunctor (k := k) T).map
            (MagnitudeConjecture.LinearPathCategory.pathHom q)
        refine ⟨0, T.singleOutgoingCoefficient a₀ (r • qHom), ?_⟩
        rw [T.outgoingSum_single]
        have hdiag : T.diagonalScalar (k := k) x z (0 : k) = 0 := by
          simp [diagonalScalar]
        rw [hdiag, zero_add]
        dsimp only [a₀, qHom, outgoingArrowHom]
        change r • (quotientFunctor (k := k) T).map
            (MagnitudeConjecture.LinearPathCategory.pathHom (q.cons a)) =
          (quotientFunctor (k := k) T).map
              (MagnitudeConjecture.LinearPathCategory.pathHom a.toPath) ≫
            (r • (quotientFunctor (k := k) T).map
              (MagnitudeConjecture.LinearPathCategory.pathHom q))
        rw [CategoryTheory.Linear.comp_smul,
          ← (quotientFunctor (k := k) T).map_comp,
          MagnitudeConjecture.LinearPathCategory.pathHom_comp]
        rfl

/-- One coefficient morphism after each arrow out of the source, with an
arbitrary raw mesh-category object as target. -/
abbrev RawOutgoingCoefficient (x : Q) (Z : RawCategory (k := k) T) :=
  ∀ a : OutgoingArrow x, obj (k := k) T a.1 ⟶ Z

/-- Compose all arrows out of a source with raw-target coefficients. -/
def rawOutgoingSum {x : Q} {Z : RawCategory (k := k) T}
    (c : RawOutgoingCoefficient (k := k) T x Z) :
    obj (k := k) T x ⟶ Z :=
  ∑ a : OutgoingArrow x, T.outgoingArrowHom a ≫ c a

/-- The scalar identity term for an arbitrary raw target object, and zero
unless that target is the displayed source vertex. -/
def targetRawDiagonalScalar (x : Q) (Z : RawCategory (k := k) T) (c : k) :
    obj (k := k) T x ⟶ Z := by
  classical
  exact if h : obj (k := k) T x = Z then c • eqToHom h else 0

/-- Decomposition by the first arrow for an arbitrary raw target object.
This is the target-side counterpart of
`exists_eq_rawDiagonalScalar_add_rawIncomingSum`. -/
theorem exists_eq_targetRawDiagonalScalar_add_rawOutgoingSum
    {x : Q} {Z : RawCategory (k := k) T}
    (f : obj (k := k) T x ⟶ Z) :
    ∃ (c : k) (h : RawOutgoingCoefficient (k := k) T x Z),
      f = T.targetRawDiagonalScalar x Z c + T.rawOutgoingSum h := by
  classical
  rcases Z with ⟨Z⟩
  let z := MagnitudeConjecture.LinearPathCategory.vertex Z
  have hobj :
      ({ as := Z } : RawCategory (k := k) T) = obj (k := k) T z := rfl
  let f' : obj (k := k) T x ⟶ obj (k := k) T z :=
    f ≫ eqToHom hobj
  obtain ⟨c, h, hf⟩ :=
    T.exists_eq_diagonalScalar_add_outgoingSum (x := x) (z := z) f'
  let h' : RawOutgoingCoefficient (k := k) T x ({ as := Z }) :=
    fun a ↦ h a ≫ eqToHom hobj.symm
  refine ⟨c, h', ?_⟩
  have houtgoing :
      T.outgoingSum h ≫ eqToHom hobj.symm = T.rawOutgoingSum h' := by
    unfold outgoingSum rawOutgoingSum
    rw [Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro a _
    simp [h', Category.assoc]
  have hdiag :
      T.diagonalScalar x z c ≫ eqToHom hobj.symm =
        T.targetRawDiagonalScalar x ({ as := Z }) c := by
    by_cases hx : x = z
    · have hrawEq : obj (k := k) T x =
          ({ as := Z } : RawCategory (k := k) T) :=
        (congrArg (fun q ↦ obj (k := k) T q) hx).trans hobj.symm
      unfold targetRawDiagonalScalar diagonalScalar
      rw [dif_pos hx, dif_pos hrawEq]
      simp
    · have hraw :
          obj (k := k) T x ≠ ({ as := Z } : RawCategory (k := k) T) := by
        intro hEq
        apply hx
        exact congrArg
          (fun Y : RawCategory (k := k) T ↦
            MagnitudeConjecture.LinearPathCategory.vertex Y.as) hEq
      simp [targetRawDiagonalScalar, diagonalScalar, hx, hraw]
  calc
    f = f' ≫ eqToHom hobj.symm := by simp [f']
    _ = (T.diagonalScalar x z c + T.outgoingSum h) ≫
        eqToHom hobj.symm := by rw [← hf]
    _ = T.targetRawDiagonalScalar x ({ as := Z }) c +
        T.rawOutgoingSum h' := by rw [Preadditive.add_comp, hdiag, houtgoing]

end RightMeshData

end MagnitudeConjecture.MeshCategory
