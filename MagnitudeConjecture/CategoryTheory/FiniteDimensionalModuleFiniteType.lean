import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleHomFinite
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteGeneratorRadicalNilpotence

/-!
# Finite indecomposable skeletons of finite-dimensional module categories

A finite family covering every indecomposable module can be deduplicated by
isomorphism.  The resulting finite skeleton decomposes every object, is a
finite additive generator, and therefore carries the canonical nilpotent
categorical radical required by finite tau-category data.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- A duplicate-free finite and complete skeleton of indecomposable
finite-dimensional modules. -/
structure FiniteDimensionalModuleIndecomposableSkeleton where
  n : ℕ
  obj : Fin n →
    FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k
  indecomposable : ∀ i, Indecomposable (obj i)
  skeletal : ∀ {i j}, Nonempty (obj i ≅ obj j) → i = j
  complete :
    ∀ (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k),
      Indecomposable M → ∃ i, Nonempty (M ≅ obj i)

namespace FiniteDimensionalModuleIndecomposableSkeleton

variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

/-- Isomorphism of members of a finite family is an equivalence relation on
its index type. -/
def familyIsoSetoid {n : ℕ}
    (X : Fin n →
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Setoid (Fin n) where
  r i j := Nonempty (X i ≅ X j)
  iseqv := {
    refl := fun i ↦ ⟨Iso.refl (X i)⟩
    symm := fun h ↦ h.map Iso.symm
    trans := fun hij hjl ↦ Nonempty.map2 Iso.trans hij hjl }

/-- Deduplicate any finite family which covers all indecomposable modules. -/
noncomputable def ofFamily
    {n : ℕ}
    (X : Fin n →
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (hX : ∀ i, Indecomposable (X i))
    (hcover :
      ∀ (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k),
        Indecomposable M → ∃ i, Nonempty (M ≅ X i)) :
    FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C) := by
  classical
  let s : Setoid (Fin n) := familyIsoSetoid X
  letI : DecidableRel ((· ≈ ·) : Fin n → Fin n → Prop) :=
    Classical.decRel _
  letI : Fintype (Quotient s) := Quotient.fintype s
  let e : Quotient s ≃ Fin (Fintype.card (Quotient s)) :=
    Fintype.equivFin (Quotient s)
  let Y : Fin (Fintype.card (Quotient s)) →
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
    fun i ↦ X (e.symm i).out
  refine
    { n := Fintype.card (Quotient s)
      obj := Y
      indecomposable := fun i ↦ hX (e.symm i).out
      skeletal := ?_
      complete := ?_ }
  · intro i j hij
    apply e.symm.injective
    apply Quotient.out_equiv_out.mp
    exact hij
  · intro M hM
    obtain ⟨i, ⟨hMi⟩⟩ := hcover M hM
    let q : Quotient s := Quotient.mk'' i
    let j := e q
    have hq : e.symm j = q := e.symm_apply_apply q
    have hout : (e.symm j).out ≈ i := by
      apply Quotient.exact
      rw [hq, Quotient.out_eq]
    obtain ⟨houtIso⟩ := hout
    exact ⟨j, ⟨hMi.trans houtIso.symm⟩⟩

/-- Every finite-dimensional module decomposes as a finite biproduct of the
chosen duplicate-free representatives. -/
theorem obj_decomposition
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    ∃ (n : ℕ) (label : Fin n → Fin S.n),
      Nonempty (M ≅ ⨁ fun i ↦ S.obj (label i)) := by
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition M
  have hcomplete (i : Fin d.n) :
      ∃ j, Nonempty (d.summand i ≅ S.obj j) :=
    S.complete (d.summand i) (d.indecomposable i)
  choose label hlabel using hcomplete
  exact ⟨d.n, label, ⟨d.isoBiproduct.trans
    (biproduct.mapIso fun i ↦ Classical.choice (hlabel i))⟩⟩

/-- Chosen representatives have local endomorphism rings. -/
theorem obj_end_local (i : Fin S.n) : IsLocalRing (End (S.obj i)) :=
  finiteDimensionalModule_end_isLocalRing k (S.obj i)
    (S.indecomposable i)

/-- The biproduct of the chosen representatives. -/
abbrev generator :
    FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
  ⨁ S.obj

/-- The finite skeleton biproduct is a finite additive generator. -/
theorem generator_isFiniteAddGenerator :
    MagnitudeConjecture.CategoryTheory.IsFiniteAddGenerator S.generator := by
  intro M
  obtain ⟨n, label, ⟨e⟩⟩ := S.obj_decomposition M
  let F : Fin n →
      FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
    fun i ↦ S.obj (label i)
  let inc (i : Fin n) : F i ⟶ S.generator :=
    biproduct.ι S.obj (label i)
  let ret (i : Fin n) : S.generator ⟶ F i :=
    biproduct.π S.obj (label i)
  refine ⟨
    { n := n
      retract :=
        { i := e.hom ≫ biproduct.map inc
          r := biproduct.map ret ≫ e.inv
          retract := ?_ } }⟩
  dsimp only [inc, ret]
  have hmaps :
      biproduct.map (fun i ↦ biproduct.ι S.obj (label i)) ≫
          biproduct.map (fun i ↦ biproduct.π S.obj (label i)) =
        𝟙 (⨁ fun i : Fin n ↦ S.obj (label i)) := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  calc
    (e.hom ≫ biproduct.map (fun i ↦ biproduct.ι S.obj (label i))) ≫
          biproduct.map (fun i ↦ biproduct.π S.obj (label i)) ≫ e.inv =
        e.hom ≫
          ((biproduct.map (fun i ↦ biproduct.ι S.obj (label i)) ≫
            biproduct.map (fun i ↦ biproduct.π S.obj (label i))) ≫
              e.inv) := by simp only [Category.assoc]
    _ = e.hom ≫ e.inv := by rw [hmaps, Category.id_comp]
    _ = 𝟙 M := e.hom_inv_id

/-- The categorical radical of the finite-dimensional module category is
nilpotent once a finite indecomposable skeleton is available. -/
def nilpotentRadicalData :
    QuotientSubmoduleEquidistribution.CategoricalRadical.NilpotentRadicalData
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) := by
  letI : IsArtinianRing (End S.generator) := by
    letI : Module.Finite k (End S.generator) := inferInstance
    exact IsArtinianRing.of_finite k (End S.generator)
  exact MagnitudeConjecture.CategoryTheory.nilpotentRadicalDataOfArtinianGenerator
    S.generator S.generator_isFiniteAddGenerator

end FiniteDimensionalModuleIndecomposableSkeleton

end MagnitudeConjecture.CoveringHom
