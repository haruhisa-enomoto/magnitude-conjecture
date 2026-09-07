import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleExtension

/-!
# Directed finite-support module categories

The covering argument uses directedness before choosing any finite global
skeleton: every intermediate object-deletion category still has a directed
category of finite-support modules.  This file records that literal property
and proves its inheritance under extension by zero.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- A nonzero nonisomorphism whose source and target are indecomposable
finite-support modules. -/
def FiniteModuleNonzeroNonisomorphism
    (M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) : Prop :=
  Indecomposable M ∧ Indecomposable N ∧
    ∃ f : M ⟶ N, f ≠ 0 ∧ ¬ IsIso f

/-- The manuscript's assertion that `mod C` is directed, expressed without
choosing a global set of indecomposable representatives. -/
def HasAcyclicFiniteModuleNonzeroNonisomorphisms : Prop :=
  ∀ M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
    ¬ Relation.TransGen
      (FiniteModuleNonzeroNonisomorphism (k := k) (C := C)) M M

universe u'

variable {D : Type u'} [Category.{v} D] [Preadditive D] [Linear k D]

universe uE vE

variable {E : Type uE} [Category.{vE} E] [Preadditive E]

/-- A full faithful realization of all indecomposable finite modules from a
category whose nonzero nonisomorphisms strictly decrease an integer rank makes
the finite-module category directed. -/
theorem hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_ranked_realization
    (F : E ⥤ FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    [F.Full] [F.Faithful]
    (rank : E → ℤ)
    (hstrict : ∀ {X Y : E},
      (∃ f : X ⟶ Y, f ≠ 0 ∧ ¬ IsIso f) → rank Y < rank X)
    (hdense : ∀ (M : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := C) k), Indecomposable M →
      ∃ X : E, Nonempty (F.obj X ≅ M)) :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C) := by
  let liftObj (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := C) k) (hM : Indecomposable M) : E :=
    Classical.choose (hdense M hM)
  let liftIso (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := C) k) (hM : Indecomposable M) :
      F.obj (liftObj M hM) ≅ M :=
    Classical.choice (Classical.choose_spec (hdense M hM))
  have stepRank {M N : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := C) k}
      (hMN : FiniteModuleNonzeroNonisomorphism (k := k) (C := C) M N) :
      rank (liftObj N hMN.2.1) < rank (liftObj M hMN.1) := by
    rcases hMN with ⟨hM, hN, f, hf, hnotIso⟩
    let eM := liftIso M hM
    let eN := liftIso N hN
    let f' : F.obj (liftObj M hM) ⟶ F.obj (liftObj N hN) :=
      eM.hom ≫ f ≫ eN.inv
    let q : liftObj M hM ⟶ liftObj N hN := F.preimage f'
    have hmap : F.map q = f' := F.map_preimage f'
    have hq : q ≠ 0 := by
      intro hzero
      apply hf
      rw [show f = eM.inv ≫ f' ≫ eN.hom by simp [f', eM, eN]]
      rw [← hmap, hzero, F.map_zero]
      simp
    have hqnotIso : ¬ IsIso q := by
      intro hqIso
      letI : IsIso q := hqIso
      have hf'Iso : IsIso f' := by
        rw [← hmap]
        infer_instance
      letI : IsIso f' := hf'Iso
      apply hnotIso
      rw [show f = eM.inv ≫ f' ≫ eN.hom by simp [f', eM, eN]]
      infer_instance
    exact hstrict ⟨q, hq, hqnotIso⟩
  intro M hcycle
  have sourceIndecomposable {X Y :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
      (hXY : Relation.TransGen
        (FiniteModuleNonzeroNonisomorphism (k := k) (C := C)) X Y) :
      Indecomposable X := by
    induction hXY using Relation.TransGen.head_induction_on with
    | single h => exact h.1
    | head h _ _ => exact h.1
  have targetIndecomposable {X Y :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
      (hXY : Relation.TransGen
        (FiniteModuleNonzeroNonisomorphism (k := k) (C := C)) X Y) :
      Indecomposable Y := by
    induction hXY using Relation.TransGen.trans_induction_on with
    | single h => exact h.2.1
    | trans _ _ _ ih => exact ih
  have rankTrans {X Y : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := C) k}
      (hXY : Relation.TransGen
        (FiniteModuleNonzeroNonisomorphism (k := k) (C := C)) X Y) :
      ∀ (hX : Indecomposable X) (hY : Indecomposable Y),
        rank (liftObj Y hY) < rank (liftObj X hX) := by
    induction hXY using Relation.TransGen.trans_induction_on with
    | single h =>
        intro hX hY
        simpa using stepRank h
    | trans hXY hYZ ihXY ihYZ =>
        intro hX hZ
        have hY := targetIndecomposable hXY
        exact (ihYZ hY hZ).trans (ihXY hX hY)
  have hM : Indecomposable M := sourceIndecomposable hcycle
  exact (lt_irrefl (rank (liftObj M hM))) (rankTrans hcycle hM hM)

private theorem finiteModuleNonzeroNonisomorphism_map_equivalence
    (F : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u', v, v, v} (C := D) k)
    [F.Additive] [F.IsEquivalence]
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (h : FiniteModuleNonzeroNonisomorphism (k := k) (C := C) M N) :
    FiniteModuleNonzeroNonisomorphism (k := k) (C := D)
      (F.obj M) (F.obj N) := by
  rcases h with ⟨hM, hN, f, hf, hnotIso⟩
  refine ⟨(MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      F M).2 hM, ?_⟩
  refine ⟨(MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      F N).2 hN, F.map f, ?_, ?_⟩
  · intro hzero
    apply hf
    apply F.map_injective
    simpa using hzero
  · intro hmapIso
    apply hnotIso
    letI : IsIso (F.map f) := hmapIso
    exact isIso_of_reflects_iso f F

/-- Directedness of finite-support module categories is invariant under an
additive equivalence. -/
theorem hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_equivalence
    (F : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ⥤
      FiniteDimensionalModuleCategory.{u', v, v, v} (C := D) k)
    [F.Additive] [F.IsEquivalence]
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := D)) :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C) := by
  have mapTrans {M N :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
      (h : Relation.TransGen
        (FiniteModuleNonzeroNonisomorphism (k := k) (C := C)) M N) :
      Relation.TransGen
        (FiniteModuleNonzeroNonisomorphism (k := k) (C := D))
        (F.obj M) (F.obj N) := by
    induction h using Relation.TransGen.trans_induction_on with
    | single hMN =>
        exact Relation.TransGen.single
          (finiteModuleNonzeroNonisomorphism_map_equivalence
            (k := k) F hMN)
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  intro M hcycle
  exact H (F.obj M) (mapTrans hcycle)

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

private theorem finiteModuleNonzeroNonisomorphism_extensionByZero
    (S : Set C)
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (h : FiniteModuleNonzeroNonisomorphism
      (k := k) (C := DeletionCategory (k := k) C S) M N) :
    FiniteModuleNonzeroNonisomorphism (k := k) (C := C)
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M)
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj N) := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  rcases h with ⟨hM, hN, f, hf, hnotIso⟩
  refine ⟨finiteDimensionalModuleExtensionByZero_indec
      (k := k) C S M hM,
    finiteDimensionalModuleExtensionByZero_indec (k := k) C S N hN,
    F.map f, ?_, ?_⟩
  · intro hzero
    apply hf
    apply F.map_injective
    simpa using hzero
  · intro hmapIso
    apply hnotIso
    letI : IsIso (F.map f) := hmapIso
    exact isIso_of_reflects_iso f F

private theorem finiteModuleTransGen_extensionByZero
    (S : Set C)
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (h : Relation.TransGen
      (FiniteModuleNonzeroNonisomorphism
        (k := k) (C := DeletionCategory (k := k) C S)) M N) :
    Relation.TransGen
      (FiniteModuleNonzeroNonisomorphism (k := k) (C := C))
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M)
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj N) := by
  induction h with
  | single hMN =>
      exact Relation.TransGen.single
        (finiteModuleNonzeroNonisomorphism_extensionByZero
          (k := k) (C := C) S hMN)
  | tail hMN hNP ih =>
      exact ih.tail
        (finiteModuleNonzeroNonisomorphism_extensionByZero
          (k := k) (C := C) S hNP)

/-- Directedness of the finite-support module category is inherited by every
literal object-deletion quotient. -/
theorem hasAcyclicFiniteModuleNonzeroNonisomorphisms_deletion
    (S : Set C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C)) :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := DeletionCategory (k := k) C S) := by
  intro M hcycle
  exact H ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M)
    (finiteModuleTransGen_extensionByZero
      (k := k) (C := C) S hcycle)

end MagnitudeConjecture.ObjectDeletion
