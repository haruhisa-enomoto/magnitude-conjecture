import Mathlib.CategoryTheory.Preadditive.Schur
import MagnitudeConjecture.Algebra.RightModuleFactorCategory

/-!
# Directedness for the finite right-module skeleton

This file adapts the representation-directed order kernel from the clean
`subcat-research-mathlib-only` formalization to the magnitude package's
literal finite right-module skeleton.  It retains only the part needed here:
cycle-freeness makes nonzero endomorphisms invertible, hence scalar over an
algebraically closed field, and the scalar conclusion descends to every
literal factor object.

Donor provenance is recorded in the magnitude formalization thread.  The
implementation is expressed entirely in the local right-module vocabulary and
introduces no dependency on the donor repository.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A nonzero nonisomorphism between two selected indecomposable right
modules. -/
def NonzeroNonisomorphism (i j : Fin S.n) : Prop :=
  ∃ f : S.fgObj i ⟶ S.fgObj j, f ≠ 0 ∧ ¬ IsIso f

/-- The cycle-free part of representation-directedness on the finite
duplicate-free skeleton. -/
def HasAcyclicNonzeroNonisomorphisms : Prop :=
  ∀ i : Fin S.n, ¬ Relation.TransGen S.NonzeroNonisomorphism i i

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
/-- In a directed skeleton every nonzero indecomposable endomorphism is an
isomorphism: otherwise it is a one-edge cycle. -/
theorem HasAcyclicNonzeroNonisomorphisms.isIso_of_ne_zero_endomorphism
    (H : S.HasAcyclicNonzeroNonisomorphisms) (i : Fin S.n)
    (f : S.fgObj i ⟶ S.fgObj i) (hf : f ≠ 0) :
    IsIso f := by
  by_contra hfiso
  exact H i (Relation.TransGen.single ⟨f, hf, hfiso⟩)

/-- Algebraic closedness and directedness make every selected
indecomposable endomorphism space one-dimensional. -/
theorem HasAcyclicNonzeroNonisomorphisms.finrank_endomorphism_eq_one
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (i : Fin S.n) :
    Module.finrank k (S.fgObj i ⟶ S.fgObj i) = 1 := by
  letI : FiniteDimensional k (S.fgObj i ⟶ S.fgObj i) := inferInstance
  apply CategoryTheory.finrank_endomorphism_eq_one k
  intro f
  constructor
  · intro hfiso
    letI : IsIso f := hfiso
    intro hfzero
    have hzero : IsZero (S.fgObj i) := IsZero.of_mono_eq_zero f hfzero
    exact (S.fgObj_indecomposable i).1 hzero
  · exact H.isIso_of_ne_zero_endomorphism S i f

/-- Constructive Schur form: every selected indecomposable endomorphism is a
scalar multiple of its identity. -/
theorem HasAcyclicNonzeroNonisomorphisms.endomorphism_eq_smul_id
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (i : Fin S.n) (f : S.fgObj i ⟶ S.fgObj i) :
    ∃ c : k, c • CategoryStruct.id (S.fgObj i) = f := by
  letI : FiniteDimensional k (S.fgObj i ⟶ S.fgObj i) := inferInstance
  have hid :
      (CategoryStruct.id (S.fgObj i) : S.fgObj i ⟶ S.fgObj i) ≠ 0 := by
    intro hzero
    have hz : IsZero (S.fgObj i) :=
      IsZero.of_mono_eq_zero (CategoryStruct.id (S.fgObj i)) hzero
    exact (S.fgObj_indecomposable i).1 hz
  exact
    ((finrank_eq_one_iff_of_nonzero'
      (CategoryStruct.id (S.fgObj i)) hid).mp
        (H.finrank_endomorphism_eq_one S i)) f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe w

variable {k A : Type w} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Directed scalar endomorphisms descend through the literal quotient
functor to every surviving factor object. -/
theorem HasAcyclicNonzeroNonisomorphisms.factorObject_endomorphism_eq_smul_id
    [IsAlgClosed k] (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (f : S.factorObject K x ⟶ S.factorObject K x) :
    ∃ c : k,
      c • CategoryStruct.id (S.factorObject K x) = f := by
  let F := S.factorFunctor K
  obtain ⟨g, rfl⟩ := F.map_surjective f
  obtain ⟨c, hc⟩ := H.endomorphism_eq_smul_id S x.1 g.hom
  refine ⟨c, ?_⟩
  rw [← F.map_id, ← F.map_smul]
  apply congrArg F.map
  apply ObjectProperty.hom_ext
  exact hc

/-- Two surviving factor indecomposables admitting nonzero maps in both
directions have the same label.  Any pair of distinct labels would lift to a
two-edge cycle of nonzero nonisomorphisms in the ambient directed skeleton. -/
theorem HasAcyclicNonzeroNonisomorphisms.factorObject_label_eq_of_two_way
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x y : S.SurvivingLabel K)
    (f : S.factorObject K x ⟶ S.factorObject K y) (hf : f ≠ 0)
    (g : S.factorObject K y ⟶ S.factorObject K x) (hg : g ≠ 0) :
    x = y := by
  let F := S.factorFunctor K
  obtain ⟨f', rfl⟩ := F.map_surjective f
  obtain ⟨g', rfl⟩ := F.map_surjective g
  have hf' : f'.hom ≠ 0 := by
    intro hzero
    apply hf
    rw [show f' = 0 by
      apply ObjectProperty.hom_ext
      exact hzero]
    exact F.map_zero _ _
  have hg' : g'.hom ≠ 0 := by
    intro hzero
    apply hg
    rw [show g' = 0 by
      apply ObjectProperty.hom_ext
      exact hzero]
    exact F.map_zero _ _
  have hlabel : x.1 = y.1 := by
    by_contra hne
    have hfnot : ¬ IsIso f'.hom := by
      intro hfiso
      obtain ⟨q, hq₁, hq₂⟩ := hfiso.out
      exact hne (S.fgObj_skeletal ⟨
        { hom := f'.hom
          inv := q
          hom_inv_id := hq₁
          inv_hom_id := hq₂ }⟩)
    have hgnot : ¬ IsIso g'.hom := by
      intro hgiso
      obtain ⟨q, hq₁, hq₂⟩ := hgiso.out
      exact Ne.symm hne (S.fgObj_skeletal ⟨
        { hom := g'.hom
          inv := q
          hom_inv_id := hq₁
          inv_hom_id := hq₂ }⟩)
    exact H x.1
      (Relation.TransGen.trans
        (Relation.TransGen.single ⟨f'.hom, hf', hfnot⟩)
        (Relation.TransGen.single ⟨g'.hom, hg', hgnot⟩))
  exact Subtype.ext hlabel

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
