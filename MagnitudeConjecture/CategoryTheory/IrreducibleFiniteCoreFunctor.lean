import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import MagnitudeConjecture.CategoryTheory.IrreducibleLocalFunctor

/-!
# Irreducible morphisms from finite indecomposable cores

A finite control window for indecomposable objects cannot literally contain
every decomposable intermediate object of a factorization.  This file gives
the precise replacement.  Decompose an arbitrary intermediate object and
retain only those summands on which both incident coordinate maps are
nonzero.  The resulting finite biproduct is a factorization core: deleting
the other summands does not change the composite.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- An additive faithful functor reflects indecomposability.  Fullness is not
needed: faithfulness already reflects zero objects, and additivity preserves
binary biproduct decompositions. -/
theorem indecomposable_of_faithful_additive
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.Faithful]
    (X : C) (hX : Indecomposable (F.obj X)) : Indecomposable X := by
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  have reflectZero : ∀ Z : C, IsZero (F.obj Z) → IsZero Z := by
    intro Z hFZ
    rw [IsZero.iff_id_eq_zero]
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact hFZ.eq_of_src _ _
  constructor
  · intro hzero
    exact hX.1 (F.map_isZero hzero)
  · intro Y Z e
    let e' : F.obj X ≅ F.obj Y ⊞ F.obj Z :=
      F.mapIso e ≪≫ F.mapBiprod Y Z
    rcases hX.2 _ _ e' with hY | hZ
    · exact Or.inl (reflectZero Y hY)
    · exact Or.inr (reflectZero Z hZ)

/-- Every indecomposable object which supports nonzero maps between the two
fixed endpoints belongs to the essential image of `F`. -/
def IsLocallyIndecomposableBifactorClosed
    [HasBinaryBiproducts D]
    (F : C ⥤ D) (X Y : C) : Prop :=
  ∀ (M : D), Indecomposable M →
    ∀ (g : F.obj X ⟶ M), g ≠ 0 →
      ∀ (h : M ⟶ F.obj Y), h ≠ 0 →
        ∃ W : C, Nonempty (F.obj W ≅ M)

/-- A fully faithful additive functor preserves an irreducible morphism when
the target category has finite indecomposable decompositions and the
indecomposable objects that interact nontrivially with both endpoints lie in
the local essential image. -/
theorem irreducible_map_of_full_faithful_of_finiteIndecomposableCore
    [HasFiniteBiproducts C] [HasBinaryBiproducts D]
    [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (decomposition : ∀ M : D,
      Nonempty (CategoryTheory.FiniteIndecomposableDecomposition M))
    {X Y : C} {f : X ⟶ Y}
    (hf : IsIrreducibleMorphism f)
    (hclosed : IsLocallyIndecomposableBifactorClosed F X Y) :
    IsIrreducibleMorphism (F.map f) := by
  classical
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    exact hf.not_isSplitMono ((F.isSplitMono_iff f).1 hsplit)
  · intro hsplit
    exact hf.not_isSplitEpi ((F.isSplitEpi_iff f).1 hsplit)
  · intro M g h hgh
    by_cases hg : IsSplitMono g
    · exact Or.inl hg
    by_cases hh : IsSplitEpi h
    · exact Or.inr hh
    obtain ⟨d⟩ := decomposition M
    let a (j : Fin d.n) : F.obj X ⟶ d.summand j :=
      g ≫ d.isoBiproduct.hom ≫ biproduct.π d.summand j
    let b (j : Fin d.n) : d.summand j ⟶ F.obj Y :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv ≫ h
    let Relevant (j : Fin d.n) : Prop := a j ≠ 0 ∧ b j ≠ 0
    choose W e using fun q : {j : Fin d.n // Relevant j} ↦
      hclosed (d.summand q.1) (d.indecomposable q.1)
        (a q.1) q.2.1 (b q.1) q.2.2
    let core : D := ⨁ fun q : {j : Fin d.n // Relevant j} ↦ d.summand q.1
    let sourceCore : C := ⨁ W
    let E : F.obj sourceCore ≅ core :=
      F.mapBiproduct W ≪≫ biproduct.mapIso
        (fun q ↦ Classical.choice (e q))
    let gc : F.obj X ⟶ core := biproduct.lift fun q ↦ a q.1
    let hc : core ⟶ F.obj Y := biproduct.desc fun q ↦ b q.1
    have hcomplement :
        (∑ q : {j : Fin d.n // ¬ Relevant j}, a q.1 ≫ b q.1) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      by_cases ha : a q.1 = 0
      · simp [ha]
      · have hb : b q.1 = 0 := by
          by_contra hb
          exact q.2 ⟨ha, hb⟩
        simp [hb]
    have hrelevantSum :
        (∑ q : {j : Fin d.n // Relevant j}, a q.1 ≫ b q.1) =
          ∑ j : Fin d.n, a j ≫ b j := by
      have hpartition := Fintype.sum_subtype_add_sum_subtype Relevant
        (fun j : Fin d.n ↦ a j ≫ b j)
      calc
        (∑ q : {j : Fin d.n // Relevant j}, a q.1 ≫ b q.1) =
            (∑ q : {j : Fin d.n // Relevant j}, a q.1 ≫ b q.1) +
              ∑ q : {j : Fin d.n // ¬ Relevant j}, a q.1 ≫ b q.1 := by
                rw [hcomplement, add_zero]
        _ = ∑ j : Fin d.n, a j ≫ b j := hpartition
    have hallSum : (∑ j : Fin d.n, a j ≫ b j) = g ≫ h := by
      calc
        (∑ j : Fin d.n, a j ≫ b j) =
            biproduct.lift a ≫ biproduct.desc b :=
              biproduct.lift_desc.symm
        _ = (g ≫ d.isoBiproduct.hom) ≫
              (d.isoBiproduct.inv ≫ h) := by
            congr 1
            · apply biproduct.hom_ext
              intro j
              simp [a]
            · apply biproduct.hom_ext'
              intro j
              simp [b]
        _ = g ≫ h := by simp
    have hcoreFactor : gc ≫ hc = F.map f := by
      rw [biproduct.lift_desc]
      exact hrelevantSum.trans (hallSum.trans hgh)
    let g' : X ⟶ sourceCore := F.preimage (gc ≫ E.inv)
    let h' : sourceCore ⟶ Y := F.preimage (E.hom ≫ hc)
    have hfactor : g' ≫ h' = f := by
      apply F.map_injective
      simp only [g', h', F.map_comp, F.map_preimage]
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hcoreFactor
    rcases hf.factorization g' h' hfactor with hg' | hh'
    · left
      letI : IsSplitMono g' := hg'
      letI : IsSplitMono (F.map g') := inferInstance
      have hgcMap : gc = F.map g' ≫ E.hom := by
        simp [g', Category.assoc]
      have hgcSplit : IsSplitMono gc := by
        rw [hgcMap]
        infer_instance
      letI : IsSplitMono gc := hgcSplit
      let p : M ⟶ core :=
        d.isoBiproduct.hom ≫
          biproduct.lift (fun q : {j : Fin d.n // Relevant j} ↦
            biproduct.π d.summand q.1)
      have hgp : g ≫ p = gc := by
        apply biproduct.hom_ext
        intro q
        simp [p, gc, a, Category.assoc]
      exact IsSplitMono.mk'
        { retraction := p ≫ retraction gc
          id := by
            rw [← Category.assoc]
            rw [hgp]
            exact IsSplitMono.id gc }
    · right
      letI : IsSplitEpi h' := hh'
      letI : IsSplitEpi (F.map h') := inferInstance
      have hhcMap : hc = E.inv ≫ F.map h' := by
        simp [h']
      have hhcSplit : IsSplitEpi hc := by
        rw [hhcMap]
        infer_instance
      letI : IsSplitEpi hc := hhcSplit
      let i : core ⟶ M :=
        biproduct.desc (fun q : {j : Fin d.n // Relevant j} ↦
          biproduct.ι d.summand q.1) ≫ d.isoBiproduct.inv
      have hih : i ≫ h = hc := by
        apply biproduct.hom_ext'
        intro q
        simp [i, hc, b, Category.assoc]
      exact IsSplitEpi.mk'
        { section_ := section_ hc ≫ i
          id := by
            rw [Category.assoc]
            rw [hih]
            exact IsSplitEpi.id hc }

/-- Under finite indecomposable-core closure, full faithfulness identifies
irreducibility on the nose. -/
theorem isIrreducibleMorphism_map_iff_of_finiteIndecomposableCore
    [HasFiniteBiproducts C] [HasBinaryBiproducts D]
    [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (decomposition : ∀ M : D,
      Nonempty (CategoryTheory.FiniteIndecomposableDecomposition M))
    {X Y : C} {f : X ⟶ Y}
    (hclosed : IsLocallyIndecomposableBifactorClosed F X Y) :
    IsIrreducibleMorphism (F.map f) ↔ IsIrreducibleMorphism f :=
  ⟨fun hf ↦ irreducible_of_map_of_full_faithful F hf,
    fun hf ↦ irreducible_map_of_full_faithful_of_finiteIndecomposableCore
      F decomposition hf hclosed⟩

end MagnitudeConjecture
