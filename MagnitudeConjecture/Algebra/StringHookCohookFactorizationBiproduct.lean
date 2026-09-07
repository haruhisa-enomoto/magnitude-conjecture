import MagnitudeConjecture.Algebra.StringLeftHookCohookFactorizationMaximality

/-!
# Hook and cohook factorizations through sums of string modules

A factorization through a finite biproduct is the sum of its factorizations
through the individual summands.  Since a canonical hook or cohook map has a
nonzero coefficient on its distinguished graph component, one summand makes
a nonzero contribution there.  Component-pair maximality on that summand
forces the original map into the biproduct to split monic or the original map
out of it to split epic.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u v

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

private theorem isSplitMono_of_comp_biproduct_π
    {V : Type v} [CategoryTheory.Category V] [Preadditive V]
    {ι : Type} [Fintype ι] {F : ι → V} [HasBiproduct F]
    {X : V} (f : X ⟶ ⨁ F) (i : ι)
    (hfi : IsSplitMono (f ≫ biproduct.π F i)) :
    IsSplitMono f := by
  let fi := f ≫ biproduct.π F i
  letI : IsSplitMono fi := hfi
  exact IsSplitMono.mk'
    { retraction := biproduct.π F i ≫ retraction fi
      id := by
        rw [← Category.assoc]
        exact IsSplitMono.id fi }

private theorem isSplitEpi_of_biproduct_ι_comp
    {V : Type v} [CategoryTheory.Category V] [Preadditive V]
    {ι : Type} [Fintype ι] {F : ι → V} [HasBiproduct F]
    {Y : V} (g : (⨁ F) ⟶ Y) (i : ι)
    (hgi : IsSplitEpi (biproduct.ι F i ≫ g)) :
    IsSplitEpi g := by
  let gi := biproduct.ι F i ≫ g
  letI : IsSplitEpi gi := hgi
  exact IsSplitEpi.mk'
    { section_ := section_ gi ≫ biproduct.ι F i
      id := by
        rw [Category.assoc]
        exact IsSplitEpi.id gi }

private theorem splitFactors_of_conjugated_middle
    {V : Type v} [CategoryTheory.Category V]
    {X Y N N' : V} (e : N ≅ N') (f : X ⟶ N) (g : N ⟶ Y)
    (h : IsSplitMono (f ≫ e.hom) ∨ IsSplitEpi (e.inv ≫ g)) :
    IsSplitMono f ∨ IsSplitEpi g := by
  rcases h with hf | hg
  · left
    letI : IsSplitMono (f ≫ e.hom) := hf
    have hsplit : IsSplitMono ((f ≫ e.hom) ≫ e.inv) := inferInstance
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hsplit
  · right
    letI : IsSplitEpi (e.inv ≫ g) := hg
    have hsplit : IsSplitEpi (e.hom ≫ (e.inv ≫ g)) := inferInstance
    simpa only [← Category.assoc, Iso.hom_inv_id,
      Category.id_comp] using hsplit

/-- If a morphism through a finite biproduct of literal string modules has a
nonzero coefficient on the distinguished component of a right hook, then its
two factors cannot both be nonsplit. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_biproduct_factorization_of_coefficient_ne_zero
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    (f : D.rightModule hmono ⟶ ⨁ fun i ↦ (M i).rightModule hmono)
    (g : (⨁ fun i ↦ (M i).rightModule hmono) ⟶ C.rightModule hmono)
    (hcoefficient : D.morphismCoefficientAt C hmono hmono (f ≫ g)
      (hook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  classical
  let F := fun i : ι ↦ (M i).rightModule hmono
  let fi (i : ι) : D.rightModule hmono ⟶ (M i).rightModule hmono :=
    f ≫ biproduct.π F i
  let gi (i : ι) : (M i).rightModule hmono ⟶ C.rightModule hmono :=
    biproduct.ι F i ≫ g
  have hsum : (∑ i : ι, fi i ≫ gi i) = f ≫ g := by
    calc
      (∑ i : ι, fi i ≫ gi i) =
          f ≫ (∑ i : ι, biproduct.π F i ≫ biproduct.ι F i) ≫ g := by
        simp only [fi, gi, Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = f ≫ g := by
        dsimp only [F]
        have htotal :
            (∑ i : ι,
              biproduct.π (fun i ↦ (M i).rightModule hmono) i ≫
                biproduct.ι (fun i ↦ (M i).rightModule hmono) i) =
              𝟙 (⨁ fun i ↦ (M i).rightModule hmono) :=
          biproduct.total
        rw [htotal]
        simp
      _ = f ≫ g := rfl
  let p := (hook.moduleMapComponent hmono).1.representative
  have hsumCoefficient :
      (∑ i : ι,
        D.morphismCoefficientAt C hmono hmono (fi i ≫ gi i) p) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun t : D.rightModule hmono ⟶ C.rightModule hmono ↦
        D.morphismCoefficientAt C hmono hmono t p) hsum
    rw [D.morphismCoefficientAt_sum C hmono hmono Finset.univ
      (fun i ↦ fi i ≫ gi i)] at hcoeff
    rw [hzero] at hcoeff
    exact hcoefficient hcoeff.symm
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumCoefficient
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct⟩ :=
    D.exists_component_pair_of_comp_coefficient_ne_zero
      (M i) C hmono hmono hmono (fi i) (gi i) p hi
  have hproduct_ne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap
          (M i) hmono hmono first ≫
        (M i).boundaryFreeMorphismCoefficientComponentMap
          C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  rcases hook.isSplitMono_or_isSplitEpi_of_component_pair hmono
      (fi i) (gi i) first second hfirstCoefficient hsecondCoefficient
      hproduct_ne with hfi | hgi
  · exact Or.inl (isSplitMono_of_comp_biproduct_π f i hfi)
  · exact Or.inr (isSplitEpi_of_biproduct_ι_comp g i hgi)

/-- A right-hook factorization through a finite biproduct of literal string
modules has a split first or second factor. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_biproduct_factorization
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    (f : D.rightModule hmono ⟶ ⨁ fun i ↦ (M i).rightModule hmono)
    (g : (⨁ fun i ↦ (M i).rightModule hmono) ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  apply hook.isSplitMono_or_isSplitEpi_of_biproduct_factorization_of_coefficient_ne_zero
    hmono M f g
  rw [hfactor, hook.moduleMap_eq_componentMap hmono,
    D.morphismCoefficientAt_boundaryFreeComponentMap,
    D.coefficientComponentIndicator_eq_one C _ _ (Relation.EqvGen.refl _)]
  exact (one_ne_zero : (1 : k) ≠ 0)

/-- If a morphism through a finite biproduct of literal string modules has a
nonzero coefficient on the distinguished component of a right cohook, then its
two factors cannot both be nonsplit. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_biproduct_factorization_of_coefficient_ne_zero
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    (f : C.rightModule hmono ⟶ ⨁ fun i ↦ (M i).rightModule hmono)
    (g : (⨁ fun i ↦ (M i).rightModule hmono) ⟶ D.rightModule hmono)
    (hcoefficient : C.morphismCoefficientAt D hmono hmono (f ≫ g)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  classical
  let F := fun i : ι ↦ (M i).rightModule hmono
  let fi (i : ι) : C.rightModule hmono ⟶ (M i).rightModule hmono :=
    f ≫ biproduct.π F i
  let gi (i : ι) : (M i).rightModule hmono ⟶ D.rightModule hmono :=
    biproduct.ι F i ≫ g
  have hsum : (∑ i : ι, fi i ≫ gi i) = f ≫ g := by
    calc
      (∑ i : ι, fi i ≫ gi i) =
          f ≫ (∑ i : ι, biproduct.π F i ≫ biproduct.ι F i) ≫ g := by
        simp only [fi, gi, Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = f ≫ g := by
        dsimp only [F]
        have htotal :
            (∑ i : ι,
              biproduct.π (fun i ↦ (M i).rightModule hmono) i ≫
                biproduct.ι (fun i ↦ (M i).rightModule hmono) i) =
              𝟙 (⨁ fun i ↦ (M i).rightModule hmono) :=
          biproduct.total
        rw [htotal]
        simp
      _ = f ≫ g := rfl
  let p := (cohook.moduleMapComponent hmono).1.representative
  have hsumCoefficient :
      (∑ i : ι,
        C.morphismCoefficientAt D hmono hmono (fi i ≫ gi i) p) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun t : C.rightModule hmono ⟶ D.rightModule hmono ↦
        C.morphismCoefficientAt D hmono hmono t p) hsum
    rw [C.morphismCoefficientAt_sum D hmono hmono Finset.univ
      (fun i ↦ fi i ≫ gi i)] at hcoeff
    rw [hzero] at hcoeff
    exact hcoefficient hcoeff.symm
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumCoefficient
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient, hproduct⟩ :=
    C.exists_component_pair_of_comp_coefficient_ne_zero
      (M i) D hmono hmono hmono (fi i) (gi i) p hi
  have hproduct_ne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap
          (M i) hmono hmono first ≫
        (M i).boundaryFreeMorphismCoefficientComponentMap
          D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  rcases cohook.isSplitMono_or_isSplitEpi_of_component_pair hmono
      (fi i) (gi i) first second hfirstCoefficient hsecondCoefficient
      hproduct_ne with hfi | hgi
  · exact Or.inl (isSplitMono_of_comp_biproduct_π f i hfi)
  · exact Or.inr (isSplitEpi_of_biproduct_ι_comp g i hgi)

/-- A right-cohook factorization through a finite biproduct of literal
string modules has a split first or second factor. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_biproduct_factorization
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    (f : C.rightModule hmono ⟶ ⨁ fun i ↦ (M i).rightModule hmono)
    (g : (⨁ fun i ↦ (M i).rightModule hmono) ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  apply cohook.isSplitMono_or_isSplitEpi_of_biproduct_factorization_of_coefficient_ne_zero
    hmono M f g
  rw [hfactor, cohook.moduleMap_eq_componentMap hmono,
    C.morphismCoefficientAt_boundaryFreeComponentMap,
    C.coefficientComponentIndicator_eq_one D _ _ (Relation.EqvGen.refl _)]
  exact (one_ne_zero : (1 : k) ≠ 0)

/-- A right-hook factorization through an object explicitly isomorphic to a
finite biproduct of literal string modules has a split factor. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    {N : (Category R)ᵒᵖ ⥤ ModuleCat k}
    (e : N ≅ ⨁ fun i ↦ (M i).rightModule hmono)
    (f : D.rightModule hmono ⟶ N) (g : N ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  let fSum := f ≫ e.hom
  let gSum := e.inv ≫ g
  have hfactorSum : fSum ≫ gSum = hook.moduleMap hmono := by
    simp only [fSum, gSum, Category.assoc, Iso.hom_inv_id_assoc, hfactor]
  exact splitFactors_of_conjugated_middle e f g
    (hook.isSplitMono_or_isSplitEpi_of_biproduct_factorization
      hmono M fSum gSum hfactorSum)

/-- The distinguished-coefficient form of the right-hook factorization
criterion is invariant under replacing the intermediate object by an
isomorphic finite string sum. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization_of_coefficient_ne_zero
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    {N : (Category R)ᵒᵖ ⥤ ModuleCat k}
    (e : N ≅ ⨁ fun i ↦ (M i).rightModule hmono)
    (f : D.rightModule hmono ⟶ N) (g : N ⟶ C.rightModule hmono)
    (hcoefficient : D.morphismCoefficientAt C hmono hmono (f ≫ g)
      (hook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  let fSum := f ≫ e.hom
  let gSum := e.inv ≫ g
  have hcomposite : fSum ≫ gSum = f ≫ g := by
    simp only [fSum, gSum, Category.assoc, Iso.hom_inv_id_assoc]
  apply splitFactors_of_conjugated_middle e f g
  apply hook.isSplitMono_or_isSplitEpi_of_biproduct_factorization_of_coefficient_ne_zero
    hmono M fSum gSum
  rw [hcomposite]
  exact hcoefficient

/-- A right-cohook factorization through an object explicitly isomorphic to
a finite biproduct of literal string modules has a split factor. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    {N : (Category R)ᵒᵖ ⥤ ModuleCat k}
    (e : N ≅ ⨁ fun i ↦ (M i).rightModule hmono)
    (f : C.rightModule hmono ⟶ N) (g : N ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  let fSum := f ≫ e.hom
  let gSum := e.inv ≫ g
  have hfactorSum : fSum ≫ gSum = cohook.moduleMap hmono := by
    simp only [fSum, gSum, Category.assoc, Iso.hom_inv_id_assoc, hfactor]
  exact splitFactors_of_conjugated_middle e f g
    (cohook.isSplitMono_or_isSplitEpi_of_biproduct_factorization
      hmono M fSum gSum hfactorSum)

/-- The distinguished-coefficient form of the right-cohook factorization
criterion is invariant under replacing the intermediate object by an
isomorphic finite string sum. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization_of_coefficient_ne_zero
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    {N : (Category R)ᵒᵖ ⥤ ModuleCat k}
    (e : N ≅ ⨁ fun i ↦ (M i).rightModule hmono)
    (f : C.rightModule hmono ⟶ N) (g : N ⟶ D.rightModule hmono)
    (hcoefficient : C.morphismCoefficientAt D hmono hmono (f ≫ g)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  let fSum := f ≫ e.hom
  let gSum := e.inv ≫ g
  have hcomposite : fSum ≫ gSum = f ≫ g := by
    simp only [fSum, gSum, Category.assoc, Iso.hom_inv_id_assoc]
  apply splitFactors_of_conjugated_middle e f g
  apply cohook.isSplitMono_or_isSplitEpi_of_biproduct_factorization_of_coefficient_ne_zero
    hmono M fSum gSum
  rw [hcomposite]
  exact hcoefficient

/-- Reversal transports the finite-biproduct factorization clause to a left
hook. -/
theorem LeftHookExtension.isSplitMono_or_isSplitEpi_of_biproduct_factorization
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    (f : hook.result.rightModule hmono ⟶
      ⨁ fun i ↦ (M i).rightModule hmono)
    (g : (⨁ fun i ↦ (M i).rightModule hmono) ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  dsimp only [LeftHookExtension.result] at f hfactor ⊢
  let fReverse := (reverseRightModuleIso hook.reverseResult hmono).hom ≫ f
  let gReverse := g ≫ (reverseRightModuleIso C hmono).hom
  have hfactorReverse : fReverse ≫ gReverse = hook.hook.moduleMap hmono := by
    calc
      fReverse ≫ gReverse =
          (reverseRightModuleIso hook.reverseResult hmono).hom ≫
            (f ≫ g) ≫ (reverseRightModuleIso C hmono).hom := by
        simp only [fReverse, gReverse, Category.assoc]
      _ = (reverseRightModuleIso hook.reverseResult hmono).hom ≫
            hook.moduleMap hmono ≫
              (reverseRightModuleIso C hmono).hom := by rw [hfactor]
      _ = hook.hook.moduleMap hmono := by
        dsimp only [LeftHookExtension.moduleMap,
          LeftHookExtension.toLeftPositiveBoundaryExtension,
          LeftPositiveBoundaryExtension.moduleMap,
          LeftPositiveBoundaryExtension.result, HookExtension.moduleMap]
        simp only [Category.assoc]
        rw [(reverseRightModuleIso hook.reverseResult hmono).hom_inv_id_assoc]
        rw [(reverseRightModuleIso C hmono).inv_hom_id]
        simp
  rcases hook.hook.isSplitMono_or_isSplitEpi_of_biproduct_factorization
      hmono M fReverse gReverse hfactorReverse with hf | hg
  · left
    letI : IsSplitMono fReverse := hf
    have hsplit : IsSplitMono
        ((reverseRightModuleIso hook.reverseResult hmono).inv ≫ fReverse) :=
      inferInstance
    simpa only [fReverse, Category.assoc, Iso.inv_hom_id_assoc] using hsplit
  · right
    letI : IsSplitEpi gReverse := hg
    have hsplit : IsSplitEpi
        (gReverse ≫ (reverseRightModuleIso C hmono).inv) := inferInstance
    simpa only [gReverse, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using hsplit

/-- Reversal transports the finite-biproduct factorization clause to a left
cohook. -/
theorem LeftCohookExtension.isSplitMono_or_isSplitEpi_of_biproduct_factorization
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    (f : C.rightModule hmono ⟶ ⨁ fun i ↦ (M i).rightModule hmono)
    (g : (⨁ fun i ↦ (M i).rightModule hmono) ⟶
      cohook.result.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  dsimp only [LeftCohookExtension.result] at g hfactor ⊢
  have hfactorUnfolded := hfactor
  dsimp only [LeftCohookExtension.moduleMap,
    LeftCohookExtension.toLeftNegativeBoundaryExtension,
    LeftNegativeBoundaryExtension.moduleMap,
    LeftNegativeBoundaryExtension.result] at hfactorUnfolded
  let fReverse := (reverseRightModuleIso C hmono).inv ≫ f
  let gReverse := g ≫ (reverseRightModuleIso cohook.reverseResult hmono).inv
  have hfactorReverse : fReverse ≫ gReverse =
      cohook.cohook.moduleMap hmono := by
    calc
      fReverse ≫ gReverse =
          (reverseRightModuleIso C hmono).inv ≫
            (f ≫ g) ≫
              (reverseRightModuleIso cohook.reverseResult hmono).inv := by
        simp only [fReverse, gReverse, Category.assoc]
      _ = (reverseRightModuleIso C hmono).inv ≫
            ((reverseRightModuleIso C hmono).hom ≫
              cohook.cohook.toNegativeBoundaryExtension.rightModuleInclusion
                hmono ≫
              (reverseRightModuleIso cohook.reverseResult hmono).hom) ≫
            (reverseRightModuleIso cohook.reverseResult hmono).inv := by
        rw [hfactorUnfolded]
      _ = cohook.cohook.moduleMap hmono := by
        dsimp only [CohookExtension.moduleMap]
        simp only [Category.assoc]
        rw [(reverseRightModuleIso C hmono).inv_hom_id_assoc]
        rw [(reverseRightModuleIso cohook.reverseResult hmono).hom_inv_id]
        simp
  rcases cohook.cohook.isSplitMono_or_isSplitEpi_of_biproduct_factorization
      hmono M fReverse gReverse hfactorReverse with hf | hg
  · left
    letI : IsSplitMono fReverse := hf
    have hsplit : IsSplitMono
        ((reverseRightModuleIso C hmono).hom ≫ fReverse) := inferInstance
    simpa only [fReverse, Category.assoc, Iso.hom_inv_id_assoc] using hsplit
  · right
    letI : IsSplitEpi gReverse := hg
    have hsplit : IsSplitEpi
        (gReverse ≫
          (reverseRightModuleIso cohook.reverseResult hmono).hom) :=
      inferInstance
    simpa only [gReverse, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using hsplit

/-- A left-hook factorization through an object explicitly isomorphic to a
finite biproduct of literal string modules has a split factor. -/
theorem LeftHookExtension.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    {N : (Category R)ᵒᵖ ⥤ ModuleCat k}
    (e : N ≅ ⨁ fun i ↦ (M i).rightModule hmono)
    (f : hook.result.rightModule hmono ⟶ N)
    (g : N ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  let fSum := f ≫ e.hom
  let gSum := e.inv ≫ g
  have hfactorSum : fSum ≫ gSum = hook.moduleMap hmono := by
    simp only [fSum, gSum, Category.assoc, Iso.hom_inv_id_assoc, hfactor]
  exact splitFactors_of_conjugated_middle e f g
    (hook.isSplitMono_or_isSplitEpi_of_biproduct_factorization
      hmono M fSum gSum hfactorSum)

/-- A left-cohook factorization through an object explicitly isomorphic to a
finite biproduct of literal string modules has a split factor. -/
theorem LeftCohookExtension.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    {ι : Type} [Fintype ι] (M : ι → Word R)
    {N : (Category R)ᵒᵖ ⥤ ModuleCat k}
    (e : N ≅ ⨁ fun i ↦ (M i).rightModule hmono)
    (f : C.rightModule hmono ⟶ N)
    (g : N ⟶ cohook.result.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  let fSum := f ≫ e.hom
  let gSum := e.inv ≫ g
  have hfactorSum : fSum ≫ gSum = cohook.moduleMap hmono := by
    simp only [fSum, gSum, Category.assoc, Iso.hom_inv_id_assoc, hfactor]
  exact splitFactors_of_conjugated_middle e f g
    (cohook.isSplitMono_or_isSplitEpi_of_biproduct_factorization
      hmono M fSum gSum hfactorSum)

end MagnitudeConjecture.BoundQuiver.StringWord.Word
