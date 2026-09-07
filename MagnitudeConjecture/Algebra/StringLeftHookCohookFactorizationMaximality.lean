import MagnitudeConjecture.Algebra.StringHookCohookFactorizationMaximality

/-!
# Literal factorization clauses at the left endpoint

Word reversal conjugates the left hook and cohook maps to the corresponding
right-end maps.  Their literal-string factorization clauses therefore
transport through the canonical reversal isomorphisms without repeating the
component-boundary argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Every factorization of a canonical left-hook projection through a literal
string module has a split first factor or a split second factor. -/
theorem LeftHookExtension.isSplitMono_or_isSplitEpi_of_moduleMap_factorization
    {C M : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    (f : hook.result.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  dsimp only [LeftHookExtension.result] at f hfactor ⊢
  let fReverse : hook.reverseResult.rightModule hmono ⟶
      M.rightModule hmono :=
    (reverseRightModuleIso hook.reverseResult hmono).hom ≫ f
  let gReverse : M.rightModule hmono ⟶ C.reverse.rightModule hmono :=
    g ≫ (reverseRightModuleIso C hmono).hom
  have hfactorReverse : fReverse ≫ gReverse =
      hook.hook.moduleMap hmono := by
    calc
      fReverse ≫ gReverse =
          (reverseRightModuleIso hook.reverseResult hmono).hom ≫
            (f ≫ g) ≫ (reverseRightModuleIso C hmono).hom := by
        simp only [fReverse, gReverse, Category.assoc]
      _ = (reverseRightModuleIso hook.reverseResult hmono).hom ≫
            hook.moduleMap hmono ≫
              (reverseRightModuleIso C hmono).hom := by
        rw [hfactor]
      _ = hook.hook.moduleMap hmono := by
        dsimp only [LeftHookExtension.moduleMap,
          LeftHookExtension.toLeftPositiveBoundaryExtension,
          LeftPositiveBoundaryExtension.moduleMap,
          LeftPositiveBoundaryExtension.result, HookExtension.moduleMap]
        simp only [Category.assoc]
        rw [(reverseRightModuleIso hook.reverseResult hmono).hom_inv_id_assoc]
        rw [(reverseRightModuleIso C hmono).inv_hom_id]
        simp
  rcases hook.hook.isSplitMono_or_isSplitEpi_of_moduleMap_factorization
      hmono fReverse gReverse hfactorReverse with hf | hg
  · left
    letI : IsSplitMono fReverse := hf
    have hsplit : IsSplitMono
        ((reverseRightModuleIso hook.reverseResult hmono).inv ≫
          fReverse) := inferInstance
    simpa only [fReverse, Category.assoc, Iso.inv_hom_id_assoc] using hsplit
  · right
    letI : IsSplitEpi gReverse := hg
    have hsplit : IsSplitEpi
        (gReverse ≫ (reverseRightModuleIso C hmono).inv) := inferInstance
    simpa only [gReverse, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using hsplit

/-- Every factorization of a canonical left-cohook inclusion through a
literal string module has a split first factor or a split second factor. -/
theorem LeftCohookExtension.isSplitMono_or_isSplitEpi_of_moduleMap_factorization
    {C M : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ cohook.result.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  dsimp only [LeftCohookExtension.result] at g hfactor ⊢
  have hfactorUnfolded := hfactor
  dsimp only [LeftCohookExtension.moduleMap,
    LeftCohookExtension.toLeftNegativeBoundaryExtension,
    LeftNegativeBoundaryExtension.moduleMap,
    LeftNegativeBoundaryExtension.result] at hfactorUnfolded
  let fReverse : C.reverse.rightModule hmono ⟶ M.rightModule hmono :=
    (reverseRightModuleIso C hmono).inv ≫ f
  let gReverse : M.rightModule hmono ⟶
      cohook.reverseResult.rightModule hmono :=
    g ≫ (reverseRightModuleIso cohook.reverseResult hmono).inv
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
  rcases cohook.cohook.isSplitMono_or_isSplitEpi_of_moduleMap_factorization
      hmono fReverse gReverse hfactorReverse with hf | hg
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

end MagnitudeConjecture.BoundQuiver.StringWord.Word
