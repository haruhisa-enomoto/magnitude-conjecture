import MagnitudeConjecture.Algebra.StringGraphComponentFullSupport

/-!
# Equal-length branches of hook and cohook factorizations

The graph-component extraction retains nonzero coefficients of the actual
factor maps.  If the intermediate word has the same length as the old hook or
cohook word, the selected one-sided full-support component is automatically
two-sided, so the corresponding factor itself is an isomorphism.  Thus a
nonsplit factor forces strict growth of the intermediate word.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- In a right-hook factorization through an equal-length string, the second
factor is an isomorphism. -/
theorem HookExtension.secondFactor_isIso_of_intermediate_length_eq
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono)
    (hlength : M.length = C.length) :
    IsIso g := by
  obtain ⟨first, second, _, hsecondCoefficient, _, houtput⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hinput : second.HasFullInputSupport :=
    BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.hasFullInputSupport_of_length_eq
      second houtput hlength
  exact second.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    hmono hmono hinput houtput g hsecondCoefficient

/-- A nonsplit second factor of a right hook must pass through a strictly
longer intermediate string than the hook target. -/
theorem HookExtension.base_length_lt_intermediate_of_not_isSplitEpi
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono)
    (hg : ¬ IsSplitEpi g) :
    C.length < M.length := by
  obtain ⟨_, second, _, _, _, houtput⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hle := houtput.target_length_le_source_length second
  apply lt_of_le_of_ne hle
  intro hlength
  letI : IsIso g := hook.secondFactor_isIso_of_intermediate_length_eq
    hmono f g hfactor hlength.symm
  exact hg inferInstance

/-- In a right-cohook factorization through an equal-length string, the first
factor is an isomorphism. -/
theorem CohookExtension.firstFactor_isIso_of_intermediate_length_eq
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono)
    (hlength : M.length = C.length) :
    IsIso f := by
  obtain ⟨first, second, hfirstCoefficient, _, _, hinput⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have houtput : first.HasFullOutputSupport :=
    BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.hasFullOutputSupport_of_length_eq
      first hinput hlength.symm
  exact first.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    hmono hmono hinput houtput f hfirstCoefficient

/-- A nonsplit first factor of a right cohook must pass through a strictly
longer intermediate string than the cohook source. -/
theorem CohookExtension.base_length_lt_intermediate_of_not_isSplitMono
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono)
    (hf : ¬ IsSplitMono f) :
    C.length < M.length := by
  obtain ⟨first, _, _, _, _, hinput⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hle := hinput.source_length_le_target_length first
  apply lt_of_le_of_ne hle
  intro hlength
  letI : IsIso f := cohook.firstFactor_isIso_of_intermediate_length_eq
    hmono f g hfactor hlength.symm
  exact hf inferInstance

/-- In a left-hook factorization through an equal-length string, the second
factor is an isomorphism. -/
theorem LeftHookExtension.secondFactor_isIso_of_intermediate_length_eq
    {C M : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    (f : hook.result.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono)
    (hlength : M.length = C.length) :
    IsIso g := by
  obtain ⟨first, second, _, hsecondCoefficient, _, houtput⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hinput : second.HasFullInputSupport :=
    BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.hasFullInputSupport_of_length_eq
      second houtput hlength
  exact second.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    hmono hmono hinput houtput g hsecondCoefficient

/-- A nonsplit second factor of a left hook must pass through a strictly
longer intermediate string than the hook target. -/
theorem LeftHookExtension.base_length_lt_intermediate_of_not_isSplitEpi
    {C M : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    (f : hook.result.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono)
    (hg : ¬ IsSplitEpi g) :
    C.length < M.length := by
  obtain ⟨_, second, _, _, _, houtput⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hle := houtput.target_length_le_source_length second
  apply lt_of_le_of_ne hle
  intro hlength
  letI : IsIso g := hook.secondFactor_isIso_of_intermediate_length_eq
    hmono f g hfactor hlength.symm
  exact hg inferInstance

/-- In a left-cohook factorization through an equal-length string, the first
factor is an isomorphism. -/
theorem LeftCohookExtension.firstFactor_isIso_of_intermediate_length_eq
    {C M : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ cohook.result.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono)
    (hlength : M.length = C.length) :
    IsIso f := by
  obtain ⟨first, second, hfirstCoefficient, _, _, hinput⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have houtput : first.HasFullOutputSupport :=
    BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.hasFullOutputSupport_of_length_eq
      first hinput hlength.symm
  exact first.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    hmono hmono hinput houtput f hfirstCoefficient

/-- A nonsplit first factor of a left cohook must pass through a strictly
longer intermediate string than the cohook source. -/
theorem LeftCohookExtension.base_length_lt_intermediate_of_not_isSplitMono
    {C M : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ cohook.result.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono)
    (hf : ¬ IsSplitMono f) :
    C.length < M.length := by
  obtain ⟨first, _, _, _, _, hinput⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hle := hinput.source_length_le_target_length first
  apply lt_of_le_of_ne hle
  intro hlength
  letI : IsIso f := cohook.firstFactor_isIso_of_intermediate_length_eq
    hmono f g hfactor hlength.symm
  exact hf inferInstance

end MagnitudeConjecture.BoundQuiver.StringWord.Word
