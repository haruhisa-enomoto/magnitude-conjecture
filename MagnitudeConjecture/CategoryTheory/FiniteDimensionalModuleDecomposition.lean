import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleBiproducts
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite decompositions of finite-dimensional modules

The total dimension of a finite-support module is the finite sum of its
pointwise dimensions.  It vanishes only on a zero module and is additive under
binary biproduct decompositions.  Strong induction on this rank therefore
decomposes every finite-dimensional module into finitely many indecomposables.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.CoveringHom

universe u v uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [CategoryTheory.Linear k C]

/-- The sum of the pointwise dimensions of a finite-support module. -/
def moduleTotalDimension
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) : ℕ :=
  ∑ᶠ X : C, Module.finrank k (M.obj.obj.obj X)

/-- The pointwise dimension function of a finite-dimensional module has finite
support. -/
theorem moduleFinrank_hasFiniteSupport
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    (fun X : C ↦ Module.finrank k (M.obj.obj.obj X)).HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  refine (finite_moduleSupport k M).subset ?_
  intro X hX
  rw [Function.mem_support] at hX
  exact Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)

/-- Every epic endomorphism of a finite-support pointwise
finite-dimensional module is invertible. -/
theorem isIso_of_epi_finiteDimensionalModule_endo
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (e : M ⟶ M) [Epi e] : IsIso e := by
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let I := (IsLinearModule (C := C) k).ι
  letI : J.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesEpimorphisms :=
    ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
      (IsLinearModule (C := C) k)
  haveI : Epi (I.map (J.map e)) := I.map_epi (J.map e)
  haveI happ (X : C) : Epi ((I.map (J.map e)).app X) := inferInstance
  haveI hisoApp (X : C) : IsIso ((I.map (J.map e)).app X) := by
    change IsIso (e.hom.hom.app X)
    letI : FiniteDimensional k (M.obj.obj.obj X) := M.property.1 X
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hsurj : Function.Surjective ((I.map (J.map e)).app X) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    exact ⟨
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).2 hsurj,
      hsurj⟩
  haveI : IsIso (I.map (J.map e)) := NatIso.isIso_of_isIso_app _
  haveI : IsIso (J.map e) := isIso_of_reflects_iso (J.map e) I
  exact isIso_of_reflects_iso e J

/-- Every monic endomorphism of a finite-support pointwise
finite-dimensional module is invertible. -/
theorem isIso_of_mono_finiteDimensionalModule_endo
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (e : M ⟶ M) [Mono e] : IsIso e := by
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let I := (IsLinearModule (C := C) k).ι
  letI : J.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsLinearModule (C := C) k)
  haveI : Mono (I.map (J.map e)) := I.map_mono (J.map e)
  haveI happ (X : C) : Mono ((I.map (J.map e)).app X) := inferInstance
  haveI hisoApp (X : C) : IsIso ((I.map (J.map e)).app X) := by
    change IsIso (e.hom.hom.app X)
    letI : FiniteDimensional k (M.obj.obj.obj X) := M.property.1 X
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hinj : Function.Injective ((I.map (J.map e)).app X) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).1 hinj⟩
  haveI : IsIso (I.map (J.map e)) := NatIso.isIso_of_isIso_app _
  haveI : IsIso (J.map e) := isIso_of_reflects_iso (J.map e) I
  exact isIso_of_reflects_iso e J

/-- A proper subobject of a finite module has strictly smaller total
pointwise dimension. -/
theorem moduleTotalDimension_lt_of_mono_not_isIso
    (N M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (i : N ⟶ M) [Mono i] (hi : ¬ IsIso i) :
    moduleTotalDimension N < moduleTotalDimension M := by
  classical
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let I := (IsLinearModule (C := C) k).ι
  letI : J.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsLinearModule (C := C) k)
  haveI : Mono (I.map (J.map i)) := I.map_mono (J.map i)
  haveI hiApp (X : C) : Mono ((I.map (J.map i)).app X) := inferInstance
  have hle (X : C) :
      Module.finrank k (N.obj.obj.obj X) ≤
        Module.finrank k (M.obj.obj.obj X) := by
    exact LinearMap.finrank_le_finrank_of_injective
      ((ModuleCat.mono_iff_injective _).mp (hiApp X))
  have hbad : ∃ X : C, ¬ IsIso ((I.map (J.map i)).app X) := by
    by_contra h
    push Not at h
    letI hiAppIso (X : C) : IsIso ((I.map (J.map i)).app X) := h X
    haveI : IsIso (I.map (J.map i)) := NatIso.isIso_of_isIso_app _
    haveI : IsIso (J.map i) := isIso_of_reflects_iso (J.map i) I
    haveI : IsIso i := isIso_of_reflects_iso i J
    exact hi inferInstance
  obtain ⟨X, hX⟩ := hbad
  have hlt : Module.finrank k (N.obj.obj.obj X) <
      Module.finrank k (M.obj.obj.obj X) := by
    refine (hle X).lt_of_ne ?_
    intro heq
    apply hX
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hinj : Function.Injective ((I.map (J.map i)).app X) :=
      (ModuleCat.mono_iff_injective _).mp (hiApp X)
    exact ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj⟩
  let f : C → ℕ := fun Y ↦ Module.finrank k (N.obj.obj.obj Y)
  let g : C → ℕ := fun Y ↦ Module.finrank k (M.obj.obj.obj Y)
  have hf := moduleFinrank_hasFiniteSupport N
  have hg := moduleFinrank_hasFiniteSupport M
  let s := (hf.union hg).toFinset
  rw [moduleTotalDimension, moduleTotalDimension,
    finsum_eq_finsetSum_of_support_subset f
      (s := s) (by
        intro Y hY
        change Y ∈ (hf.union hg).toFinset
        rw [Set.Finite.mem_toFinset, Set.mem_union]
        exact Or.inl hY),
    finsum_eq_finsetSum_of_support_subset g
      (s := s) (by
        intro Y hY
        change Y ∈ (hf.union hg).toFinset
        rw [Set.Finite.mem_toFinset, Set.mem_union]
        exact Or.inr hY)]
  apply Finset.sum_lt_sum
  · intro Y hY
    exact hle Y
  · refine ⟨X, ?_, hlt⟩
    change X ∈ (hf.union hg).toFinset
    rw [Set.Finite.mem_toFinset, Set.mem_union]
    right
    change Module.finrank k (M.obj.obj.obj X) ≠ 0
    omega

/-- The image of a noninvertible endomorphism of a finite module has
strictly smaller total pointwise dimension. -/
theorem moduleTotalDimension_image_lt_of_not_isIso
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (e : M ⟶ M) (he : ¬ IsIso e) :
    moduleTotalDimension (Abelian.image e) < moduleTotalDimension M := by
  classical
  let Q := Abelian.image e
  let i : Q ⟶ M := Abelian.image.ι e
  have hiNot : ¬ IsIso i := by
    intro hi
    letI : IsIso i := hi
    haveI : Epi e := by
      rw [← Abelian.image.fac e]
      infer_instance
    exact he (isIso_of_epi_finiteDimensionalModule_endo M e)
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let I := (IsLinearModule (C := C) k).ι
  letI : J.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsLinearModule (C := C) k)
  haveI : Mono (I.map (J.map i)) := I.map_mono (J.map i)
  haveI hiApp (X : C) : Mono ((I.map (J.map i)).app X) := inferInstance
  have hle (X : C) :
      Module.finrank k (Q.obj.obj.obj X) ≤
        Module.finrank k (M.obj.obj.obj X) := by
    exact LinearMap.finrank_le_finrank_of_injective
      ((ModuleCat.mono_iff_injective _).mp (hiApp X))
  have hbad : ∃ X : C, ¬ IsIso ((I.map (J.map i)).app X) := by
    by_contra h
    push Not at h
    letI hiAppIso (X : C) : IsIso ((I.map (J.map i)).app X) := h X
    haveI : IsIso (I.map (J.map i)) := NatIso.isIso_of_isIso_app _
    haveI : IsIso (J.map i) := isIso_of_reflects_iso (J.map i) I
    haveI : IsIso i := isIso_of_reflects_iso i J
    exact hiNot inferInstance
  obtain ⟨X, hX⟩ := hbad
  have hlt : Module.finrank k (Q.obj.obj.obj X) <
      Module.finrank k (M.obj.obj.obj X) := by
    refine (hle X).lt_of_ne ?_
    intro heq
    apply hX
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have hinj : Function.Injective ((I.map (J.map i)).app X) :=
      (ModuleCat.mono_iff_injective _).mp (hiApp X)
    exact ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj⟩
  let f : C → ℕ := fun Y ↦ Module.finrank k (Q.obj.obj.obj Y)
  let g : C → ℕ := fun Y ↦ Module.finrank k (M.obj.obj.obj Y)
  have hf := moduleFinrank_hasFiniteSupport Q
  have hg := moduleFinrank_hasFiniteSupport M
  let s := (hf.union hg).toFinset
  rw [moduleTotalDimension, moduleTotalDimension,
    finsum_eq_finsetSum_of_support_subset f
      (s := s) (by
        intro Y hY
        change Y ∈ (hf.union hg).toFinset
        rw [Set.Finite.mem_toFinset, Set.mem_union]
        exact Or.inl hY),
    finsum_eq_finsetSum_of_support_subset g
      (s := s) (by
        intro Y hY
        change Y ∈ (hf.union hg).toFinset
        rw [Set.Finite.mem_toFinset, Set.mem_union]
        exact Or.inr hY)]
  apply Finset.sum_lt_sum
  · intro Y hY
    exact hle Y
  · refine ⟨X, ?_, hlt⟩
    change X ∈ (hf.union hg).toFinset
    rw [Set.Finite.mem_toFinset, Set.mem_union]
    right
    change Module.finrank k (M.obj.obj.obj X) ≠ 0
    omega

/-- A finite-dimensional module of total dimension zero is a zero object. -/
theorem isZero_of_moduleTotalDimension_eq_zero
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : moduleTotalDimension M = 0) : IsZero M := by
  have hpoint : ∀ X : C, Module.finrank k (M.obj.obj.obj X) = 0 := by
    intro X
    by_contra hX
    have hpos : 0 < moduleTotalDimension M :=
      finsum_pos (fun _ ↦ Nat.zero_le _)
        ⟨X, Nat.pos_of_ne_zero hX⟩ (moduleFinrank_hasFiniteSupport M)
    omega
  have hfun : IsZero M.obj.obj := by
    apply Functor.isZero
    intro X
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (Module.finrank_zero_iff.mp (hpoint X))
  have hlinear : IsZero M.obj :=
    IsZero.of_full_of_faithful_of_isZero
      (IsLinearModule (C := C) k).ι M.obj hfun
  exact IsZero.of_full_of_faithful_of_isZero
    (IsFiniteDimensionalModule (C := C) k).ι M hlinear

/-- Every nonzero finite-dimensional module contains a simple submodule. -/
theorem finiteDimensionalModule_exists_simple_subobject
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : ¬ IsZero M) :
    ∃ (N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
      (i : N ⟶ M), Simple N ∧ Mono i := by
  classical
  let p : ℕ → Prop := fun n ↦ ∃
    (N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (i : N ⟶ M), Mono i ∧ ¬ IsZero N ∧ moduleTotalDimension N = n
  have hp : ∃ n, p n := ⟨moduleTotalDimension M, M, 𝟙 M,
    inferInstance, hM, rfl⟩
  obtain ⟨N, i, hi, hN, hdim⟩ := Nat.find_spec hp
  letI : Mono i := hi
  refine ⟨N, i, ?_, inferInstance⟩
  constructor
  intro X f hf
  constructor
  · intro hIso hzero
    letI : IsIso f := hIso
    letI : Epi f := inferInstance
    exact hN (IsZero.of_epi_eq_zero f hzero)
  · intro hnonzero
    by_contra hnotIso
    have hX : ¬ IsZero X := by
      intro hXzero
      exact hnonzero (hXzero.eq_of_src f 0)
    have hlt : moduleTotalDimension X < moduleTotalDimension N :=
      moduleTotalDimension_lt_of_mono_not_isIso X N f hnotIso
    have hmin : Nat.find hp ≤ moduleTotalDimension X :=
      Nat.find_min' hp ⟨X, f ≫ i, inferInstance, hX, rfl⟩
    rw [hdim] at hlt
    exact (not_lt_of_ge hmin) hlt

/-- Total dimension is additive across any displayed binary biproduct
decomposition. -/
theorem moduleTotalDimension_biprod
    {X Y Z : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k}
    (e : X ≅ (Y ⊞ Z)) :
    moduleTotalDimension X =
      moduleTotalDimension Y + moduleTotalDimension Z := by
  have hpoint : ∀ T : C,
      Module.finrank k (X.obj.obj.obj T) =
        Module.finrank k (Y.obj.obj.obj T) +
          Module.finrank k (Z.obj.obj.obj T) := by
    intro T
    let P := IsFiniteDimensionalModule.{u, v, uK, uM} (C := C) k
    let Q := IsLinearModule.{u, v, uK, uM} (C := C) k
    let I : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        LinearModuleCategory.{u, v, uK, uM} (C := C) k := P.ι
    let J : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        (C ⥤ ModuleCat.{uM} k) := Q.ι
    let E := (evaluation C (ModuleCat.{uM} k)).obj T
    let V := I ⋙ J ⋙ E
    letI : V.Additive := inferInstance
    letI : FiniteDimensional k (V.obj Y) := Y.property.1 T
    letI : FiniteDimensional k (V.obj Z) := Z.property.1 T
    have hb : (V.mapBinaryBicone
        (BinaryBiproduct.bicone Y Z)).IsBilimit :=
      isBinaryBilimitOfTotal _ (by
        change
          V.map (BinaryBiproduct.bicone Y Z).fst ≫
              V.map (BinaryBiproduct.bicone Y Z).inl +
            V.map (BinaryBiproduct.bicone Y Z).snd ≫
              V.map (BinaryBiproduct.bicone Y Z).inr =
            𝟙 (V.obj (Y ⊞ Z))
        have htotal := congrArg V.map
          (IsBilimit.binary_total (BinaryBiproduct.isBilimit Y Z))
        simpa only [V.map_comp, V.map_add, V.map_id] using htotal)
    let eT : V.obj X ≅ ModuleCat.of k (V.obj Y × V.obj Z) :=
      V.mapIso e ≪≫ hb.isLimit.conePointUniqueUpToIso
        (ModuleCat.binaryProductLimitCone (V.obj Y) (V.obj Z)).isLimit
    change Module.finrank k (V.obj X) =
      Module.finrank k (V.obj Y) + Module.finrank k (V.obj Z)
    rw [eT.toLinearEquiv.finrank_eq, Module.finrank_prod]
  rw [moduleTotalDimension, moduleTotalDimension, moduleTotalDimension,
    finsum_congr hpoint]
  exact finsum_add_distrib
    (moduleFinrank_hasFiniteSupport Y) (moduleFinrank_hasFiniteSupport Z)

/-- Every finite-dimensional finite-support linear module admits a finite
biproduct decomposition into indecomposable modules. -/
theorem finiteDimensionalModule_finiteIndecomposableDecomposition
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    Nonempty
      (MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition M) :=
  MagnitudeConjecture.CategoryTheory.finiteIndecomposableDecomposition_of_rank
    moduleTotalDimension isZero_of_moduleTotalDimension_eq_zero
      moduleTotalDimension_biprod M

end MagnitudeConjecture.CoveringHom
