import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleBiproducts
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Abelian categories of finite-dimensional linear modules

Kernels and cokernels of additive linear module functors are again additive
and linear.  Pointwise, a kernel embeds into its source and a cokernel is a
quotient of its target.  Finite-dimensionality and finite object support
therefore pass to both constructions.  Together with the previously
constructed finite biproducts, this makes the linear-module category and its
finite-dimensional, finite-support full subcategory abelian.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MagnitudeConjecture.CoveringHom

universe u v uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [CategoryTheory.Linear k C]

instance isLinearModule_containsZero :
    (IsLinearModule.{u, v, uK, uM} (C := C) k).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    constructor
    · exact { map_add := by intros; simp }
    · exact { map_smul := by intros; simp }⟩

instance isLinearModule_closedUnderKernels :
    (IsLinearModule.{u, v, uK, uM} (C := C) k).IsClosedUnderKernels where
  kernels_le := by
    intro K hK
    rcases hK with ⟨f, s, hs, ⟨hX, hY⟩⟩
    letI : _ := hX.1
    letI : _ := hX.2
    letI : Mono s.ι := Fork.IsLimit.mono hs
    constructor
    · constructor
      intro A B p q
      apply (cancel_mono (s.ι.app B)).1
      rw [s.ι.naturality (p + q), Preadditive.add_comp,
        s.ι.naturality p, s.ι.naturality q, Functor.map_add,
        Preadditive.comp_add]
    · constructor
      intro A B p r
      apply (cancel_mono (s.ι.app B)).1
      rw [s.ι.naturality (r • p), CategoryTheory.Linear.smul_comp,
        s.ι.naturality p, Functor.map_smul,
        CategoryTheory.Linear.comp_smul]

instance isLinearModule_closedUnderCokernels :
    (IsLinearModule.{u, v, uK, uM} (C := C) k).IsClosedUnderCokernels where
  cokernels_le := by
    intro Q hQ
    rcases hQ with ⟨f, s, hs, ⟨hX, hY⟩⟩
    letI : _ := hY.1
    letI : _ := hY.2
    letI : Epi s.π := Cofork.IsColimit.epi hs
    constructor
    · constructor
      intro A B p q
      apply (cancel_epi (s.π.app A)).1
      rw [← s.π.naturality (p + q), Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add,
        s.π.naturality p, s.π.naturality q]
    · constructor
      intro A B p r
      apply (cancel_epi (s.π.app A)).1
      rw [← s.π.naturality (r • p), Functor.map_smul,
        CategoryTheory.Linear.smul_comp,
        CategoryTheory.Linear.comp_smul, s.π.naturality p]

instance isFiniteDimensionalModule_containsZero :
    (IsFiniteDimensionalModule.{u, v, uK, uM}
      (C := C) k).ContainsZero where
  exists_zero := by
    let Z : LinearModuleCategory.{u, v, uK, uM} (C := C) k :=
      ⟨0, by
        constructor
        · exact { map_add := by intros; simp }
        · exact { map_smul := by intros; simp }⟩
    refine ⟨Z, ?_, ?_⟩
    · exact IsZero.of_full_of_faithful_of_isZero
        (IsLinearModule (C := C) k).ι Z (isZero_zero _)
    · constructor
      · intro X
        change FiniteDimensional k ((0 : C ⥤ ModuleCat.{uM} k).obj X)
        letI : Subsingleton ((0 : C ⥤ ModuleCat.{uM} k).obj X) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj X)
        infer_instance
      · refine Set.finite_empty.subset ?_
        intro X hX
        change Nontrivial ((0 : C ⥤ ModuleCat.{uM} k).obj X) at hX
        letI : Subsingleton ((0 : C ⥤ ModuleCat.{uM} k).obj X) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj X)
        exact (not_nontrivial _ hX).elim

instance isFiniteDimensionalModule_closedUnderKernels :
    (IsFiniteDimensionalModule.{u, v, uK, uM}
      (C := C) k).IsClosedUnderKernels where
  kernels_le := by
    intro K hK
    rcases hK with ⟨f, s, hs, ⟨hX, hY⟩⟩
    letI : Mono s.ι := Fork.IsLimit.mono hs
    let I : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        C ⥤ ModuleCat.{uM} k := (IsLinearModule (C := C) k).ι
    letI : I.PreservesMonomorphisms :=
      (IsLinearModule (C := C) k).preservesMonomorphisms_ι_of_isNormalEpiCategory
    haveI : Mono (I.map s.ι) := I.map_mono s.ι
    constructor
    · intro X
      haveI : Mono (s.ι.hom.app X) := by
        change Mono ((I.map s.ι).app X)
        infer_instance
      letI := hX.1 X
      exact FiniteDimensional.of_injective
        (s.ι.hom.app X).hom
        ((ModuleCat.mono_iff_injective _).mp inferInstance)
    · refine hX.2.subset ?_
      intro X hXnontrivial
      haveI : Mono (s.ι.hom.app X) := by
        change Mono ((I.map s.ι).app X)
        infer_instance
      have hinj : Function.Injective (s.ι.hom.app X) :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      change Nontrivial (s.pt.obj.obj X) at hXnontrivial
      letI : Nontrivial (s.pt.obj.obj X) := hXnontrivial
      exact hinj.nontrivial

instance isFiniteDimensionalModule_closedUnderCokernels :
    (IsFiniteDimensionalModule.{u, v, uK, uM}
      (C := C) k).IsClosedUnderCokernels where
  cokernels_le := by
    intro Q hQ
    rcases hQ with ⟨f, s, hs, ⟨hX, hY⟩⟩
    letI : Epi s.π := Cofork.IsColimit.epi hs
    let I : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
        C ⥤ ModuleCat.{uM} k := (IsLinearModule (C := C) k).ι
    letI : I.PreservesEpimorphisms :=
      (IsLinearModule (C := C) k).preservesEpimorphisms_ι_of_isNormalMonoCategory
    haveI : Epi (I.map s.π) := I.map_epi s.π
    constructor
    · intro X
      haveI : Epi (s.π.hom.app X) := by
        change Epi ((I.map s.π).app X)
        infer_instance
      letI := hY.1 X
      exact Module.Finite.of_surjective
        (s.π.hom.app X).hom
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    · refine hY.2.subset ?_
      intro X hXnontrivial
      haveI : Epi (s.π.hom.app X) := by
        change Epi ((I.map s.π).app X)
        infer_instance
      have hsurj : Function.Surjective (s.π.hom.app X) :=
        (ModuleCat.epi_iff_surjective _).mp inferInstance
      change Nontrivial (s.pt.obj.obj X) at hXnontrivial
      letI : Nontrivial (s.pt.obj.obj X) := hXnontrivial
      exact hsurj.nontrivial

end MagnitudeConjecture.CoveringHom
