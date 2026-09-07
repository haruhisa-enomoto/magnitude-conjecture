import MagnitudeConjecture.Algebra.StringHookCohookFactorizationBiproduct
import MagnitudeConjecture.Algebra.StringHookCohookStrict
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.RadicalMinimality
import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleCofinite

/-!
# Irreducible hook and cohook maps in the finite module category

This file isolates the exact finite-string-sum input needed to turn the raw
string-sum factorization theorems into categorical irreducibility.  A
finite-dimensional module is a finite string sum when its underlying raw
functor is isomorphic to a finite biproduct of literal string modules.  If
every finite-dimensional module has this form, all four canonical hook and
cohook maps are irreducible in the finite-dimensional module category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q} [Fintype Q]

/-- The right-hook map bundled in the finite-dimensional linear-module
category. -/
def HookExtension.finiteModuleMap
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) :
    D.finiteRightModule hmono ⟶ C.finiteRightModule hmono :=
  ObjectProperty.homMk (ObjectProperty.homMk (hook.moduleMap hmono))

/-- The right-cohook map bundled in the finite-dimensional linear-module
category. -/
def CohookExtension.finiteModuleMap
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) :
    C.finiteRightModule hmono ⟶ D.finiteRightModule hmono :=
  ObjectProperty.homMk (ObjectProperty.homMk (cohook.moduleMap hmono))

/-- The left-hook map bundled in the finite-dimensional linear-module
category. -/
def LeftHookExtension.finiteModuleMap
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) :
    hook.result.finiteRightModule hmono ⟶ C.finiteRightModule hmono :=
  ObjectProperty.homMk (ObjectProperty.homMk (hook.moduleMap hmono))

/-- The left-cohook map bundled in the finite-dimensional linear-module
category. -/
def LeftCohookExtension.finiteModuleMap
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) :
    C.finiteRightModule hmono ⟶ cohook.result.finiteRightModule hmono :=
  ObjectProperty.homMk (ObjectProperty.homMk (cohook.moduleMap hmono))

@[simp]
theorem HookExtension.finiteModuleMap_hom_hom
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) :
    (hook.finiteModuleMap hmono).hom.hom = hook.moduleMap hmono :=
  rfl

@[simp]
theorem CohookExtension.finiteModuleMap_hom_hom
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) :
    (cohook.finiteModuleMap hmono).hom.hom = cohook.moduleMap hmono :=
  rfl

@[simp]
theorem LeftHookExtension.finiteModuleMap_hom_hom
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) :
    (hook.finiteModuleMap hmono).hom.hom = hook.moduleMap hmono :=
  rfl

@[simp]
theorem LeftCohookExtension.finiteModuleMap_hom_hom
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) :
    (cohook.finiteModuleMap hmono).hom.hom = cohook.moduleMap hmono :=
  rfl

/-- Transport the result word of a right cohook along a literal equality. -/
def CohookExtension.transportResult
    {C D D' : Word R} (cohook : CohookExtension C D)
    (h : D = D') : CohookExtension C D' :=
  Eq.mp (congrArg (fun W : Word R ↦ CohookExtension C W) h) cohook

/-- Transporting a cohook result agrees with postcomposition by the induced
equality isomorphism of finite string modules. -/
theorem CohookExtension.finiteModuleMap_transportResult
    {C D D' : Word R} (cohook : CohookExtension C D)
    (h : D = D') (hmono : IsMonomial R) :
    (cohook.transportResult h).finiteModuleMap hmono =
      cohook.finiteModuleMap hmono ≫
        (eqToIso (congrArg
          (fun W : Word R ↦ W.finiteRightModule hmono) h)).hom := by
  subst D'
  simp [CohookExtension.transportResult]

/-- Transport the source word of a right cohook along a literal equality. -/
def CohookExtension.transportSource
    {C C' D : Word R} (cohook : CohookExtension C D)
    (h : C = C') : CohookExtension C' D :=
  Eq.mp (congrArg (fun W : Word R ↦ CohookExtension W D) h) cohook

/-- Transporting a cohook source agrees with precomposition by the inverse
of the induced equality isomorphism of finite string modules. -/
theorem CohookExtension.finiteModuleMap_transportSource
    {C C' D : Word R} (cohook : CohookExtension C D)
    (h : C = C') (hmono : IsMonomial R) :
    (cohook.transportSource h).finiteModuleMap hmono =
      (eqToIso (congrArg
        (fun W : Word R ↦ W.finiteRightModule hmono) h)).inv ≫
          cohook.finiteModuleMap hmono := by
  subst C'
  simp [CohookExtension.transportSource]

/-- A finite-dimensional module is a finite string sum when its underlying
raw module is isomorphic to a finite biproduct of literal string modules. -/
def IsFiniteStringSum (hmono : IsMonomial R)
    (N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k) : Prop :=
  ∃ (n : ℕ) (M : Fin n → Word R),
    Nonempty (N.obj.obj ≅ ⨁ fun i ↦ (M i).rightModule hmono)

/-- The exact object-coverage statement needed below: every
finite-dimensional module is a finite sum of literal string modules. -/
def EveryFiniteModuleIsFiniteStringSum (hmono : IsMonomial R) : Prop :=
  ∀ N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k,
    IsFiniteStringSum hmono N

omit [Fintype Q] in
private theorem isSplitMono_underlying_iff
    {X Y : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k} (f : X ⟶ Y) :
    IsSplitMono f.hom.hom ↔ IsSplitMono f := by
  let J : CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category R)ᵒᵖ) k ⥤
      ((Category R)ᵒᵖ ⥤ ModuleCat k) :=
    (CoveringHom.IsFiniteDimensionalModule
        (C := (Category R)ᵒᵖ) k).ι ⋙
      (CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k).ι
  have h := J.isSplitMono_iff f
  change IsSplitMono f.hom.hom ↔ IsSplitMono f at h
  exact h

omit [Fintype Q] in
private theorem isSplitEpi_underlying_iff
    {X Y : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k} (f : X ⟶ Y) :
    IsSplitEpi f.hom.hom ↔ IsSplitEpi f := by
  let J : CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category R)ᵒᵖ) k ⥤
      ((Category R)ᵒᵖ ⥤ ModuleCat k) :=
    (CoveringHom.IsFiniteDimensionalModule
        (C := (Category R)ᵒᵖ) k).ι ⋙
      (CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k).ι
  have h := J.isSplitEpi_iff f
  change IsSplitEpi f.hom.hom ↔ IsSplitEpi f at h
  exact h

/-- The right-hook factorization clause in the finite-dimensional category,
assuming only that this particular intermediate object is a finite string
sum. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    {N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k}
    (hN : IsFiniteStringSum hmono N)
    (f : D.finiteRightModule hmono ⟶ N)
    (g : N ⟶ C.finiteRightModule hmono)
    (hfactor : f ≫ g = hook.finiteModuleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨n, M, ⟨e⟩⟩ := hN
  have hfactorRaw : f.hom.hom ≫ g.hom.hom = hook.moduleMap hmono := by
    simpa using congrArg (fun q ↦ q.hom.hom) hfactor
  rcases hook.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
      hmono M e f.hom.hom g.hom.hom hfactorRaw with hf | hg
  · exact Or.inl ((isSplitMono_underlying_iff f).1 hf)
  · exact Or.inr ((isSplitEpi_underlying_iff g).1 hg)

/-- The right-cohook factorization clause in the finite-dimensional category
for one finite-string-sum intermediate object. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    {N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k}
    (hN : IsFiniteStringSum hmono N)
    (f : C.finiteRightModule hmono ⟶ N)
    (g : N ⟶ D.finiteRightModule hmono)
    (hfactor : f ≫ g = cohook.finiteModuleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨n, M, ⟨e⟩⟩ := hN
  have hfactorRaw : f.hom.hom ≫ g.hom.hom = cohook.moduleMap hmono := by
    simpa using congrArg (fun q ↦ q.hom.hom) hfactor
  rcases cohook.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
      hmono M e f.hom.hom g.hom.hom hfactorRaw with hf | hg
  · exact Or.inl ((isSplitMono_underlying_iff f).1 hf)
  · exact Or.inr ((isSplitEpi_underlying_iff g).1 hg)

/-- The right-hook distinguished-coefficient criterion in the bundled
finite-dimensional module category. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_finiteModule_factorization_of_coefficient_ne_zero
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    {N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k}
    (hN : IsFiniteStringSum hmono N)
    (f : D.finiteRightModule hmono ⟶ N)
    (g : N ⟶ C.finiteRightModule hmono)
    (hcoefficient : D.morphismCoefficientAt C hmono hmono
      (f ≫ g).hom.hom
      (hook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨n, M, ⟨e⟩⟩ := hN
  change D.morphismCoefficientAt C hmono hmono
    (f.hom.hom ≫ g.hom.hom)
    (hook.moduleMapComponent hmono).1.representative ≠ 0 at hcoefficient
  rcases
      hook.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization_of_coefficient_ne_zero
        hmono M e f.hom.hom g.hom.hom hcoefficient with hf | hg
  · exact Or.inl ((isSplitMono_underlying_iff f).1 hf)
  · exact Or.inr ((isSplitEpi_underlying_iff g).1 hg)

/-- The right-cohook distinguished-coefficient criterion in the bundled
finite-dimensional module category. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_finiteModule_factorization_of_coefficient_ne_zero
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    {N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k}
    (hN : IsFiniteStringSum hmono N)
    (f : C.finiteRightModule hmono ⟶ N)
    (g : N ⟶ D.finiteRightModule hmono)
    (hcoefficient : C.morphismCoefficientAt D hmono hmono
      (f ≫ g).hom.hom
      (cohook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨n, M, ⟨e⟩⟩ := hN
  change C.morphismCoefficientAt D hmono hmono
    (f.hom.hom ≫ g.hom.hom)
    (cohook.moduleMapComponent hmono).1.representative ≠ 0 at hcoefficient
  rcases
      cohook.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization_of_coefficient_ne_zero
        hmono M e f.hom.hom g.hom.hom hcoefficient with hf | hg
  · exact Or.inl ((isSplitMono_underlying_iff f).1 hf)
  · exact Or.inr ((isSplitEpi_underlying_iff g).1 hg)

/-- The left-hook factorization clause in the finite-dimensional category
for one finite-string-sum intermediate object. -/
theorem LeftHookExtension.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    {N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k}
    (hN : IsFiniteStringSum hmono N)
    (f : hook.result.finiteRightModule hmono ⟶ N)
    (g : N ⟶ C.finiteRightModule hmono)
    (hfactor : f ≫ g = hook.finiteModuleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨n, M, ⟨e⟩⟩ := hN
  have hfactorRaw : f.hom.hom ≫ g.hom.hom = hook.moduleMap hmono := by
    simpa using congrArg (fun q ↦ q.hom.hom) hfactor
  rcases hook.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
      hmono M e f.hom.hom g.hom.hom hfactorRaw with hf | hg
  · exact Or.inl ((isSplitMono_underlying_iff f).1 hf)
  · exact Or.inr ((isSplitEpi_underlying_iff g).1 hg)

/-- The left-cohook factorization clause in the finite-dimensional category
for one finite-string-sum intermediate object. -/
theorem LeftCohookExtension.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    {N : CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k}
    (hN : IsFiniteStringSum hmono N)
    (f : C.finiteRightModule hmono ⟶ N)
    (g : N ⟶ cohook.result.finiteRightModule hmono)
    (hfactor : f ≫ g = cohook.finiteModuleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨n, M, ⟨e⟩⟩ := hN
  have hfactorRaw : f.hom.hom ≫ g.hom.hom = cohook.moduleMap hmono := by
    simpa using congrArg (fun q ↦ q.hom.hom) hfactor
  rcases cohook.isSplitMono_or_isSplitEpi_of_iso_biproduct_factorization
      hmono M e f.hom.hom g.hom.hom hfactorRaw with hf | hg
  · exact Or.inl ((isSplitMono_underlying_iff f).1 hf)
  · exact Or.inr ((isSplitEpi_underlying_iff g).1 hg)

/-- A radical map with a nonzero coefficient on a distinguished right-hook
component is irreducible, provided finite modules are finite string sums. -/
theorem HookExtension.isIrreducibleMorphism_of_isRadicalMorphism_of_coefficient_ne_zero
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (t : D.finiteRightModule hmono ⟶ C.finiteRightModule hmono)
    (hradical : IsRadicalMorphism t)
    (hcoefficient : D.morphismCoefficientAt C hmono hmono t.hom.hom
      (hook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsIrreducibleMorphism t := by
  letI : IsLocalRing (End (C.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (C.finiteRightModule hmono)
      (C.finiteRightModule_indecomposable hmono)
  refine
    { not_isSplitMono :=
        MagnitudeConjecture.CategoryTheory.not_isSplitMono_of_isRadicalMorphism
          (D.finiteRightModule_indecomposable hmono).1 hradical
      not_isSplitEpi :=
        (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
          (C.finiteRightModule_indecomposable hmono).1 t).1 hradical
      factorization := ?_ }
  intro N f g hfactor
  apply hook.isSplitMono_or_isSplitEpi_of_finiteModule_factorization_of_coefficient_ne_zero
    hmono (hcover N) f g
  have hraw : (f ≫ g).hom.hom = t.hom.hom :=
    congrArg (fun q ↦ q.hom.hom) hfactor
  rw [hraw]
  exact hcoefficient

/-- A radical map with a nonzero coefficient on a distinguished right-cohook
component is irreducible, provided finite modules are finite string sums. -/
theorem CohookExtension.isIrreducibleMorphism_of_isRadicalMorphism_of_coefficient_ne_zero
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (t : C.finiteRightModule hmono ⟶ D.finiteRightModule hmono)
    (hradical : IsRadicalMorphism t)
    (hcoefficient : C.morphismCoefficientAt D hmono hmono t.hom.hom
      (cohook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsIrreducibleMorphism t := by
  letI : IsLocalRing (End (D.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (D.finiteRightModule hmono)
      (D.finiteRightModule_indecomposable hmono)
  refine
    { not_isSplitMono :=
        MagnitudeConjecture.CategoryTheory.not_isSplitMono_of_isRadicalMorphism
          (C.finiteRightModule_indecomposable hmono).1 hradical
      not_isSplitEpi :=
        (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitEpi_of_local_end
          (D.finiteRightModule_indecomposable hmono).1 t).1 hradical
      factorization := ?_ }
  intro N f g hfactor
  apply cohook.isSplitMono_or_isSplitEpi_of_finiteModule_factorization_of_coefficient_ne_zero
    hmono (hcover N) f g
  have hraw : (f ≫ g).hom.hom = t.hom.hom :=
    congrArg (fun q ↦ q.hom.hom) hfactor
  rw [hraw]
  exact hcoefficient

/-- Under finite-string-sum coverage, the right-hook projection is an
irreducible morphism in the finite-dimensional module category. -/
theorem HookExtension.finiteModuleMap_isIrreducible_of_finiteStringSum
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism (hook.finiteModuleMap hmono) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    exact hook.moduleMap_not_isSplitMono hmono
      ((isSplitMono_underlying_iff (hook.finiteModuleMap hmono)).2 hsplit)
  · intro hsplit
    exact hook.moduleMap_not_isSplitEpi hmono
      ((isSplitEpi_underlying_iff (hook.finiteModuleMap hmono)).2 hsplit)
  · intro N f g hfactor
    exact hook.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
      hmono (hcover N) f g hfactor

/-- Under finite-string-sum coverage, the right-cohook inclusion is an
irreducible morphism in the finite-dimensional module category. -/
theorem CohookExtension.finiteModuleMap_isIrreducible_of_finiteStringSum
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism (cohook.finiteModuleMap hmono) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    exact cohook.moduleMap_not_isSplitMono hmono
      ((isSplitMono_underlying_iff (cohook.finiteModuleMap hmono)).2 hsplit)
  · intro hsplit
    exact cohook.moduleMap_not_isSplitEpi hmono
      ((isSplitEpi_underlying_iff (cohook.finiteModuleMap hmono)).2 hsplit)
  · intro N f g hfactor
    exact cohook.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
      hmono (hcover N) f g hfactor

/-- Under finite-string-sum coverage, the left-hook projection is an
irreducible morphism in the finite-dimensional module category. -/
theorem LeftHookExtension.finiteModuleMap_isIrreducible_of_finiteStringSum
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism (hook.finiteModuleMap hmono) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    exact hook.moduleMap_not_isSplitMono hmono
      ((isSplitMono_underlying_iff (hook.finiteModuleMap hmono)).2 hsplit)
  · intro hsplit
    exact hook.moduleMap_not_isSplitEpi hmono
      ((isSplitEpi_underlying_iff (hook.finiteModuleMap hmono)).2 hsplit)
  · intro N f g hfactor
    exact hook.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
      hmono (hcover N) f g hfactor

/-- Under finite-string-sum coverage, the left-cohook inclusion is an
irreducible morphism in the finite-dimensional module category. -/
theorem LeftCohookExtension.finiteModuleMap_isIrreducible_of_finiteStringSum
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono) :
    IsIrreducibleMorphism (cohook.finiteModuleMap hmono) := by
  refine
    { not_isSplitMono := ?_
      not_isSplitEpi := ?_
      factorization := ?_ }
  · intro hsplit
    exact cohook.moduleMap_not_isSplitMono hmono
      ((isSplitMono_underlying_iff (cohook.finiteModuleMap hmono)).2 hsplit)
  · intro hsplit
    exact cohook.moduleMap_not_isSplitEpi hmono
      ((isSplitEpi_underlying_iff (cohook.finiteModuleMap hmono)).2 hsplit)
  · intro N f g hfactor
    exact cohook.isSplitMono_or_isSplitEpi_of_finiteModule_factorization
      hmono (hcover N) f g hfactor

/-- Subtracting a scalar multiple of a radical map whose distinguished
right-hook coefficient vanishes leaves a nonzero distinguished coefficient,
and hence remains irreducible. -/
theorem HookExtension.finiteModuleMap_sub_smul_isIrreducible_of_coefficient_eq_zero
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (first : D.finiteRightModule hmono ⟶ C.finiteRightModule hmono)
    (hfirstRadical : IsRadicalMorphism first)
    (hfirstCoefficient : D.morphismCoefficientAt C hmono hmono
      first.hom.hom
      (hook.moduleMapComponent hmono).1.representative = 0)
    (c : k) :
    IsIrreducibleMorphism
      (hook.finiteModuleMap hmono - c • first) := by
  letI : IsLocalRing (End (D.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (D.finiteRightModule hmono)
      (D.finiteRightModule_indecomposable hmono)
  have hhookIrreducible :=
    hook.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hhookRadical : IsRadicalMorphism (hook.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (D.finiteRightModule_indecomposable hmono).1
      (hook.finiteModuleMap hmono)).2 hhookIrreducible.not_isSplitMono
  have hscaledRadical : IsRadicalMorphism (c • first) := by
    simpa only [Linear.smul_comp, Category.id_comp] using
      isRadicalMorphism_precomp (c • 𝟙 (D.finiteRightModule hmono))
        hfirstRadical
  have hdifferenceRadical : IsRadicalMorphism
      (hook.finiteModuleMap hmono - c • first) := by
    rw [sub_eq_add_neg]
    exact isRadicalMorphism_add hhookRadical
      (isRadicalMorphism_neg hscaledRadical)
  apply hook.isIrreducibleMorphism_of_isRadicalMorphism_of_coefficient_ne_zero
    hmono hcover _ hdifferenceRadical
  have hraw : D.morphismCoefficientAt C hmono hmono
      (hook.moduleMap hmono - c •
        (show D.rightModule hmono ⟶ C.rightModule hmono from first.hom.hom))
      (hook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [D.morphismCoefficientAt_sub, D.morphismCoefficientAt_smul,
      hook.moduleMap_eq_componentMap hmono,
      D.morphismCoefficientAt_boundaryFreeComponentMap,
      D.coefficientComponentIndicator_eq_one C _ _ (Relation.EqvGen.refl _),
      hfirstCoefficient]
    simp
  convert hraw using 1 <;> rfl

/-- The dual coefficient criterion for a right-cohook inclusion. -/
theorem CohookExtension.finiteModuleMap_sub_smul_isIrreducible_of_coefficient_eq_zero
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (first : C.finiteRightModule hmono ⟶ D.finiteRightModule hmono)
    (hfirstRadical : IsRadicalMorphism first)
    (hfirstCoefficient : C.morphismCoefficientAt D hmono hmono
      first.hom.hom
      (cohook.moduleMapComponent hmono).1.representative = 0)
    (c : k) :
    IsIrreducibleMorphism
      (cohook.finiteModuleMap hmono - c • first) := by
  letI : IsLocalRing (End (C.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (C.finiteRightModule hmono)
      (C.finiteRightModule_indecomposable hmono)
  have hcohookIrreducible :=
    cohook.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hcohookRadical : IsRadicalMorphism (cohook.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (C.finiteRightModule_indecomposable hmono).1
      (cohook.finiteModuleMap hmono)).2 hcohookIrreducible.not_isSplitMono
  have hscaledRadical : IsRadicalMorphism (c • first) := by
    simpa only [Linear.smul_comp, Category.id_comp] using
      isRadicalMorphism_precomp (c • 𝟙 (C.finiteRightModule hmono))
        hfirstRadical
  have hdifferenceRadical : IsRadicalMorphism
      (cohook.finiteModuleMap hmono - c • first) := by
    rw [sub_eq_add_neg]
    exact isRadicalMorphism_add hcohookRadical
      (isRadicalMorphism_neg hscaledRadical)
  apply cohook.isIrreducibleMorphism_of_isRadicalMorphism_of_coefficient_ne_zero
    hmono hcover _ hdifferenceRadical
  have hraw : C.morphismCoefficientAt D hmono hmono
      (cohook.moduleMap hmono - c •
        (show C.rightModule hmono ⟶ D.rightModule hmono from first.hom.hom))
      (cohook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [C.morphismCoefficientAt_sub, C.morphismCoefficientAt_smul,
      cohook.moduleMap_eq_componentMap hmono,
      C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_one D _ _ (Relation.EqvGen.refl _),
      hfirstCoefficient]
    simp
  convert hraw using 1 <;> rfl

/-- If two right hooks between the same literal string modules have distinct
graph components, every scalar row operation on their maps remains
irreducible.  This is the coefficient-basis form of the exceptional
two-dimensional irreducible space. -/
theorem HookExtension.finiteModuleMap_sub_smul_isIrreducible_of_component_ne
    {C D : Word R} (first second : HookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hcomponents : ¬ Relation.EqvGen (D.MorphismCoefficientStep C)
      (first.moduleMapComponent hmono).1.representative
      (second.moduleMapComponent hmono).1.representative)
    (c : k) :
    IsIrreducibleMorphism
      (second.finiteModuleMap hmono - c • first.finiteModuleMap hmono) := by
  letI : IsLocalRing (End (D.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (D.finiteRightModule hmono)
      (D.finiteRightModule_indecomposable hmono)
  have hfirstIrreducible :=
    first.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hsecondIrreducible :=
    second.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hfirstRadical : IsRadicalMorphism (first.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (D.finiteRightModule_indecomposable hmono).1
      (first.finiteModuleMap hmono)).2 hfirstIrreducible.not_isSplitMono
  have hsecondRadical : IsRadicalMorphism (second.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (D.finiteRightModule_indecomposable hmono).1
      (second.finiteModuleMap hmono)).2 hsecondIrreducible.not_isSplitMono
  have hscaledRadical :
      IsRadicalMorphism (c • first.finiteModuleMap hmono) := by
    simpa only [Linear.smul_comp, Category.id_comp] using
      isRadicalMorphism_precomp (c • 𝟙 (D.finiteRightModule hmono))
        hfirstRadical
  have hdifferenceRadical : IsRadicalMorphism
      (second.finiteModuleMap hmono - c • first.finiteModuleMap hmono) := by
    rw [sub_eq_add_neg]
    exact isRadicalMorphism_add hsecondRadical
      (isRadicalMorphism_neg hscaledRadical)
  apply second.isIrreducibleMorphism_of_isRadicalMorphism_of_coefficient_ne_zero
    hmono hcover _ hdifferenceRadical
  have hraw : D.morphismCoefficientAt C hmono hmono
      (second.moduleMap hmono - c • first.moduleMap hmono)
      (second.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [D.morphismCoefficientAt_sub, D.morphismCoefficientAt_smul,
      second.moduleMap_eq_componentMap hmono,
      D.morphismCoefficientAt_boundaryFreeComponentMap,
      D.coefficientComponentIndicator_eq_one C _ _ (Relation.EqvGen.refl _),
      first.moduleMap_eq_componentMap hmono,
      D.morphismCoefficientAt_boundaryFreeComponentMap,
      D.coefficientComponentIndicator_eq_zero C _ _ hcomponents]
    simp
  convert hraw using 1 <;> rfl

/-- If two right cohooks between the same literal string modules have
distinct graph components, every scalar row operation on their maps remains
irreducible. -/
theorem CohookExtension.finiteModuleMap_sub_smul_isIrreducible_of_component_ne
    {C D : Word R} (first second : CohookExtension C D)
    (hmono : IsMonomial R)
    (hcover : EveryFiniteModuleIsFiniteStringSum hmono)
    (hcomponents : ¬ Relation.EqvGen (C.MorphismCoefficientStep D)
      (first.moduleMapComponent hmono).1.representative
      (second.moduleMapComponent hmono).1.representative)
    (c : k) :
    IsIrreducibleMorphism
      (second.finiteModuleMap hmono - c • first.finiteModuleMap hmono) := by
  letI : IsLocalRing (End (C.finiteRightModule hmono)) :=
    CoveringHom.finiteDimensionalModule_end_isLocalRing k
      (C.finiteRightModule hmono)
      (C.finiteRightModule_indecomposable hmono)
  have hfirstIrreducible :=
    first.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hsecondIrreducible :=
    second.finiteModuleMap_isIrreducible_of_finiteStringSum hmono hcover
  have hfirstRadical : IsRadicalMorphism (first.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (C.finiteRightModule_indecomposable hmono).1
      (first.finiteModuleMap hmono)).2 hfirstIrreducible.not_isSplitMono
  have hsecondRadical : IsRadicalMorphism (second.finiteModuleMap hmono) :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (C.finiteRightModule_indecomposable hmono).1
      (second.finiteModuleMap hmono)).2 hsecondIrreducible.not_isSplitMono
  have hscaledRadical :
      IsRadicalMorphism (c • first.finiteModuleMap hmono) := by
    simpa only [Linear.smul_comp, Category.id_comp] using
      isRadicalMorphism_precomp (c • 𝟙 (C.finiteRightModule hmono))
        hfirstRadical
  have hdifferenceRadical : IsRadicalMorphism
      (second.finiteModuleMap hmono - c • first.finiteModuleMap hmono) := by
    rw [sub_eq_add_neg]
    exact isRadicalMorphism_add hsecondRadical
      (isRadicalMorphism_neg hscaledRadical)
  apply second.isIrreducibleMorphism_of_isRadicalMorphism_of_coefficient_ne_zero
    hmono hcover _ hdifferenceRadical
  have hraw : C.morphismCoefficientAt D hmono hmono
      (second.moduleMap hmono - c • first.moduleMap hmono)
      (second.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [C.morphismCoefficientAt_sub, C.morphismCoefficientAt_smul,
      second.moduleMap_eq_componentMap hmono,
      C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_one D _ _ (Relation.EqvGen.refl _),
      first.moduleMap_eq_componentMap hmono,
      C.morphismCoefficientAt_boundaryFreeComponentMap,
      C.coefficientComponentIndicator_eq_zero D _ _ hcomponents]
    simp
  convert hraw using 1 <;> rfl

end MagnitudeConjecture.BoundQuiver.StringWord.Word
