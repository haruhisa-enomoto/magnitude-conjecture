import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleEnoughInjectives
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleHomFinite
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteGeneratorRadicalNilpotence
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix
import MagnitudeConjecture.CategoryTheory.RadicalMinimality
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite

/-!
# Finite Auslander--Reiten component exhaustion

A finite family of indecomposable finite modules is exhaustive as soon as its
members have left almost-split maps whose middle summands stay in the family
and the family contains every indecomposable injective and projective.  This is the
nilpotence argument behind Auslander's finite-component theorem used in
Gabriel's density proof.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- A finite family of indecomposable finite modules, equipped at every
member with a left almost-split map whose target is a finite biproduct of
members of the same family. -/
structure FiniteLeftAlmostSplitFamily where
  n : ℕ
  obj : Fin n →
    FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k
  indecomposable : ∀ i, Indecomposable (obj i)
  middleMultiplicity : Fin n → ℕ
  middleLabel : ∀ i, Fin (middleMultiplicity i) → Fin n
  map : ∀ i, obj i ⟶
    ⨁ fun t : Fin (middleMultiplicity i) ↦ obj (middleLabel i t)
  leftAlmostSplit : ∀ i, IsLeftAlmostSplit (map i)

namespace FiniteLeftAlmostSplitFamily

variable (S : FiniteLeftAlmostSplitFamily (k := k) (C := C))

/-- An object is represented by the finite family. -/
def Covers
    (Y : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Prop :=
  ∃ i, Nonempty (S.obj i ≅ Y)

/-- The finite biproduct of the family. -/
abbrev generator :
    FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
  ⨁ S.obj

private theorem map_isRadicalMorphism (i : Fin S.n) :
    IsRadicalMorphism (S.map i) := by
  letI : IsLocalRing (End (S.obj i)) :=
    finiteDimensionalModule_end_isLocalRing k (S.obj i)
      (S.indecomposable i)
  exact
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      (S.indecomposable i).1 (S.map i)).2
        (S.leftAlmostSplit i).not_isSplitMono

private theorem component_isRadicalMorphism
    (i : Fin S.n) (t : Fin (S.middleMultiplicity i)) :
    IsRadicalMorphism
      (S.map i ≫ biproduct.π
        (fun t : Fin (S.middleMultiplicity i) ↦
          S.obj (S.middleLabel i t)) t) :=
  isRadicalMorphism_postcomp _ (S.map_isRadicalMorphism i)

/-- If an indecomposable is not represented by the family, every morphism
from a family member to it vanishes.  Iterated left almost-split
factorization puts every such morphism in every power of the Jacobson
radical of the finite family generator; Artinian nilpotence then kills it. -/
private theorem hom_eq_zero_of_not_covers
    [EnoughInjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    (hinjective :
      ∀ (I : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k),
        Indecomposable I → Injective I → S.Covers I)
    {Y : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (hY : Indecomposable Y) (hYout : ¬ S.Covers Y) :
    ∀ (i : Fin S.n) (f : S.obj i ⟶ Y), f = 0 := by
  classical
  let J := Ring.jacobson (End (⨁ S.obj))
  letI : IsArtinianRing (End (⨁ S.obj)) := by
    letI : Module.Finite k (End (⨁ S.obj)) := inferInstance
    exact IsArtinianRing.of_finite k (End (⨁ S.obj))
  have hpower :
      ∀ (q : ℕ) (i : Fin S.n) (f : S.obj i ⟶ Y)
        (b : Y ⟶ ⨁ S.obj),
        End.of (biproduct.π S.obj i ≫ f ≫ b) ∈ J ^ q := by
    intro q
    induction q with
    | zero =>
        intro i f b
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Set.mem_univ _
    | succ q ih =>
        intro i f b
        have hfNotSplit : ¬ IsSplitMono f := by
          intro hf
          letI : IsSplitMono f := hf
          letI : IsIso f :=
            MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
              hY f (S.indecomposable i).1
          exact hYout ⟨i, ⟨asIso f⟩⟩
        obtain ⟨h, hh⟩ := (S.leftAlmostSplit i).factors f hfNotSplit
        let F : Fin (S.middleMultiplicity i) →
            FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
          fun t ↦ S.obj (S.middleLabel i t)
        let left (t : Fin (S.middleMultiplicity i)) : End (⨁ S.obj) :=
          biproduct.π S.obj i ≫
            (S.map i ≫ biproduct.π F t) ≫
              biproduct.ι S.obj (S.middleLabel i t)
        let right (t : Fin (S.middleMultiplicity i)) : End (⨁ S.obj) :=
          biproduct.π S.obj (S.middleLabel i t) ≫
            (biproduct.ι F t ≫ h) ≫ b
        have hleft (t : Fin (S.middleMultiplicity i)) :
            left t ∈ J := by
          simpa only [left, Category.assoc] using
            MagnitudeConjecture.CategoryTheory.sandwich_mem_jacobson
              (S.component_isRadicalMorphism i t)
              (biproduct.π S.obj i)
              (biproduct.ι S.obj (S.middleLabel i t))
        have hright (t : Fin (S.middleMultiplicity i)) :
            right t ∈ J ^ q := by
          simpa only [right, Category.assoc] using
            ih (S.middleLabel i t) (biproduct.ι F t ≫ h) b
        have hterm (t : Fin (S.middleMultiplicity i)) :
            right t * left t = End.of
              (biproduct.π S.obj i ≫ S.map i ≫ biproduct.π F t ≫
                biproduct.ι F t ≫ h ≫ b) := by
          change
            (biproduct.π S.obj i ≫
                (S.map i ≫ biproduct.π F t) ≫
                  biproduct.ι S.obj (S.middleLabel i t)) ≫
              (biproduct.π S.obj (S.middleLabel i t) ≫
                (biproduct.ι F t ≫ h) ≫ b) =
              biproduct.π S.obj i ≫ S.map i ≫ biproduct.π F t ≫
                biproduct.ι F t ≫ h ≫ b
          simp only [Category.assoc, bicone_ι_π_self_assoc]
        have hexpand :
            End.of (biproduct.π S.obj i ≫ S.map i ≫ h ≫ b) =
              ∑ t : Fin (S.middleMultiplicity i), End.of
                (biproduct.π S.obj i ≫ S.map i ≫ biproduct.π F t ≫
                  biproduct.ι F t ≫ h ≫ b) := by
          change
            biproduct.π S.obj i ≫ S.map i ≫ h ≫ b =
              ∑ t : Fin (S.middleMultiplicity i),
                biproduct.π S.obj i ≫ S.map i ≫ biproduct.π F t ≫
                  biproduct.ι F t ≫ h ≫ b
          calc
            _ = biproduct.π S.obj i ≫ S.map i ≫ 𝟙 (⨁ F) ≫ h ≫ b := by
                  have hid : S.map i ≫ 𝟙 (⨁ F) = S.map i :=
                    Category.comp_id _
                  have hconjugated := congrArg
                    (fun z ↦ biproduct.π S.obj i ≫ z ≫ h ≫ b) hid
                  simpa only [Category.assoc] using hconjugated.symm
            _ = biproduct.π S.obj i ≫ S.map i ≫
                (∑ t : Fin (S.middleMultiplicity i),
                  biproduct.π F t ≫ biproduct.ι F t) ≫ h ≫ b := by
                  rw [biproduct.total]
            _ = _ := by
                  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
                    Category.assoc]
        have hsum :
            End.of (biproduct.π S.obj i ≫ f ≫ b) =
              ∑ t : Fin (S.middleMultiplicity i), right t * left t := by
          calc
            End.of (biproduct.π S.obj i ≫ f ≫ b) =
                End.of (biproduct.π S.obj i ≫ S.map i ≫ h ≫ b) := by
                  change biproduct.π S.obj i ≫ f ≫ b =
                    biproduct.π S.obj i ≫ S.map i ≫ h ≫ b
                  have hcomp := congrArg
                    (fun z : S.obj i ⟶ Y ↦
                      biproduct.π S.obj i ≫ z ≫ b) hh
                  simpa only [Category.assoc] using hcomp.symm
            _ = ∑ t : Fin (S.middleMultiplicity i), End.of
                (biproduct.π S.obj i ≫ S.map i ≫ biproduct.π F t ≫
                  biproduct.ι F t ≫ h ≫ b) := hexpand
            _ = ∑ t : Fin (S.middleMultiplicity i), right t * left t := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  exact (hterm t).symm
        rw [hsum]
        apply Ideal.sum_mem
        intro t ht
        have hp := Ideal.mul_mem_mul (hright t) (hleft t)
        rw [Submodule.pow_succ]
        exact hp
  obtain ⟨q, hq⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End (⨁ S.obj))
  intro i f
  let P := (EnoughInjectives.presentation Y).some
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition P.J
  apply (cancel_mono P.f).1
  apply (cancel_mono d.isoBiproduct.hom).1
  apply biproduct.hom_ext
  intro t
  let inc : d.summand t ⟶ P.J :=
    biproduct.ι d.summand t ≫ d.isoBiproduct.inv
  let ret : P.J ⟶ d.summand t :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand t
  letI : Injective (d.summand t) :=
    Retract.injective
      { i := inc
        r := ret
        retract := by simp [inc, ret, Category.assoc] }
  obtain ⟨l, ⟨e⟩⟩ :=
    hinjective (d.summand t) (d.indecomposable t) inferInstance
  let b : Y ⟶ ⨁ S.obj :=
    P.f ≫ d.isoBiproduct.hom ≫ biproduct.π d.summand t ≫
      e.inv ≫ biproduct.ι S.obj l
  have hmem := hpower q i f b
  have hzero : End.of
      (biproduct.π S.obj i ≫ f ≫ b) = 0 := by
    have hq' : J ^ q = 0 := by
      simpa only [J, Ideal.jacobson_bot] using hq
    rw [hq'] at hmem
    exact hmem
  have hcomponent :
      f ≫ P.f ≫ d.isoBiproduct.hom ≫
          biproduct.π d.summand t = 0 := by
    apply (cancel_epi (biproduct.π S.obj i)).1
    apply (cancel_mono e.inv).1
    apply (cancel_mono (biproduct.ι S.obj l)).1
    have hzeroHom := congrArg End.asHom hzero
    change
      biproduct.π S.obj i ≫ f ≫ P.f ≫ d.isoBiproduct.hom ≫
        biproduct.π d.summand t ≫ e.inv ≫ biproduct.ι S.obj l = 0
      at hzeroHom
    simpa only [b, Category.assoc, zero_comp, comp_zero] using hzeroHom
  simpa only [Category.assoc, zero_comp] using hcomponent

/-- Auslander's finite-component exhaustion: if every indecomposable
injective and projective is represented by a finite family closed under left
almost-split middle terms, then every indecomposable is represented by that
family. -/
theorem covers_all_indecomposables
    [EnoughInjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]
    (hinjective :
      ∀ (I : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k),
        Indecomposable I → Injective I → S.Covers I)
    (hprojective :
      ∀ (P : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k),
        Indecomposable P → Projective P → S.Covers P) :
    ∀ (Y : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k),
      Indecomposable Y → S.Covers Y := by
  intro Y hY
  by_contra hYout
  let P := (EnoughProjectives.presentation Y).some
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition P.p
  have hcomponent (t : Fin d.n) :
      biproduct.ι d.summand t ≫ d.isoBiproduct.inv ≫ P.f = 0 := by
    let inc : d.summand t ⟶ P.p :=
      biproduct.ι d.summand t ≫ d.isoBiproduct.inv
    let ret : P.p ⟶ d.summand t :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand t
    letI : Projective (d.summand t) :=
      Retract.projective
        { i := inc
          r := ret
          retract := by simp [inc, ret, Category.assoc] }
    obtain ⟨i, ⟨e⟩⟩ :=
      hprojective (d.summand t) (d.indecomposable t) inferInstance
    have hz := S.hom_eq_zero_of_not_covers hinjective hY hYout i
      (e.hom ≫ biproduct.ι d.summand t ≫ d.isoBiproduct.inv ≫ P.f)
    apply (cancel_epi e.hom).1
    simpa only [Category.assoc, zero_comp, comp_zero] using hz
  have hzero : d.isoBiproduct.inv ≫ P.f = 0 := by
    apply biproduct.hom_ext'
    intro t
    simpa only [Category.assoc, zero_comp, comp_zero] using hcomponent t
  have hPf : P.f = 0 := by
    apply (cancel_epi d.isoBiproduct.inv).1
    simpa only [Category.assoc, zero_comp, comp_zero] using hzero
  exact hY.1 (IsZero.of_epi_eq_zero P.f hPf)

end FiniteLeftAlmostSplitFamily

end MagnitudeConjecture.CoveringHom
