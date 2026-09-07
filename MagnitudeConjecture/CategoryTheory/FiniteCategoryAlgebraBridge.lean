import MagnitudeConjecture.Algebra.RightModuleDirected
import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDirected
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite

/-!
# The finite linear category--algebra bridge

For a finite linear category, pointwise local representation-finiteness is
global.  Combining the resulting finite indecomposable skeleton with the
projective-generator equivalence identifies the finite category algebra as
representation-finite and transfers the manuscript's directedness condition
to any duplicate-free algebra-module skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Fintype C]

/-- Transport a duplicate-free finite skeleton of category modules forward
along an additive equivalence to finitely generated right modules. -/
def pushforwardRightModuleIndecomposableSkeleton
    {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ]
    (E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ≌
      RightModule.FinitelyGeneratedCategory A)
    [E.functor.Additive]
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    RightModule.FiniteIndecomposableSkeleton k A := by
  letI : E.inverse.Additive := inferInstance
  refine
    { n := S.n
      obj := fun i ↦ (E.functor.obj (S.obj i)).obj
      obj_finite := fun i ↦
        RightModule.finite_over_field_of_finitelyGenerated k A
          (E.functor.obj (S.obj i))
      obj_indecomposable := ?_
      eq_of_iso := ?_
      complete := ?_ }
  · intro i
    apply (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := A) (E.functor.obj (S.obj i))).1
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor (S.obj i)).2 (S.indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    apply S.skeletal
    exact ⟨E.functor.preimageIso (ObjectProperty.isoMk _ hij)⟩
  · intro M hM
    let Mfg : RightModule.FinitelyGeneratedCategory A :=
      @RightModule.finitelyGeneratedOfFiniteDimensional k _ A _ _ M hM.1
    have hMfg : Indecomposable Mfg :=
      (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := A) Mfg).2 hM.2
    have hInv : Indecomposable (E.inverse.obj Mfg) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse Mfg).2 hMfg
    obtain ⟨i, ⟨hi⟩⟩ := S.complete (E.inverse.obj Mfg) hInv
    let efg : Mfg ≅ E.functor.obj (S.obj i) :=
      (E.counitIso.app Mfg).symm ≪≫ E.functor.mapIso hi
    exact ⟨i, ⟨(forget₂ (RightModule.FinitelyGeneratedCategory A)
      (RightModule.Category A)).mapIso efg⟩⟩

/-- The pushed-forward skeleton object, rebundled as finitely generated, is
canonically the image of the original category-module skeleton object. -/
def pushforwardRightModuleIndecomposableSkeletonObjIso
    {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ]
    (E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ≌
      RightModule.FinitelyGeneratedCategory A)
    [E.functor.Additive]
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (i : Fin S.n) :
    (pushforwardRightModuleIndecomposableSkeleton E S).fgObj i ≅
      E.functor.obj (S.obj i) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- On a finite base category, the finitely many local fibers assemble into
a complete finite indecomposable module skeleton. -/
def finiteCategoryModuleIndecomposableSkeleton
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C) := by
  classical
  let H (X : C) := Classical.choice (hrep X)
  let I := Σ X : C, Fin (H X).n
  letI : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  apply FiniteDimensionalModuleIndecomposableSkeleton.ofFamily
    (fun i ↦ (H (e i).1).obj (e i).2)
    (fun i ↦ (H (e i).1).indecomposable (e i).2)
  intro M hM
  have hnontrivial : ∃ X : C, Nontrivial (M.obj.obj.obj X) := by
    by_contra hall
    push Not at hall
    have hfunctor : IsZero M.obj.obj := by
      apply Functor.isZero
      intro X
      exact ModuleCat.isZero_iff_subsingleton.mpr (hall X)
    have hlinear : IsZero M.obj :=
      IsZero.of_full_of_faithful_of_isZero
        (IsLinearModule (C := C) k).ι M.obj hfunctor
    exact hM.1 (IsZero.of_full_of_faithful_of_isZero
      (IsFiniteDimensionalModule (C := C) k).ι M hlinear)
  obtain ⟨X, hX⟩ := hnontrivial
  obtain ⟨j, hj⟩ := (H X).covers hM hX
  let i : Fin (Fintype.card I) := e.symm ⟨X, j⟩
  refine ⟨i, ?_⟩
  rw [show e i = ⟨X, j⟩ from e.apply_symm_apply ⟨X, j⟩]
  exact hj.map Iso.symm

namespace finiteCategoryProjectiveGenerator

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

/-- A finite locally representation-finite linear category has a
representation-finite category algebra. -/
theorem algebra_isRepresentationFinite
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    RightModule.IsRepresentationFinite k (algebra hP) := by
  let A := algebra hP
  letI : FiniteDimensional k A := algebra_finiteDimensional hP
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  let E := moduleEquivalence hP
  letI : E.functor.Additive :=
    { map_add := by
        intro X Y f g
        change (representedFGFunctor hP).map (f + g) =
          (representedFGFunctor hP).map f +
            (representedFGFunctor hP).map g
        exact (representedFGFunctor hP).map_add }
  letI : E.inverse.Additive := inferInstance
  let S := finiteCategoryModuleIndecomposableSkeleton hrep
  apply (RightModule.isRepresentationFinite_iff_finitelyGenerated k A).2
  refine ⟨S.n, fun i ↦ E.functor.obj (S.obj i), ?_, ?_⟩
  · intro i
    apply (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := A) (E.functor.obj (S.obj i))).1
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor (S.obj i)).2 (S.indecomposable i)
  · intro M hM
    have hM' : Indecomposable M :=
      (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := A) M).2 hM
    have hInv : Indecomposable (E.inverse.obj M) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse M).2 hM'
    obtain ⟨i, ⟨e⟩⟩ := S.complete (E.inverse.obj M) hInv
    exact ⟨i, ⟨(E.counitIso.app M).symm.trans (E.functor.mapIso e)⟩⟩

/-- Directedness of the finite module category transfers through the
category-algebra equivalence to every chosen algebra-module skeleton. -/
theorem algebraSkeleton_hasAcyclicNonzeroNonisomorphisms
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP)) :
    S.HasAcyclicNonzeroNonisomorphisms := by
  letI : FiniteDimensional k (algebra hP) := algebra_finiteDimensional hP
  letI : IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ
  let E := moduleEquivalence hP
  letI : E.functor.Additive :=
    { map_add := by
        intro X Y f g
        change (representedFGFunctor hP).map (f + g) =
          (representedFGFunctor hP).map f +
            (representedFGFunctor hP).map g
        exact (representedFGFunctor hP).map_add }
  letI : E.inverse.Additive := inferInstance
  let liftLabel (i : Fin S.n) := E.inverse.obj (S.fgObj i)
  have hLiftIndecomposable (i : Fin S.n) :
      Indecomposable (liftLabel i) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse (S.fgObj i)).2 (S.fgObj_indecomposable i)
  have mapEdge {i j : Fin S.n} (h : S.NonzeroNonisomorphism i j) :
      FiniteModuleNonzeroNonisomorphism (k := k) (C := C)
        (liftLabel i) (liftLabel j) := by
    rcases h with ⟨f, hf, hnotIso⟩
    refine ⟨hLiftIndecomposable i, hLiftIndecomposable j,
      E.inverse.map f, ?_, ?_⟩
    · intro hzero
      apply hf
      apply E.inverse.map_injective
      simpa using hzero
    · intro hmapIso
      apply hnotIso
      letI : IsIso (E.inverse.map f) := hmapIso
      exact isIso_of_reflects_iso f E.inverse
  have mapPath {i j : Fin S.n}
      (h : Relation.TransGen S.NonzeroNonisomorphism i j) :
      Relation.TransGen
        (FiniteModuleNonzeroNonisomorphism (k := k) (C := C))
        (liftLabel i) (liftLabel j) := by
    induction h with
    | single hij => exact Relation.TransGen.single (mapEdge hij)
    | tail _ hjl ih => exact ih.tail (mapEdge hjl)
  intro i hcycle
  exact H (liftLabel i) (mapPath hcycle)

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
