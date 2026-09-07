import MagnitudeConjecture.Algebra.RightModuleCovariantRepresentable

/-!
# Projective-stable covariant representables on the finite module skeleton

This is the functor `\underline{Hom}(X, -)` used in
Auslander--Reiten, Proposition 1.3(a)(iii).
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The restriction of projective-stable `Hom(X, -)` to the finite skeleton
of indecomposable right modules. -/
def projectiveStableCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.IndecCategory ⥤ ModuleCat.{u} k where
  obj Y := ModuleCat.of k
    (ProjectiveStable.Hom (k := k) X.obj (S.inclusion.obj Y))
  map f := ModuleCat.ofHom <|
    ProjectiveStable.postcomp (k := k) X.obj (S.inclusion.map f)
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change ProjectiveStable.mk (k := k)
        (h ≫ (S.inclusion.map f ≫ S.inclusion.map g)) =
      ProjectiveStable.mk (k := k)
        ((h ≫ S.inclusion.map f) ≫ S.inclusion.map g)
    rw [Category.assoc]

instance projectiveStableCovariantRepresentable_additive
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.projectiveStableCovariantRepresentable X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change ProjectiveStable.mk (k := k)
        (h ≫ (S.inclusion.map f + S.inclusion.map g)) =
      ProjectiveStable.mk (k := k) (h ≫ S.inclusion.map f) +
        ProjectiveStable.mk (k := k) (h ≫ S.inclusion.map g)
    simp

instance projectiveStableCovariantRepresentable_linear
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.projectiveStableCovariantRepresentable X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change ProjectiveStable.mk (k := k)
        (h ≫ (r • S.inclusion.map f)) =
      r • ProjectiveStable.mk (k := k) (h ≫ S.inclusion.map f)
    simp

/-- The restricted projective-stable covariant representable as a linear
module. -/
def projectiveStableCovariantRepresentableLinearModule
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.LinearModuleCategory (C := S.IndecCategory) k :=
  ⟨S.projectiveStableCovariantRepresentable X, inferInstance, inferInstance⟩

/-- On the finite skeleton, the projective-stable covariant representable is
pointwise finite-dimensional with finite support. -/
theorem projectiveStableCovariantRepresentable_isFiniteDimensional
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      (S.projectiveStableCovariantRepresentableLinearModule X) := by
  constructor
  · intro Y
    letI : Module.Finite k X.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A X
    letI : Module.Finite k (S.inclusion.obj Y) :=
      S.indecCategory_obj_finite Y
    letI : Module.Finite k (X.obj ⟶ S.inclusion.obj Y) :=
      moduleCat_hom_finite (k := k) (A := A) X.obj (S.inclusion.obj Y)
    change Module.Finite k
      (ProjectiveStable.Hom (k := k) X.obj (S.inclusion.obj Y))
    exact Module.Finite.quotient k
      (ProjectiveStable.factorSubmodule (k := k)
        X.obj (S.inclusion.obj Y))
  · exact Set.toFinite _

/-- The projective-stable covariant representable as an object of the finite
functor category. -/
def finiteProjectiveStableCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  ⟨S.projectiveStableCovariantRepresentableLinearModule X,
    S.projectiveStableCovariantRepresentable_isFiniteDimensional X⟩

/-- The objectwise quotient from ordinary Hom to projective-stable Hom. -/
def projectiveStableCovariantQuotientLinearModule
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.finiteRestrictedCovariantRepresentable X).obj ⟶
      (S.finiteProjectiveStableCovariantRepresentable X).obj :=
  ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom (ProjectiveStable.mk (k := k))
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro h
        rfl }

/-- The quotient from ordinary Hom to projective-stable Hom in the finite
functor category. -/
def finiteProjectiveStableCovariantQuotient
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedCovariantRepresentable X ⟶
      S.finiteProjectiveStableCovariantRepresentable X :=
  ObjectProperty.homMk (S.projectiveStableCovariantQuotientLinearModule X)

instance finiteProjectiveStableCovariantQuotient_epi
    (X : RightModule.FinitelyGeneratedCategory A) :
    Epi (S.finiteProjectiveStableCovariantQuotient X) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule (C := S.IndecCategory) k).ι
  have happ (Y : S.IndecCategory) : Epi
      ((I.map (J.map
        (S.finiteProjectiveStableCovariantQuotient X))).app Y) := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (ProjectiveStable.mk (k := k) :
      (X.obj ⟶ S.inclusion.obj Y) →ₗ[k]
        ProjectiveStable.Hom (k := k) X.obj (S.inclusion.obj Y))
    exact Submodule.Quotient.mk_surjective _
  have hnat : Epi (I.map (J.map
      (S.finiteProjectiveStableCovariantQuotient X))) :=
    NatTrans.epi_of_epi_app _
  have hlinear : Epi (J.map
      (S.finiteProjectiveStableCovariantQuotient X)) :=
    I.epi_of_epi_map hnat
  exact J.epi_of_epi_map hlinear

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
