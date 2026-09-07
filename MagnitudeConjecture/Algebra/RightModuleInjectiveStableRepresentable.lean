import MagnitudeConjecture.Algebra.RightModuleStableRepresentable
import MagnitudeConjecture.CategoryTheory.InjectiveStableHom

/-!
# Injective-stable covariant representables on the finite module skeleton

This file packages the costable functor `Hom(X, -)` modulo maps factoring
through injectives.  It is the functor-category target in the
Auslander–Reiten Proposition 1.3 passage from a uniserial stable
contravariant representable to a uniserial syzygy.
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

/-- The restriction of injective-stable `Hom(X, -)` to the finite skeleton
of indecomposable right modules. -/
def injectiveStableCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.IndecCategory ⥤ ModuleCat.{u} k where
  obj Y := ModuleCat.of k
    (InjectiveStable.Hom (k := k) X.obj (S.inclusion.obj Y))
  map f := ModuleCat.ofHom <|
    InjectiveStable.postcomp (k := k) X.obj (S.inclusion.map f)
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
    change InjectiveStable.mk (k := k)
        (h ≫ (S.inclusion.map f ≫ S.inclusion.map g)) =
      InjectiveStable.mk (k := k)
        ((h ≫ S.inclusion.map f) ≫ S.inclusion.map g)
    rw [Category.assoc]

instance injectiveStableCovariantRepresentable_additive
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.injectiveStableCovariantRepresentable X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change InjectiveStable.mk (k := k)
        (h ≫ (S.inclusion.map f + S.inclusion.map g)) =
      InjectiveStable.mk (k := k) (h ≫ S.inclusion.map f) +
        InjectiveStable.mk (k := k) (h ≫ S.inclusion.map g)
    simp

instance injectiveStableCovariantRepresentable_linear
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.injectiveStableCovariantRepresentable X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change InjectiveStable.mk (k := k)
        (h ≫ (r • S.inclusion.map f)) =
      r • InjectiveStable.mk (k := k) (h ≫ S.inclusion.map f)
    simp

/-- The restricted injective-stable covariant representable as a linear
module. -/
def injectiveStableCovariantRepresentableLinearModule
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.LinearModuleCategory (C := S.IndecCategory) k :=
  ⟨S.injectiveStableCovariantRepresentable X, inferInstance, inferInstance⟩

/-- On the finite indecomposable skeleton, the injective-stable covariant
representable is pointwise finite-dimensional with finite support. -/
theorem injectiveStableCovariantRepresentable_isFiniteDimensional
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      (S.injectiveStableCovariantRepresentableLinearModule X) := by
  constructor
  · intro Y
    letI : Module.Finite k X.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A X
    letI : Module.Finite k (S.inclusion.obj Y) :=
      S.indecCategory_obj_finite Y
    letI : Module.Finite k (X.obj ⟶ S.inclusion.obj Y) :=
      moduleCat_hom_finite (k := k) (A := A) X.obj (S.inclusion.obj Y)
    change Module.Finite k
      (InjectiveStable.Hom (k := k) X.obj (S.inclusion.obj Y))
    exact Module.Finite.quotient k
      (InjectiveStable.factorSubmodule (k := k)
        X.obj (S.inclusion.obj Y))
  · exact Set.toFinite _

/-- The restricted injective-stable covariant representable as an object of
the finite functor category. -/
def finiteInjectiveStableCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  ⟨S.injectiveStableCovariantRepresentableLinearModule X,
    S.injectiveStableCovariantRepresentable_isFiniteDimensional X⟩

/-- The ordinary covariant representable `Hom(X, -)` restricted to the
finite indecomposable skeleton. -/
def restrictedCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.IndecCategory ⥤ ModuleCat.{u} k where
  obj Y := ModuleCat.of k (X.obj ⟶ S.inclusion.obj Y)
  map f := ModuleCat.ofHom <| CategoryTheory.Linear.rightComp k X.obj
    (S.inclusion.map f)
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ S.inclusion.map (f ≫ g) =
      (h ≫ S.inclusion.map f) ≫ S.inclusion.map g
    rw [Functor.map_comp]
    rw [Category.assoc]

instance restrictedCovariantRepresentable_additive
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.restrictedCovariantRepresentable X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ (S.inclusion.map f + S.inclusion.map g) =
      h ≫ S.inclusion.map f + h ≫ S.inclusion.map g
    simp

instance restrictedCovariantRepresentable_linear
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.restrictedCovariantRepresentable X).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ (r • S.inclusion.map f) = r • (h ≫ S.inclusion.map f)
    simp

/-- The ordinary restricted covariant representable as a linear module. -/
def restrictedCovariantRepresentableLinearModule
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.LinearModuleCategory (C := S.IndecCategory) k :=
  ⟨S.restrictedCovariantRepresentable X, inferInstance, inferInstance⟩

/-- The ordinary restricted covariant representable is finite-dimensional on
the finite indecomposable skeleton. -/
theorem restrictedCovariantRepresentable_isFiniteDimensional
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      (S.restrictedCovariantRepresentableLinearModule X) := by
  constructor
  · intro Y
    letI : Module.Finite k X.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A X
    letI : Module.Finite k (S.inclusion.obj Y) :=
      S.indecCategory_obj_finite Y
    exact moduleCat_hom_finite (k := k) (A := A) X.obj
      (S.inclusion.obj Y)
  · exact Set.toFinite _

/-- The ordinary restricted covariant representable in the finite functor
category. -/
def finiteRestrictedCovariantRepresentable
    (X : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k :=
  ⟨S.restrictedCovariantRepresentableLinearModule X,
    S.restrictedCovariantRepresentable_isFiniteDimensional X⟩

/-- The objectwise quotient from ordinary Hom to injective-stable Hom. -/
def injectiveStableCovariantQuotientLinearModule
    (X : RightModule.FinitelyGeneratedCategory A) :
    (S.finiteRestrictedCovariantRepresentable X).obj ⟶
      (S.finiteInjectiveStableCovariantRepresentable X).obj :=
  ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom (InjectiveStable.mk (k := k))
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro h
        rfl }

/-- The quotient from ordinary Hom to injective-stable Hom in the finite
functor category. -/
def finiteInjectiveStableCovariantQuotient
    (X : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedCovariantRepresentable X ⟶
      S.finiteInjectiveStableCovariantRepresentable X :=
  ObjectProperty.homMk (S.injectiveStableCovariantQuotientLinearModule X)

instance finiteInjectiveStableCovariantQuotient_epi
    (X : RightModule.FinitelyGeneratedCategory A) :
    Epi (S.finiteInjectiveStableCovariantQuotient X) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).ι
  let I := (CoveringHom.IsLinearModule (C := S.IndecCategory) k).ι
  have happ (Y : S.IndecCategory) : Epi
      ((I.map (J.map
        (S.finiteInjectiveStableCovariantQuotient X))).app Y) := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (InjectiveStable.mk (k := k) :
      (X.obj ⟶ S.inclusion.obj Y) →ₗ[k]
        InjectiveStable.Hom (k := k) X.obj (S.inclusion.obj Y))
    exact Submodule.Quotient.mk_surjective _
  have hnat : Epi (I.map (J.map
      (S.finiteInjectiveStableCovariantQuotient X))) :=
    NatTrans.epi_of_epi_app _
  have hlinear : Epi (J.map
      (S.finiteInjectiveStableCovariantQuotient X)) :=
    I.epi_of_epi_map hnat
  exact J.epi_of_epi_map hlinear

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
