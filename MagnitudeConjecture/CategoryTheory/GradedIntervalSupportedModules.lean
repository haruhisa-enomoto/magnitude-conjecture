import MagnitudeConjecture.CategoryTheory.GradedIntervalOppositeDeletion
import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator

/-!
# Interval representations and supported graded representations

Contravariant finite-dimensional representations of a finite degree interval
are equivalent to contravariant representations of the full degree category
vanishing outside that interval. The latter are the categorical form of
supported graded modules. Their identification with modules over the original
graded algebra is a separate step.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)
variable (h : ℕ)
variable (hbound : ∀ X Y d, d < 0 ∨ (h : ℤ) < d → G.component X Y d = ⊥)

/-- The interval/deletion comparison is literally bijective on objects,
not merely essentially surjective. Thus finite literal support is preserved. -/
theorem intervalOpDeletion_obj_bijective (m : ℕ) :
    Function.Bijective (G.intervalOpDeletionEquivalence h hbound m).functor.obj := by
  constructor
  · intro X Y hXY
    have heq := congrArg (fun Z ↦ Z.obj.as.unop) hXY
    change G.intervalObject m X.unop = G.intervalObject m Y.unop at heq
    apply Opposite.unop_injective
    apply Prod.ext
    · exact congrArg DegreeObject.obj heq
    · apply Fin.ext
      have hd := congrArg DegreeObject.degree heq
      change (X.unop.2.val : ℤ) = Y.unop.2.val at hd
      exact_mod_cast hd
  · intro Y
    have hy := Y.property
    change ¬ (Y.obj.as.unop.degree < 0 ∨ (m : ℤ) < Y.obj.as.unop.degree) at hy
    let X : G.Interval m := (Y.obj.as.unop.obj, ⟨Y.obj.as.unop.degree.toNat, by omega⟩)
    refine ⟨op X, ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    apply Opposite.unop_injective
    change (⟨Y.obj.as.unop.obj, (Y.obj.as.unop.degree.toNat : ℤ)⟩ : DegreeObject G) =
      Y.obj.as.unop
    have hd : (Y.obj.as.unop.degree.toNat : ℤ) = Y.obj.as.unop.degree := by omega
    rw [hd]

/-- Finite-dimensional contravariant interval representations are precisely
the ambient contravariant degree representations supported on the interval. -/
def intervalSupportedModuleEquivalence (m : ℕ) :
    CoveringHom.FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := (G.Interval m)ᵒᵖ) k ≌
    ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m) := by
  let e := G.intervalOpDeletionEquivalence h hbound m
  let eo := Equiv.ofBijective e.functor.obj
    (G.intervalOpDeletion_obj_bijective h hbound m)
  exact (CoveringHom.finiteDimensionalModuleCongrEquivalence
    (k := k) e eo (fun _ ↦ rfl)).symm.trans
      (ObjectDeletion.finiteDimensionalModuleExtensionByZeroVanishingEquivalence
        (k := k) (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m))

variable [Fintype C]

local instance intervalOppositeFintype (m : ℕ) : Fintype (G.Interval m)ᵒᵖ :=
  Fintype.ofEquiv (G.Interval m) Opposite.equivToOpposite

/-- All contravariant interval representables have finite dimension and
finite object support. -/
theorem intervalFiniteRepresentables
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)) (m : ℕ)
    (X : (G.Interval m)ᵒᵖ) :
    CoveringHom.IsFiniteDimensionalModule (C := (G.Interval m)ᵒᵖ) k
      (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k (Y.unop.1 ⟶ X.unop.1) := hfinite _ _
    exact Module.Finite.equiv (CoveringHom.oppositeHomLinearEquiv (k := k) X Y).symm
  · exact Set.toFinite _

/-- The endomorphism algebra of the sum of the interval representables.
Its finitely generated right modules have the required contravariant variance. -/
abbrev intervalAlgebra
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)) (m : ℕ) :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    (G.intervalFiniteRepresentables hfinite m)

theorem intervalAlgebra_finiteDimensional
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)) (m : ℕ) :
    FiniteDimensional k (G.intervalAlgebra hfinite m) :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (G.intervalFiniteRepresentables hfinite m)

/-- Finitely generated right modules over the interval algebra are precisely
finite-dimensional contravariant degree representations supported there. -/
def intervalAlgebraSupportedModuleEquivalence
    (hfinite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)) (m : ℕ) :
    FGModuleCat.{max u v} (G.intervalAlgebra hfinite m)ᵐᵒᵖ ≌
    ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (DegreeObject G)ᵒᵖ (G.outsideIntervalOp m) :=
  (CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence
    (G.intervalFiniteRepresentables hfinite m)).symm.trans
      (G.intervalSupportedModuleEquivalence h hbound m)

end MagnitudeConjecture.GradedCategory.HomGrading
