import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCover
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix

/-!
# Finite-representable coordinates on projective modules

When the representing objects have local endomorphism rings, every
indecomposable projective finite module is a covariant representable.  Finite
indecomposable decomposition therefore puts every projective finite module in
literal finite-representable coordinates.  Applying this to projective covers
produces exact minimal two-step presentations in the matrix model used by the
Nakayama push-down comparison.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uK uD w

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

private def endRingEquivOfFullyFaithful
    {D : Type uD} [Category.{w} D] [Preadditive D]
    (F : Cᵒᵖ ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X : Cᵒᵖ) :
    End X ≃+* End (F.obj X) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f

private def oppositeEndRingEquiv (X : C) :
    (End X)ᵐᵒᵖ ≃+* End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

private theorem isLocalRing_mulOpposite
    {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

theorem finiteDimensionalLinearCoyoneda_end_isLocalRing
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    IsLocalRing (End
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X))) := by
  letI : IsLocalRing (End X) := hlocal X
  letI : IsLocalRing (End X)ᵐᵒᵖ := isLocalRing_mulOpposite
  letI : IsLocalRing (End (Opposite.op X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (oppositeEndRingEquiv X)
  let F := finiteDimensionalLinearCoyonedaFunctor (k := k) hP
  letI : F.Full := by
    dsimp [F, finiteDimensionalLinearCoyonedaFunctor,
      linearCoyonedaLinearModuleFunctor]
    infer_instance
  letI : F.Faithful := by
    dsimp [F, finiteDimensionalLinearCoyonedaFunctor,
      linearCoyonedaLinearModuleFunctor]
    infer_instance
  change IsLocalRing (End (F.obj (Opposite.op X)))
  let e : End (Opposite.op X) ≃+* End (F.obj (Opposite.op X)) :=
    endRingEquivOfFullyFaithful F (Opposite.op X)
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm e

theorem finiteDimensionalLinearCoyoneda_indecomposable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    Indecomposable
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X)) := by
  letI : IsLocalRing (End
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X))) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hP hlocal X
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _

theorem indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (P : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    [Projective P] (hPind : Indecomposable P) :
    ∃ X : C, Nonempty
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X) ≅ P) := by
  classical
  obtain ⟨Q⟩ := finiteRepresentablePresentation_nonempty hP P
  let F := fun i : Fin Q.n ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op (Q.X i))
  let s : P ⟶ Q.source := Projective.factorThru (𝟙 P) Q.f
  have hs : s ≫ Q.f = 𝟙 P :=
    Projective.factorThru_comp (𝟙 P) Q.f
  let c (i : Fin Q.n) : End P :=
    (s ≫ biproduct.π F i) ≫ (biproduct.ι F i ≫ Q.f)
  have hsum : ∑ i : Fin Q.n, c i = 𝟙 P := by
    change ∑ i : Fin Q.n,
        (s ≫ biproduct.π F i) ≫ (biproduct.ι F i ≫ Q.f) =
      𝟙 P
    calc
      ∑ i : Fin Q.n,
          (s ≫ biproduct.π F i) ≫ (biproduct.ι F i ≫ Q.f) =
        s ≫ (∑ i : Fin Q.n,
          biproduct.π F i ≫ biproduct.ι F i) ≫ Q.f := by
            simp only [Category.assoc, Preadditive.comp_sum,
              Preadditive.sum_comp]
      _ = s ≫ Q.f := by
        rw [biproduct.total, Category.id_comp]
      _ = 𝟙 P := hs
  letI : IsLocalRing (End P) :=
    finiteDimensionalModule_end_isLocalRing k P hPind
  have hunit : IsUnit (∑ i : Fin Q.n, c i) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨i, _, hi⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := c) hunit
  let a : P ⟶ F i := s ≫ biproduct.π F i
  let b : F i ⟶ P := biproduct.ι F i ≫ Q.f
  have habI : IsIso (a ≫ b) := by
    apply (isUnit_iff_isIso (a ≫ b)).1
    simpa only [c, a, b] using hi
  letI : IsIso (a ≫ b) := habI
  have haSplit : IsSplitMono a := by
    apply IsSplitMono.mk'
    exact
      { retraction := b ≫ inv (a ≫ b)
        id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  letI : IsSplitMono a := haSplit
  have hFi : Indecomposable (F i) :=
    finiteDimensionalLinearCoyoneda_indecomposable hP hlocal (Q.X i)
  haveI : IsIso a :=
    MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
      hFi a hPind.1
  exact ⟨Q.X i, ⟨(asIso a).symm⟩⟩

/-- Literal finite-representable coordinates on a finite projective module. -/
structure FiniteRepresentableCoordinates
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (P : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) where
  n : ℕ
  X : Fin n → C
  isoSource :
    (⨁ fun i ↦ (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op (X i))) ≅ P

theorem finiteRepresentableCoordinates_nonempty_of_projective
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (P : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    [Projective P] :
    Nonempty (FiniteRepresentableCoordinates hP P) := by
  classical
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition P
  have hprojective (j : Fin d.n) : Projective (d.summand j) := by
    let i : d.summand j ⟶ P :=
      biproduct.ι d.summand j ≫ d.isoBiproduct.inv
    let r : P ⟶ d.summand j :=
      d.isoBiproduct.hom ≫ biproduct.π d.summand j
    apply projective_of_retract (P := P) (Q := d.summand j)
      (inferInstance : Projective P) i r
    simp [i, r, Category.assoc]
  have hdense (j : Fin d.n) :
      ∃ X : C, Nonempty
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op X) ≅ d.summand j) := by
    letI : Projective (d.summand j) := hprojective j
    exact indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      hP hlocal (d.summand j) (d.indecomposable j)
  choose X e using hdense
  exact ⟨{
    n := d.n
    X := X
    isoSource :=
      biproduct.mapIso (fun j ↦ Classical.choice (e j)) ≪≫
        d.isoBiproduct.symm }⟩

/-- A minimal projective presentation in literal finite-representable
coordinates. -/
structure MinimalFiniteRepresentablePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    extends FiniteRepresentablePresentation hP M where
  rightMinimal : IsRightMinimal f

namespace MinimalFiniteRepresentablePresentation

variable
    {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)}
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}

/-- The finite sum of representables underlying a minimal presentation. -/
abbrev source (P : MinimalFiniteRepresentablePresentation hP M) :=
  P.toFiniteRepresentablePresentation.source

instance (P : MinimalFiniteRepresentablePresentation hP M) :
    Projective P.source := by
  change Projective P.toFiniteRepresentablePresentation.source
  infer_instance

instance (P : MinimalFiniteRepresentablePresentation hP M) : Epi P.f :=
  P.toFiniteRepresentablePresentation.epi

/-- Forgetting the literal representable coordinates gives an ordinary
minimal projective presentation. -/
def toMinimalProjectivePresentation
    (P : MinimalFiniteRepresentablePresentation hP M) :
    MinimalProjectivePresentation M where
  p := P.source
  f := P.f
  rightMinimal := P.rightMinimal

/-- Transport an abstract minimal projective presentation into chosen literal
finite-representable coordinates on its source. -/
def ofMinimalProjectivePresentation
    (P : MinimalProjectivePresentation M)
    (Q : FiniteRepresentableCoordinates hP P.p) :
    MinimalFiniteRepresentablePresentation hP M where
  n := Q.n
  X := Q.X
  f := Q.isoSource.hom ≫ P.f
  rightMinimal := P.rightMinimal.precomp_splitMono Q.isoSource.hom

end MinimalFiniteRepresentablePresentation

/-- Every finite module has a minimal projective presentation whose source is
literally a finite sum of representables, provided representing objects have
local endomorphism rings. -/
theorem minimalFiniteRepresentablePresentation_nonempty
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (MinimalFiniteRepresentablePresentation hP M) := by
  obtain ⟨P⟩ :=
    finiteDimensionalModule_minimalProjectivePresentation_nonempty hP M
  obtain ⟨Q⟩ :=
    finiteRepresentableCoordinates_nonempty_of_projective hP hlocal P.p
  exact ⟨MinimalFiniteRepresentablePresentation.ofMinimalProjectivePresentation
    P Q⟩

/-- A two-step minimal projective presentation in literal finite-representable
matrix coordinates. -/
structure TwoStepMinimalFiniteRepresentablePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) where
  augmentation : MinimalFiniteRepresentablePresentation hP M
  syzygyPresentation :
    MinimalFiniteRepresentablePresentation hP (kernel augmentation.f)

namespace TwoStepMinimalFiniteRepresentablePresentation

variable
    {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)}
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}

/-- Forgetting minimality gives the existing literal matrix presentation. -/
def toTwoStepFiniteRepresentablePresentation
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    TwoStepFiniteRepresentablePresentation hP M where
  augmentation := P.augmentation.toFiniteRepresentablePresentation
  syzygyPresentation :=
    P.syzygyPresentation.toFiniteRepresentablePresentation

/-- Forgetting coordinates gives the generic two-step minimal projective
presentation. -/
def toTwoStepMinimalProjectivePresentation
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    TwoStepMinimalProjectivePresentation M where
  augmentation := P.augmentation.toMinimalProjectivePresentation
  syzygyPresentation :=
    P.syzygyPresentation.toMinimalProjectivePresentation

/-- The literal finite-matrix presentation is exact. -/
theorem presentationComplex_exact
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    P.toTwoStepFiniteRepresentablePresentation.presentationComplex.Exact :=
  P.toTwoStepFiniteRepresentablePresentation.presentationComplex_exact

end TwoStepMinimalFiniteRepresentablePresentation

/-- Every finite module has an exact two-step minimal projective presentation
in literal finite-representable matrix coordinates. -/
theorem twoStepMinimalFiniteRepresentablePresentation_nonempty
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (TwoStepMinimalFiniteRepresentablePresentation hP M) := by
  obtain ⟨P₀⟩ :=
    minimalFiniteRepresentablePresentation_nonempty hP hlocal M
  obtain ⟨P₁⟩ :=
    minimalFiniteRepresentablePresentation_nonempty hP hlocal
      (kernel P₀.f)
  exact ⟨{ augmentation := P₀, syzygyPresentation := P₁ }⟩

end MagnitudeConjecture.CoveringHom
