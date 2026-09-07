import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.OrbitPushdownNakayama
import MagnitudeConjecture.CategoryTheory.ProjectiveCover
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite representable projective presentations

Every finite-support finite-dimensional covariant linear module is generated
by finitely many elements.  Linear coyoneda turns those generators into an
epimorphism from a finite sum of representables, and the same construction on
its kernel gives an exact two-step projective presentation.  Fullness of
linear coyoneda records the first differential as a literal finite matrix of
representing-object morphisms, matching the Nakayama push-down interface.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- For finite modules, essential projective epimorphisms and right-minimal
projective epimorphisms are equivalent without an extra Hopfian hypothesis. -/
theorem finiteDimensionalModule_isEssentialEpi_iff_isRightMinimal
    {P M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    [Projective P] (f : P ⟶ M) [Epi f] :
    IsEssentialEpi f ↔ IsRightMinimal f :=
  isEssentialEpi_iff_isRightMinimal f fun e hepi ↦ by
    letI : Epi e := hepi
    exact isIso_of_epi_finiteDimensionalModule_endo P e

/-- The morphism from a covariant linear representable determined by an
element at its representing object. -/
noncomputable def linearCoyonedaHom
    (M : LinearModuleCategory.{u, v, uK, v} (C := C) k)
    (X : C) (x : M.obj.obj X) :
    linearCoyonedaLinearModule (k := k) X ⟶ M :=
  ObjectProperty.homMk
    { app := fun Y ↦ ModuleCat.ofHom
        { toFun := fun q ↦ M.obj.map q x
          map_add' := fun q r ↦ by
            change M.obj.map (q + r) x = _
            rw [M.obj.map_add]
            rfl
          map_smul' := fun r q ↦ by
            change M.obj.map (r • q) x = _
            rw [M.obj.map_smul]
            rfl }
      naturality := by
        intro Y Z f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        change M.obj.map (q ≫ f) x = M.obj.map f (M.obj.map q x)
        exact congrArg (fun z ↦ z x) (M.obj.map_comp q f) }

@[simp]
theorem linearCoyonedaHom_app_apply
    (M : LinearModuleCategory.{u, v, uK, v} (C := C) k)
    (X Y : C) (x : M.obj.obj X) (q : X ⟶ Y) :
    (linearCoyonedaHom M X x).hom.app Y q = M.obj.map q x :=
  rfl

@[simp]
theorem linearCoyonedaHom_app_id
    (M : LinearModuleCategory.{u, v, uK, v} (C := C) k)
    (X : C) (x : M.obj.obj X) :
    (linearCoyonedaHom M X x).hom.app X (𝟙 X) = x := by
  simp

@[simp]
theorem linearCoyonedaHom_self
    (M : LinearModuleCategory.{u, v, uK, v} (C := C) k)
    (X : C) (f : linearCoyonedaLinearModule (k := k) X ⟶ M) :
    linearCoyonedaHom M X (f.hom.app X (𝟙 X)) = f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change M.obj.map q (f.hom.app X (𝟙 X)) = f.hom.app Y q
  have h := ConcreteCategory.congr_hom (f.hom.naturality q) (𝟙 X)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
  change f.hom.app Y ((𝟙 X) ≫ q) =
    M.obj.map q (f.hom.app X (𝟙 X)) at h
  rw [Category.id_comp] at h
  exact h.symm

/-- Linear Yoneda for covariant modules. -/
def linearCoyonedaHomEquiv
    (M : LinearModuleCategory.{u, v, uK, v} (C := C) k) (X : C) :
    (linearCoyonedaLinearModule (k := k) X ⟶ M) ≃ₗ[k]
      M.obj.obj X where
  toFun f := f.hom.app X (𝟙 X)
  invFun x := linearCoyonedaHom M X x
  left_inv f := linearCoyonedaHom_self M X f
  right_inv x := linearCoyonedaHom_app_id M X x
  map_add' f g := by rfl
  map_smul' r f := by rfl

theorem linearCoyonedaHom_comp
    (M N : LinearModuleCategory.{u, v, uK, v} (C := C) k)
    (X : C) (x : M.obj.obj X) (f : M ⟶ N) :
    linearCoyonedaHom M X x ≫ f =
      linearCoyonedaHom N X (f.hom.app X x) := by
  rw [← linearCoyonedaHom_self N X
    (linearCoyonedaHom M X x ≫ f)]
  simp

instance finiteDimensionalLinearCoyoneda_projective
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    Projective (finiteDimensionalLinearCoyoneda (k := k) X hX) where
  factors := by
    intro E N f e hepi
    let J := (IsFiniteDimensionalModule (C := C) k).ι
    let I := (IsLinearModule (C := C) k).ι
    letI : J.PreservesEpimorphisms :=
      ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
        (IsFiniteDimensionalModule (C := C) k)
    letI : I.PreservesEpimorphisms :=
      ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory
        (IsLinearModule (C := C) k)
    haveI : Epi (I.map (J.map e)) := I.map_epi (J.map e)
    haveI : Epi ((I.map (J.map e)).app X) := inferInstance
    letI : Epi (e.hom.hom.app X) := by
      change Epi ((I.map (J.map e)).app X)
      infer_instance
    have hsurj : Function.Surjective (e.hom.hom.app X) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨x, hx⟩ := hsurj (f.hom.hom.app X (𝟙 X))
    let l : linearCoyonedaLinearModule (k := k) X ⟶ E.obj :=
      linearCoyonedaHom E.obj X x
    refine ⟨J.preimage l, ?_⟩
    apply J.map_injective
    rw [J.map_comp, J.map_preimage]
    change l ≫ e.hom = f.hom
    rw [linearCoyonedaHom_comp, ← linearCoyonedaHom_self N.obj X f.hom]
    rw [hx]
    rfl

/-- A finite projective presentation whose source is literally a finite
biproduct of covariant representables. -/
structure FiniteRepresentablePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) where
  n : ℕ
  X : Fin n → C
  f : (⨁ fun i ↦ (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op (X i))) ⟶ M
  [epi : Epi f]

attribute [instance] FiniteRepresentablePresentation.epi

namespace FiniteRepresentablePresentation

variable
    {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)}
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}

/-- The literal finite sum of representables underlying the presentation. -/
abbrev source (P : FiniteRepresentablePresentation hP M) :
    FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k :=
  ⨁ fun i ↦ (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op (P.X i))

/-- The same finite representable sum as an object of Mathlib's matrix
envelope. -/
def matrixObject (P : FiniteRepresentablePresentation hP M) :
    Mat_ (Cᵒᵖ) where
  ι := Fin P.n
  X i := Opposite.op (P.X i)

instance (P : FiniteRepresentablePresentation hP M) :
    Projective P.source := by
  let Q := fun i : Fin P.n ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op (P.X i))
  change Projective (⨁ Q)
  letI (i : Fin P.n) : Projective
      (Q i) :=
    finiteDimensionalLinearCoyoneda_projective
      (P.X i) (hP (P.X i))
  constructor
  intro E X f e hepi
  refine ⟨biproduct.desc (fun i ↦
    Projective.factorThru (biproduct.ι Q i ≫ f) e), ?_⟩
  apply biproduct.hom_ext'
  intro i
  simp

/-- Forgetting the chosen finite matrix coordinates gives an ordinary
projective presentation. -/
def toProjectivePresentation (P : FiniteRepresentablePresentation hP M) :
    ProjectivePresentation M where
  p := P.source
  f := P.f

variable
    {N : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}

/-- The matrix of representing-object morphisms underlying a map between
two finite sums of covariant representables. -/
noncomputable def representingMatrix
    (P : FiniteRepresentablePresentation hP M)
    (Q : FiniteRepresentablePresentation hP N)
    (f : P.source ⟶ Q.source) : P.matrixObject ⟶ Q.matrixObject :=
  fun i j ↦ (linearCoyoneda k C).preimage
    ((biproduct.ι
      (fun a : Fin P.n ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op (P.X a))) i ≫ f ≫
    biproduct.π
      (fun b : Fin Q.n ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op (Q.X b))) j).hom.hom)

set_option backward.isDefEq.respectTransparency false in
/-- Applying the finite representable functor to the extracted matrix
recovers the original map. -/
theorem map_representingMatrix
    (P : FiniteRepresentablePresentation hP M)
    (Q : FiniteRepresentablePresentation hP N)
    (f : P.source ⟶ Q.source) :
    (finiteProjectiveRepresentableSumFunctor (k := k) hP).map
      (P.representingMatrix Q f) = f := by
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  let g := biproduct.ι
      (fun a : Fin P.n ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op (P.X a))) i ≫ f ≫
    biproduct.π
      (fun b : Fin Q.n ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op (Q.X b))) j
  have hmap :
      (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).map
          ((linearCoyoneda k C).preimage g.hom.hom) = g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (linearCoyoneda k C).map_preimage g.hom.hom
  simpa [finiteProjectiveRepresentableSumFunctor,
    finiteDimensionalLinearCoyonedaFunctor,
    finiteDimensionalLinearCoyoneda, finiteMatrixLift, matrixObject,
    representingMatrix, g] using hmap

end FiniteRepresentablePresentation

/-- Every finite-support finite-dimensional linear module is an epimorphic
image of a finite sum of finite-dimensional covariant representables. -/
theorem finiteRepresentablePresentation_nonempty
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (FiniteRepresentablePresentation hP M) := by
  classical
  let S := moduleSupport k M.obj.obj
  letI : Fintype S := M.property.2.fintype
  let basis (X : S) := Module.finBasis k (M.obj.obj.obj X.1)
  let Idx := Σ X : S, Fin (Module.finrank k (M.obj.obj.obj X.1))
  letI : Fintype Idx := Fintype.ofFinite Idx
  let e : Idx ≃ Fin (Fintype.card Idx) := Fintype.equivFin Idx
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let Q := fun j : Fin (Fintype.card Idx) ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op (e.symm j).1.1)
  let generator (i : Idx) : M.obj.obj.obj i.1.1 := basis i.1 i.2
  have generator_transport {a b : Idx} (h : a = b) :
      M.obj.obj.map (eqToHom (congrArg (fun z : Idx ↦ z.1.1) h))
          (generator a) = generator b := by
    subst b
    simp [generator]
  let component (j : Fin (Fintype.card Idx)) : Q j ⟶ M :=
    ObjectProperty.homMk
      (linearCoyonedaHom M.obj (e.symm j).1.1 (generator (e.symm j)))
  let p : (⨁ Q) ⟶ M := biproduct.desc component
  have hpSurjective (Y : C) : Function.Surjective (p.hom.hom.app Y) := by
    by_cases hY : Nontrivial (M.obj.obj.obj Y)
    · let YS : S := ⟨Y, hY⟩
      rw [← LinearMap.range_eq_top]
      apply eq_top_iff.mpr
      rw [← (basis YS).span_eq]
      apply Submodule.span_le.mpr
      rintro y ⟨j, rfl⟩
      let i : Idx := ⟨YS, j⟩
      have hei : e.symm (e i) = i := e.symm_apply_apply i
      let q : (e.symm (e i)).1.1 ⟶ Y :=
        eqToHom (congrArg (fun z : Idx ↦ z.1.1) hei)
      let z :=
        ((biproduct.ι Q (e i)).hom.hom.app Y) q
      refine ⟨z, ?_⟩
      change p.hom.hom.app Y z = basis YS j
      have hcomp :
          biproduct.ι Q (e i) ≫ p = component (e i) := by
        simp [p]
      have hcompApp := congrArg
        (fun t : Q (e i) ⟶ M ↦ t.hom.hom.app Y) hcomp
      have happ := ConcreteCategory.congr_hom
        hcompApp q
      have hrhs :
          (component (e i)).hom.hom.app Y q = basis YS j := by
        change M.obj.obj.map q (generator (e.symm (e i))) =
          generator i
        exact generator_transport hei
      change p.hom.hom.app Y z = basis YS j
      change p.hom.hom.app Y z =
        (component (e i)).hom.hom.app Y q at happ
      rw [hrhs] at happ
      exact happ
    · haveI : Subsingleton (M.obj.obj.obj Y) :=
        not_nontrivial_iff_subsingleton.mp hY
      intro y
      refine ⟨0, ?_⟩
      simp [Subsingleton.elim y 0]
  let I := (IsLinearModule (C := C) k).ι
  haveI hpApp (Y : C) : Epi (p.hom.hom.app Y) :=
    (ModuleCat.epi_iff_surjective _).mpr (hpSurjective Y)
  haveI : Epi p.hom.hom :=
    (NatTrans.epi_iff_epi_app p.hom.hom).mpr fun Y ↦ hpApp Y
  have hnat : Epi (I.map (J.map p)) := by
    change Epi p.hom.hom
    infer_instance
  letI : Epi (I.map (J.map p)) := hnat
  have hlin : Epi (J.map p) :=
    I.epi_of_epi_map (f := J.map p) inferInstance
  letI : Epi (J.map p) := hlin
  have hp : Epi p := J.epi_of_epi_map (f := p) inferInstance
  letI : Epi p := hp
  exact ⟨{
    n := Fintype.card Idx
    X := fun j ↦ (e.symm j).1.1
    f := p }⟩

/-- Two explicit finite representable covers give a two-step projective
presentation. -/
structure TwoStepFiniteRepresentablePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) where
  augmentation : FiniteRepresentablePresentation hP M
  syzygyPresentation :
    FiniteRepresentablePresentation hP (kernel augmentation.f)

namespace TwoStepFiniteRepresentablePresentation

variable
    {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)}
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}

/-- The first differential between the two finite sums of representables. -/
def differential (P : TwoStepFiniteRepresentablePresentation hP M) :
    P.syzygyPresentation.source ⟶ P.augmentation.source :=
  P.syzygyPresentation.f ≫ kernel.ι P.augmentation.f

@[simp]
theorem differential_comp_augmentation
    (P : TwoStepFiniteRepresentablePresentation hP M) :
    P.differential ≫ P.augmentation.f = 0 := by
  simp [differential]

/-- The differential in literal representing-object matrix coordinates. -/
noncomputable def matrixDifferential
    (P : TwoStepFiniteRepresentablePresentation hP M) :
    P.syzygyPresentation.matrixObject ⟶
      P.augmentation.matrixObject :=
  P.syzygyPresentation.representingMatrix P.augmentation P.differential

set_option backward.isDefEq.respectTransparency false in
theorem map_matrixDifferential
    (P : TwoStepFiniteRepresentablePresentation hP M) :
    (finiteProjectiveRepresentableSumFunctor (k := k) hP).map
        P.matrixDifferential = P.differential :=
  P.syzygyPresentation.map_representingMatrix
    P.augmentation P.differential

/-- The associated exact two-term projective complex. -/
def presentationComplex
    (P : TwoStepFiniteRepresentablePresentation hP M) :
    ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :=
  ShortComplex.mk P.differential P.augmentation.f
    P.differential_comp_augmentation

theorem presentationComplex_exact
    (P : TwoStepFiniteRepresentablePresentation hP M) :
    P.presentationComplex.Exact := by
  apply (ShortComplex.exact_iff_epi_kernel_lift _).2
  have hlift :
      kernel.lift P.augmentation.f P.differential
          P.differential_comp_augmentation =
        P.syzygyPresentation.f := by
    apply (cancel_mono (kernel.ι P.augmentation.f)).1
    simp [differential]
  change Epi (kernel.lift P.augmentation.f P.differential
    P.differential_comp_augmentation)
  rw [hlift]
  infer_instance

end TwoStepFiniteRepresentablePresentation

/-- Every finite-support finite-dimensional module has an explicit two-step
projective presentation by finite sums of representables. -/
theorem twoStepFiniteRepresentablePresentation_nonempty
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) :
    Nonempty (TwoStepFiniteRepresentablePresentation hP M) := by
  obtain ⟨P₀⟩ := finiteRepresentablePresentation_nonempty hP M
  obtain ⟨P₁⟩ := finiteRepresentablePresentation_nonempty hP (kernel P₀.f)
  exact ⟨{ augmentation := P₀, syzygyPresentation := P₁ }⟩

/-- Finite representables supply enough projectives in the literal finite
module category. -/
theorem enoughProjectives_of_finiteRepresentables
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) where
  presentation M :=
    (finiteRepresentablePresentation_nonempty hP M).map
      FiniteRepresentablePresentation.toProjectivePresentation

end MagnitudeConjecture.CoveringHom
