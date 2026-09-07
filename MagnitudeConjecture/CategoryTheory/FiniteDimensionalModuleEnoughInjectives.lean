import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaInjective
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Enough injectives in the finite functor category

A finite-support module embeds into a finite sum of coefficient-dual
corepresentables.  For every supported object we take a basis of the dual of
the module value and assemble the corresponding dual co-Yoneda maps.  The
identity component detects every vector, so the resulting natural map is
pointwise injective.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- An explicit monomorphism from a finite module to a finite nested
biproduct of coefficient-dual corepresentables.  The chosen `Fintype`
structure is stored so the target remains available as explicit data. -/
structure FiniteDualCorepresentableCopresentation
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) where
  supportFintype : Fintype (moduleSupport k M.obj.obj)
  d : moduleSupport k M.obj.obj → ℕ
  f :
    letI := supportFintype
    M ⟶
      ⨁ fun X : moduleSupport k M.obj.obj ↦
        ⨁ fun _ : Fin (d X) ↦
          finiteDimensionalDualLinearYoneda (k := k) X.1 (hI X.1)
  mono_f : Mono f

namespace FiniteDualCorepresentableCopresentation

variable
    {hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)}
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}

/-- The finite injective target of an explicit dual-corepresentable
copresentation. -/
abbrev target (P : FiniteDualCorepresentableCopresentation hI M) :=
  letI := P.supportFintype
  ⨁ fun X : moduleSupport k M.obj.obj ↦
    ⨁ fun _ : Fin (P.d X) ↦
      finiteDimensionalDualLinearYoneda (k := k) X.1 (hI X.1)

instance target_injective
    (P : FiniteDualCorepresentableCopresentation hI M) :
    Injective P.target := by
  letI : Fintype (moduleSupport k M.obj.obj) := P.supportFintype
  letI hIObj (X : moduleSupport k M.obj.obj) :
      Injective
        (finiteDimensionalDualLinearYoneda (k := k) X.1 (hI X.1)) :=
    finiteDimensionalDualLinearYoneda_injective X.1 (hI X.1)
  dsimp only [target]
  infer_instance

end FiniteDualCorepresentableCopresentation

/-- The explicit finite dual-corepresentable copresentation exists for every
finite-support pointwise finite-dimensional module. -/
theorem finiteDualCorepresentableCopresentation_nonempty
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Nonempty (FiniteDualCorepresentableCopresentation hI M) := by
  classical
  let S := moduleSupport k M.obj.obj
  let supportFintype : Fintype S := M.property.2.fintype
  letI : Fintype S := supportFintype
  let d (X : S) := Module.finrank k (Module.Dual k (M.obj.obj.obj X.1))
  let b (X : S) := Module.finBasis k (Module.Dual k (M.obj.obj.obj X.1))
  let I (X : S) :=
    finiteDimensionalDualLinearYoneda (k := k) X.1 (hI X.1)
  let B (X : S) :
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⨁ fun _ : Fin (d X) ↦ I X
  let a (X : S) (r : Fin (d X)) : M ⟶ I X :=
    (finiteDualLinearYonedaHomEquiv M X.1 (hI X.1)).symm (b X r)
  let component (X : S) : M ⟶ B X := biproduct.lift (a X)
  let E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⨁ B
  let f : M ⟶ E := biproduct.lift component
  have hInjective (X : C) : Function.Injective (f.hom.hom.app X) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_cases hxzero : x = 0
      · exact hxzero
      · letI : Nontrivial (M.obj.obj.obj X) :=
          ⟨⟨0, x, Ne.symm hxzero⟩⟩
        let Xs : S :=
          ⟨X, show Nontrivial (M.obj.obj.obj X) from inferInstance⟩
        rw [← Module.forall_dual_apply_eq_zero_iff k]
        intro ell
        have hbzero (r : Fin (d Xs)) : b Xs r x = 0 := by
          have hmap :
              f ≫ biproduct.π B Xs ≫
                  biproduct.π (fun _ : Fin (d Xs) ↦ I Xs) r =
                a Xs r := by
            dsimp only [f]
            rw [← Category.assoc, biproduct.lift_π]
            dsimp only [component]
            exact biproduct.lift_π _ _
          have hvalue : (a Xs r).hom.hom.app X x = 0 := by
            rw [← hmap]
            change
              ((biproduct.π B Xs).hom.hom.app X ≫
                (biproduct.π
                  (fun _ : Fin (d Xs) ↦ I Xs) r).hom.hom.app X)
                  (f.hom.hom.app X x) = 0
            rw [hx]
            simp
          have heq :
              finiteDualLinearYonedaHomEquiv M X (hI X) (a Xs r) =
                b Xs r := by
            exact LinearEquiv.apply_symm_apply _ _
          rw [← heq]
          rw [finiteDualLinearYonedaHomEquiv_apply]
          change
            dualLinearYonedaValueLinearEquiv (k := k) X X
                ((a Xs r).hom.hom.app X x) (𝟙 X) = 0
          rw [hvalue]
          rfl
        calc
          ell x = (∑ r : Fin (d Xs), (b Xs).repr ell r • b Xs r) x := by
            rw [(b Xs).sum_repr ell]
          _ = ∑ r : Fin (d Xs), (b Xs).repr ell r • b Xs r x := by
            simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
          _ = 0 := by simp [hbzero]
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let L := (IsLinearModule (C := C) k).ι
  haveI hmonoApp (X : C) : Mono ((L.map (J.map f)).app X) := by
    rw [ModuleCat.mono_iff_injective]
    exact hInjective X
  haveI : Mono (L.map (J.map f)) := NatTrans.mono_of_mono_app _
  haveI : Mono (J.map f) := L.mono_of_mono_map
    (show Mono (L.map (J.map f)) from inferInstance)
  haveI : Mono f := J.mono_of_mono_map
    (show Mono (J.map f) from inferInstance)
  exact ⟨{
    supportFintype := supportFintype
    d := d
    f := f
    mono_f := inferInstance }⟩

/-- Finite dual corepresentables provide enough injectives in the category
of finite-support pointwise finite-dimensional modules. -/
theorem finiteDimensionalModuleCategoryEnoughInjectives
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    EnoughInjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) where
  presentation M := by
    obtain ⟨P⟩ := finiteDualCorepresentableCopresentation_nonempty hI M
    letI : Mono P.f := P.mono_f
    exact ⟨{
      J := P.target
      f := P.f }⟩

end MagnitudeConjecture.CoveringHom
