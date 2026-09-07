import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaHom
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Injectivity of finite dual corepresentables

Coefficient-dual corepresentables are injective in the category of
finite-support pointwise finite-dimensional linear modules.  The proof is the
dual co-Yoneda lemma followed by extension of a linear functional along the
component of a monomorphism.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

local instance : Module.Injective k k :=
  Module.injective_of_isSemisimpleRing k k

/-- Dual co-Yoneda inside the finite-dimensional module subcategory. -/
def finiteDualLinearYonedaHomEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (X : C)
    (hI : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (M ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI) ≃ₗ[k]
      Module.Dual k (M.obj.obj.obj X) :=
  (InducedCategory.homLinearEquiv (R := k)).trans
    (dualLinearYonedaHomEquiv M.obj X)

@[simp]
theorem finiteDualLinearYonedaHomEquiv_apply
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (X : C)
    (hI : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (a : M ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI)
    (x : M.obj.obj.obj X) :
    finiteDualLinearYonedaHomEquiv M X hI a x =
      dualLinearYonedaValueLinearEquiv (k := k) X X
        (a.hom.hom.app X x) (𝟙 X) :=
  rfl

/-- Naturality of finite dual co-Yoneda in the source module. -/
theorem finiteDualLinearYonedaHomEquiv_naturality
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (X : C)
    (hI : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (g : M ⟶ N)
    (a : N ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI)
    (x : M.obj.obj.obj X) :
    finiteDualLinearYonedaHomEquiv M X hI (g ≫ a) x =
      finiteDualLinearYonedaHomEquiv N X hI a
        (g.hom.hom.app X x) :=
  rfl

/-- A finite-dimensional dual corepresentable is injective. -/
theorem finiteDimensionalDualLinearYoneda_injective
    (X : C)
    (hI : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    Injective (finiteDimensionalDualLinearYoneda (k := k) X hI) := by
  constructor
  intro E N f e _
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let I := (IsLinearModule (C := C) k).ι
  letI : J.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsFiniteDimensionalModule (C := C) k)
  letI : I.PreservesMonomorphisms :=
    ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory
      (IsLinearModule (C := C) k)
  haveI : Mono (J.map e) := J.map_mono e
  haveI : Mono (I.map (J.map e)) := I.map_mono (J.map e)
  haveI : Mono (e.hom.hom.app X) := by
    change Mono ((I.map (J.map e)).app X)
    infer_instance
  have heInjective : Function.Injective (e.hom.hom.app X) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  let ell : Module.Dual k (E.obj.obj.obj X) :=
    finiteDualLinearYonedaHomEquiv E X hI f
  obtain ⟨ell', hell'⟩ := Module.Injective.extension_property k k
    (E.obj.obj.obj X) (N.obj.obj.obj X) (e.hom.hom.app X).hom
    heInjective ell
  let g : N ⟶ finiteDimensionalDualLinearYoneda (k := k) X hI :=
    (finiteDualLinearYonedaHomEquiv N X hI).symm ell'
  refine ⟨g, ?_⟩
  apply (finiteDualLinearYonedaHomEquiv E X hI).injective
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hell' x
  rw [finiteDualLinearYonedaHomEquiv_naturality]
  calc
    finiteDualLinearYonedaHomEquiv N X hI g
          (e.hom.hom.app X x) =
        ell' (e.hom.hom.app X x) := by
          rw [show finiteDualLinearYonedaHomEquiv N X hI g = ell' by
            simp [g]]
    _ = ell x := hx
    _ = finiteDualLinearYonedaHomEquiv E X hI f x := rfl

/-- A literal finite Nakayama sum is injective. -/
theorem finiteNakayamaRepresentableSum_injective
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (Q : Mat_ (Cᵒᵖ)) :
    Injective ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q) := by
  let I := fun i : Q.ι ↦
    finiteDimensionalDualLinearYoneda (k := k) (Q.X i).unop
      (hI (Q.X i).unop)
  change Injective (⨁ I)
  letI (i : Q.ι) : Injective (I i) :=
    finiteDimensionalDualLinearYoneda_injective
      (Q.X i).unop (hI (Q.X i).unop)
  infer_instance

end MagnitudeConjecture.CoveringHom
