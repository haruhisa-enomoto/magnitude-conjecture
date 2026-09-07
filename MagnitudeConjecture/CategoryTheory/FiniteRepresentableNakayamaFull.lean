import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleHomFinite
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaHom
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Full faithfulness of finite-representable Nakayama duality

The Nakayama images of literal finite sums of representables have the same
Hom spaces as the projective sums themselves.  The equivalence is obtained by
applying the finite Nakayama--Hom pairing twice and using finite-dimensional
double-dual evaluation.  Its compatibility with composition is the exact
interface needed by the minimal-presentation argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable
  (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (linearCoyonedaLinearModule (k := k) X))
  (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (dualLinearYonedaLinearModule (k := k) X))

/-- Nakayama duality is fully faithful on literal finite sums of
representables. -/
def finiteRepresentableNakayamaMapLinearEquiv (Q' Q : Mat_ (Cᵒᵖ)) :
    ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q' ⟶
        (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q) ≃ₗ[k]
      ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q' ⟶
        (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q) :=
  (Module.evalEquiv k
      ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q' ⟶
        (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q)).trans
    ((finiteRepresentableSumNakayamaHomEquiv hP hI Q'
      ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q)).dualMap
      |>.trans
        (finiteRepresentableSumNakayamaHomEquiv hP hI Q
          ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')).symm)

/-- The defining pairing identity for the finite-projective Nakayama map. -/
theorem finiteRepresentableNakayamaMapLinearEquiv_pairing
    (Q' Q : Mat_ (Cᵒᵖ))
    (e : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q' ⟶
      (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q)
    (b : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q') :
    finiteRepresentableSumNakayamaHomEquiv hP hI Q
        ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')
        (finiteRepresentableNakayamaMapLinearEquiv hP hI Q' Q e) b =
      finiteRepresentableSumNakayamaHomEquiv hP hI Q'
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q) b e := by
  simp [finiteRepresentableNakayamaMapLinearEquiv,
    LinearEquiv.trans_apply]

/-- The equivalence sends a literal representing-object matrix to the map of
that matrix under the finite Nakayama functor. -/
theorem finiteRepresentableNakayamaMapLinearEquiv_map
    {Q' Q : Mat_ (Cᵒᵖ)} (d : Q' ⟶ Q) :
    finiteRepresentableNakayamaMapLinearEquiv hP hI Q' Q
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).map d) =
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).map d := by
  apply (finiteRepresentableSumNakayamaHomEquiv hP hI Q
    ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')).injective
  apply LinearMap.ext
  intro b
  rw [finiteRepresentableNakayamaMapLinearEquiv_pairing]
  calc
    finiteRepresentableSumNakayamaHomEquiv hP hI Q'
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q) b
          ((finiteProjectiveRepresentableSumFunctor (k := k) hP).map d) =
      finiteRepresentableSumNakayamaHomEquiv hP hI Q'
        ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')
          (𝟙 _) ((finiteProjectiveRepresentableSumFunctor (k := k) hP).map d ≫ b) := by
            simpa using finiteRepresentableSumNakayamaHomEquiv_naturality
              hP hI Q' b (𝟙 _) _
    _ = finiteRepresentableSumNakayamaHomEquiv hP hI Q
        ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')
          ((finiteNakayamaRepresentableSumFunctor (k := k) hI).map d) b := by
            symm
            simpa using finiteRepresentableSumNakayamaHomEquiv_projectiveNaturality
              hP hI d
              ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q')
              (𝟙 _) b

/-- Nakayama maps of finite projective sums preserve composition. -/
theorem finiteRepresentableNakayamaMapLinearEquiv_comp
    (Q₀ Q₁ Q₂ : Mat_ (Cᵒᵖ))
    (e : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₀ ⟶
      (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₁)
    (f : (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₁ ⟶
      (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₂) :
    finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₂ (e ≫ f) =
      finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e ≫
        finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₂ f := by
  apply (finiteRepresentableSumNakayamaHomEquiv hP hI Q₂
    ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₀)).injective
  apply LinearMap.ext
  intro b
  rw [finiteRepresentableNakayamaMapLinearEquiv_pairing]
  calc
    finiteRepresentableSumNakayamaHomEquiv hP hI Q₀
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₂)
          b (e ≫ f) =
      finiteRepresentableSumNakayamaHomEquiv hP hI Q₀
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₁)
          (f ≫ b) e := by
            symm
            simpa using finiteRepresentableSumNakayamaHomEquiv_naturality
              hP hI Q₀ f b e
    _ = finiteRepresentableSumNakayamaHomEquiv hP hI Q₁
        ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₀)
          (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e)
          (f ≫ b) := by
            symm
            exact finiteRepresentableNakayamaMapLinearEquiv_pairing
              hP hI Q₀ Q₁ e (f ≫ b)
    _ = finiteRepresentableSumNakayamaHomEquiv hP hI Q₁
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q₂)
          (b ≫ finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e) f := by
            symm
            simpa using finiteRepresentableSumNakayamaHomEquiv_naturality
              hP hI Q₁ b
                (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e) f
    _ = finiteRepresentableSumNakayamaHomEquiv hP hI Q₂
        ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₁)
          (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₂ f)
          (b ≫ finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e) := by
            symm
            exact finiteRepresentableNakayamaMapLinearEquiv_pairing
              hP hI Q₁ Q₂ f
                (b ≫ finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e)
    _ = finiteRepresentableSumNakayamaHomEquiv hP hI Q₂
        ((finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₀)
          (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e ≫
            finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₂ f) b := by
              symm
              simpa [Category.assoc] using
                finiteRepresentableSumNakayamaHomEquiv_naturality
                  hP hI Q₂
                    (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ e)
                    (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₂ f) b

@[simp]
theorem finiteRepresentableNakayamaMapLinearEquiv_id (Q : Mat_ (Cᵒᵖ)) :
    finiteRepresentableNakayamaMapLinearEquiv hP hI Q Q (𝟙 _) = 𝟙 _ := by
  rw [← (finiteProjectiveRepresentableSumFunctor (k := k) hP).map_id Q,
    finiteRepresentableNakayamaMapLinearEquiv_map,
    (finiteNakayamaRepresentableSumFunctor (k := k) hI).map_id]

/-- The projective map corresponding to a morphism between finite Nakayama
sums. -/
def finiteRepresentableNakayamaMapPreimage (Q' Q : Mat_ (Cᵒᵖ))
    (a : (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q' ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q) :
    (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q' ⟶
      (finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q :=
  (finiteRepresentableNakayamaMapLinearEquiv hP hI Q' Q).symm a

@[simp]
theorem finiteRepresentableNakayamaMap_preimage
    (Q' Q : Mat_ (Cᵒᵖ))
    (a : (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q' ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q) :
    finiteRepresentableNakayamaMapLinearEquiv hP hI Q' Q
        (finiteRepresentableNakayamaMapPreimage hP hI Q' Q a) = a :=
  LinearEquiv.apply_symm_apply _ a

end MagnitudeConjecture.CoveringHom
