import MagnitudeConjecture.CategoryTheory.MeshRiedtmannDuality
import MagnitudeConjecture.CategoryTheory.MeshSimplePresentation

/-!
# Contravariant module duality from Riedtmann condition (c)

Coefficient-dualizing condition (c) identifies the injective
`D Hom(p,-)` in the contravariant mesh-module category with the
contravariant representable `Hom(-,j)`.  This is the orientation used in
the Bongartz--Gabriel injective-resolution argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver Q]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable (T : RightMeshData Q)

/-- Recover the underlying mesh vertex from an object of the opposite strict
vertex category. -/
abbrev oppositeVertex
    (X : (T.VertexCategory (k := k))ᵒᵖ) : Q :=
  X.unop

/-- The coefficient-dual form of the perfect pairing in condition (c). -/
noncomputable def riedtmannProjectiveCoefficientDualityLinearEquiv
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y))
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (x : Q) :
    Module.Dual k
        (MeshCategory.obj (k := k) T p ⟶ MeshCategory.obj (k := k) T x) ≃ₗ[k]
      (MeshCategory.obj (k := k) T x ⟶
        MeshCategory.obj (k := k) T D.dualVertex) := by
  letI : FiniteDimensional k
      (MeshCategory.obj (k := k) T x ⟶
        MeshCategory.obj (k := k) T D.dualVertex) :=
    hfinite x D.dualVertex
  exact
    (T.riedtmannProjectiveDualityLinearEquiv (k := k) D x).dualMap.symm.trans
      (Module.evalEquiv k
        (MeshCategory.obj (k := k) T x ⟶
          MeshCategory.obj (k := k) T D.dualVertex)).symm

/-- Evaluation characterizes the coefficient-dual form of condition (c). -/
theorem riedtmannProjectiveCoefficientDualityLinearEquiv_evaluation
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y))
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (x : Q)
    (phi : Module.Dual k
      (MeshCategory.obj (k := k) T p ⟶ MeshCategory.obj (k := k) T x))
    (ell : Module.Dual k
      (MeshCategory.obj (k := k) T x ⟶
        MeshCategory.obj (k := k) T D.dualVertex)) :
    ell (T.riedtmannProjectiveCoefficientDualityLinearEquiv
      (k := k) hfinite D x phi) =
      phi ((T.riedtmannProjectiveDualityLinearEquiv
        (k := k) D x).symm ell) := by
  letI : FiniteDimensional k
      (MeshCategory.obj (k := k) T x ⟶
        MeshCategory.obj (k := k) T D.dualVertex) :=
    hfinite x D.dualVertex
  change ell ((Module.evalEquiv k
      (MeshCategory.obj (k := k) T x ⟶
        MeshCategory.obj (k := k) T D.dualVertex)).symm
      ((T.riedtmannProjectiveDualityLinearEquiv
        (k := k) D x).dualMap.symm phi)) = _
  rw [Module.apply_evalEquiv_symm_apply]
  exact LinearEquiv.dualMap_apply
    (T.riedtmannProjectiveDualityLinearEquiv (k := k) D x).symm phi ell

/-- The objectwise coefficient-dual condition-(c) equivalence in the strict
vertex model and the opposite-category convention for contravariant
modules. -/
noncomputable def riedtmannProjectiveContravariantLinearEquiv
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y))
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (X : (T.VertexCategory (k := k))ᵒᵖ) :
    Module.Dual k (X ⟶ Opposite.op p) ≃ₗ[k]
      (X.unop ⟶ (D.dualVertex : T.VertexCategory (k := k))) :=
  (((oppositeHomLinearEquiv X (Opposite.op p)).dualMap.symm).trans
    ((InducedCategory.homLinearEquiv (R := k)).dualMap.symm)).trans
    ((T.riedtmannProjectiveCoefficientDualityLinearEquiv
      (k := k) hfinite D (T.oppositeVertex (k := k) X)).trans
      (InducedCategory.homLinearEquiv (R := k)).symm)

/-- Evaluation formula for the strict-vertex coefficient-dual
condition-(c) equivalence. -/
theorem riedtmannProjectiveContravariantLinearEquiv_evaluation
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y))
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (X : (T.VertexCategory (k := k))ᵒᵖ)
    (phi : Module.Dual k (X ⟶ Opposite.op p))
    (ell : Module.Dual k
      (MeshCategory.obj (k := k) T (T.oppositeVertex (k := k) X) ⟶
        MeshCategory.obj (k := k) T D.dualVertex)) :
    ell ((T.riedtmannProjectiveContravariantLinearEquiv
      (k := k) hfinite D X phi).hom) =
      phi ((InducedCategory.homMk
        ((T.riedtmannProjectiveDualityLinearEquiv
          (k := k) D (T.oppositeVertex (k := k) X)).symm ell)).op) := by
  unfold riedtmannProjectiveContravariantLinearEquiv
  simp only [LinearEquiv.trans_apply]
  change ell (T.riedtmannProjectiveCoefficientDualityLinearEquiv
      (k := k) hfinite D (T.oppositeVertex (k := k) X)
      ((InducedCategory.homLinearEquiv (R := k)).dualMap.symm
        ((oppositeHomLinearEquiv X (Opposite.op p)).dualMap.symm phi))) = _
  rw [T.riedtmannProjectiveCoefficientDualityLinearEquiv_evaluation
    (k := k) hfinite D (T.oppositeVertex (k := k) X)]
  rfl

/-- Coefficient-dualizing condition (c) identifies the injective
`D Hom(p,-)` with the contravariant representable `Hom(-,j)`. -/
noncomputable def riedtmannProjectiveContravariantLinearModuleIso
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y))
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p) :
    dualLinearYonedaLinearModule
        (k := k) (C := (T.VertexCategory (k := k))ᵒᵖ) (Opposite.op p) ≅
      T.contravariantRepresentableLinearModule
        (k := k) D.dualVertex := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun X ↦
    (T.riedtmannProjectiveContravariantLinearEquiv
      (k := k) hfinite D X).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change
    T.riedtmannProjectiveContravariantLinearEquiv
        (k := k) hfinite D Y
        ((dualLinearYoneda (k := k) (C :=
          (T.VertexCategory (k := k))ᵒᵖ) (Opposite.op p)).map f phi) =
      (T.contravariantRepresentableLinearModule
        (k := k) D.dualVertex).obj.map f
        (T.riedtmannProjectiveContravariantLinearEquiv
          (k := k) hfinite D X phi)
  apply InducedCategory.hom_ext
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro ell
  change ell ((T.riedtmannProjectiveContravariantLinearEquiv
      (k := k) hfinite D Y
      (((dualLinearYoneda (k := k) (C :=
        (T.VertexCategory (k := k))ᵒᵖ) (Opposite.op p)).map f).hom
          phi)).hom) =
    ell ((((T.contravariantRepresentableLinearModule
      (k := k) D.dualVertex).obj.map f).hom
        (T.riedtmannProjectiveContravariantLinearEquiv
          (k := k) hfinite D X phi)).hom)
  rw [T.riedtmannProjectiveContravariantLinearEquiv_evaluation
      (k := k) hfinite D Y]
  change (show Module.Dual k
      (X ⟶ Opposite.op
        (show T.VertexCategory (k := k) from p)) from phi)
      (f ≫ (InducedCategory.homMk
        ((T.riedtmannProjectiveDualityLinearEquiv
          (k := k) D (T.oppositeVertex (k := k) Y)).symm ell)).op) =
    (show Module.Dual k
        (MeshCategory.obj (k := k) T (T.oppositeVertex (k := k) X) ⟶
          MeshCategory.obj (k := k) T D.dualVertex) from
      (CategoryTheory.Linear.leftComp k
        (MeshCategory.obj (k := k) T D.dualVertex)
        f.unop.hom).dualMap ell)
      ((T.riedtmannProjectiveContravariantLinearEquiv
        (k := k) hfinite D X phi).hom)
  rw [T.riedtmannProjectiveContravariantLinearEquiv_evaluation
    (k := k) hfinite D X]
  congr 1
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  apply (T.riedtmannProjectiveDualityLinearEquiv
    (k := k) D (T.oppositeVertex (k := k) X)).injective
  apply LinearMap.ext
  intro q
  simp only [unop_comp, Quiver.Hom.unop_op,
    InducedCategory.comp_hom, InducedCategory.homMk_hom]
  simp only [T.riedtmannProjectiveDualityLinearEquiv_apply_apply]
  calc
    D.epsilon
        ((((T.riedtmannProjectiveDualityLinearEquiv
            (k := k) D (T.oppositeVertex (k := k) Y)).symm ell) ≫
          f.unop.hom) ≫ q) =
      D.epsilon
        ((T.riedtmannProjectiveDualityLinearEquiv
            (k := k) D (T.oppositeVertex (k := k) Y)).symm ell ≫
          (f.unop.hom ≫ q)) := by rw [Category.assoc]
    _ = ell (f.unop.hom ≫ q) := by
      rw [← T.riedtmannProjectiveDualityLinearEquiv_apply_apply
        (k := k) D (T.oppositeVertex (k := k) Y),
        LinearEquiv.apply_symm_apply]
    _ = ((CategoryTheory.Linear.leftComp k
        (MeshCategory.obj (k := k) T D.dualVertex)
        f.unop.hom).dualMap ell) q := rfl
    _ = D.epsilon
        ((T.riedtmannProjectiveDualityLinearEquiv
            (k := k) D (T.oppositeVertex (k := k) X)).symm
          ((CategoryTheory.Linear.leftComp k
            (MeshCategory.obj (k := k) T D.dualVertex)
            f.unop.hom).dualMap ell) ≫ q) := by
      rw [← T.riedtmannProjectiveDualityLinearEquiv_apply_apply
        (k := k) D (T.oppositeVertex (k := k) X),
        LinearEquiv.apply_symm_apply]

/-- Finite-module form of the coefficient-dual condition-(c)
isomorphism. -/
noncomputable def riedtmannProjectiveContravariantFiniteModuleIso
    (hfinite : ∀ x y : Q,
      FiniteDimensional k
        (MeshCategory.obj (k := k) T x ⟶ MeshCategory.obj (k := k) T y))
    (hP : T.FiniteContravariantRepresentables (k := k))
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (hI : IsFiniteDimensionalModule
      (C := (T.VertexCategory (k := k))ᵒᵖ) k
      (dualLinearYonedaLinearModule
        (k := k) (C := (T.VertexCategory (k := k))ᵒᵖ)
        (Opposite.op p))) :
    finiteDimensionalDualLinearYoneda
        (k := k) (C := (T.VertexCategory (k := k))ᵒᵖ)
        (Opposite.op p) hI ≅
      T.contravariantRepresentableFiniteModule
        (k := k) hP D.dualVertex :=
  ObjectProperty.isoMk _
    (T.riedtmannProjectiveContravariantLinearModuleIso
      (k := k) hfinite D)

end MagnitudeConjecture.MeshCategory.RightMeshData
