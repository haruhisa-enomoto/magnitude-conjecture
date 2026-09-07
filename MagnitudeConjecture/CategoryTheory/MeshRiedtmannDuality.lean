import MagnitudeConjecture.CategoryTheory.MeshRiedtmann

/-!
# Perfect pairings from Riedtmann condition (c)

This file packages the objectwise perfect composition pairing supplied by
Riedtmann condition (c).  The contravariant finite-module orientation used
by the recovery proof is built separately in
`MeshRiedtmannContravariantDuality`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.MeshCategory.RightMeshData

universe u

variable {k : Type u} [Field k]
variable {Q : Type} [Quiver.{0} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

variable (T : MeshCategory.RightMeshData Q)

/-- The objectwise perfect composition pairing supplied by Riedtmann
condition (c). -/
noncomputable def riedtmannProjectiveDualityLinearEquiv
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (x : Q) :
    (MeshCategory.obj (k := k) T p ⟶ MeshCategory.obj (k := k) T x) ≃ₗ[k]
      Module.Dual k
        (MeshCategory.obj (k := k) T x ⟶
          MeshCategory.obj (k := k) T D.dualVertex) :=
  LinearEquiv.ofBijective
    (T.compositionDualityLinearMap (k := k)
      p x D.dualVertex D.epsilon)
    (D.pairing_bijective x)

@[simp]
theorem riedtmannProjectiveDualityLinearEquiv_apply_apply
    {p : Q} (D : T.RiedtmannProjectiveDualityData (k := k) p)
    (x : Q)
    (f : MeshCategory.obj (k := k) T p ⟶
      MeshCategory.obj (k := k) T x)
    (g : MeshCategory.obj (k := k) T x ⟶
      MeshCategory.obj (k := k) T D.dualVertex) :
    T.riedtmannProjectiveDualityLinearEquiv (k := k) D x f g =
      D.epsilon (f ≫ g) :=
  rfl

end MagnitudeConjecture.MeshCategory.RightMeshData
