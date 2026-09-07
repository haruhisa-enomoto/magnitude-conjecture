import MagnitudeConjecture.Algebra.CoordinateThinModule

/-!
# Kernel subquotient obstructions for biseriality

The Pogorzały--Skowroński induction repeatedly constructs a kernel inside a
binary product and exhibits two equal composition layers in it.  This file
packages the routine module-theoretic part: a product of two branch
submodules, modulo branch submodules with a common quotient, is a repeated
self-subquotient of the kernel.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- A product of two submodules with the same nonzero quotient gives a
repeated self-subquotient of every ambient submodule which contains that
product. -/
theorem hasRepeatedSelfSubquotient_of_prod_submodule_quotients
    (Y Z F : FinitelyGeneratedCategory A) [Nontrivial F]
    (W : Submodule Aᵐᵒᵖ (prodFGObj Y Z))
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (hPW : (PY.prod PZ : Submodule Aᵐᵒᵖ (Y × Z)) ≤ W)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    HasRepeatedSelfSubquotient
      (submoduleFGObj (prodFGObj Y Z) W) := by
  let P : Submodule Aᵐᵒᵖ
      (submoduleFGObj (prodFGObj Y Z) W) :=
    (PY.prod PZ).comap W.subtype
  let pY : P →ₗ[Aᵐᵒᵖ] PY :=
    ((LinearMap.fst Aᵐᵒᵖ Y Z).comp
      (W.subtype.comp P.subtype)).codRestrict PY (fun x ↦ x.2.1)
  let pZ : P →ₗ[Aᵐᵒᵖ] PZ :=
    ((LinearMap.snd Aᵐᵒᵖ Y Z).comp
      (W.subtype.comp P.subtype)).codRestrict PZ (fun x ↦ x.2.2)
  let qY : P →ₗ[Aᵐᵒᵖ] F :=
    eY.toLinearMap.comp (QY.mkQ.comp pY)
  let qZ : P →ₗ[Aᵐᵒᵖ] F :=
    eZ.toLinearMap.comp (QZ.mkQ.comp pZ)
  let q : P →ₗ[Aᵐᵒᵖ] (F × F) := qY.prod qZ
  have hq : Function.Surjective q := by
    intro t
    obtain ⟨y, hy⟩ := QY.mkQ_surjective (eY.symm t.1)
    obtain ⟨z, hz⟩ := QZ.mkQ_surjective (eZ.symm t.2)
    let w : W := ⟨(y.1, z.1), hPW ⟨y.2, z.2⟩⟩
    let p : P := ⟨w, ⟨y.2, z.2⟩⟩
    refine ⟨p, Prod.ext ?_ ?_⟩
    · change eY (QY.mkQ y) = t.1
      rw [hy]
      exact eY.apply_symm_apply t.1
    · change eZ (QZ.mkQ z) = t.2
      rw [hz]
      exact eZ.apply_symm_apply t.2
  refine ⟨F, inferInstance, P, q.ker, ?_⟩
  exact ⟨
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ (q.quotKerEquivOfSurjective hq)⟩

/-- Kernel form of the product-subquotient obstruction.  It is enough to
check that the branch product is killed by the defining map. -/
theorem hasRepeatedSelfSubquotient_kernel_of_prod_submodule_quotients
    (Y Z T F : FinitelyGeneratedCategory A) [Nontrivial F]
    (g : (Y × Z) →ₗ[Aᵐᵒᵖ] T)
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (hkill : ∀ y : PY, ∀ z : PZ, g (y.1, z.1) = 0)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    HasRepeatedSelfSubquotient
      (submoduleFGObj (prodFGObj Y Z) g.ker) := by
  apply hasRepeatedSelfSubquotient_of_prod_submodule_quotients
    (Y := Y) (Z := Z) (F := F) (W := g.ker)
    (PY := PY) (PZ := PZ) (QY := QY) (QZ := QZ)
    (eY := eY) (eZ := eZ)
  · rintro ⟨y, z⟩ hyz
    exact LinearMap.mem_ker.mpr
      (hkill ⟨y, hyz.1⟩ ⟨z, hyz.2⟩)

/-- Difference of two maps to a common target.  Its kernel is their module
fiber product. -/
def fiberKernelMap
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T) :
    (Y × Z) →ₗ[Aᵐᵒᵖ] T :=
  LinearMap.coprod f (-g)

/-- The finitely generated module carried by a module fiber product. -/
def fiberKernelFGObj
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T) :
    FinitelyGeneratedCategory A :=
  submoduleFGObj (prodFGObj Y Z) (fiberKernelMap Y Z T f g).ker

/-- If both branch maps kill submodules with the same nonzero quotient,
their fiber-product kernel has a repeated self-subquotient. -/
theorem hasRepeatedSelfSubquotient_fiberKernel_of_submodule_quotients
    (Y Z T F : FinitelyGeneratedCategory A) [Nontrivial F]
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (hPY : PY ≤ f.ker) (hPZ : PZ ≤ g.ker)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    HasRepeatedSelfSubquotient
      (fiberKernelFGObj Y Z T f g) := by
  apply hasRepeatedSelfSubquotient_kernel_of_prod_submodule_quotients
    (Y := Y) (Z := Z) (T := T) (F := F)
    (g := fiberKernelMap Y Z T f g)
    (PY := PY) (PZ := PZ) (QY := QY) (QZ := QZ)
    (eY := eY) (eZ := eZ)
  intro y z
  simp [fiberKernelMap, LinearMap.mem_ker.mp (hPY y.2),
    LinearMap.mem_ker.mp (hPZ z.2)]

/-- Under complete coordinate thinness, a fiber-product kernel carrying the
two equal branch quotients above cannot be indecomposable.  This is the exact
contradiction endpoint for the kernel modules in the
Pogorzały--Skowroński induction. -/
theorem not_indec_fiberKernel_of_all_coordinateThin
    {ι : Type w} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (Y Z T F : FinitelyGeneratedCategory A) [Nontrivial F]
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (hPY : PY ≤ f.ker) (hPZ : PZ ≤ g.ker)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    ¬ Indecomposable (fiberKernelFGObj Y Z T f g) := by
  intro hW
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H (fiberKernelFGObj Y Z T f g) hW
    (hasRepeatedSelfSubquotient_fiberKernel_of_submodule_quotients
      Y Z T F f g PY PZ hPY hPZ QY QZ eY eZ)

end MagnitudeConjecture.RightModule
