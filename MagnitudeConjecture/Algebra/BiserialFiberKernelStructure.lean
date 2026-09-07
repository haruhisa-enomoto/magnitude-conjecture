import MagnitudeConjecture.Algebra.BiserialKernelObstruction
import MagnitudeConjecture.Algebra.SocleModule

/-!
# Structure of the biserial fiber-kernel module

The first and last obstructions in the Pogorzały--Skowroński induction are
fiber products of two length-three branches over a common simple quotient.
This file records the exact length and socle calculations for that
construction.  The source-specific element calculation used to prove
indecomposability is kept separate.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The difference map defining a fiber kernel is surjective as soon as
its left branch is surjective. -/
theorem fiberKernelMap_surjective_of_left
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) :
    Function.Surjective (fiberKernelMap Y Z T f g) := by
  intro t
  obtain ⟨y, hy⟩ := hf t
  refine ⟨(y, 0), ?_⟩
  simp [fiberKernelMap, hy]

/-- The finitely generated wrapper of a fiber kernel is linearly equivalent
to the literal kernel subtype.  Keeping this transport explicit avoids
depending on reducibility of the bundled module object. -/
def fiberKernelFGObjLinearEquiv
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T) :
    fiberKernelFGObj Y Z T f g ≃ₗ[Aᵐᵒᵖ]
      (fiberKernelMap Y Z T f g).ker where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical inclusion of the bundled fiber kernel into the ambient
binary product. -/
def fiberKernelInclusion
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T) :
    fiberKernelFGObj Y Z T f g →ₗ[Aᵐᵒᵖ] (Y × Z) :=
  (fiberKernelMap Y Z T f g).ker.subtype.comp
    (fiberKernelFGObjLinearEquiv Y Z T f g).toLinearMap

/-- The canonical fiber-kernel inclusion is injective. -/
theorem fiberKernelInclusion_injective
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T) :
    Function.Injective (fiberKernelInclusion Y Z T f g) :=
  (fiberKernelMap Y Z T f g).ker.subtype_injective.comp
    (fiberKernelFGObjLinearEquiv Y Z T f g).injective

/-- The product of the two branch radicals inside the ambient product. -/
def fiberKernelBranchRadical
    (Y Z : FinitelyGeneratedCategory A) :
    Submodule Aᵐᵒᵖ (Y × Z) :=
  (Module.jacobson Aᵐᵒᵖ Y).prod (Module.jacobson Aᵐᵒᵖ Z)

/-- The part of a fiber kernel lying in both branch radicals. -/
def fiberKernelRadicalPreimage
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T) :
    Submodule Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) :=
  (fiberKernelBranchRadical Y Z).comap
    (fiberKernelInclusion Y Z T f g)

/-- If both branch maps are onto a nonzero common quotient and the left
branch radical is killed by its quotient map, the fiber kernel is not
contained in the product of the branch radicals. -/
theorem fiberKernelRadicalPreimage_ne_top
    (Y Z T : FinitelyGeneratedCategory A) [Nontrivial T]
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hYrad : Module.jacobson Aᵐᵒᵖ Y ≤ f.ker) :
    fiberKernelRadicalPreimage Y Z T f g ≠ ⊤ := by
  obtain ⟨t, ht⟩ := exists_ne (0 : T)
  obtain ⟨y, hy⟩ := hf t
  obtain ⟨z, hz⟩ := hg t
  let w₀ : (fiberKernelMap Y Z T f g).ker :=
    ⟨(y, z), by
      apply LinearMap.mem_ker.mpr
      simp [fiberKernelMap, hy, hz]⟩
  let w : fiberKernelFGObj Y Z T f g :=
    (fiberKernelFGObjLinearEquiv Y Z T f g).symm w₀
  intro htop
  have hw : w ∈ fiberKernelRadicalPreimage Y Z T f g := by
    rw [htop]
    exact Submodule.mem_top
  have hw' : (y, z) ∈ fiberKernelBranchRadical Y Z := by
    exact hw
  have hyRad : y ∈ Module.jacobson Aᵐᵒᵖ Y := hw'.1
  have hfy : f y = 0 := LinearMap.mem_ker.mp (hYrad hyRad)
  exact ht (hy ▸ hfy)

/-- Composition length is additive across the short exact sequence
defined by a surjective fiber-kernel map. -/
theorem length_prod_eq_length_fiberKernel_add
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) :
    Module.length Aᵐᵒᵖ Y + Module.length Aᵐᵒᵖ Z =
      Module.length Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) +
        Module.length Aᵐᵒᵖ T := by
  let h : (Y × Z) →ₗ[Aᵐᵒᵖ] T := fiberKernelMap Y Z T f g
  let eW : fiberKernelFGObj Y Z T f g ≃ₗ[Aᵐᵒᵖ] h.ker :=
    fiberKernelFGObjLinearEquiv Y Z T f g
  have hexact := Module.length_eq_add_of_exact
    h.ker.subtype h h.ker.subtype_injective
    (fiberKernelMap_surjective_of_left Y Z T f g hf)
    (LinearMap.exact_subtype_ker_map h)
  rw [eW.length_eq]
  simpa [h, Module.length_prod] using hexact

/-- Two length-three branches over a simple quotient have a fiber kernel
of composition length five. -/
theorem length_fiberKernel_eq_five
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f)
    (hY : Module.length Aᵐᵒᵖ Y = 3)
    (hZ : Module.length Aᵐᵒᵖ Z = 3)
    (hT : Module.length Aᵐᵒᵖ T = 1) :
    Module.length Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) = 5 := by
  have hlength := length_prod_eq_length_fiberKernel_add Y Z T f g hf
  rw [hY, hZ, hT] at hlength
  apply WithTop.add_right_cancel ENat.one_ne_top
  calc
    Module.length Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) + 1 = 3 + 3 :=
      hlength.symm
    _ = 5 + 1 := by norm_num

/-- If the simple socles of both branches are killed by the quotient maps,
then the socle of their fiber kernel maps onto the product of the two branch
socles inside the ambient product. -/
theorem map_moduleSocle_fiberKernel_eq_prod
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)).map
        (fiberKernelInclusion Y Z T f g) =
      (moduleSocle Aᵐᵒᵖ Y).prod (moduleSocle Aᵐᵒᵖ Z) := by
  let W := fiberKernelFGObj Y Z T f g
  let j : W →ₗ[Aᵐᵒᵖ] (Y × Z) :=
    fiberKernelInclusion Y Z T f g
  have hj : Function.Injective j :=
    fiberKernelInclusion_injective Y Z T f g
  apply le_antisymm
  · have hmap : (moduleSocle Aᵐᵒᵖ W).map j ≤
        moduleSocle Aᵐᵒᵖ (Y × Z) :=
      map_moduleSocle_le_of_injective j hj
    rw [moduleSocle_prod] at hmap
    exact hmap
  · let iY0 : (moduleSocle Aᵐᵒᵖ Y) →ₗ[Aᵐᵒᵖ]
        (fiberKernelMap Y Z T f g).ker := {
      toFun y := ⟨(y.1, 0), by
        change fiberKernelMap Y Z T f g (y.1, 0) = 0
        simp [fiberKernelMap, LinearMap.mem_ker.mp (hYkill y.2)]⟩
      map_add' _ _ := by
        apply Subtype.ext
        apply Prod.ext <;> simp
      map_smul' _ _ := by
        apply Subtype.ext
        apply Prod.ext <;> simp }
    let iZ0 : (moduleSocle Aᵐᵒᵖ Z) →ₗ[Aᵐᵒᵖ]
        (fiberKernelMap Y Z T f g).ker := {
      toFun z := ⟨(0, z.1), by
        change fiberKernelMap Y Z T f g (0, z.1) = 0
        simp [fiberKernelMap, LinearMap.mem_ker.mp (hZkill z.2)]⟩
      map_add' _ _ := by
        apply Subtype.ext
        apply Prod.ext <;> simp
      map_smul' _ _ := by
        apply Subtype.ext
        apply Prod.ext <;> simp }
    let iY : (moduleSocle Aᵐᵒᵖ Y) →ₗ[Aᵐᵒᵖ] W :=
      (fiberKernelFGObjLinearEquiv Y Z T f g).symm.toLinearMap.comp iY0
    let iZ : (moduleSocle Aᵐᵒᵖ Z) →ₗ[Aᵐᵒᵖ] W :=
      (fiberKernelFGObjLinearEquiv Y Z T f g).symm.toLinearMap.comp iZ0
    have hiY : Function.Injective iY := by
      apply (fiberKernelFGObjLinearEquiv Y Z T f g).symm.injective.comp
      intro y y' h
      apply Subtype.ext
      exact congrArg (fun w : (fiberKernelMap Y Z T f g).ker ↦ w.1.1) h
    have hiZ : Function.Injective iZ := by
      apply (fiberKernelFGObjLinearEquiv Y Z T f g).symm.injective.comp
      intro z z' h
      apply Subtype.ext
      exact congrArg (fun w : (fiberKernelMap Y Z T f g).ker ↦ w.1.2) h
    have hiYsimple : IsSimpleModule Aᵐᵒᵖ iY.range := by
      letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y) := hYsimple
      exact IsSimpleModule.congr (LinearEquiv.ofInjective iY hiY).symm
    have hiZsimple : IsSimpleModule Aᵐᵒᵖ iZ.range := by
      letI : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z) := hZsimple
      exact IsSimpleModule.congr (LinearEquiv.ofInjective iZ hiZ).symm
    have hiYsocle : iY.range ≤ moduleSocle Aᵐᵒᵖ W :=
      le_moduleSocle_of_simple iY.range hiYsimple
    have hiZsocle : iZ.range ≤ moduleSocle Aᵐᵒᵖ W :=
      le_moduleSocle_of_simple iZ.range hiZsimple
    rintro yz ⟨hy, hz⟩
    let y : moduleSocle Aᵐᵒᵖ Y := ⟨yz.1, hy⟩
    let z : moduleSocle Aᵐᵒᵖ Z := ⟨yz.2, hz⟩
    have hiy : iY y ∈ moduleSocle Aᵐᵒᵖ W :=
      hiYsocle ⟨y, rfl⟩
    have hiz : iZ z ∈ moduleSocle Aᵐᵒᵖ W :=
      hiZsocle ⟨z, rfl⟩
    refine ⟨iY y + iZ z,
      (moduleSocle Aᵐᵒᵖ W).add_mem hiy hiz, ?_⟩
    have hjy : j (iY y) = (y.1, 0) := by
      change (iY0 y).1 = (y.1, 0)
      rfl
    have hjz : j (iZ z) = (0, z.1) := by
      change (iZ0 z).1 = (0, z.1)
      rfl
    rw [map_add, hjy, hjz]
    apply Prod.ext <;> simp [y, z]

/-- Under the preceding branch hypotheses, the socle of the fiber kernel is
linearly equivalent to the product of the two branch socles. -/
def fiberKernelSocleLinearEquiv
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) ≃ₗ[Aᵐᵒᵖ]
      moduleSocle Aᵐᵒᵖ Y × moduleSocle Aᵐᵒᵖ Z :=
  let j : fiberKernelFGObj Y Z T f g →ₗ[Aᵐᵒᵖ] (Y × Z) :=
    fiberKernelInclusion Y Z T f g
  let P : Submodule Aᵐᵒᵖ (Y × Z) :=
    (moduleSocle Aᵐᵒᵖ Y).prod (moduleSocle Aᵐᵒᵖ Z)
  let hSocle :
      (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)).map j = P := by
    dsimp only [j, P]
    exact map_moduleSocle_fiberKernel_eq_prod
      Y Z T f g hYsimple hZsimple hYkill hZkill
  let q : moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) →ₗ[Aᵐᵒᵖ] P :=
    (j.comp
      (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)).subtype).codRestrict
        P (fun x ↦ by
      have hx : j x.1 ∈
          (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)).map j :=
        ⟨x.1, x.2, rfl⟩
      rw [hSocle] at hx
      exact hx)
  let eqv : moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) ≃ₗ[Aᵐᵒᵖ] P :=
    LinearEquiv.ofBijective q ⟨by
      intro x y hxy
      apply Subtype.ext
      apply fiberKernelInclusion_injective Y Z T f g
      have hxy' : (q x : Y × Z) = q y :=
        congrArg (fun z : P ↦ (z.1 : Y × Z)) hxy
      exact hxy', by
      intro yz
      have hyz : yz.1 ∈
          (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)).map j := by
        rw [hSocle]
        exact yz.2
      obtain ⟨w, hw, hjw⟩ := hyz
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      exact hjw⟩
  eqv.trans (submoduleProdLinearEquiv
    (moduleSocle Aᵐᵒᵖ Y) (moduleSocle Aᵐᵒᵖ Z)).symm

/-- If both branch socles are simple, the fiber kernel has socle length two.
-/
theorem length_moduleSocle_fiberKernel_eq_two
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    Module.length Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)) = 2 := by
  rw [(fiberKernelSocleLinearEquiv
    Y Z T f g hYsimple hZsimple hYkill hZkill).length_eq,
    Module.length_prod,
    Module.length_eq_one_iff.mpr hYsimple,
    Module.length_eq_one_iff.mpr hZsimple]
  norm_num

/-- Quotient both coordinates of a fiber kernel by their branch socles. -/
def fiberKernelSocleQuotientMap
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    fiberKernelFGObj Y Z T f g →ₗ[Aᵐᵒᵖ]
      fiberKernelFGObj
        (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y))
        (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) T
        (quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill)
        (quotientFGLift Z T (moduleSocle Aᵐᵒᵖ Z) g hZkill) :=
  let qProd : (Y × Z) →ₗ[Aᵐᵒᵖ]
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y) ×
        quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) :=
    (quotientFGMkQ Y (moduleSocle Aᵐᵒᵖ Y)).prodMap
      (quotientFGMkQ Z (moduleSocle Aᵐᵒᵖ Z))
  let q := qProd.comp (fiberKernelInclusion Y Z T f g)
  q.codRestrict
    (fiberKernelMap
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y))
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) T
      (quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill)
      (quotientFGLift Z T (moduleSocle Aᵐᵒᵖ Z) g hZkill)).ker
    (fun w ↦ by
      apply LinearMap.mem_ker.mpr
      have hw : fiberKernelMap Y Z T f g
          (fiberKernelInclusion Y Z T f g w) = 0 := by
        exact LinearMap.mem_ker.mp
          ((fiberKernelFGObjLinearEquiv Y Z T f g w).2)
      dsimp only [q]
      rw [LinearMap.comp_apply, LinearMap.prodMap_apply]
      simp only [fiberKernelMap, LinearMap.coprod_apply,
        LinearMap.neg_apply]
      rw [quotientFGLift_apply_mkQ, quotientFGLift_apply_mkQ]
      simpa [fiberKernelMap] using hw)

/-- Quotienting the branch socles maps onto the corresponding fiber kernel
of quotient branches. -/
theorem fiberKernelSocleQuotientMap_surjective
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    Function.Surjective
      (fiberKernelSocleQuotientMap Y Z T f g hYkill hZkill) := by
  let Yq := quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)
  let Zq := quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)
  let fq : Yq →ₗ[Aᵐᵒᵖ] T :=
    quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill
  let gq : Zq →ₗ[Aᵐᵒᵖ] T :=
    quotientFGLift Z T (moduleSocle Aᵐᵒᵖ Z) g hZkill
  let jq := fiberKernelInclusion Yq Zq T fq gq
  intro wbar
  obtain ⟨y, hy⟩ := quotientFGMkQ_surjective
    Y (moduleSocle Aᵐᵒᵖ Y) (jq wbar).1
  obtain ⟨z, hz⟩ := quotientFGMkQ_surjective
    Z (moduleSocle Aᵐᵒᵖ Z) (jq wbar).2
  have hrel : fiberKernelMap Y Z T f g (y, z) = 0 := by
    have hwbar : fiberKernelMap Yq Zq T fq gq (jq wbar) = 0 := by
      exact LinearMap.mem_ker.mp
        ((fiberKernelFGObjLinearEquiv Yq Zq T fq gq wbar).2)
    simp only [fiberKernelMap, LinearMap.coprod_apply,
      LinearMap.neg_apply] at hwbar
    rw [← hy, ← hz] at hwbar
    dsimp only [fq, gq] at hwbar
    rw [quotientFGLift_apply_mkQ, quotientFGLift_apply_mkQ] at hwbar
    simpa [fiberKernelMap] using hwbar
  let w : fiberKernelFGObj Y Z T f g := ⟨(y, z), hrel⟩
  refine ⟨w, ?_⟩
  apply fiberKernelInclusion_injective Yq Zq T fq gq
  exact Prod.ext hy hz

/-- The kernel of the branch-socle quotient map is precisely the fiber
kernel's socle. -/
theorem fiberKernelSocleQuotientMap_ker
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    (fiberKernelSocleQuotientMap Y Z T f g hYkill hZkill).ker =
      moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g) := by
  let W := fiberKernelFGObj Y Z T f g
  let j := fiberKernelInclusion Y Z T f g
  have hj : Function.Injective j :=
    fiberKernelInclusion_injective Y Z T f g
  have hmap : (moduleSocle Aᵐᵒᵖ W).map j =
      (moduleSocle Aᵐᵒᵖ Y).prod (moduleSocle Aᵐᵒᵖ Z) :=
    map_moduleSocle_fiberKernel_eq_prod
      Y Z T f g hYsimple hZsimple hYkill hZkill
  have hsocle_iff (w : W) :
      w ∈ moduleSocle Aᵐᵒᵖ W ↔
        j w ∈ (moduleSocle Aᵐᵒᵖ Y).prod
          (moduleSocle Aᵐᵒᵖ Z) := by
    constructor
    · intro hw
      rw [← hmap]
      exact ⟨w, hw, rfl⟩
    · intro hw
      rw [← hmap] at hw
      obtain ⟨w', hw', hww'⟩ := hw
      have heq : w' = w := hj hww'
      simpa [heq] using hw'
  ext w
  rw [LinearMap.mem_ker]
  constructor
  · intro hw
    have hw' := congrArg Subtype.val hw
    change
      ((moduleSocle Aᵐᵒᵖ Y).mkQ (j w).1,
        (moduleSocle Aᵐᵒᵖ Z).mkQ (j w).2) = 0 at hw'
    rw [hsocle_iff]
    simpa using hw'
  · intro hw
    apply Subtype.ext
    change
      ((moduleSocle Aᵐᵒᵖ Y).mkQ (j w).1,
        (moduleSocle Aᵐᵒᵖ Z).mkQ (j w).2) = 0
    rw [hsocle_iff] at hw
    simpa using hw

/-- Quotienting a fiber kernel by its socle is the fiber kernel of the two
branch quotients by their socles. -/
def fiberKernelQuotientSocleLinearEquiv
    (Y Z T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker) :
    (fiberKernelFGObj Y Z T f g ⧸
      moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)) ≃ₗ[Aᵐᵒᵖ]
      fiberKernelFGObj
        (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y))
        (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) T
        (quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill)
        (quotientFGLift Z T (moduleSocle Aᵐᵒᵖ Z) g hZkill) :=
  let q := fiberKernelSocleQuotientMap Y Z T f g hYkill hZkill
  (Submodule.quotEquivOfEq
    (moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)) q.ker
    (fiberKernelSocleQuotientMap_ker
      Y Z T f g hYsimple hZsimple hYkill hZkill).symm).trans
    (q.quotKerEquivOfSurjective
      (fiberKernelSocleQuotientMap_surjective
        Y Z T f g hYkill hZkill))

omit [IsNoetherianRing Aᵐᵒᵖ] in
include k in
/-- For a length-three branch onto a length-one top, the induced map from
the quotient by the branch socle kills the simple next socle layer. -/
theorem quotientBranchSocle_le_quotientFGLift_ker
    (Y T : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (hf : Function.Surjective f)
    (hYlength : Module.length Aᵐᵒᵖ Y = 3)
    (hTlength : Module.length Aᵐᵒᵖ T = 1)
    (hYsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hYnextSimple : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ
        (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)))) :
    moduleSocle Aᵐᵒᵖ
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)) ≤
        (quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill).ker := by
  let Yq := quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)
  let fq : Yq →ₗ[Aᵐᵒᵖ] T :=
    quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill
  have hfiniteLength : IsFiniteLength Aᵐᵒᵖ Yq :=
    FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) Yq
  letI : IsArtinian Aᵐᵒᵖ Yq :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).2
  have hYqlength : Module.length Aᵐᵒᵖ Yq = 2 := by
    change Module.length Aᵐᵒᵖ
      (Y ⧸ moduleSocle Aᵐᵒᵖ Y) = 2
    exact length_quotient_moduleSocle_eq_two_of_length_eq_three
      hYsocle hYlength
  exact moduleSocle_le_ker_of_surjective_of_length_eq_two_to_one
    fq (quotientFGLift_surjective
      Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill hf)
      hYqlength hTlength hYnextSimple

/-- If the two branch next socle layers are copies of the same simple module,
then the next socle layer of their fiber kernel is their product. -/
def fiberKernelNextSocleLinearEquiv
    (Y Z T F : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (hFsimple : IsSimpleModule Aᵐᵒᵖ F)
    (hYnextKill : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)) ≤
        (quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill).ker)
    (hZnextKill : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) ≤
        (quotientFGLift Z T (moduleSocle Aᵐᵒᵖ Z) g hZkill).ker)
    (eY : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) ≃ₗ[Aᵐᵒᵖ] F) :
    moduleSocle Aᵐᵒᵖ
      (fiberKernelFGObj Y Z T f g ⧸
        moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)) ≃ₗ[Aᵐᵒᵖ]
          (F × F) :=
  let Yq := quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)
  let Zq := quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)
  let fq : Yq →ₗ[Aᵐᵒᵖ] T :=
    quotientFGLift Y T (moduleSocle Aᵐᵒᵖ Y) f hYkill
  let gq : Zq →ₗ[Aᵐᵒᵖ] T :=
    quotientFGLift Z T (moduleSocle Aᵐᵒᵖ Z) g hZkill
  let W := fiberKernelFGObj Y Z T f g
  let Wq := fiberKernelFGObj Yq Zq T fq gq
  let eQuot : (W ⧸ moduleSocle Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ] Wq :=
    fiberKernelQuotientSocleLinearEquiv
      Y Z T f g hYsimple hZsimple hYkill hZkill
  let eSoc : moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ]
      moduleSocle Aᵐᵒᵖ Wq :=
    (eQuot.submoduleMap
      (moduleSocle Aᵐᵒᵖ (W ⧸ moduleSocle Aᵐᵒᵖ W))).trans
      (LinearEquiv.ofEq _ _ (map_moduleSocle_eq_of_linearEquiv eQuot))
  let hYqSimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Yq) := by
    letI : IsSimpleModule Aᵐᵒᵖ F := hFsimple
    exact IsSimpleModule.congr eY
  let hZqSimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Zq) := by
    letI : IsSimpleModule Aᵐᵒᵖ F := hFsimple
    exact IsSimpleModule.congr eZ
  eSoc.trans
    ((fiberKernelSocleLinearEquiv Yq Zq T fq gq hYqSimple hZqSimple
      hYnextKill hZnextKill).trans (LinearEquiv.prodCongr eY eZ))

include k in
/-- For two length-three branches over a length-one top, identifying both
branch next socles with one simple module computes the next socle of the
fiber kernel.  The kernel conditions for those branch next socles follow
from the length data and surjectivity. -/
def fiberKernelNextSocleLinearEquivOfLengthThree
    (Y Z T F : FinitelyGeneratedCategory A)
    (f : Y →ₗ[Aᵐᵒᵖ] T) (g : Z →ₗ[Aᵐᵒᵖ] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hYlength : Module.length Aᵐᵒᵖ Y = 3)
    (hZlength : Module.length Aᵐᵒᵖ Z = 3)
    (hTlength : Module.length Aᵐᵒᵖ T = 1)
    (hYsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Y))
    (hZsimple : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ Z))
    (hYkill : moduleSocle Aᵐᵒᵖ Y ≤ f.ker)
    (hZkill : moduleSocle Aᵐᵒᵖ Z ≤ g.ker)
    (hFsimple : IsSimpleModule Aᵐᵒᵖ F)
    (eY : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y)) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : moduleSocle Aᵐᵒᵖ
      (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z)) ≃ₗ[Aᵐᵒᵖ] F) :
    moduleSocle Aᵐᵒᵖ
      (fiberKernelFGObj Y Z T f g ⧸
        moduleSocle Aᵐᵒᵖ (fiberKernelFGObj Y Z T f g)) ≃ₗ[Aᵐᵒᵖ]
          (F × F) := by
  have hYnextSimple : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ
        (quotientFGObj Y (moduleSocle Aᵐᵒᵖ Y))) := by
    letI : IsSimpleModule Aᵐᵒᵖ F := hFsimple
    exact IsSimpleModule.congr eY
  have hZnextSimple : IsSimpleModule Aᵐᵒᵖ
      (moduleSocle Aᵐᵒᵖ
        (quotientFGObj Z (moduleSocle Aᵐᵒᵖ Z))) := by
    letI : IsSimpleModule Aᵐᵒᵖ F := hFsimple
    exact IsSimpleModule.congr eZ
  have hYnextKill :=
    quotientBranchSocle_le_quotientFGLift_ker
      (k := k) Y T f hf hYlength hTlength hYsimple hYkill
        hYnextSimple
  have hZnextKill :=
    quotientBranchSocle_le_quotientFGLift_ker
      (k := k) Z T g hg hZlength hTlength hZsimple hZkill
        hZnextSimple
  exact fiberKernelNextSocleLinearEquiv Y Z T F f g hYsimple hZsimple
    hYkill hZkill hFsimple hYnextKill hZnextKill eY eZ

end MagnitudeConjecture.RightModule
