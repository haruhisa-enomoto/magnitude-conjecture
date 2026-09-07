import MagnitudeConjecture.Algebra.BiserialIntersectionCokernel

/-!
# Diagonal cokernels from common radical extensions

Two one-step extensions of the same nonsimple uniserial module give the
diagonal cokernel used to exclude a nonsemisimple biserial branch
intersection.  This file packages its layer identifications and discharges
its indecomposability criterion from ambient coordinate thinness.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u}
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Quotienting below the radical canonically preserves the module top. -/
def moduleTopQuotientLinearEquiv
    (M : FinitelyGeneratedCategory A)
    (K : Submodule Aᵐᵒᵖ M)
    (hK : K ≤ Module.jacobson Aᵐᵒᵖ M) :
    ((M ⧸ K) ⧸ Module.jacobson Aᵐᵒᵖ (M ⧸ K)) ≃ₗ[Aᵐᵒᵖ]
      (M ⧸ Module.jacobson Aᵐᵒᵖ M) := by
  let J := Module.jacobson Aᵐᵒᵖ M
  let eEq : ((M ⧸ K) ⧸ Module.jacobson Aᵐᵒᵖ (M ⧸ K)) ≃ₗ[Aᵐᵒᵖ]
      ((M ⧸ K) ⧸ J.map K.mkQ) :=
    Submodule.quotEquivOfEq _ _
      (Module.jacobson_quotient_of_le hK)
  exact eEq.trans
    (Submodule.quotientQuotientEquivQuotient K J hK)

/-- When `E` is identified with the radical of `D`, quotienting `D` by the
image of `rad E` leaves a radical canonically equivalent to `top E`. -/
def commonRadicalQuotientRadicalLinearEquiv
    (E D : FinitelyGeneratedCategory A)
    (iD : E →ₗ[Aᵐᵒᵖ] D) (hiD : Function.Injective iD)
    (hiDrange : iD.range = Module.jacobson Aᵐᵒᵖ D) :
    let K := Module.jacobson Aᵐᵒᵖ E
    let sD : K →ₗ[Aᵐᵒᵖ] D := iD.comp K.subtype
    (E ⧸ K) ≃ₗ[Aᵐᵒᵖ]
      Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range) := by
  let K := Module.jacobson Aᵐᵒᵖ E
  let sD : K →ₗ[Aᵐᵒᵖ] D := iD.comp K.subtype
  have hsDrad : sD.range ≤ Module.jacobson Aᵐᵒᵖ D := by
    rw [← hiDrange]
    rintro y ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  let g : E →ₗ[Aᵐᵒᵖ] (D ⧸ sD.range) :=
    sD.range.mkQ.comp iD
  have hgker : g.ker = K := by
    ext x
    constructor
    · intro hx
      have hxq : sD.range.mkQ (iD x) = 0 :=
        LinearMap.mem_ker.mp hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxq
      obtain ⟨y, hy⟩ := hxq
      have hxy : x = y.1 := by
        apply hiD
        exact hy.symm
      exact hxy ▸ y.2
    · intro hx
      apply LinearMap.mem_ker.mpr
      change sD.range.mkQ (iD x) = 0
      rw [show iD x = sD ⟨x, hx⟩ by rfl]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ⟨⟨x, hx⟩, rfl⟩
  have hgrange : g.range =
      Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range) := by
    calc
      g.range = iD.range.map sD.range.mkQ := by
        exact LinearMap.range_comp iD sD.range.mkQ
      _ = (Module.jacobson Aᵐᵒᵖ D).map sD.range.mkQ := by
        rw [hiDrange]
      _ = Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range) := by
        exact (Module.jacobson_quotient_of_le hsDrad).symm
  exact
    ((Submodule.quotEquivOfEq K g.ker hgker.symm).trans
      g.quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ hgrange)

/-- If `E` is the radical of a coordinate-thin module `C`, the top of `C`
cannot be isomorphic to the top of `E`. -/
theorem moduleTop_nonisomorphic_commonRadicalTop_of_coordinateThin
    {ι : Type*} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (E C : FinitelyGeneratedCategory A)
    (iC : E →ₗ[Aᵐᵒᵖ] C) (hiC : Function.Injective iC)
    (hiCrange : iC.range = Module.jacobson Aᵐᵒᵖ C)
    (hCthin : IsCoordinateThin (k := k) e C)
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E)) :
    ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        (E ⧸ Module.jacobson Aᵐᵒᵖ E)) := by
  let K := Module.jacobson Aᵐᵒᵖ E
  let sC : K →ₗ[Aᵐᵒᵖ] C := iC.comp K.subtype
  have hsCrad : sC.range ≤ Module.jacobson Aᵐᵒᵖ C := by
    rw [← hiCrange]
    rintro y ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  let X : FinitelyGeneratedCategory A := quotientFGObj C sC.range
  let eTop :
      (X ⧸ Module.jacobson Aᵐᵒᵖ X) ≃ₗ[Aᵐᵒᵖ]
        (C ⧸ Module.jacobson Aᵐᵒᵖ C) :=
    moduleTopQuotientLinearEquiv C sC.range hsCrad
  let eRad :
      (E ⧸ K) ≃ₗ[Aᵐᵒᵖ] Module.jacobson Aᵐᵒᵖ X :=
    commonRadicalQuotientRadicalLinearEquiv E C iC hiC hiCrange
  letI : Nontrivial (E ⧸ K) := hEtop.nontrivial
  have hXthin : IsCoordinateThin (k := k) e X :=
    hCthin.quotient hall.idem sC.range
  have hRadne : Module.jacobson Aᵐᵒᵖ X ≠ ⊥ := by
    rw [← Submodule.nontrivial_iff_ne_bot]
    exact eRad.symm.toEquiv.nontrivial
  have hnoniso : ¬ Nonempty
      (Module.jacobson Aᵐᵒᵖ X ≃ₗ[Aᵐᵒᵖ]
        (X ⧸ Module.jacobson Aᵐᵒᵖ X)) :=
    nonisomorphic_submodule_and_top_of_coordinateThin
      e hall X hXthin (Module.jacobson Aᵐᵒᵖ X) hRadne le_rfl
  rintro ⟨u⟩
  exact hnoniso ⟨eRad.symm.trans (u.symm.trans eTop.symm)⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The kernel of the canonical map from `D` to `L/C` is the intrinsic
pullback to `D` of the ambient intersection with `C`. -/
theorem crossSubmoduleToQuotient_ker
    (L : FinitelyGeneratedCategory A)
    (C D : Submodule Aᵐᵒᵖ L) :
    (C.mkQ.comp D.subtype).ker = C.comap D.subtype := by
  ext x
  change C.mkQ x.1 = 0 ↔ x.1 ∈ C
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- The simple tops of two submodules of a coordinate-thin ambient module
cannot coincide when the second branch maps into the quotient by the first
with precisely its radical as kernel. -/
theorem moduleTops_nonisomorphic_of_coordinateThin_of_crossKernel
    {ι : Type*} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (C D : Submodule Aᵐᵒᵖ L)
    (hCtop : IsSimpleModule Aᵐᵒᵖ
      (submoduleFGObj L C ⧸
        Module.jacobson Aᵐᵒᵖ (submoduleFGObj L C)))
    (hker : (C.mkQ.comp D.subtype).ker =
      Module.jacobson Aᵐᵒᵖ (submoduleFGObj L D)) :
    ¬ Nonempty
      ((submoduleFGObj L C ⧸
          Module.jacobson Aᵐᵒᵖ (submoduleFGObj L C)) ≃ₗ[Aᵐᵒᵖ]
        (submoduleFGObj L D ⧸
          Module.jacobson Aᵐᵒᵖ (submoduleFGObj L D))) := by
  let CObj : FinitelyGeneratedCategory A := submoduleFGObj L C
  let DObj : FinitelyGeneratedCategory A := submoduleFGObj L D
  let CTop : FinitelyGeneratedCategory A :=
    quotientFGObj CObj (Module.jacobson Aᵐᵒᵖ CObj)
  let DTop : FinitelyGeneratedCategory A :=
    quotientFGObj DObj (Module.jacobson Aᵐᵒᵖ DObj)
  let cross : DObj →ₗ[Aᵐᵒᵖ] quotientFGObj L C :=
    C.mkQ.comp D.subtype
  rintro ⟨u⟩
  let eDRange : DTop ≃ₗ[Aᵐᵒᵖ] cross.range :=
    (Submodule.quotEquivOfEq
      (Module.jacobson Aᵐᵒᵖ DObj) cross.ker hker.symm).trans
        cross.quotKerEquivRange
  let g : CTop →ₗ[Aᵐᵒᵖ] quotientFGObj L C :=
    cross.range.subtype.comp (eDRange.toLinearMap.comp u.toLinearMap)
  have hgInjective : Function.Injective g :=
    cross.range.subtype_injective.comp
      (eDRange.injective.comp u.injective)
  let qC : CObj →ₗ[Aᵐᵒᵖ] CTop :=
    (Module.jacobson Aᵐᵒᵖ CObj).mkQ
  have hcomp : g.comp qC = 0 := by
    exact linearMap_submodule_to_quotient_eq_zero_of_coordinateThin
      e hall L hL C hCtop (g.comp qC)
  have hg : g = 0 := by
    ext x
    obtain ⟨c, rfl⟩ :=
      (Module.jacobson Aᵐᵒᵖ CObj).mkQ_surjective x
    change (g.comp qC) c = 0
    rw [hcomp]
    rfl
  letI : Nontrivial CTop := hCtop.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : CTop)
  apply hx
  apply hgInjective
  rw [hg]
  rfl

/-- Two local modules with a common radical yield an indecomposable
diagonal cokernel after gluing the radical of that common radical. -/
theorem isIndecomposableModule_diagonalCommonRadicalCokernel
    (E C D : FinitelyGeneratedCategory A)
    (iC : E →ₗ[Aᵐᵒᵖ] C) (iD : E →ₗ[Aᵐᵒᵖ] D)
    (hiC : Function.Injective iC) (hiD : Function.Injective iD)
    (hiCrange : iC.range = Module.jacobson Aᵐᵒᵖ C)
    (hiDrange : iD.range = Module.jacobson Aᵐᵒᵖ D)
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E))
    (hCtop : IsSimpleModule Aᵐᵒᵖ
      (C ⧸ Module.jacobson Aᵐᵒᵖ C))
    (hDtop : IsSimpleModule Aᵐᵒᵖ
      (D ⧸ Module.jacobson Aᵐᵒᵖ D))
    (hCtopDtop : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        (D ⧸ Module.jacobson Aᵐᵒᵖ D)))
    (hCtopEtop : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        (E ⧸ Module.jacobson Aᵐᵒᵖ E)))
    (hDtopEtop : ¬ Nonempty
      ((D ⧸ Module.jacobson Aᵐᵒᵖ D) ≃ₗ[Aᵐᵒᵖ]
        (E ⧸ Module.jacobson Aᵐᵒᵖ E)))
    [Nontrivial (Module.jacobson Aᵐᵒᵖ E)] :
    let K := Module.jacobson Aᵐᵒᵖ E
    let sC : K →ₗ[Aᵐᵒᵖ] C := iC.comp K.subtype
    let sD : K →ₗ[Aᵐᵒᵖ] D := iD.comp K.subtype
    let h : K →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ (cokernelFGObj (submoduleFGObj E K) (prodFGObj C D) h) := by
  let K := Module.jacobson Aᵐᵒᵖ E
  let sC : K →ₗ[Aᵐᵒᵖ] C := iC.comp K.subtype
  let sD : K →ₗ[Aᵐᵒᵖ] D := iD.comp K.subtype
  let h : K →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
  letI : Nontrivial (submoduleFGObj E K) := ‹Nontrivial K›
  have hsC : Function.Injective sC := hiC.comp K.subtype_injective
  have hsD : Function.Injective sD := hiD.comp K.subtype_injective
  have hsCrad : sC.range ≤ Module.jacobson Aᵐᵒᵖ C := by
    rw [← hiCrange]
    rintro y ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  have hsDrad : sD.range ≤ Module.jacobson Aᵐᵒᵖ D := by
    rw [← hiDrange]
    rintro y ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  let eCtop := moduleTopQuotientLinearEquiv C sC.range hsCrad
  let eDtop := moduleTopQuotientLinearEquiv D sD.range hsDrad
  let eCrad := commonRadicalQuotientRadicalLinearEquiv
    E C iC hiC hiCrange
  let eDrad := commonRadicalQuotientRadicalLinearEquiv
    E D iD hiD hiDrange
  have hCquotTop : IsSimpleModule Aᵐᵒᵖ
      ((C ⧸ sC.range) ⧸ Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range)) := by
    letI : IsSimpleModule Aᵐᵒᵖ
        (C ⧸ Module.jacobson Aᵐᵒᵖ C) := hCtop
    exact IsSimpleModule.congr eCtop
  have hDquotTop : IsSimpleModule Aᵐᵒᵖ
      ((D ⧸ sD.range) ⧸ Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range)) := by
    letI : IsSimpleModule Aᵐᵒᵖ
        (D ⧸ Module.jacobson Aᵐᵒᵖ D) := hDtop
    exact IsSimpleModule.congr eDtop
  have hCquotRad : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range)) := by
    letI : IsSimpleModule Aᵐᵒᵖ (E ⧸ K) := hEtop
    exact IsSimpleModule.congr eCrad.symm
  have hDquotRad : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range)) := by
    letI : IsSimpleModule Aᵐᵒᵖ (E ⧸ K) := hEtop
    exact IsSimpleModule.congr eDrad.symm
  have hCtopDquotTop : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        ((D ⧸ sD.range) ⧸
          Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range))) := by
    rintro ⟨u⟩
    exact hCtopDtop ⟨u.trans eDtop⟩
  have hCtopDquotRad : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range)) := by
    rintro ⟨u⟩
    exact hCtopEtop ⟨u.trans eDrad.symm⟩
  have hDtopCquotTop : ¬ Nonempty
      ((D ⧸ Module.jacobson Aᵐᵒᵖ D) ≃ₗ[Aᵐᵒᵖ]
        ((C ⧸ sC.range) ⧸
          Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range))) := by
    rintro ⟨u⟩
    exact hCtopDtop ⟨(u.trans eCtop).symm⟩
  have hDtopCquotRad : ¬ Nonempty
      ((D ⧸ Module.jacobson Aᵐᵒᵖ D) ≃ₗ[Aᵐᵒᵖ]
        Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range)) := by
    rintro ⟨u⟩
    exact hDtopEtop ⟨u.trans eCrad.symm⟩
  exact isIndecomposableModule_diagonalCokernel_of_crossLayers
    (submoduleFGObj E K) C D sC sD hsC hsD hCtop hDtop
      hDquotTop hDquotRad hCtopDquotTop hCtopDquotRad
      hCquotTop hCquotRad hDtopCquotTop hDtopCquotRad

/-- For coordinate-thin common-radical extensions, separation of the two
outer tops is the only nonisomorphism hypothesis needed by the diagonal
cokernel criterion. -/
theorem isIndecomposableModule_diagonalCommonRadicalCokernel_of_coordinateThin
    {ι : Type*} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (E C D : FinitelyGeneratedCategory A)
    (iC : E →ₗ[Aᵐᵒᵖ] C) (iD : E →ₗ[Aᵐᵒᵖ] D)
    (hiC : Function.Injective iC) (hiD : Function.Injective iD)
    (hiCrange : iC.range = Module.jacobson Aᵐᵒᵖ C)
    (hiDrange : iD.range = Module.jacobson Aᵐᵒᵖ D)
    (hCthin : IsCoordinateThin (k := k) e C)
    (hDthin : IsCoordinateThin (k := k) e D)
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E))
    (hCtop : IsSimpleModule Aᵐᵒᵖ
      (C ⧸ Module.jacobson Aᵐᵒᵖ C))
    (hDtop : IsSimpleModule Aᵐᵒᵖ
      (D ⧸ Module.jacobson Aᵐᵒᵖ D))
    (hCtopDtop : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        (D ⧸ Module.jacobson Aᵐᵒᵖ D)))
    [Nontrivial (Module.jacobson Aᵐᵒᵖ E)] :
    let K := Module.jacobson Aᵐᵒᵖ E
    let sC : K →ₗ[Aᵐᵒᵖ] C := iC.comp K.subtype
    let sD : K →ₗ[Aᵐᵒᵖ] D := iD.comp K.subtype
    let h : K →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ (cokernelFGObj (submoduleFGObj E K) (prodFGObj C D) h) := by
  have hCtopEtop :=
    moduleTop_nonisomorphic_commonRadicalTop_of_coordinateThin
      e hall E C iC hiC hiCrange hCthin hEtop
  have hDtopEtop :=
    moduleTop_nonisomorphic_commonRadicalTop_of_coordinateThin
      e hall E D iD hiD hiDrange hDthin hEtop
  exact isIndecomposableModule_diagonalCommonRadicalCokernel
    E C D iC iD hiC hiD hiCrange hiDrange hEtop hCtop hDtop
      hCtopDtop hCtopEtop hDtopEtop

/-- Ambient coordinate thinness discharges every separation hypothesis for
two submodules whose common-radical structure is compatible with the cross
projection to `L/C`. -/
theorem isIndecomposableModule_diagonalCommonRadicalCokernel_of_ambient
    {ι : Type*} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (C D : Submodule Aᵐᵒᵖ L)
    (E : FinitelyGeneratedCategory A)
    (iC : E →ₗ[Aᵐᵒᵖ] submoduleFGObj L C)
    (iD : E →ₗ[Aᵐᵒᵖ] submoduleFGObj L D)
    (hiC : Function.Injective iC) (hiD : Function.Injective iD)
    (hiCrange : iC.range =
      Module.jacobson Aᵐᵒᵖ (submoduleFGObj L C))
    (hiDrange : iD.range =
      Module.jacobson Aᵐᵒᵖ (submoduleFGObj L D))
    (hcrossKer : (C.mkQ.comp D.subtype).ker =
      Module.jacobson Aᵐᵒᵖ (submoduleFGObj L D))
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E))
    (hCtop : IsSimpleModule Aᵐᵒᵖ
      (submoduleFGObj L C ⧸
        Module.jacobson Aᵐᵒᵖ (submoduleFGObj L C)))
    (hDtop : IsSimpleModule Aᵐᵒᵖ
      (submoduleFGObj L D ⧸
        Module.jacobson Aᵐᵒᵖ (submoduleFGObj L D)))
    [Nontrivial (Module.jacobson Aᵐᵒᵖ E)] :
    let K := Module.jacobson Aᵐᵒᵖ E
    let sC : K →ₗ[Aᵐᵒᵖ] submoduleFGObj L C :=
      iC.comp K.subtype
    let sD : K →ₗ[Aᵐᵒᵖ] submoduleFGObj L D :=
      iD.comp K.subtype
    let h : K →ₗ[Aᵐᵒᵖ]
        (submoduleFGObj L C × submoduleFGObj L D) := sC.prod sD
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ
        (cokernelFGObj (submoduleFGObj E K)
          (prodFGObj (submoduleFGObj L C) (submoduleFGObj L D)) h) := by
  have hCtopDtop :=
    moduleTops_nonisomorphic_of_coordinateThin_of_crossKernel
      e hall L hL C D hCtop hcrossKer
  exact
    isIndecomposableModule_diagonalCommonRadicalCokernel_of_coordinateThin
      e hall E (submoduleFGObj L C) (submoduleFGObj L D)
        iC iD hiC hiD hiCrange hiDrange
        (hL.submodule C) (hL.submodule D)
        hEtop hCtop hDtop hCtopDtop

end MagnitudeConjecture.RightModule
