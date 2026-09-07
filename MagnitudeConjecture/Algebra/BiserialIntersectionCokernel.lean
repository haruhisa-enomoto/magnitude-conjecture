import MagnitudeConjecture.Algebra.BiserialCokernelObstruction
import MagnitudeConjecture.Algebra.BiserialRadicalTruncation

/-!
# Diagonal cokernels from biserial branch intersections

A coordinate-thin ambient module has no nonzero map from a simple-top
submodule to its complementary ambient quotient.  Applied to two branches
with a semisimple length-two intersection, this forces the cross-Hom
vanishing needed to prove the diagonal-summand cokernel indecomposable.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} {ι : Type w}
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]


/-- In a coordinate-thin module, every map from a simple-top submodule to
the quotient by that same submodule is zero. -/
theorem linearMap_submodule_to_quotient_eq_zero_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P : Submodule Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (f : submoduleFGObj L P →ₗ[Aᵐᵒᵖ] quotientFGObj L P) :
    f = 0 := by
  let C : FinitelyGeneratedCategory A := submoduleFGObj L P
  let Q : FinitelyGeneratedCategory A := quotientFGObj L P
  let J : Submodule Aᵐᵒᵖ C := Module.jacobson Aᵐᵒᵖ C
  by_contra hf
  have hkerNeTop : f.ker ≠ ⊤ := by
    intro hker
    exact hf (LinearMap.ker_eq_top.mp hker)
  have hkerJ : f.ker ≤ J :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hPtop hkerNeTop
  let Top : FinitelyGeneratedCategory A := quotientFGObj C J
  let KerQuot : FinitelyGeneratedCategory A := quotientFGObj C f.ker
  let Range : FinitelyGeneratedCategory A := submoduleFGObj Q f.range
  letI : Nontrivial Top := hPtop.nontrivial
  obtain ⟨i, hiTop⟩ := exists_positive_idempotentCoordinate
    (k := k) e hall Top
  let qKerTop : KerQuot →ₗ[Aᵐᵒᵖ] Top :=
    quotientFGMapQ C f.ker J hkerJ
  have hqKerTop : Function.Surjective qKerTop :=
    quotientFGMapQ_surjective C f.ker J hkerJ
  dsimp only [KerQuot, Top, C] at qKerTop hqKerTop
  have hiKerQuot : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) KerQuot) := by
    dsimp only [KerQuot]
    let qCoord := idempotentCoordinateLinearMap (k := k) (e i) qKerTop
    have hqCoord : Function.Surjective qCoord :=
      idempotentCoordinateLinearMap_surjective
        (k := k) (hall.idem i) qKerTop hqKerTop
    letI : Module.Finite k
        (quotientFGObj (submoduleFGObj L P) f.ker) :=
      finite_over_field_of_finitelyGenerated k A
        (quotientFGObj (submoduleFGObj L P) f.ker)
    exact hiTop.trans_le
      (LinearMap.finrank_le_finrank_of_surjective hqCoord)
  let eKerRange : KerQuot ≃ₗ[Aᵐᵒᵖ] f.range := f.quotKerEquivRange
  let eKerRangeIso : KerQuot ≅ Range :=
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ eKerRange
  dsimp only [KerQuot, Range, C, Q] at eKerRangeIso
  have hiRange : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) Range) := by
    dsimp only [Range]
    rw [← (idempotentCoordinateLinearEquivOfIso
      (k := k) (hall.idem i) eKerRangeIso).finrank_eq]
    exact hiKerQuot
  have hiQ : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) Q) := by
    dsimp only [Q]
    letI : Module.Finite k (submoduleFGObj (quotientFGObj L P) f.range) :=
      finite_over_field_of_finitelyGenerated k A
        (submoduleFGObj (quotientFGObj L P) f.range)
    letI : Module.Finite k (quotientFGObj L P) :=
      finite_over_field_of_finitelyGenerated k A (quotientFGObj L P)
    exact hiRange.trans_le
      (LinearMap.finrank_le_finrank_of_injective
        (idempotentCoordinateSubmoduleLinearMap_injective
          (k := k) (e i) Q f.range))
  have hiC : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) C) := by
    dsimp only [C]
    let qCoord := idempotentCoordinateQuotientLinearMap
      (k := k) (e i) (submoduleFGObj L P) J
    have hqCoord : Function.Surjective qCoord :=
      idempotentCoordinateQuotientLinearMap_surjective
        (k := k) (hall.idem i) (submoduleFGObj L P) J
    letI : Module.Finite k (submoduleFGObj L P) :=
      finite_over_field_of_finitelyGenerated k A (submoduleFGObj L P)
    exact hiTop.trans_le
      (LinearMap.finrank_le_finrank_of_surjective hqCoord)
  have hdim := finrank_idempotentCoordinate_eq_add_submodule_quotient
    (k := k) (hall.idem i) L P
  have hthin := hL i
  rw [hdim] at hthin
  dsimp only [C, Q] at hiC hiQ
  omega

/-- A cross map out of a simple-top branch vanishes when projection to the
ambient branch quotient has a simple kernel different from the source top. -/
theorem linearMap_to_crossBranch_eq_zero_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P : Submodule Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (N : FinitelyGeneratedCategory A)
    (g : N →ₗ[Aᵐᵒᵖ] quotientFGObj L P)
    (hkerSimple : IsSimpleModule Aᵐᵒᵖ g.ker)
    (hnoniso : ¬ Nonempty
      ((P ⧸ Module.jacobson Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ] g.ker))
    (f : submoduleFGObj L P →ₗ[Aᵐᵒᵖ] N) :
    f = 0 := by
  have hgf : g.comp f = 0 :=
    linearMap_submodule_to_quotient_eq_zero_of_coordinateThin
      e hall L hL P hPtop (g.comp f)
  by_contra hf
  have hrangeNe : f.range ≠ ⊥ := by
    intro hrange
    exact hf (LinearMap.range_eq_bot.mp hrange)
  have hrangeLe : f.range ≤ g.ker := by
    rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (g.comp f) x = 0
    rw [hgf]
    rfl
  have hrangeEq : f.range = g.ker :=
    (isSimpleModule_iff_isAtom.mp hkerSimple).le_iff_eq hrangeNe |>.mp hrangeLe
  let fKer : submoduleFGObj L P →ₗ[Aᵐᵒᵖ] g.ker :=
    f.codRestrict g.ker (fun x ↦ hrangeLe ⟨x, rfl⟩)
  have hfKer : Function.Surjective fKer := by
    intro y
    have hy : y.1 ∈ f.range := hrangeEq.symm ▸ y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact hnoniso ⟨moduleTopLinearEquivOfSurjectiveToSimple
    (submoduleFGObj L P) (submoduleFGObj N g.ker)
      hPtop hkerSimple fKer hfKer⟩

/-- The intersection of two submodules maps canonically to the left one. -/
def infToLeftLinearMap
    {L : FinitelyGeneratedCategory A}
    (P Q : Submodule Aᵐᵒᵖ L) :
    (P ⊓ Q : Submodule Aᵐᵒᵖ L) →ₗ[Aᵐᵒᵖ] P where
  toFun x := ⟨x.1, x.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The intersection of two submodules maps canonically to the right one. -/
def infToRightLinearMap
    {L : FinitelyGeneratedCategory A}
    (P Q : Submodule Aᵐᵒᵖ L) :
    (P ⊓ Q : Submodule Aᵐᵒᵖ L) →ₗ[Aᵐᵒᵖ] Q where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem infToLeftLinearMap_injective
    {L : FinitelyGeneratedCategory A}
    (P Q : Submodule Aᵐᵒᵖ L) :
    Function.Injective (infToLeftLinearMap P Q) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : P ↦ (z : L)) hxy

omit [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
theorem infToRightLinearMap_injective
    {L : FinitelyGeneratedCategory A}
    (P Q : Submodule Aᵐᵒᵖ L) :
    Function.Injective (infToRightLinearMap P Q) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : Q ↦ (z : L)) hxy

/-- A chosen submodule of an intersection maps into the right branch. -/
def infSubmoduleToRightLinearMap
    {L : FinitelyGeneratedCategory A}
    (P Q : Submodule Aᵐᵒᵖ L)
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    K →ₗ[Aᵐᵒᵖ] Q :=
  (infToRightLinearMap P Q).comp K.subtype

/-- A chosen submodule of an intersection maps into the left branch. -/
def infSubmoduleToLeftLinearMap
    {L : FinitelyGeneratedCategory A}
    (P Q : Submodule Aᵐᵒᵖ L)
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    K →ₗ[Aᵐᵒᵖ] P :=
  (infToLeftLinearMap P Q).comp K.subtype

/-- The right branch modulo a chosen intersection submodule projects to
the ambient quotient by the left branch. -/
def crossBranchQuotientProjection
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    quotientFGObj (submoduleFGObj L Q)
        (infSubmoduleToRightLinearMap P Q K).range →ₗ[Aᵐᵒᵖ]
      quotientFGObj L P :=
  quotientFGLift (submoduleFGObj L Q) (quotientFGObj L P)
    (infSubmoduleToRightLinearMap P Q K).range
    (P.mkQ.comp Q.subtype) (by
      rintro y ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change P.mkQ x.1.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.1.2.1)

/-- The left branch modulo a chosen intersection submodule projects to
the ambient quotient by the right branch. -/
def crossBranchLeftQuotientProjection
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    quotientFGObj (submoduleFGObj L P)
        (infSubmoduleToLeftLinearMap P Q K).range →ₗ[Aᵐᵒᵖ]
      quotientFGObj L Q :=
  quotientFGLift (submoduleFGObj L P) (quotientFGObj L Q)
    (infSubmoduleToLeftLinearMap P Q K).range
    (Q.mkQ.comp P.subtype) (by
      rintro y ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change Q.mkQ x.1.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.1.2.2)

/-- The kernel of the projection from the right branch modulo a chosen
intersection submodule is the corresponding quotient of the whole
intersection. -/
def crossBranchQuotientProjectionKernelLinearEquiv
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    ((P ⊓ Q : Submodule Aᵐᵒᵖ L) ⧸ K) ≃ₗ[Aᵐᵒᵖ]
      (crossBranchQuotientProjection L P Q K).ker := by
  let I : Submodule Aᵐᵒᵖ L := P ⊓ Q
  let iQ : I →ₗ[Aᵐᵒᵖ] Q := infToRightLinearMap P Q
  let sQ : K →ₗ[Aᵐᵒᵖ] Q := infSubmoduleToRightLinearMap P Q K
  let qP : Q →ₗ[Aᵐᵒᵖ] quotientFGObj L P :=
    P.mkQ.comp Q.subtype
  let Nbar := quotientFGObj (submoduleFGObj L Q) sQ.range
  let g : Nbar →ₗ[Aᵐᵒᵖ] quotientFGObj L P :=
    crossBranchQuotientProjection L P Q K
  have hg_apply (q : Q) : g (sQ.range.mkQ q) = qP q := by
    dsimp only [g, crossBranchQuotientProjection, sQ,
      infSubmoduleToRightLinearMap, qP]
    exact quotientFGLift_apply_mkQ
      (submoduleFGObj L Q) (quotientFGObj L P)
        (infSubmoduleToRightLinearMap P Q K).range
        (P.mkQ.comp Q.subtype) _ q
  let tI : I →ₗ[Aᵐᵒᵖ] Nbar :=
    sQ.range.mkQ.comp iQ
  have htIker : tI.ker = K := by
    ext x
    constructor
    · intro hx
      have hxq : sQ.range.mkQ (iQ x) = 0 :=
        LinearMap.mem_ker.mp hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxq
      obtain ⟨y, hy⟩ := hxq
      have hxy : x = y.1 := by
        apply infToRightLinearMap_injective P Q
        exact hy.symm
      exact hxy ▸ y.2
    · intro hx
      apply LinearMap.mem_ker.mpr
      change sQ.range.mkQ (iQ x) = 0
      rw [show iQ x = sQ ⟨x, hx⟩ by rfl]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (show sQ ⟨x, hx⟩ ∈ sQ.range from ⟨⟨x, hx⟩, rfl⟩)
  have htIrange : tI.range = g.ker := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change g (sQ.range.mkQ (iQ x)) = 0
      rw [hg_apply]
      change P.mkQ x.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2.1
    · intro y hy
      obtain ⟨q, rfl⟩ := sQ.range.mkQ_surjective y
      have hqzero : qP q = 0 := by
        have := LinearMap.mem_ker.mp hy
        rw [hg_apply] at this
        exact this
      have hqP : q.1 ∈ P := by
        change P.mkQ q.1 = 0 at hqzero
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hqzero
        exact hqzero
      let x : I := ⟨q.1, hqP, q.2⟩
      exact ⟨x, rfl⟩
  exact
    ((Submodule.quotEquivOfEq K tI.ker htIker.symm).trans
      tI.quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ htIrange)

/-- Left-hand version of
`crossBranchQuotientProjectionKernelLinearEquiv`. -/
def crossBranchLeftQuotientProjectionKernelLinearEquiv
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    ((P ⊓ Q : Submodule Aᵐᵒᵖ L) ⧸ K) ≃ₗ[Aᵐᵒᵖ]
      (crossBranchLeftQuotientProjection L P Q K).ker := by
  let I : Submodule Aᵐᵒᵖ L := P ⊓ Q
  let iP : I →ₗ[Aᵐᵒᵖ] P := infToLeftLinearMap P Q
  let sP : K →ₗ[Aᵐᵒᵖ] P := infSubmoduleToLeftLinearMap P Q K
  let qQ : P →ₗ[Aᵐᵒᵖ] quotientFGObj L Q :=
    Q.mkQ.comp P.subtype
  let Mbar := quotientFGObj (submoduleFGObj L P) sP.range
  let g : Mbar →ₗ[Aᵐᵒᵖ] quotientFGObj L Q :=
    crossBranchLeftQuotientProjection L P Q K
  have hg_apply (p : P) : g (sP.range.mkQ p) = qQ p := by
    dsimp only [g, crossBranchLeftQuotientProjection, sP,
      infSubmoduleToLeftLinearMap, qQ]
    exact quotientFGLift_apply_mkQ
      (submoduleFGObj L P) (quotientFGObj L Q)
        (infSubmoduleToLeftLinearMap P Q K).range
        (Q.mkQ.comp P.subtype) _ p
  let tI : I →ₗ[Aᵐᵒᵖ] Mbar :=
    sP.range.mkQ.comp iP
  have htIker : tI.ker = K := by
    ext x
    constructor
    · intro hx
      have hxq : sP.range.mkQ (iP x) = 0 :=
        LinearMap.mem_ker.mp hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxq
      obtain ⟨y, hy⟩ := hxq
      have hxy : x = y.1 := by
        apply infToLeftLinearMap_injective P Q
        exact hy.symm
      exact hxy ▸ y.2
    · intro hx
      apply LinearMap.mem_ker.mpr
      change sP.range.mkQ (iP x) = 0
      rw [show iP x = sP ⟨x, hx⟩ by rfl]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (show sP ⟨x, hx⟩ ∈ sP.range from ⟨⟨x, hx⟩, rfl⟩)
  have htIrange : tI.range = g.ker := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change g (sP.range.mkQ (iP x)) = 0
      rw [hg_apply]
      change Q.mkQ x.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2.2
    · intro y hy
      obtain ⟨p, rfl⟩ := sP.range.mkQ_surjective y
      have hpzero : qQ p = 0 := by
        have := LinearMap.mem_ker.mp hy
        rw [hg_apply] at this
        exact this
      have hpQ : p.1 ∈ Q := by
        change Q.mkQ p.1 = 0 at hpzero
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hpzero
        exact hpzero
      let x : I := ⟨p.1, p.2, hpQ⟩
      exact ⟨x, rfl⟩
  exact
    ((Submodule.quotEquivOfEq K tI.ker htIker.symm).trans
      tI.quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ htIrange)

/-- If the whole branch intersection maps into the left branch radical,
every map from the left branch to the right branch modulo an intersection
submodule is zero.  Projection to the ambient quotient kills the map first;
its remaining image is a subquotient of the source radical, which coordinate
thinness also kills. -/
theorem linearMap_to_crossBranchQuotient_eq_zero_of_coordinateThin_of_inf_left_le_jacobson
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L))
    (hInfJ : (infToLeftLinearMap P Q).range ≤
      Module.jacobson Aᵐᵒᵖ P)
    (f : submoduleFGObj L P →ₗ[Aᵐᵒᵖ]
      quotientFGObj (submoduleFGObj L Q)
        (infSubmoduleToRightLinearMap P Q K).range) :
    f = 0 := by
  let g := crossBranchQuotientProjection L P Q K
  have hgf : g.comp f = 0 :=
    linearMap_submodule_to_quotient_eq_zero_of_coordinateThin
      e hall L hL P hPtop (g.comp f)
  have hrange : f.range ≤ g.ker := by
    rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (g.comp f) x = 0
    rw [hgf]
    rfl
  let fKer : submoduleFGObj L P →ₗ[Aᵐᵒᵖ] g.ker :=
    f.codRestrict g.ker (fun x ↦ hrange ⟨x, rfl⟩)
  let eQuotKer := crossBranchQuotientProjectionKernelLinearEquiv L P Q K
  let fQuot : submoduleFGObj L P →ₗ[Aᵐᵒᵖ]
      quotientFGObj (submoduleFGObj L (P ⊓ Q)) K :=
    eQuotKer.symm.toLinearMap.comp fKer
  have hfQuot : fQuot = 0 :=
    linearMap_to_injective_jacobson_subquotient_eq_zero_of_coordinateThin
      e hall (submoduleFGObj L P) (hL.submodule P) hPtop
        (submoduleFGObj L (P ⊓ Q)) (infToLeftLinearMap P Q)
        (infToLeftLinearMap_injective P Q) hInfJ K fQuot
  apply LinearMap.ext
  intro x
  have hx : fQuot x = 0 := by rw [hfQuot]; rfl
  have hkerZero : fKer x = 0 := by
    have hx' : eQuotKer.symm (fKer x) = 0 := by
      change fQuot x = 0
      exact hx
    exact eQuotKer.symm.injective
      (hx'.trans eQuotKer.symm.map_zero.symm)
  exact congrArg Subtype.val hkerZero

/-- Right-hand version of
`linearMap_to_crossBranchQuotient_eq_zero_of_coordinateThin_of_inf_left_le_jacobson`. -/
theorem linearMap_to_crossBranchLeftQuotient_eq_zero_of_coordinateThin_of_inf_right_le_jacobson
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    (K : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L))
    (hInfJ : (infToRightLinearMap P Q).range ≤
      Module.jacobson Aᵐᵒᵖ Q)
    (f : submoduleFGObj L Q →ₗ[Aᵐᵒᵖ]
      quotientFGObj (submoduleFGObj L P)
        (infSubmoduleToLeftLinearMap P Q K).range) :
    f = 0 := by
  let g := crossBranchLeftQuotientProjection L P Q K
  have hgf : g.comp f = 0 :=
    linearMap_submodule_to_quotient_eq_zero_of_coordinateThin
      e hall L hL Q hQtop (g.comp f)
  have hrange : f.range ≤ g.ker := by
    rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (g.comp f) x = 0
    rw [hgf]
    rfl
  let fKer : submoduleFGObj L Q →ₗ[Aᵐᵒᵖ] g.ker :=
    f.codRestrict g.ker (fun x ↦ hrange ⟨x, rfl⟩)
  let eQuotKer :=
    crossBranchLeftQuotientProjectionKernelLinearEquiv L P Q K
  let fQuot : submoduleFGObj L Q →ₗ[Aᵐᵒᵖ]
      quotientFGObj (submoduleFGObj L (P ⊓ Q)) K :=
    eQuotKer.symm.toLinearMap.comp fKer
  have hfQuot : fQuot = 0 :=
    linearMap_to_injective_jacobson_subquotient_eq_zero_of_coordinateThin
      e hall (submoduleFGObj L Q) (hL.submodule Q) hQtop
        (submoduleFGObj L (P ⊓ Q)) (infToRightLinearMap P Q)
        (infToRightLinearMap_injective P Q) hInfJ K fQuot
  apply LinearMap.ext
  intro x
  have hx : fQuot x = 0 := by rw [hfQuot]; rfl
  have hkerZero : fKer x = 0 := by
    have hx' : eQuotKer.symm (fKer x) = 0 := by
      change fQuot x = 0
      exact hx
    exact eQuotKer.symm.injective
      (hx'.trans eQuotKer.symm.map_zero.symm)
  exact congrArg Subtype.val hkerZero

/-- Projection from the right branch modulo a chosen intersection summand
to the ambient quotient by the left branch has kernel the complementary
intersection summand. -/
theorem crossBranchQuotientProjection_simple_kernel
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (K T : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L))
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hcompl : IsCompl K T) :
    IsSimpleModule Aᵐᵒᵖ
        (crossBranchQuotientProjection L P Q K).ker ∧
      Nonempty
        ((crossBranchQuotientProjection L P Q K).ker ≃ₗ[Aᵐᵒᵖ] T) := by
  let I : Submodule Aᵐᵒᵖ L := P ⊓ Q
  let iQ : I →ₗ[Aᵐᵒᵖ] Q := infToRightLinearMap P Q
  let sQ : K →ₗ[Aᵐᵒᵖ] Q := infSubmoduleToRightLinearMap P Q K
  let qP : Q →ₗ[Aᵐᵒᵖ] quotientFGObj L P :=
    P.mkQ.comp Q.subtype
  have hsQqP : sQ.range ≤ qP.ker := by
    rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    change P.mkQ x.1.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.1.2.1
  let Nbar := quotientFGObj (submoduleFGObj L Q) sQ.range
  let g : Nbar →ₗ[Aᵐᵒᵖ] quotientFGObj L P :=
    crossBranchQuotientProjection L P Q K
  change IsSimpleModule Aᵐᵒᵖ g.ker ∧
    Nonempty (g.ker ≃ₗ[Aᵐᵒᵖ] T)
  have hg_apply (q : Q) : g (sQ.range.mkQ q) = qP q := by
    dsimp only [g, crossBranchQuotientProjection, sQ,
      infSubmoduleToRightLinearMap, qP]
    exact quotientFGLift_apply_mkQ
      (submoduleFGObj L Q) (quotientFGObj L P)
        (infSubmoduleToRightLinearMap P Q K).range
        (P.mkQ.comp Q.subtype) _ q
  let tI : I →ₗ[Aᵐᵒᵖ] Nbar :=
    sQ.range.mkQ.comp iQ
  have htIker : tI.ker = K := by
    ext x
    constructor
    · intro hx
      have hxq : sQ.range.mkQ (iQ x) = 0 :=
        LinearMap.mem_ker.mp hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxq
      obtain ⟨y, hy⟩ := hxq
      have hxy : x = y.1 := by
        apply infToRightLinearMap_injective P Q
        exact hy.symm
      exact hxy ▸ y.2
    · intro hx
      apply LinearMap.mem_ker.mpr
      change sQ.range.mkQ (iQ x) = 0
      rw [show iQ x = sQ ⟨x, hx⟩ by rfl]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (show sQ ⟨x, hx⟩ ∈ sQ.range from ⟨⟨x, hx⟩, rfl⟩)
  have htIrange : tI.range = g.ker := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change g (sQ.range.mkQ (iQ x)) = 0
      rw [hg_apply]
      change P.mkQ x.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2.1
    · intro y hy
      obtain ⟨q, rfl⟩ := sQ.range.mkQ_surjective y
      have hqzero : qP q = 0 := by
        have := LinearMap.mem_ker.mp hy
        rw [hg_apply] at this
        exact this
      have hqP : q.1 ∈ P := by
        change P.mkQ q.1 = 0 at hqzero
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hqzero
        exact hqzero
      let x : I := ⟨q.1, hqP, q.2⟩
      exact ⟨x, rfl⟩
  let eQuotRange : (I ⧸ K) ≃ₗ[Aᵐᵒᵖ] tI.range :=
    (Submodule.quotEquivOfEq K tI.ker htIker.symm).trans
      tI.quotKerEquivRange
  let eRangeKer : tI.range ≃ₗ[Aᵐᵒᵖ] g.ker :=
    LinearEquiv.ofEq _ _ htIrange
  let eQuotT : (I ⧸ K) ≃ₗ[Aᵐᵒᵖ] T :=
    K.quotientEquivOfIsCompl T hcompl
  let eKerT : g.ker ≃ₗ[Aᵐᵒᵖ] T :=
    eRangeKer.symm.trans (eQuotRange.symm.trans eQuotT)
  refine ⟨?_, ⟨eKerT⟩⟩
  letI : IsSimpleModule Aᵐᵒᵖ T := hTsimple
  exact IsSimpleModule.congr eKerT

/-- The left-hand version of
`crossBranchQuotientProjection_simple_kernel`. -/
theorem crossBranchLeftQuotientProjection_simple_kernel
    (L : FinitelyGeneratedCategory A)
    (P Q : Submodule Aᵐᵒᵖ L)
    (K T : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L))
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hcompl : IsCompl K T) :
    IsSimpleModule Aᵐᵒᵖ
        (crossBranchLeftQuotientProjection L P Q K).ker ∧
      Nonempty
        ((crossBranchLeftQuotientProjection L P Q K).ker ≃ₗ[Aᵐᵒᵖ] T) := by
  let I : Submodule Aᵐᵒᵖ L := P ⊓ Q
  let iP : I →ₗ[Aᵐᵒᵖ] P := infToLeftLinearMap P Q
  let sP : K →ₗ[Aᵐᵒᵖ] P := infSubmoduleToLeftLinearMap P Q K
  let qQ : P →ₗ[Aᵐᵒᵖ] quotientFGObj L Q :=
    Q.mkQ.comp P.subtype
  have hsPqQ : sP.range ≤ qQ.ker := by
    rintro y ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    change Q.mkQ x.1.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.1.2.2
  let Mbar := quotientFGObj (submoduleFGObj L P) sP.range
  let g : Mbar →ₗ[Aᵐᵒᵖ] quotientFGObj L Q :=
    crossBranchLeftQuotientProjection L P Q K
  change IsSimpleModule Aᵐᵒᵖ g.ker ∧
    Nonempty (g.ker ≃ₗ[Aᵐᵒᵖ] T)
  have hg_apply (p : P) : g (sP.range.mkQ p) = qQ p := by
    dsimp only [g, crossBranchLeftQuotientProjection, sP,
      infSubmoduleToLeftLinearMap, qQ]
    exact quotientFGLift_apply_mkQ
      (submoduleFGObj L P) (quotientFGObj L Q)
        (infSubmoduleToLeftLinearMap P Q K).range
        (Q.mkQ.comp P.subtype) _ p
  let tI : I →ₗ[Aᵐᵒᵖ] Mbar :=
    sP.range.mkQ.comp iP
  have htIker : tI.ker = K := by
    ext x
    constructor
    · intro hx
      have hxq : sP.range.mkQ (iP x) = 0 :=
        LinearMap.mem_ker.mp hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxq
      obtain ⟨y, hy⟩ := hxq
      have hxy : x = y.1 := by
        apply infToLeftLinearMap_injective P Q
        exact hy.symm
      exact hxy ▸ y.2
    · intro hx
      apply LinearMap.mem_ker.mpr
      change sP.range.mkQ (iP x) = 0
      rw [show iP x = sP ⟨x, hx⟩ by rfl]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (show sP ⟨x, hx⟩ ∈ sP.range from ⟨⟨x, hx⟩, rfl⟩)
  have htIrange : tI.range = g.ker := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      change g (sP.range.mkQ (iP x)) = 0
      rw [hg_apply]
      change Q.mkQ x.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact x.2.2
    · intro y hy
      obtain ⟨p, rfl⟩ := sP.range.mkQ_surjective y
      have hpzero : qQ p = 0 := by
        have := LinearMap.mem_ker.mp hy
        rw [hg_apply] at this
        exact this
      have hpQ : p.1 ∈ Q := by
        change Q.mkQ p.1 = 0 at hpzero
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hpzero
        exact hpzero
      let x : I := ⟨p.1, p.2, hpQ⟩
      exact ⟨x, rfl⟩
  let eQuotRange : (I ⧸ K) ≃ₗ[Aᵐᵒᵖ] tI.range :=
    (Submodule.quotEquivOfEq K tI.ker htIker.symm).trans
      tI.quotKerEquivRange
  let eRangeKer : tI.range ≃ₗ[Aᵐᵒᵖ] g.ker :=
    LinearEquiv.ofEq _ _ htIrange
  let eQuotT : (I ⧸ K) ≃ₗ[Aᵐᵒᵖ] T :=
    K.quotientEquivOfIsCompl T hcompl
  let eKerT : g.ker ≃ₗ[Aᵐᵒᵖ] T :=
    eRangeKer.symm.trans (eQuotRange.symm.trans eQuotT)
  refine ⟨?_, ⟨eKerT⟩⟩
  letI : IsSimpleModule Aᵐᵒᵖ T := hTsimple
  exact IsSimpleModule.congr eKerT

/-- Gluing one simple summand of a length-two branch intersection gives an
indecomposable cokernel.  Coordinate thinness of the ambient local module
replaces the source's unnecessary branch-length-three reduction. -/
theorem isIndecomposableModule_diagonalInfSummandCokernel_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    (K T : Submodule Aᵐᵒᵖ (P ⊓ Q : Submodule Aᵐᵒᵖ L))
    (hKsimple : IsSimpleModule Aᵐᵒᵖ K)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hcompl : IsCompl K T)
    (hTopPTP : ¬ Nonempty
      ((P ⧸ Module.jacobson Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ]
        T.map (infToLeftLinearMap P Q)))
    (hTopQTQ : ¬ Nonempty
      ((Q ⧸ Module.jacobson Aᵐᵒᵖ Q) ≃ₗ[Aᵐᵒᵖ]
        T.map (infToRightLinearMap P Q))) :
    let I := submoduleFGObj L (P ⊓ Q)
    let S := submoduleFGObj I K
    let C := submoduleFGObj L P
    let D := submoduleFGObj L Q
    let sC : S →ₗ[Aᵐᵒᵖ] C :=
      (infToLeftLinearMap P Q).comp K.subtype
    let sD : S →ₗ[Aᵐᵒᵖ] D :=
      (infToRightLinearMap P Q).comp K.subtype
    let h : S →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ (cokernelFGObj S (prodFGObj C D) h) := by
  let I := submoduleFGObj L (P ⊓ Q)
  let S := submoduleFGObj I K
  let C := submoduleFGObj L P
  let D := submoduleFGObj L Q
  let sC : S →ₗ[Aᵐᵒᵖ] C :=
    (infToLeftLinearMap P Q).comp K.subtype
  let sD : S →ₗ[Aᵐᵒᵖ] D :=
    (infToRightLinearMap P Q).comp K.subtype
  let h : S →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
  letI : Nontrivial S := hKsimple.nontrivial
  have hsC : Function.Injective sC :=
    (infToLeftLinearMap_injective P Q).comp K.subtype_injective
  have hsD : Function.Injective sD :=
    (infToRightLinearMap_injective P Q).comp K.subtype_injective
  let eTTP : T ≃ₗ[Aᵐᵒᵖ] T.map (infToLeftLinearMap P Q) :=
    submoduleMapLinearEquivOfInjective
      (infToLeftLinearMap P Q) (infToLeftLinearMap_injective P Q) T
  let eTTQ : T ≃ₗ[Aᵐᵒᵖ] T.map (infToRightLinearMap P Q) :=
    submoduleMapLinearEquivOfInjective
      (infToRightLinearMap P Q) (infToRightLinearMap_injective P Q) T
  let gQ := crossBranchQuotientProjection L P Q K
  obtain ⟨hgQsimple, ⟨egQT⟩⟩ :=
    crossBranchQuotientProjection_simple_kernel L P Q K T
      hTsimple hcompl
  have hTopPgQ : ¬ Nonempty
      ((P ⧸ Module.jacobson Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ] gQ.ker) := by
    rintro ⟨u⟩
    exact hTopPTP ⟨u.trans (egQT.trans eTTP)⟩
  let gP := crossBranchLeftQuotientProjection L P Q K
  obtain ⟨hgPsimple, ⟨egPT⟩⟩ :=
    crossBranchLeftQuotientProjection_simple_kernel L P Q K T
      hTsimple hcompl
  have hTopQgP : ¬ Nonempty
      ((Q ⧸ Module.jacobson Aᵐᵒᵖ Q) ≃ₗ[Aᵐᵒᵖ] gP.ker) := by
    rintro ⟨u⟩
    exact hTopQTQ ⟨u.trans (egPT.trans eTTQ)⟩
  apply isIndecomposableModule_diagonalCokernel_of_crossHom_eq_zero
    S C D sC sD hsC hsD
  · exact IsUniserialModule.isIndecomposableModule_of_simpleTop hPtop
  · exact IsUniserialModule.isIndecomposableModule_of_simpleTop hQtop
  · intro f
    exact linearMap_to_crossBranch_eq_zero_of_coordinateThin
      (k := k) e hall L hL P hPtop _ gQ hgQsimple hTopPgQ f
  · intro f
    exact linearMap_to_crossBranch_eq_zero_of_coordinateThin
      (k := k) e hall L hL Q hQtop _ gP hgPsimple hTopQgP f

end MagnitudeConjecture.RightModule
