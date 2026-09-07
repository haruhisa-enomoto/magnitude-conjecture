import MagnitudeConjecture.Algebra.BiserialCommonRadicalExtension
import MagnitudeConjecture.Algebra.FiniteLengthSemisimple
import Mathlib.LinearAlgebra.Projection

/-!
# Branch placement in a coordinate-thin biserial sum

After quotienting the intersection of two submodules, their sum is the
product of the two branch images.  Coordinate thinness then prevents a
simple-top submodule of the sum from projecting nontrivially to both factors.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} {ι : Type w}
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- A branch regarded as a submodule of the sum of two branches. -/
def leftBranchInSup
    (L : FinitelyGeneratedCategory A)
    (U V : Submodule Aᵐᵒᵖ L) :
    Submodule Aᵐᵒᵖ (U ⊔ V : Submodule Aᵐᵒᵖ L) :=
  U.comap (U ⊔ V : Submodule Aᵐᵒᵖ L).subtype

/-- The other branch regarded as a submodule of the sum. -/
def rightBranchInSup
    (L : FinitelyGeneratedCategory A)
    (U V : Submodule Aᵐᵒᵖ L) :
    Submodule Aᵐᵒᵖ (U ⊔ V : Submodule Aᵐᵒᵖ L) :=
  V.comap (U ⊔ V : Submodule Aᵐᵒᵖ L).subtype

/-- The branch intersection regarded inside the branch sum. -/
def branchInfInSup
    (L : FinitelyGeneratedCategory A)
    (U V : Submodule Aᵐᵒᵖ L) :
    Submodule Aᵐᵒᵖ (U ⊔ V : Submodule Aᵐᵒᵖ L) :=
  (U ⊓ V).comap (U ⊔ V : Submodule Aᵐᵒᵖ L).subtype

/-- In the quotient of a branch sum by the branch intersection, the two
branch images are complementary. -/
theorem branchImages_isCompl
    (L : FinitelyGeneratedCategory A)
    (U V : Submodule Aᵐᵒᵖ L) :
    IsCompl
      ((leftBranchInSup L U V).map (branchInfInSup L U V).mkQ)
      ((rightBranchInSup L U V).map (branchInfInSup L U V).mkQ) := by
  let S : Submodule Aᵐᵒᵖ L := U ⊔ V
  let U' : Submodule Aᵐᵒᵖ S := leftBranchInSup L U V
  let V' : Submodule Aᵐᵒᵖ S := rightBranchInSup L U V
  let K : Submodule Aᵐᵒᵖ S := branchInfInSup L U V
  let q : S →ₗ[Aᵐᵒᵖ] (S ⧸ K) := K.mkQ
  have hUVtop : U' ⊔ V' = ⊤ := by
    apply Submodule.map_injective_of_injective S.subtype_injective
    dsimp only [U', V', S, leftBranchInSup, rightBranchInSup]
    rw [Submodule.map_sup, Submodule.map_comap_subtype,
      Submodule.map_comap_subtype]
    simp
  have hKinf : K = U' ⊓ V' := by
    dsimp only [K, U', V', branchInfInSup, leftBranchInSup,
      rightBranchInSup]
    exact (Submodule.comap_inf _ _ _).symm
  have hKleU : K ≤ U' := by rw [hKinf]; exact inf_le_left
  have hKleV : K ≤ V' := by rw [hKinf]; exact inf_le_right
  constructor
  · rw [disjoint_iff]
    apply (Submodule.comap_injective_of_surjective K.mkQ_surjective)
    rw [Submodule.comap_inf, Submodule.comap_map_mkQ,
      Submodule.comap_map_mkQ, Submodule.comap_bot,
      Submodule.ker_mkQ, sup_eq_right.mpr hKleU,
      sup_eq_right.mpr hKleV, ← hKinf]
  · rw [codisjoint_iff, ← Submodule.map_sup, hUVtop]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr K.mkQ_surjective

/-- The quotient of a two-branch sum by the branch intersection is the
product of the two branch images. -/
def branchSupInfQuotientProdLinearEquiv
    (L : FinitelyGeneratedCategory A)
    (U V : Submodule Aᵐᵒᵖ L) :
    quotientFGObj (submoduleFGObj L (U ⊔ V)) (branchInfInSup L U V) ≃ₗ[Aᵐᵒᵖ]
      ((leftBranchInSup L U V).map (branchInfInSup L U V).mkQ ×
        (rightBranchInSup L U V).map (branchInfInSup L U V).mkQ) :=
  (Submodule.prodEquivOfIsCompl
    ((leftBranchInSup L U V).map (branchInfInSup L U V).mkQ)
    ((rightBranchInSup L U V).map (branchInfInSup L U V).mkQ)
    (branchImages_isCompl L U V)).symm

/-- The range of a map from a simple-top module into a coordinate-thin sum
of two branches lies in one branch.  Modulo the branch intersection the sum
is a product; nonzero projections to both factors would repeat a coordinate
of the simple top. -/
theorem linearMap_range_le_left_or_le_right_of_coordinateThin_sup_of_simpleTop
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (U V : Submodule Aᵐᵒᵖ L)
    (E : FinitelyGeneratedCategory A)
    (j : E →ₗ[Aᵐᵒᵖ] L)
    (hj : j.range ≤ U ⊔ V)
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E)) :
    j.range ≤ U ∨ j.range ≤ V := by
  let S : FinitelyGeneratedCategory A := submoduleFGObj L (U ⊔ V)
  let K : Submodule Aᵐᵒᵖ S := branchInfInSup L U V
  let Q : FinitelyGeneratedCategory A := quotientFGObj S K
  let Ubar : Submodule Aᵐᵒᵖ Q :=
    (leftBranchInSup L U V).map K.mkQ
  let Vbar : Submodule Aᵐᵒᵖ Q :=
    (rightBranchInSup L U V).map K.mkQ
  let decomp : Q ≃ₗ[Aᵐᵒᵖ] (Ubar × Vbar) :=
    branchSupInfQuotientProdLinearEquiv L U V
  let decompIso : Q ≅ prodFGObj (submoduleFGObj Q Ubar)
      (submoduleFGObj Q Vbar) :=
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ decomp
  have hQ : IsCoordinateThin (k := k) e Q :=
    (hL.submodule (U ⊔ V)).quotient hall.idem K
  have hprod : IsCoordinateThin (k := k) e
      (prodFGObj (submoduleFGObj Q Ubar) (submoduleFGObj Q Vbar)) :=
    IsCoordinateThin.congr e hall.idem decompIso hQ
  let eToS : E →ₗ[Aᵐᵒᵖ] S :=
    j.codRestrict (U ⊔ V) (fun x ↦ hj ⟨x, rfl⟩)
  let eToQ : E →ₗ[Aᵐᵒᵖ] Q := K.mkQ.comp eToS
  let eToProd : E →ₗ[Aᵐᵒᵖ] (Ubar × Vbar) :=
    decomp.toLinearMap.comp eToQ
  let f : E →ₗ[Aᵐᵒᵖ] submoduleFGObj Q Ubar :=
    (LinearMap.fst Aᵐᵒᵖ Ubar Vbar).comp eToProd
  let g : E →ₗ[Aᵐᵒᵖ] submoduleFGObj Q Vbar :=
    (LinearMap.snd Aᵐᵒᵖ Ubar Vbar).comp eToProd
  rcases linearMap_eq_zero_or_eq_zero_of_coordinateThin_prod_of_simpleTop
      e hall (submoduleFGObj Q Ubar) (submoduleFGObj Q Vbar)
        hprod E hEtop f g with hf | hg
  · right
    rintro _ ⟨xE, rfl⟩
    have hfst : (decomp (eToQ xE)).1 = 0 := by
      change f xE = 0
      rw [hf]
      rfl
    have hxVbar : eToQ xE ∈ Vbar :=
      (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero
        Ubar Vbar (branchImages_isCompl L U V)).mp hfst
    obtain ⟨v, hvV, hvq⟩ := hxVbar
    have hxsub : eToS xE - v ∈ K := by
      rw [← Submodule.ker_mkQ K]
      apply LinearMap.mem_ker.mpr
      rw [map_sub, sub_eq_zero]
      exact hvq.symm
    have hxV' : eToS xE ∈ rightBranchInSup L U V := by
      have hxsubV : eToS xE - v ∈ rightBranchInSup L U V := by
        apply (show K ≤ rightBranchInSup L U V by
          dsimp only [K, branchInfInSup, rightBranchInSup]
          exact Submodule.comap_mono inf_le_right)
        exact hxsub
      rw [show eToS xE = (eToS xE - v) + v by abel]
      exact (rightBranchInSup L U V).add_mem hxsubV hvV
    exact hxV'
  · left
    rintro _ ⟨xE, rfl⟩
    have hsnd : (decomp (eToQ xE)).2 = 0 := by
      change g xE = 0
      rw [hg]
      rfl
    have hxUbar : eToQ xE ∈ Ubar :=
      (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
        Ubar Vbar (branchImages_isCompl L U V)).mp hsnd
    obtain ⟨u, huU, huq⟩ := hxUbar
    have hxsub : eToS xE - u ∈ K := by
      rw [← Submodule.ker_mkQ K]
      apply LinearMap.mem_ker.mpr
      rw [map_sub, sub_eq_zero]
      exact huq.symm
    have hxU' : eToS xE ∈ leftBranchInSup L U V := by
      have hxsubU : eToS xE - u ∈ leftBranchInSup L U V := by
        apply (show K ≤ leftBranchInSup L U V by
          dsimp only [K, branchInfInSup, leftBranchInSup]
          exact Submodule.comap_mono inf_le_left)
        exact hxsub
      rw [show eToS xE = (eToS xE - u) + u by abel]
      exact (leftBranchInSup L U V).add_mem hxsubU huU
    exact hxU'

/-- The range of a map from a simple-top module into the radical of a
coordinate-thin biserial module is uniserial.  The map need not be injective:
branch placement is applied to its range in the target. -/
theorem uniserial_range_of_linearMap_of_simpleTop_of_coordinateThin_of_biserial
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (E : FinitelyGeneratedCategory A)
    (j : E →ₗ[Aᵐᵒᵖ] L)
    (hj : j.range ≤ Module.jacobson Aᵐᵒᵖ L)
    (hEtop : IsSimpleModule Aᵐᵒᵖ
      (E ⧸ Module.jacobson Aᵐᵒᵖ E))
    (hLbis : IsBiserialModule Aᵐᵒᵖ L) :
    IsUniserialModule Aᵐᵒᵖ j.range := by
  rcases hLbis with ⟨U, V, hsup, hU, hV, -⟩
  have hjSup : j.range ≤ U ⊔ V := by
    rw [hsup]
    exact hj
  rcases linearMap_range_le_left_or_le_right_of_coordinateThin_sup_of_simpleTop
      e hall L hL U V E j hjSup hEtop with hjU | hjV
  · exact IsUniserialModule.of_injective hU
      (Submodule.inclusion hjU) (Submodule.inclusion_injective hjU)
  · exact IsUniserialModule.of_injective hV
      (Submodule.inclusion hjV) (Submodule.inclusion_injective hjV)

/-- The image of a simple-top radical submodule in a coordinate-thin
biserial quotient is uniserial. -/
theorem uniserial_map_quotient_of_simpleTop_submodule_of_coordinateThin_of_biserial
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (S P : Submodule Aᵐᵒᵖ L)
    (hS : S ≤ Module.jacobson Aᵐᵒᵖ L)
    (hP : P ≤ Module.jacobson Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hquotBis : IsBiserialModule Aᵐᵒᵖ (quotientFGObj L S)) :
    IsUniserialModule Aᵐᵒᵖ (P.map S.mkQ) := by
  let Q : FinitelyGeneratedCategory A := quotientFGObj L S
  let j : P →ₗ[Aᵐᵒᵖ] Q := S.mkQ.comp P.subtype
  have hjrange : j.range = P.map S.mkQ := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hj : j.range ≤ Module.jacobson Aᵐᵒᵖ Q := by
    rw [hjrange]
    change P.map S.mkQ ≤
      Module.jacobson Aᵐᵒᵖ (quotientFGObj L S)
    rw [show Module.jacobson Aᵐᵒᵖ (quotientFGObj L S) =
        (Module.jacobson Aᵐᵒᵖ L).map S.mkQ by
      exact Module.jacobson_quotient_of_le hS]
    exact Submodule.map_mono hP
  have hQthin : IsCoordinateThin (k := k) e Q :=
    hL.quotient hall.idem S
  rw [← hjrange]
  exact
    uniserial_range_of_linearMap_of_simpleTop_of_coordinateThin_of_biserial
      e hall Q hQthin (submoduleFGObj L P) j hj hPtop hquotBis

/-- Images of two submodules under a map are comparable when the full range
of the map is uniserial. -/
theorem map_le_map_or_map_le_map_of_uniserial_range
    {R : Type*} [Ring R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : IsUniserialModule R f.range)
    (P Q : Submodule R M) :
    P.map f ≤ Q.map f ∨ Q.map f ≤ P.map f := by
  let P' : Submodule R f.range := (P.map f).comap f.range.subtype
  let Q' : Submodule R f.range := (Q.map f).comap f.range.subtype
  have hPle : P.map f ≤ f.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hQle : Q.map f ≤ f.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hPmap : P'.map f.range.subtype = P.map f := by
    dsimp only [P']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPle]
  have hQmap : Q'.map f.range.subtype = Q.map f := by
    dsimp only [Q']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQle]
  rcases hf.total P' Q' with hPQ | hQP
  · left
    rw [← hPmap, ← hQmap]
    exact Submodule.map_mono hPQ
  · right
    rw [← hQmap, ← hPmap]
    exact Submodule.map_mono hQP

/-- Two disjoint submodules remain disjoint after quotienting the ambient
module by its socle.  An element that could identify the two images would
give a socle element in their direct sum, whose two coordinates already lie
in the intrinsic socles and hence vanish in the ambient socle quotient. -/
theorem inf_map_quotient_moduleSocle_eq_bot_of_inf_eq_bot
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (P Q : Submodule R M)
    (hinf : P ⊓ Q = ⊥) :
    P.map (moduleSocle R M).mkQ ⊓
        Q.map (moduleSocle R M).mkQ = ⊥ := by
  let S : Submodule R M := moduleSocle R M
  let T : Submodule R M := P ⊔ Q
  let ePQ : (P × Q) ≃ₗ[R] T :=
    submoduleProdSupLinearEquiv P Q hinf
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨p, hpP, hpx⟩ := hx.1
  obtain ⟨q, hqQ, hqx⟩ := hx.2
  have hpqS : p - q ∈ S := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change (moduleSocle R M).mkQ (p - q) = 0
    rw [map_sub, hpx, hqx, sub_self]
  let pP : P := ⟨p, hpP⟩
  let qQ : Q := ⟨q, hqQ⟩
  let yT : T := ⟨p - q, T.sub_mem
    ((show P ≤ T from le_sup_left) hpP)
    ((show Q ≤ T from le_sup_right) hqQ)⟩
  have hySocT : yT ∈ moduleSocle R T := by
    rw [← comap_moduleSocle_subtype_eq_moduleSocle T]
    exact hpqS
  have hyBack : ePQ.symm yT ∈ moduleSocle R (P × Q) := by
    have hyMap : yT ∈
        (moduleSocle R (P × Q)).map ePQ.toLinearMap := by
      rw [map_moduleSocle_eq_of_linearEquiv ePQ]
      exact hySocT
    obtain ⟨z, hz, hzy⟩ := hyMap
    have hzEq : z = ePQ.symm yT := by
      apply ePQ.injective
      rw [ePQ.apply_symm_apply]
      exact hzy
    rw [← hzEq]
    exact hz
  have hePQ : ePQ.symm yT = (pP, -qQ) := by
    apply ePQ.injective
    rw [ePQ.apply_symm_apply]
    apply Subtype.ext
    change p - q = p + -q
    exact sub_eq_add_neg p q
  have hpqSoc : (pP, -qQ) ∈
      (moduleSocle R P).prod (moduleSocle R Q) := by
    rw [← moduleSocle_prod, ← hePQ]
    exact hyBack
  have hpSoc : pP ∈ moduleSocle R P := hpqSoc.1
  have hpAmbient : p ∈ S := by
    rw [show moduleSocle R P =
        (moduleSocle R M).comap P.subtype by
      exact (comap_moduleSocle_subtype_eq_moduleSocle P).symm] at hpSoc
    exact hpSoc
  change x = 0
  rw [← hpx, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hpAmbient

/-- In a coordinate-thin module, two submodules whose intersection lies in
the socle have disjoint images after quotienting by that socle.  Otherwise a
nonzero coordinate in the common quotient image would occur in both
submodules, while their actual intersection has zero contribution in that
coordinate. -/
theorem inf_map_quotient_moduleSocle_eq_bot_of_coordinateThin_of_inf_le
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hinf : P ⊓ Q ≤ moduleSocle Aᵐᵒᵖ L) :
    P.map (moduleSocle Aᵐᵒᵖ L).mkQ ⊓
        Q.map (moduleSocle Aᵐᵒᵖ L).mkQ = ⊥ := by
  let R := Aᵐᵒᵖ
  let S : Submodule R L := moduleSocle R L
  let Lbar : FinitelyGeneratedCategory A := quotientFGObj L S
  let W : Submodule R Lbar := P.map S.mkQ ⊓ Q.map S.mkQ
  by_contra hW
  have hWne : W ≠ ⊥ := by
    intro hbot
    exact hW hbot
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  let WObj : FinitelyGeneratedCategory A := submoduleFGObj Lbar W
  letI : Nontrivial WObj := show Nontrivial W from inferInstance
  obtain ⟨i, hiW⟩ :=
    exists_positive_idempotentCoordinate (k := k) e hall WObj
  have hiLbar : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) Lbar) :=
    idempotentCoordinate_pos_of_injective (k := k) (e i)
      W.subtype W.subtype_injective hiW
  have hiSzero : Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj L S)) = 0 := by
    have hdim := finrank_idempotentCoordinate_eq_add_submodule_quotient
      (k := k) (hall.idem i) L S
    have hthin := hL i
    dsimp only [Lbar] at hiLbar
    omega
  let I : Submodule R L := P ⊓ Q
  let iI : I →ₗ[R] S := Submodule.inclusion hinf
  have hiIzero : Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj L I)) = 0 := by
    by_contra hne
    have hpos : 0 < Module.finrank k
        (idempotentCoordinate (k := k) (e i) (submoduleFGObj L I)) :=
      Nat.pos_of_ne_zero hne
    have hposS : 0 < Module.finrank k
        (idempotentCoordinate (k := k) (e i) (submoduleFGObj L S)) :=
      idempotentCoordinate_pos_of_injective (k := k) (e i)
        iI (Submodule.inclusion_injective hinf) hpos
    omega
  let Pbar : Submodule R Lbar := P.map S.mkQ
  let Qbar : Submodule R Lbar := Q.map S.mkQ
  let wP : W →ₗ[R] Pbar := Submodule.inclusion inf_le_left
  let wQ : W →ₗ[R] Qbar := Submodule.inclusion inf_le_right
  have hiPbar : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj Lbar Pbar)) :=
    idempotentCoordinate_pos_of_injective (k := k) (e i)
      wP (Submodule.inclusion_injective inf_le_left) hiW
  have hiQbar : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj Lbar Qbar)) :=
    idempotentCoordinate_pos_of_injective (k := k) (e i)
      wQ (Submodule.inclusion_injective inf_le_right) hiW
  let pToBar : P →ₗ[R] Pbar :=
    (S.mkQ.comp P.subtype).codRestrict Pbar (by
      intro p
      exact ⟨p.1, p.2, rfl⟩)
  let qToBar : Q →ₗ[R] Qbar :=
    (S.mkQ.comp Q.subtype).codRestrict Qbar (by
      intro q
      exact ⟨q.1, q.2, rfl⟩)
  have hpToBar : Function.Surjective pToBar := by
    rintro ⟨x, p, hp, hpx⟩
    exact ⟨⟨p, hp⟩, Subtype.ext hpx⟩
  have hqToBar : Function.Surjective qToBar := by
    rintro ⟨x, q, hq, hqx⟩
    exact ⟨⟨q, hq⟩, Subtype.ext hqx⟩
  have hiP : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj L P)) :=
    idempotentCoordinate_pos_of_surjective (k := k) (hall.idem i)
      pToBar hpToBar hiPbar
  have hiQ : 0 < Module.finrank k
      (idempotentCoordinate (k := k) (e i) (submoduleFGObj L Q)) :=
    idempotentCoordinate_pos_of_surjective (k := k) (hall.idem i)
      qToBar hqToBar hiQbar
  let PQ : FinitelyGeneratedCategory A :=
    prodFGObj (submoduleFGObj L P) (submoduleFGObj L Q)
  let addPQ : PQ →ₗ[R] L := P.subtype.coprod Q.subtype
  let fstPQ : PQ →ₗ[R] submoduleFGObj L P :=
    LinearMap.fst R (submoduleFGObj L P) (submoduleFGObj L Q)
  let sndPQ : PQ →ₗ[R] submoduleFGObj L Q :=
    LinearMap.snd R (submoduleFGObj L P) (submoduleFGObj L Q)
  letI : Module.Finite k L :=
    finite_over_field_of_finitelyGenerated k A L
  letI : Module.Finite k (submoduleFGObj L I) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj L I)
  letI : Module.Finite k (submoduleFGObj L P) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj L P)
  letI : Module.Finite k (submoduleFGObj L Q) :=
    finite_over_field_of_finitelyGenerated k A (submoduleFGObj L Q)
  letI : Module.Finite k PQ :=
    finite_over_field_of_finitelyGenerated k A PQ
  have hcoordAdd : Function.Injective
      (idempotentCoordinateLinearMap (k := k) (e i) addPQ) := by
    intro x y hxy
    let xP := idempotentCoordinateLinearMap (k := k) (e i) fstPQ x
    let yP := idempotentCoordinateLinearMap (k := k) (e i) fstPQ y
    let xQ := idempotentCoordinateLinearMap (k := k) (e i) sndPQ x
    let yQ := idempotentCoordinateLinearMap (k := k) (e i) sndPQ y
    have hsum : (xP.1.1 : L) + xQ.1.1 =
        (yP.1.1 : L) + yQ.1.1 := by
      dsimp only [xP, yP, xQ, yQ, fstPQ, sndPQ,
        idempotentCoordinateLinearMap]
      exact congrArg
        (fun z : idempotentCoordinate (k := k) (e i) L ↦ (z.1 : L)) hxy
    have hpq : (xP.1.1 : L) - yP.1.1 =
        -((xQ.1.1 : L) - yQ.1.1) := by
      rw [neg_sub, sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hsum
    let zI : I := ⟨(xP.1.1 : L) - yP.1.1,
      ⟨P.sub_mem xP.1.2 yP.1.2,
        hpq ▸ Q.neg_mem (Q.sub_mem xQ.1.2 yQ.1.2)⟩⟩
    have hzFixed : (MulOpposite.op (e i)) • zI = zI := by
      apply Subtype.ext
      change (MulOpposite.op (e i)) •
          ((xP.1.1 : L) - yP.1.1) =
        (xP.1.1 : L) - yP.1.1
      have hxFixed := idempotentCoordinate_fixed
        (k := k) (hall.idem i) (submoduleFGObj L P) xP
      have hyFixed := idempotentCoordinate_fixed
        (k := k) (hall.idem i) (submoduleFGObj L P) yP
      change (MulOpposite.op (e i)) • (xP.1 : P) = xP.1 at hxFixed
      change (MulOpposite.op (e i)) • (yP.1 : P) = yP.1 at hyFixed
      have hxPval := congrArg P.subtype hxFixed
      have hyPval := congrArg P.subtype hyFixed
      change (MulOpposite.op (e i)) • (xP.1.1 : L) = xP.1.1 at hxPval
      change (MulOpposite.op (e i)) • (yP.1.1 : L) = yP.1.1 at hyPval
      rw [smul_sub, hxPval, hyPval]
    let zCoord : idempotentCoordinate (k := k) (e i)
        (submoduleFGObj L I) := ⟨zI, ⟨zI, hzFixed⟩⟩
    have hzZero : zCoord = 0 :=
      (finrank_zero_iff_forall_zero.mp hiIzero) zCoord
    have hpZero : (xP.1.1 : L) - yP.1.1 = 0 := by
      exact congrArg (fun z : idempotentCoordinate (k := k) (e i)
        (submoduleFGObj L I) ↦ (z.1.1 : L)) hzZero
    have hqZero : (xQ.1.1 : L) - yQ.1.1 = 0 := by
      rw [hpZero] at hpq
      simpa using congrArg Neg.neg hpq.symm
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (xP.1.1 : L) = yP.1.1
      exact sub_eq_zero.mp hpZero
    · apply Subtype.ext
      change (xQ.1.1 : L) = yQ.1.1
      exact sub_eq_zero.mp hqZero
  have hle := LinearMap.finrank_le_finrank_of_injective hcoordAdd
  have hprod := finrank_idempotentCoordinate_prod
    (k := k) (e i) (submoduleFGObj L P) (submoduleFGObj L Q)
  have hthin := hL i
  rw [hprod] at hle
  omega

/-- Submodules contained in one uniserial submodule are comparable in the
ambient module. -/
theorem le_or_le_of_le_of_le_of_uniserial_submodule
    {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (U P Q : Submodule R M)
    (hU : IsUniserialModule R U)
    (hP : P ≤ U) (hQ : Q ≤ U) :
    P ≤ Q ∨ Q ≤ P := by
  let P' : Submodule R U := P.comap U.subtype
  let Q' : Submodule R U := Q.comap U.subtype
  have hPmap : P'.map U.subtype = P := by
    dsimp only [P']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hP]
  have hQmap : Q'.map U.subtype = Q := by
    dsimp only [Q']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQ]
  rcases hU.total P' Q' with hPQ | hQP
  · left
    rw [← hPmap, ← hQmap]
    exact Submodule.map_mono hPQ
  · right
    rw [← hQmap, ← hPmap]
    exact Submodule.map_mono hQP

/-- If two uniserial branches lie in a submodule whose image in the ambient
socle quotient is uniserial, then a terminal branch has only a simple,
disjoint companion branch.  The companion vanishes in the socle quotient
and can therefore be removed without changing the terminal branch. -/
theorem simple_disjoint_otherBranch_of_terminal_in_uniserial_socleQuotient
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P E V : Submodule Aᵐᵒᵖ L)
    (hEP : E ≤ P) (hVP : V ≤ P)
    (hPbar : IsUniserialModule Aᵐᵒᵖ
      (P.map (moduleSocle Aᵐᵒᵖ L).mkQ))
    (hEuni : IsUniserialModule Aᵐᵒᵖ E)
    (hVuni : IsUniserialModule Aᵐᵒᵖ V)
    (hEne : E ≠ ⊥)
    (hEnonsimple : ¬ IsSimpleModule Aᵐᵒᵖ E)
    (hinf : IsSimpleOrZeroModule Aᵐᵒᵖ
      ↥(E ⊓ V : Submodule Aᵐᵒᵖ L))
    (hVnotle : ¬ V ≤ E) :
    IsSimpleModule Aᵐᵒᵖ V ∧ E ⊓ V = ⊥ ∧
      V ≤ moduleSocle Aᵐᵒᵖ L := by
  let R := Aᵐᵒᵖ
  let S : Submodule R L := moduleSocle R L
  let Lbar : FinitelyGeneratedCategory A := quotientFGObj L S
  let Ebar : Submodule R Lbar := E.map S.mkQ
  let Vbar : Submodule R Lbar := V.map S.mkQ
  let Pbar : Submodule R Lbar := P.map S.mkQ
  have hinfSoc : E ⊓ V ≤ S := by
    rcases hinf with hzero | hsimple
    · have hbot : E ⊓ V = ⊥ :=
        Submodule.subsingleton_iff_eq_bot.mp hzero
      rw [hbot]
      exact bot_le
    · exact le_moduleSocle_of_simple (E ⊓ V) hsimple
  have hbarDisj : Ebar ⊓ Vbar = ⊥ :=
    inf_map_quotient_moduleSocle_eq_bot_of_coordinateThin_of_inf_le
      e hall L hL E V hinfSoc
  have hEbarPbar : Ebar ≤ Pbar := Submodule.map_mono hEP
  have hVbarPbar : Vbar ≤ Pbar := Submodule.map_mono hVP
  have hbarComp : Ebar ≤ Vbar ∨ Vbar ≤ Ebar :=
    le_or_le_of_le_of_le_of_uniserial_submodule
      Pbar Ebar Vbar hPbar hEbarPbar hVbarPbar
  have hEbarNe : Ebar ≠ ⊥ := by
    intro hbot
    have hES : E ≤ S := by
      intro x hx
      have hxmap : S.mkQ x ∈ Ebar := ⟨x, hx, rfl⟩
      have hxzero : S.mkQ x = 0 := by
        rw [hbot] at hxmap
        exact hxmap
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxzero
      exact hxzero
    let iE : E →ₗ[R] S := Submodule.inclusion hES
    letI : IsSemisimpleModule R S := moduleSocle_isSemisimple
    letI : IsSemisimpleModule R E :=
      IsSemisimpleModule.of_injective iE
        (Submodule.inclusion_injective hES)
    letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hEne
    exact hEnonsimple
      (IsUniserialModule.isSimpleModule_of_semisimple_of_isIndecomposableModule
        hEuni.isIndecomposableModule)
  have hVbarBot : Vbar = ⊥ := by
    rcases hbarComp with hEV | hVE
    · have hEbot : Ebar = ⊥ := by
        rw [← hbarDisj, inf_eq_left.mpr hEV]
      exact (hEbarNe hEbot).elim
    · rw [← hbarDisj, inf_eq_right.mpr hVE]
  have hVS : V ≤ S := by
    intro x hx
    have hxmap : S.mkQ x ∈ Vbar := ⟨x, hx, rfl⟩
    have hxzero : S.mkQ x = 0 := by
      rw [hVbarBot] at hxmap
      exact hxmap
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxzero
    exact hxzero
  have hVne : V ≠ ⊥ := by
    intro hbot
    exact hVnotle (hbot ▸ bot_le)
  let iV : V →ₗ[R] S := Submodule.inclusion hVS
  letI : IsSemisimpleModule R S := moduleSocle_isSemisimple
  letI : IsSemisimpleModule R V :=
    IsSemisimpleModule.of_injective iV
      (Submodule.inclusion_injective hVS)
  letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hVne
  have hVsimple : IsSimpleModule R V :=
    IsUniserialModule.isSimpleModule_of_semisimple_of_isIndecomposableModule
      hVuni.isIndecomposableModule
  letI : IsSimpleModule R V := hVsimple
  have hinfBot : E ⊓ V = ⊥ := by
    let IV : Submodule R V := (E ⊓ V).comap V.subtype
    rcases IsSimpleOrder.eq_bot_or_eq_top IV with hbot | htop
    · apply le_antisymm
      · intro x hx
        have hxIV : (⟨x, hx.2⟩ : V) ∈ IV := hx
        have hxzero : (⟨x, hx.2⟩ : V) = 0 := by
          have : (⟨x, hx.2⟩ : V) ∈ (⊥ : Submodule R V) := hbot ▸ hxIV
          simpa using this
        exact congrArg Subtype.val hxzero
      · exact bot_le
    · exfalso
      apply hVnotle
      intro v hv
      have hvIV : (⟨v, hv⟩ : V) ∈ IV := htop.symm ▸ Submodule.mem_top
      exact hvIV.1
  exact ⟨hVsimple, hinfBot, hVS⟩

/-- A nonsimple uniserial submodule properly contained in a local biserial
side has one of the two carrier forms needed by the common-radical
obstruction.  Either it has an ambient uniserial immediate successor, or a
simple companion branch can be quotiented out; in the latter case the
resulting uniserial carrier has the same top as the original side. -/
theorem exists_ambient_or_quotient_commonRadicalCarrier
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P E : Submodule Aᵐᵒᵖ L)
    (hEP : E < P)
    (hEne : E ≠ ⊥)
    (hEnonsimple : ¬ IsSimpleModule Aᵐᵒᵖ E)
    (hEuni : IsUniserialModule Aᵐᵒᵖ E)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hPbis : IsBiserialModule Aᵐᵒᵖ P)
    (hPbar : IsUniserialModule Aᵐᵒᵖ
      (P.map (moduleSocle Aᵐᵒᵖ L).mkQ)) :
    (∃ C : Submodule Aᵐᵒᵖ L,
      E ⋖ C ∧ C ≤ P ∧ IsUniserialModule Aᵐᵒᵖ C ∧
        E.comap C.subtype = Module.jacobson Aᵐᵒᵖ C) ∨
    (∃ C : FinitelyGeneratedCategory A,
      ∃ iC : E →ₗ[Aᵐᵒᵖ] C,
        Function.Injective iC ∧
          iC.range = Module.jacobson Aᵐᵒᵖ C ∧
          IsUniserialModule Aᵐᵒᵖ C ∧
          IsCoordinateThin (k := k) e C ∧
          IsSimpleModule Aᵐᵒᵖ
            (C ⧸ Module.jacobson Aᵐᵒᵖ C) ∧
          Nonempty
            ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
              (P ⧸ Module.jacobson Aᵐᵒᵖ P))) := by
  let R := Aᵐᵒᵖ
  let S : Submodule R L := moduleSocle R L
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hEne
  have hEtop : IsSimpleModule R (E ⧸ Module.jacobson R E) :=
    hEuni.top_isSimple
  let EP : Submodule R P := E.comap P.subtype
  have hEPproper : EP ≠ ⊤ := by
    intro htop
    apply hEP.ne
    apply le_antisymm
    · exact hEP.le
    · intro x hx
      have hxEP : (⟨x, hx⟩ : P) ∈ EP :=
        htop.symm ▸ Submodule.mem_top
      exact hxEP
  have hEPjac : EP ≤ Module.jacobson R P :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
      hPtop hEPproper
  rcases hPbis with ⟨U, V, hsup, hUuni, hVuni, hinter⟩
  let Ubar : Submodule R L := U.map P.subtype
  let Vbar : Submodule R L := V.map P.subtype
  have hEsup : E ≤ Ubar ⊔ Vbar := by
    rw [← Submodule.map_sup, hsup]
    intro x hx
    exact ⟨⟨x, hEP.le hx⟩, hEPjac hx, rfl⟩
  let jE : submoduleFGObj L E →ₗ[Aᵐᵒᵖ] L := {
    toFun := fun x ↦ x.1
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hjErange : jE.range = E := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hplacement : E ≤ Ubar ∨ E ≤ Vbar := by
    have h :=
      linearMap_range_le_left_or_le_right_of_coordinateThin_sup_of_simpleTop
        e hall L hL Ubar Vbar (submoduleFGObj L E) jE (by
          rw [hjErange]
          exact hEsup) hEtop
    rw [hjErange] at h
    exact h
  have build (U V : Submodule R P)
      (hsup : U ⊔ V = Module.jacobson R P)
      (hUuni : IsUniserialModule R U)
      (hVuni : IsUniserialModule R V)
      (hinter : IsSimpleOrZeroModule R
        ↥(U ⊓ V : Submodule R P))
      (hEU : E ≤ U.map P.subtype) :
      (∃ C : Submodule R L,
        E ⋖ C ∧ C ≤ P ∧ IsUniserialModule R C ∧
          E.comap C.subtype = Module.jacobson R C) ∨
      (∃ C : FinitelyGeneratedCategory A,
        ∃ iC : E →ₗ[R] C,
          Function.Injective iC ∧
            iC.range = Module.jacobson R C ∧
            IsUniserialModule R C ∧
            IsCoordinateThin (k := k) e C ∧
            IsSimpleModule R (C ⧸ Module.jacobson R C) ∧
            Nonempty
              ((C ⧸ Module.jacobson R C) ≃ₗ[R]
                (P ⧸ Module.jacobson R P))) := by
    let Ubar : Submodule R L := U.map P.subtype
    let Vbar : Submodule R L := V.map P.subtype
    let eUbar : U ≃ₗ[R] Ubar :=
      submoduleMapLinearEquivOfInjective
        P.subtype P.subtype_injective U
    let eVbar : V ≃ₗ[R] Vbar :=
      submoduleMapLinearEquivOfInjective
        P.subtype P.subtype_injective V
    have hUbaruni : IsUniserialModule R Ubar :=
      IsUniserialModule.congr eUbar hUuni
    have hVbaruni : IsUniserialModule R Vbar :=
      IsUniserialModule.congr eVbar hVuni
    rcases hEU.eq_or_lt with hEUeq | hEUlt
    · by_cases hVE : Vbar ≤ E
      · left
        have hEUeq' : E = Ubar := hEUeq
        have hmapRad :
            (Module.jacobson R P).map P.subtype = E := by
          calc
            (Module.jacobson R P).map P.subtype = Ubar ⊔ Vbar := by
              rw [← hsup, Submodule.map_sup]
            _ = E := by
              rw [← hEUeq', sup_eq_left.mpr hVE]
        have hEPrad : E.comap P.subtype = Module.jacobson R P := by
          apply Submodule.map_injective_of_injective
            P.subtype_injective
          rw [Submodule.map_comap_subtype,
            inf_eq_right.mpr hEP.le, hmapRad]
        let eEP : EP ≃ₗ[R] E :=
          Submodule.comapSubtypeEquivOfLe hEP.le
        have hEPuni : IsUniserialModule R EP :=
          IsUniserialModule.congr eEP.symm hEuni
        have hPraduni :
            IsUniserialModule R (Module.jacobson R P) := by
          rw [← hEPrad]
          exact hEPuni
        have hPuni : IsUniserialModule R P :=
          IsUniserialModule.of_simpleTop_of_jacobson
            hPtop hPraduni
        have hEPcov : E ⋖ P := by
          apply (covBy_iff_quot_is_simple hEP.le).2
          rw [hEPrad]
          exact hPtop
        exact ⟨P, hEPcov, le_rfl, hPuni, hEPrad⟩
      · right
        have hEUeq' : E = Ubar := hEUeq
        let eInf : (↥(U ⊓ V : Submodule R P)) ≃ₗ[R]
            ↥(Ubar ⊓ Vbar : Submodule R L) :=
          (submoduleMapLinearEquivOfInjective
              P.subtype P.subtype_injective (U ⊓ V)).trans
            (LinearEquiv.ofEq _ _
              (Submodule.map_inf P.subtype P.subtype_injective))
        have hinterBar : IsSimpleOrZeroModule R
            ↥(E ⊓ Vbar : Submodule R L) := by
          have h := IsSimpleOrZeroModule.congr eInf hinter
          rw [hEUeq']
          exact h
        obtain ⟨hVsimple, hEVbot, -⟩ :=
          simple_disjoint_otherBranch_of_terminal_in_uniserial_socleQuotient
            e hall L hL P E Vbar hEP.le
              (Submodule.map_subtype_le P V) hPbar hEuni hVbaruni
              hEne hEnonsimple hinterBar hVE
        have hUVbot : U ⊓ V = ⊥ := by
          apply Submodule.map_injective_of_injective
            P.subtype_injective
          rw [Submodule.map_inf P.subtype P.subtype_injective,
            Submodule.map_bot, ← hEUeq]
          exact hEVbot
        have hVrad : V ≤ Module.jacobson R P := by
          rw [← hsup]
          exact le_sup_right
        let eUE : U ≃ₗ[R] E :=
          eUbar.trans (LinearEquiv.ofEq Ubar E hEUeq'.symm)
        let j : U →ₗ[R] (P ⧸ V) :=
          IsBiserialModule.submoduleToQuotientLinearMap U V
        let iC : E →ₗ[R] (P ⧸ V) :=
          j.comp eUE.symm.toLinearMap
        have hj : Function.Injective j :=
          IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
            U V hUVbot
        have hiC : Function.Injective iC :=
          hj.comp eUE.symm.injective
        have hjrange : j.range = U.map V.mkQ := by
          ext x
          constructor
          · rintro ⟨u, rfl⟩
            exact ⟨u.1, u.2, rfl⟩
          · rintro ⟨u, hu, rfl⟩
            exact ⟨⟨u, hu⟩, rfl⟩
        have hiCrange : iC.range = Module.jacobson R (P ⧸ V) := by
          calc
            iC.range = j.range := by
              exact LinearMap.range_comp_of_range_eq_top j
                (LinearEquiv.range eUE.symm)
            _ = U.map V.mkQ := hjrange
            _ = Module.jacobson R (P ⧸ V) :=
              (IsBiserialModule.jacobson_quotient_eq_map_of_jacobson_eq_sup
                U V hsup).symm
        have hCuni : IsUniserialModule R (P ⧸ V) :=
          IsBiserialModule.uniserial_quotient_of_jacobson_eq_sup_of_inf_eq_bot
            U V hPtop hsup hUVbot hUuni
        have hCthin : IsCoordinateThin (k := k) e
            (quotientFGObj (submoduleFGObj L P) V) :=
          (hL.submodule P).quotient hall.idem V
        have hCtop : IsSimpleModule R
            ((P ⧸ V) ⧸ Module.jacobson R (P ⧸ V)) :=
          isSimpleModule_top_quotient_of_le_jacobson V hVrad hPtop
        exact ⟨quotientFGObj (submoduleFGObj L P) V,
          iC, hiC, hiCrange, hCuni, hCthin, hCtop,
          ⟨moduleTopQuotientLinearEquiv
            (submoduleFGObj L P) V hVrad⟩⟩
    · left
      obtain ⟨C, hEC, hCU, hCuni, hCrad⟩ :=
        IsUniserialModule.exists_covBy_le_with_comap_eq_jacobson
          Ubar hUbaruni hEUlt
      exact ⟨C, hEC, hCU.trans (Submodule.map_subtype_le P U),
        hCuni, hCrad⟩
  rcases hplacement with hEU | hEV
  · exact build U V hsup hUuni hVuni hinter hEU
  · have hsup' : V ⊔ U = Module.jacobson Aᵐᵒᵖ P := by
      rw [sup_comm]
      exact hsup
    have hinter' : IsSimpleOrZeroModule Aᵐᵒᵖ
        ↥(V ⊓ U : Submodule Aᵐᵒᵖ P) := by
      rw [inf_comm]
      exact hinter
    exact build V U hsup' hVuni hUuni hinter' hEV

/-- A nonsemisimple intersection properly contained in a biserial side has
a maximal nonsimple uniserial submodule in the ambient module.  The
biseriality hypothesis is needed only on the side, not on the ambient
module whose coordinate thinness performs the branch placement. -/
theorem exists_maximal_nonsimple_uniserial_submodule_le_of_biserial_side
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P I : Submodule Aᵐᵒᵖ L)
    (hIP : I < P)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hPbis : IsBiserialModule Aᵐᵒᵖ P)
    (hInot : ¬ IsSemisimpleModule Aᵐᵒᵖ I) :
    ∃ E : Submodule Aᵐᵒᵖ L,
      E ≤ I ∧
        Foundation.IsIndecomposableModule Aᵐᵒᵖ E ∧
        ¬ IsSimpleModule Aᵐᵒᵖ E ∧
        IsUniserialModule Aᵐᵒᵖ E ∧
        ∀ F : Submodule Aᵐᵒᵖ L, E ≤ F → F ≤ I →
          ¬ IsSimpleModule Aᵐᵒᵖ F →
          IsUniserialModule Aᵐᵒᵖ F → F = E := by
  let R := Aᵐᵒᵖ
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  obtain ⟨E₀, hE₀ind, hE₀nonsimple, hE₀top⟩ :=
    exists_nonsimple_indecomposable_simpleTop_submodule_of_not_semisimple
      hInot
  let E₀Obj : FinitelyGeneratedCategory A :=
    submoduleFGObj (submoduleFGObj L I) E₀
  let jL : E₀Obj →ₗ[R] L := {
    toFun := fun x ↦ x.1.1
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  let jP : E₀Obj →ₗ[R] P := {
    toFun := fun x ↦ ⟨x.1.1, hIP.le x.1.2⟩
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hjL : Function.Injective jL := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hjP : Function.Injective jP := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P ↦ (z : L)) hxy
  have hjLI : jL.range ≤ I := by
    rintro _ ⟨x, rfl⟩
    exact x.1.2
  let IP : Submodule R P := I.comap P.subtype
  have hIPproper : IP ≠ ⊤ := by
    intro htop
    apply hIP.ne
    apply le_antisymm
    · exact hIP.le
    · intro x hx
      have hxIP : (⟨x, hx⟩ : P) ∈ IP :=
        htop.symm ▸ Submodule.mem_top
      exact hxIP
  have hIPjac : IP ≤ Module.jacobson R P :=
    IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
      hPtop hIPproper
  have hjPrad : jP.range ≤ Module.jacobson R P := by
    rintro _ ⟨x, rfl⟩
    exact hIPjac x.1.2
  have hjPrangeUni : IsUniserialModule R jP.range :=
    uniserial_range_of_linearMap_of_simpleTop_of_coordinateThin_of_biserial
      e hall (submoduleFGObj L P) (hL.submodule P)
        E₀Obj jP hjPrad hE₀top hPbis
  let eP : E₀Obj ≃ₗ[R] jP.range := LinearEquiv.ofInjective jP hjP
  have hE₀uni : IsUniserialModule R E₀Obj :=
    IsUniserialModule.congr eP.symm hjPrangeUni
  let E : Submodule R L := jL.range
  let eE : E₀Obj ≃ₗ[R] E := LinearEquiv.ofInjective jL hjL
  have hEuni : IsUniserialModule R E :=
    IsUniserialModule.congr eE hE₀uni
  have hEnonsimple : ¬ IsSimpleModule R E := by
    intro hsimple
    letI : IsSimpleModule R E := hsimple
    exact hE₀nonsimple (IsSimpleModule.congr eE)
  let p : Submodule R L → Prop := fun F ↦
    F ≤ I ∧ ¬ IsSimpleModule R F ∧ IsUniserialModule R F
  obtain ⟨Emax, hEEmax, hEmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT p E
      ⟨hjLI, hEnonsimple, hEuni⟩
  have hEne : E ≠ ⊥ := by
    intro hEbot
    have hE₀bot : E₀ = ⊥ := by
      apply le_antisymm
      · intro x hx
        let y : E₀Obj := ⟨x, hx⟩
        have hxrange : jL y ∈ E := ⟨y, rfl⟩
        have hxzero : jL y = 0 := by
          rw [hEbot] at hxrange
          exact hxrange
        have hyzero : y = 0 := hjL hxzero
        exact congrArg Subtype.val hyzero
      · exact bot_le
    exact (Submodule.nontrivial_iff_ne_bot.mp hE₀ind.nontrivial) hE₀bot
  have hEmaxNe : Emax ≠ ⊥ := by
    intro hbot
    apply hEne
    apply le_antisymm
    · have hEmaxBot : Emax ≤ (⊥ : Submodule R L) := by
        rw [hbot]
      exact hEEmax.trans hEmaxBot
    · exact bot_le
  letI : Nontrivial Emax := Submodule.nontrivial_iff_ne_bot.mpr hEmaxNe
  have hEmaxInd : Foundation.IsIndecomposableModule R Emax :=
    hEmax.1.2.2.isIndecomposableModule
  refine ⟨Emax, hEmax.1.1, hEmaxInd, hEmax.1.2.1,
    hEmax.1.2.2, ?_⟩
  intro F hEF hFI hFnonsimple hFuni
  exact (hEmax.eq_of_le ⟨hFI, hFnonsimple, hFuni⟩ hEF).symm

/-- Two coordinate-thin uniserial extensions of the same nonsimple
uniserial radical give the common-radical diagonal-cokernel contradiction.
This endpoint is independent of whether either extension was constructed as
an ambient submodule or as a quotient carrier. -/
theorem false_of_commonRadicalCarriers_of_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (E C D : FinitelyGeneratedCategory A)
    (iC : E →ₗ[Aᵐᵒᵖ] C) (iD : E →ₗ[Aᵐᵒᵖ] D)
    (hiC : Function.Injective iC) (hiD : Function.Injective iD)
    (hiCrange : iC.range = Module.jacobson Aᵐᵒᵖ C)
    (hiDrange : iD.range = Module.jacobson Aᵐᵒᵖ D)
    (hCthin : IsCoordinateThin (k := k) e C)
    (hDthin : IsCoordinateThin (k := k) e D)
    (hEind : Foundation.IsIndecomposableModule Aᵐᵒᵖ E)
    (hEnonsimple : ¬ IsSimpleModule Aᵐᵒᵖ E)
    (hEuni : IsUniserialModule Aᵐᵒᵖ E)
    (hCuni : IsUniserialModule Aᵐᵒᵖ C)
    (hDuni : IsUniserialModule Aᵐᵒᵖ D)
    (hCtopDtop : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        (D ⧸ Module.jacobson Aᵐᵒᵖ D))) :
    False := by
  let R := Aᵐᵒᵖ
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  letI : Nontrivial E := hEind.nontrivial
  have hEtop : IsSimpleModule R (E ⧸ Module.jacobson R E) :=
    hEuni.top_isSimple
  have hEradNe : Module.jacobson R E ≠ ⊥ := by
    intro hrad
    letI : IsSemisimpleModule R E :=
      (IsArtinian.isSemisimpleModule_iff_jacobson R E).mpr hrad
    exact hEnonsimple
      (IsUniserialModule.isSimpleModule_of_semisimple_of_isIndecomposableModule
        hEind)
  letI : Nontrivial (Module.jacobson R E) :=
    Submodule.nontrivial_iff_ne_bot.mpr hEradNe
  letI : Nontrivial C := hiC.nontrivial
  letI : Nontrivial D := hiD.nontrivial
  have hCtop : IsSimpleModule R (C ⧸ Module.jacobson R C) :=
    hCuni.top_isSimple
  have hDtop : IsSimpleModule R (D ⧸ Module.jacobson R D) :=
    hDuni.top_isSimple
  let K := Module.jacobson R E
  let sC : K →ₗ[R] C := iC.comp K.subtype
  let sD : K →ₗ[R] D := iD.comp K.subtype
  let h : K →ₗ[R] (C × D) := sC.prod sD
  have hindModule : Foundation.IsIndecomposableModule R
      (cokernelFGObj (submoduleFGObj E K)
        (prodFGObj C D) h) :=
    isIndecomposableModule_diagonalCommonRadicalCokernel_of_coordinateThin
      e hall E C D iC iD hiC hiD hiCrange hiDrange
        hCthin hDthin hEtop hCtop hDtop hCtopDtop
  have hind : Indecomposable
      (cokernelFGObj (submoduleFGObj E K)
        (prodFGObj C D) h) :=
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) _).mp hindModule
  have hnot :=
    @not_indec_diagonalSubmoduleCokernel_of_all_coordinateThin
      k A _ _ _ _ _ ι _ e hall Hthin E C D K iC iD
        hiC hiD (by
          change Nontrivial (E ⧸ K)
          exact hEtop.nontrivial)
  exact hnot hind

/-- An immediate uniserial successor of a maximal nonsimple uniserial
submodule meets any other containing submodule in exactly the chosen
submodule, provided the intersection stays in the maximality region. -/
theorem inf_eq_of_covBy_of_maximal_nonsimple_uniserial
    (L : FinitelyGeneratedCategory A)
    (I E C D : Submodule Aᵐᵒᵖ L)
    (hEC : E ⋖ C) (hED : E ≤ D)
    (hCDI : C ⊓ D ≤ I)
    (hCuni : IsUniserialModule Aᵐᵒᵖ C)
    (hEne : E ≠ ⊥)
    (hEmax : ∀ F : Submodule Aᵐᵒᵖ L, E ≤ F → F ≤ I →
      ¬ IsSimpleModule Aᵐᵒᵖ F →
      IsUniserialModule Aᵐᵒᵖ F → F = E) :
    C ⊓ D = E := by
  have hEle : E ≤ C ⊓ D := le_inf hEC.le hED
  rcases hEC.eq_or_eq hEle inf_le_left with hinf | hinf
  · exact hinf
  · exfalso
    have hCD : C ≤ D := by
      rw [← inf_eq_left]
      exact hinf
    have hCleI : C ≤ I := by
      rw [← hinf]
      exact hCDI
    have hCnonsimple : ¬ IsSimpleModule Aᵐᵒᵖ C := by
      intro hCsimple
      letI : IsSimpleModule Aᵐᵒᵖ C := hCsimple
      let EC : Submodule Aᵐᵒᵖ C := E.comap C.subtype
      rcases IsSimpleOrder.eq_bot_or_eq_top EC with hbot | htop
      · apply hEne
        apply le_antisymm
        · intro x hx
          let y : C := ⟨x, hEC.le hx⟩
          have hy : y ∈ EC := hx
          have hy0 : y = 0 := by
            have : y ∈ (⊥ : Submodule Aᵐᵒᵖ C) := hbot ▸ hy
            simpa using this
          exact congrArg Subtype.val hy0
        · exact bot_le
      · have hCleE : C ≤ E := by
          intro x hx
          have hxEC : (⟨x, hx⟩ : C) ∈ EC :=
            htop.symm ▸ Submodule.mem_top
          exact hxEC
        exact hEC.1.2 hCleE
    exact hEC.ne
      (hEmax C hEC.le hCleI hCnonsimple hCuni).symm

/-- The complete carrier assembly for a nonsemisimple intersection of two
biserial local sides.  Each side supplies either an ambient immediate
successor or a quotient carrier.  Ambient intersections are controlled by
maximality, while quotient-carrier tops are transported from the original
two nonisomorphic side tops. -/
theorem false_of_not_semisimple_inf_of_biserial_sides
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hIP : P ⊓ Q < P) (hIQ : P ⊓ Q < Q)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    (hPQtop : ¬ Nonempty
      ((P ⧸ Module.jacobson Aᵐᵒᵖ P) ≃ₗ[Aᵐᵒᵖ]
        (Q ⧸ Module.jacobson Aᵐᵒᵖ Q)))
    (hPbis : IsBiserialModule Aᵐᵒᵖ P)
    (hQbis : IsBiserialModule Aᵐᵒᵖ Q)
    (hPbar : IsUniserialModule Aᵐᵒᵖ
      (P.map (moduleSocle Aᵐᵒᵖ L).mkQ))
    (hQbar : IsUniserialModule Aᵐᵒᵖ
      (Q.map (moduleSocle Aᵐᵒᵖ L).mkQ))
    (hInot : ¬ IsSemisimpleModule Aᵐᵒᵖ
      ↥(P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    False := by
  let R := Aᵐᵒᵖ
  let I : Submodule R L := P ⊓ Q
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  obtain ⟨E, hEI, hEind, hEnonsimple, hEuni, hEmax⟩ :=
    exists_maximal_nonsimple_uniserial_submodule_le_of_biserial_side
      e hall L hL P I hIP hPtop hPbis hInot
  have hEne : E ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp hEind.nontrivial
  letI : Nontrivial E := hEind.nontrivial
  have hEP : E < P := lt_of_le_of_lt hEI hIP
  have hEQ : E < Q := lt_of_le_of_lt hEI hIQ
  have hEtop : IsSimpleModule R (E ⧸ Module.jacobson R E) := by
    letI : Nontrivial E := hEind.nontrivial
    exact hEuni.top_isSimple
  have hPCarrier :=
    exists_ambient_or_quotient_commonRadicalCarrier
      e hall L hL P E hEP hEne hEnonsimple hEuni
        hPtop hPbis hPbar
  have hQCarrier :=
    exists_ambient_or_quotient_commonRadicalCarrier
      e hall L hL Q E hEQ hEne hEnonsimple hEuni
        hQtop hQbis hQbar
  rcases hPCarrier with
      ⟨C, hEC, hCP, hCuni, hCrad⟩ |
      ⟨C, iC, hiC, hiCrange, hCuni, hCthin, -, eCtop⟩
  · rcases hQCarrier with
        ⟨D, hED, hDQ, hDuni, hDrad⟩ |
        ⟨D, iD, hiD, hiDrange, hDuni, hDthin, -, eDtop⟩
    · have hCDI : C ⊓ D ≤ I := inf_le_inf hCP hDQ
      have hinf : C ⊓ D = E :=
        inf_eq_of_covBy_of_maximal_nonsimple_uniserial
          L I E C D hEC hED.le hCDI hCuni hEne hEmax
      let iC : E →ₗ[R] C := Submodule.inclusion hEC.le
      let iD : E →ₗ[R] D := Submodule.inclusion hED.le
      have hiC : Function.Injective iC :=
        Submodule.inclusion_injective hEC.le
      have hiD : Function.Injective iD :=
        Submodule.inclusion_injective hED.le
      have hiCrange : iC.range = Module.jacobson R C := by
        rw [Submodule.range_inclusion, hCrad]
      have hiDrange : iD.range = Module.jacobson R D := by
        rw [Submodule.range_inclusion, hDrad]
      letI : Nontrivial C := hiC.nontrivial
      letI : Nontrivial D := hiD.nontrivial
      have hCtop : IsSimpleModule R (C ⧸ Module.jacobson R C) :=
        hCuni.top_isSimple
      have hcross : (C.mkQ.comp D.subtype).ker =
          Module.jacobson R D :=
        crossKernel_eq_jacobson_of_inf_eq E C D hinf hDrad
      have hCDtop : ¬ Nonempty
          ((C ⧸ Module.jacobson R C) ≃ₗ[R]
            (D ⧸ Module.jacobson R D)) :=
        moduleTops_nonisomorphic_of_coordinateThin_of_crossKernel
          e hall L hL C D hCtop hcross
      exact false_of_commonRadicalCarriers_of_coordinateThin
        e hall Hthin (submoduleFGObj L E)
          (submoduleFGObj L C) (submoduleFGObj L D)
          iC iD hiC hiD hiCrange hiDrange
          (hL.submodule C) (hL.submodule D)
          hEind hEnonsimple hEuni hCuni hDuni hCDtop
    · have hCQI : C ⊓ Q ≤ I := inf_le_inf hCP le_rfl
      have hinfCQ : C ⊓ Q = E :=
        inf_eq_of_covBy_of_maximal_nonsimple_uniserial
          L I E C Q hEC hEQ.le hCQI hCuni hEne hEmax
      have hinfQC : Q ⊓ C = E := by
        rw [inf_comm]
        exact hinfCQ
      let iC' : E →ₗ[R] C := Submodule.inclusion hEC.le
      have hiC' : Function.Injective iC' :=
        Submodule.inclusion_injective hEC.le
      have hiC'range : iC'.range = Module.jacobson R C := by
        rw [Submodule.range_inclusion, hCrad]
      letI : Nontrivial C := hiC'.nontrivial
      have hQcross : (Q.mkQ.comp C.subtype).ker =
          Module.jacobson R C :=
        crossKernel_eq_jacobson_of_inf_eq E Q C hinfQC hCrad
      have hQtopCtop : ¬ Nonempty
          ((Q ⧸ Module.jacobson R Q) ≃ₗ[R]
            (C ⧸ Module.jacobson R C)) :=
        moduleTops_nonisomorphic_of_coordinateThin_of_crossKernel
          e hall L hL Q C hQtop hQcross
      obtain ⟨eDtop⟩ := eDtop
      have hCtopDtop : ¬ Nonempty
          ((C ⧸ Module.jacobson R C) ≃ₗ[R]
            (D ⧸ Module.jacobson R D)) := by
        rintro ⟨u⟩
        exact hQtopCtop ⟨(u.trans eDtop).symm⟩
      exact false_of_commonRadicalCarriers_of_coordinateThin
        e hall Hthin (submoduleFGObj L E)
          (submoduleFGObj L C) D iC' iD hiC' hiD
          hiC'range hiDrange (hL.submodule C) hDthin
          hEind hEnonsimple hEuni hCuni hDuni hCtopDtop
  · rcases hQCarrier with
        ⟨D, hED, hDQ, hDuni, hDrad⟩ |
        ⟨D, iD, hiD, hiDrange, hDuni, hDthin, -, eDtop⟩
    · have hDPI : D ⊓ P ≤ I := by
        intro x hx
        exact ⟨hx.2, hDQ hx.1⟩
      have hinfDP : D ⊓ P = E :=
        inf_eq_of_covBy_of_maximal_nonsimple_uniserial
          L I E D P hED hEP.le hDPI hDuni hEne hEmax
      have hinfPD : P ⊓ D = E := by
        rw [inf_comm]
        exact hinfDP
      let iD' : E →ₗ[R] D := Submodule.inclusion hED.le
      have hiD' : Function.Injective iD' :=
        Submodule.inclusion_injective hED.le
      have hiD'range : iD'.range = Module.jacobson R D := by
        rw [Submodule.range_inclusion, hDrad]
      letI : Nontrivial D := hiD'.nontrivial
      have hPcross : (P.mkQ.comp D.subtype).ker =
          Module.jacobson R D :=
        crossKernel_eq_jacobson_of_inf_eq E P D hinfPD hDrad
      have hPtopDtop : ¬ Nonempty
          ((P ⧸ Module.jacobson R P) ≃ₗ[R]
            (D ⧸ Module.jacobson R D)) :=
        moduleTops_nonisomorphic_of_coordinateThin_of_crossKernel
          e hall L hL P D hPtop hPcross
      obtain ⟨eCtop⟩ := eCtop
      have hCtopDtop : ¬ Nonempty
          ((C ⧸ Module.jacobson R C) ≃ₗ[R]
            (D ⧸ Module.jacobson R D)) := by
        rintro ⟨u⟩
        exact hPtopDtop ⟨eCtop.symm.trans u⟩
      exact false_of_commonRadicalCarriers_of_coordinateThin
        e hall Hthin (submoduleFGObj L E) C
          (submoduleFGObj L D) iC iD' hiC hiD'
          hiCrange hiD'range hCthin (hL.submodule D)
          hEind hEnonsimple hEuni hCuni hDuni hCtopDtop
    · obtain ⟨eCtop⟩ := eCtop
      obtain ⟨eDtop⟩ := eDtop
      have hCtopDtop : ¬ Nonempty
          ((C ⧸ Module.jacobson R C) ≃ₗ[R]
            (D ⧸ Module.jacobson R D)) := by
        rintro ⟨u⟩
        exact hPQtop ⟨eCtop.symm.trans (u.trans eDtop)⟩
      exact false_of_commonRadicalCarriers_of_coordinateThin
        e hall Hthin (submoduleFGObj L E) C D
          iC iD hiC hiD hiCrange hiDrange hCthin hDthin
          hEind hEnonsimple hEuni hCuni hDuni hCtopDtop

end MagnitudeConjecture.RightModule
