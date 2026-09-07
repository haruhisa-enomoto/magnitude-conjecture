import MagnitudeConjecture.Algebra.CoordinateThinModule
import MagnitudeConjecture.Algebra.BiserialModule

/-!
# Cokernel subquotient obstructions for biseriality

This is the cokernel counterpart of `BiserialKernelObstruction`.  If a map
into a binary product lands inside two chosen branch submodules, the cokernel
still surjects onto the product of the two branch quotients.  Equal nonzero
branch quotients therefore give the repeated self-subquotient used in the
cokernel contradictions of the Pogorzały--Skowroński induction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The finitely generated cokernel of a linear map. -/
def cokernelFGObj
    (X Y : FinitelyGeneratedCategory A) (f : X →ₗ[Aᵐᵒᵖ] Y) :
    FinitelyGeneratedCategory A :=
  quotientFGObj Y f.range

/-- If a map into `Y × Z` lands in `QY × QZ`, its cokernel surjects
onto `(Y/QY) × (Z/QZ)`.  When both quotients are the same nonzero module,
this is a repeated self-subquotient certificate. -/
theorem hasRepeatedSelfSubquotient_cokernel_of_prod_quotients
    (X Y Z F : FinitelyGeneratedCategory A) [Nontrivial F]
    (g : X →ₗ[Aᵐᵒᵖ] (Y × Z))
    (QY : Submodule Aᵐᵒᵖ Y) (QZ : Submodule Aᵐᵒᵖ Z)
    (hrange : g.range ≤ QY.prod QZ)
    (eY : (Y ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (Z ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    HasRepeatedSelfSubquotient
      (cokernelFGObj X (prodFGObj Y Z) g) := by
  let qY : Y →ₗ[Aᵐᵒᵖ] F := eY.toLinearMap.comp QY.mkQ
  let qZ : Z →ₗ[Aᵐᵒᵖ] F := eZ.toLinearMap.comp QZ.mkQ
  let h : (Y × Z) →ₗ[Aᵐᵒᵖ] (F × F) := qY.prodMap qZ
  have hhSurj : Function.Surjective h := by
    intro t
    obtain ⟨y, hy⟩ := QY.mkQ_surjective (eY.symm t.1)
    obtain ⟨z, hz⟩ := QZ.mkQ_surjective (eZ.symm t.2)
    refine ⟨(y, z), Prod.ext ?_ ?_⟩
    · change eY (QY.mkQ y) = t.1
      rw [hy]
      exact eY.apply_symm_apply t.1
    · change eZ (QZ.mkQ z) = t.2
      rw [hz]
      exact eZ.apply_symm_apply t.2
  have hRangeKer : g.range ≤ h.ker := by
    rintro yz ⟨x, rfl⟩
    have hmem : g x ∈ QY.prod QZ := hrange ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change eY (QY.mkQ (g x).1) = 0
      have hzero : QY.mkQ (g x).1 = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem.1
      rw [hzero, map_zero]
    · change eZ (QZ.mkQ (g x).2) = 0
      have hzero : QZ.mkQ (g x).2 = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem.2
      rw [hzero, map_zero]
  let q : ((Y × Z) ⧸ g.range) →ₗ[Aᵐᵒᵖ] (F × F) :=
    g.range.liftQ h hRangeKer
  have hq : Function.Surjective q := by
    intro t
    obtain ⟨yz, hyz⟩ := hhSurj t
    refine ⟨g.range.mkQ yz, ?_⟩
    exact hyz
  exact hasRepeatedSelfSubquotient_of_surjective_prod_self
    (cokernelFGObj X (prodFGObj Y Z) g) F q hq

/-- Complete coordinate thinness rules out indecomposability of the cokernel
configuration above.  This is the contradiction endpoint for the cokernel
modules in the direct biserial induction. -/
theorem not_indec_cokernel_of_all_coordinateThin
    {ι : Type w} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (X Y Z F : FinitelyGeneratedCategory A) [Nontrivial F]
    (g : X →ₗ[Aᵐᵒᵖ] (Y × Z))
    (QY : Submodule Aᵐᵒᵖ Y) (QZ : Submodule Aᵐᵒᵖ Z)
    (hrange : g.range ≤ QY.prod QZ)
    (eY : (Y ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (Z ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    ¬ Indecomposable (cokernelFGObj X (prodFGObj Y Z) g) := by
  intro hW
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H (cokernelFGObj X (prodFGObj Y Z) g) hW
    (hasRepeatedSelfSubquotient_cokernel_of_prod_quotients
      X Y Z F g QY QZ hrange eY eZ)

/-- An injective copy of a product of two branch submodules, each with the
same nonzero quotient, gives a repeated self-subquotient of the ambient
module. -/
theorem hasRepeatedSelfSubquotient_of_injective_submodule_prod
    (Y Z W F : FinitelyGeneratedCategory A) [Nontrivial F]
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (j : (PY × PZ) →ₗ[Aᵐᵒᵖ] W) (hj : Function.Injective j)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    HasRepeatedSelfSubquotient W := by
  let P : Submodule Aᵐᵒᵖ W := j.range
  let eP : (PY × PZ) ≃ₗ[Aᵐᵒᵖ] P := LinearEquiv.ofInjective j hj
  let pY : P →ₗ[Aᵐᵒᵖ] PY :=
    (LinearMap.fst Aᵐᵒᵖ PY PZ).comp eP.symm.toLinearMap
  let pZ : P →ₗ[Aᵐᵒᵖ] PZ :=
    (LinearMap.snd Aᵐᵒᵖ PY PZ).comp eP.symm.toLinearMap
  let qY : P →ₗ[Aᵐᵒᵖ] F :=
    eY.toLinearMap.comp (QY.mkQ.comp pY)
  let qZ : P →ₗ[Aᵐᵒᵖ] F :=
    eZ.toLinearMap.comp (QZ.mkQ.comp pZ)
  let q : P →ₗ[Aᵐᵒᵖ] (F × F) := qY.prod qZ
  have hq : Function.Surjective q := by
    intro t
    obtain ⟨y, hy⟩ := QY.mkQ_surjective (eY.symm t.1)
    obtain ⟨z, hz⟩ := QZ.mkQ_surjective (eZ.symm t.2)
    let p : P := eP (y, z)
    refine ⟨p, Prod.ext ?_ ?_⟩
    · change eY (QY.mkQ ((eP.symm p).1)) = t.1
      rw [eP.symm_apply_apply]
      change eY (QY.mkQ y) = t.1
      rw [hy]
      exact eY.apply_symm_apply t.1
    · change eZ (QZ.mkQ ((eP.symm p).2)) = t.2
      rw [eP.symm_apply_apply]
      change eZ (QZ.mkQ z) = t.2
      rw [hz]
      exact eZ.apply_symm_apply t.2
  refine ⟨F, inferInstance, P, q.ker, ?_⟩
  exact ⟨
    QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
      Aᵐᵒᵖ (q.quotKerEquivOfSurjective hq)⟩

/-- If a product of two branch submodules meets the image of a map trivially,
that branch product embeds in the cokernel.  Equal nonzero branch quotients
then give a repeated self-subquotient of the cokernel. -/
theorem hasRepeatedSelfSubquotient_cokernel_of_disjoint_submodule_prod
    (X Y Z F : FinitelyGeneratedCategory A) [Nontrivial F]
    (g : X →ₗ[Aᵐᵒᵖ] (Y × Z))
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (hdisjoint : (PY.prod PZ) ⊓ g.range = ⊥)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    HasRepeatedSelfSubquotient
      (cokernelFGObj X (prodFGObj Y Z) g) := by
  let branchInclusion : (PY × PZ) →ₗ[Aᵐᵒᵖ] (Y × Z) :=
    PY.subtype.prodMap PZ.subtype
  let j : (PY × PZ) →ₗ[Aᵐᵒᵖ] ((Y × Z) ⧸ g.range) :=
    g.range.mkQ.comp branchInclusion
  have hj : Function.Injective j := by
    intro a b hab
    apply sub_eq_zero.mp
    have hquotZero : g.range.mkQ (branchInclusion (a - b)) = 0 := by
      change j (a - b) = 0
      rw [map_sub, hab, sub_self]
    have hRange : branchInclusion (a - b) ∈ g.range := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hquotZero
      exact hquotZero
    have hProd : branchInclusion (a - b) ∈ PY.prod PZ := by
      exact ⟨(a - b).1.2, (a - b).2.2⟩
    have hBot : branchInclusion (a - b) ∈
        (⊥ : Submodule Aᵐᵒᵖ (Y × Z)) := by
      rw [← hdisjoint]
      exact ⟨hProd, hRange⟩
    have hzero : branchInclusion (a - b) = 0 := hBot
    apply Prod.ext
    · apply PY.subtype_injective
      exact congrArg Prod.fst hzero
    · apply PZ.subtype_injective
      exact congrArg Prod.snd hzero
  exact hasRepeatedSelfSubquotient_of_injective_submodule_prod
    Y Z (cokernelFGObj X (prodFGObj Y Z) g) F
    PY PZ j hj QY QZ eY eZ

/-- Complete coordinate thinness rules out indecomposability of the
disjoint-branch cokernel configuration.  This is the direct endpoint for the
diagonal-cokernel obstruction in the biserial induction. -/
theorem not_indec_cokernel_of_disjoint_submodule_prod_of_all_coordinateThin
    {ι : Type w} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (X Y Z F : FinitelyGeneratedCategory A) [Nontrivial F]
    (g : X →ₗ[Aᵐᵒᵖ] (Y × Z))
    (PY : Submodule Aᵐᵒᵖ Y) (PZ : Submodule Aᵐᵒᵖ Z)
    (hdisjoint : (PY.prod PZ) ⊓ g.range = ⊥)
    (QY : Submodule Aᵐᵒᵖ PY) (QZ : Submodule Aᵐᵒᵖ PZ)
    (eY : (PY ⧸ QY) ≃ₗ[Aᵐᵒᵖ] F)
    (eZ : (PZ ⧸ QZ) ≃ₗ[Aᵐᵒᵖ] F) :
    ¬ Indecomposable (cokernelFGObj X (prodFGObj Y Z) g) := by
  intro hW
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H (cokernelFGObj X (prodFGObj Y Z) g) hW
    (hasRepeatedSelfSubquotient_cokernel_of_disjoint_submodule_prod
      X Y Z F g PY PZ hdisjoint QY QZ eY eZ)



/-- If a diagonal copy of a submodule is killed inside two injective ambient
branches, the resulting cokernel contains a submodule surjecting onto two
copies of the common quotient. -/
theorem hasRepeatedSelfSubquotient_diagonalSubmoduleCokernel
    (E C D : FinitelyGeneratedCategory A)
    (K : Submodule Aᵐᵒᵖ E)
    (iC : E →ₗ[Aᵐᵒᵖ] C) (iD : E →ₗ[Aᵐᵒᵖ] D)
    (hiC : Function.Injective iC) (hiD : Function.Injective iD)
    [Nontrivial (E ⧸ K)] :
    let h : K →ₗ[Aᵐᵒᵖ] (C × D) :=
      (iC.comp K.subtype).prod (iD.comp K.subtype)
    HasRepeatedSelfSubquotient
      (cokernelFGObj (submoduleFGObj E K) (prodFGObj C D) h) := by
  let h : K →ₗ[Aᵐᵒᵖ] (C × D) :=
    (iC.comp K.subtype).prod (iD.comp K.subtype)
  let B := cokernelFGObj (submoduleFGObj E K) (prodFGObj C D) h
  let bq : (C × D) →ₗ[Aᵐᵒᵖ] B := h.range.mkQ
  let inc : (E × E) →ₗ[Aᵐᵒᵖ] (C × D) := iC.prodMap iD
  let j : (E × E) →ₗ[Aᵐᵒᵖ] B := bq.comp inc
  let q : (E × E) →ₗ[Aᵐᵒᵖ] ((E ⧸ K) × (E ⧸ K)) :=
    K.mkQ.prodMap K.mkQ
  have hker : j.ker ≤ q.ker := by
    intro x hx
    have hincRange : inc x ∈ h.range := by
      have hjx : j x = 0 := LinearMap.mem_ker.mp hx
      change h.range.mkQ (inc x) = 0 at hjx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hjx
      exact hjx
    obtain ⟨z, hz⟩ := hincRange
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change K.mkQ x.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hxz : x.1 = z.1 := by
        apply hiC
        exact congrArg Prod.fst hz.symm
      exact hxz ▸ z.2
    · change K.mkQ x.2 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hxz : x.2 = z.1 := by
        apply hiD
        exact congrArg Prod.snd hz.symm
      exact hxz ▸ z.2
  let qbar : ((E × E) ⧸ j.ker) →ₗ[Aᵐᵒᵖ]
      ((E ⧸ K) × (E ⧸ K)) :=
    j.ker.liftQ q hker
  have hqSurj : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := K.mkQ_surjective y.1
    obtain ⟨z, hz⟩ := K.mkQ_surjective y.2
    exact ⟨(x, z), Prod.ext hx hz⟩
  have hqbarSurj : Function.Surjective qbar := by
    intro y
    obtain ⟨x, hx⟩ := hqSurj y
    exact ⟨j.ker.mkQ x, hx⟩
  let P : Submodule Aᵐᵒᵖ B := j.range
  let eRange : ((E × E) ⧸ j.ker) ≃ₗ[Aᵐᵒᵖ] P :=
    j.quotKerEquivRange
  let qP : P →ₗ[Aᵐᵒᵖ] ((E ⧸ K) × (E ⧸ K)) :=
    qbar.comp eRange.symm.toLinearMap
  have hqP : Function.Surjective qP :=
    hqbarSurj.comp eRange.symm.surjective
  let F := quotientFGObj E K
  letI : Nontrivial F := ‹Nontrivial (E ⧸ K)›
  exact hasRepeatedSelfSubquotient_of_submodule_surjective_prod_self
    B F P qP hqP

/-- A surjection from a local module to a simple module identifies the
simple target with the source top. -/
def moduleTopLinearEquivOfSurjectiveToSimple
    (M S : FinitelyGeneratedCategory A)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (f : M →ₗ[Aᵐᵒᵖ] S) (hf : Function.Surjective f) :
    (M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ] S := by
  let R := Aᵐᵒᵖ
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J := isSimpleModule_iff_isCoatom.mp hMtop
  letI : IsSimpleModule R S := hSsimple
  letI : Nontrivial S := hSsimple.nontrivial
  have hJker : J ≤ f.ker :=
    IsSemisimpleModule.jacobson_le_ker R R M S f
  have hkerNeTop : f.ker ≠ ⊤ := by
    intro hker
    have hfzero : f = 0 := LinearMap.ker_eq_top.mp hker
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    obtain ⟨m, hm⟩ := hf s
    apply hs
    rw [← hm, hfzero]
    rfl
  have hkerEq : f.ker = J := by
    apply le_antisymm
    · exact ((hJcoatom.le_iff_eq hkerNeTop).mp hJker).le
    · exact hJker
  exact (Submodule.quotEquivOfEq _ _ hkerEq.symm).trans
    (f.quotKerEquivOfSurjective hf)

/-- A map between local modules vanishes when the target radical is simple
and the source top is nonisomorphic to both simple layers of the target.
Indeed, a nonzero image is either the whole target or its simple radical;
either case makes one of those layers a simple quotient of the source. -/
theorem linearMap_eq_zero_of_simpleTop_noniso_of_simpleRadical_target
    (M N : FinitelyGeneratedCategory A)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hNrad : IsSimpleModule Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ N))
    (hnonisoTop : ¬ Nonempty
      ((M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ]
        (N ⧸ Module.jacobson Aᵐᵒᵖ N)))
    (hnonisoRad : ¬ Nonempty
      ((M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ]
        Module.jacobson Aᵐᵒᵖ N))
    (f : M →ₗ[Aᵐᵒᵖ] N) : f = 0 := by
  let R := Aᵐᵒᵖ
  by_contra hf
  have hrangeNe : f.range ≠ ⊥ := by
    intro hrange
    exact hf (LinearMap.range_eq_bot.mp hrange)
  by_cases hrangeTop : f.range = ⊤
  · have hfSurj : Function.Surjective f := LinearMap.range_eq_top.mp hrangeTop
    let g : M →ₗ[R] (N ⧸ Module.jacobson R N) :=
      (Module.jacobson R N).mkQ.comp f
    have hgSurj : Function.Surjective g :=
      (Module.jacobson R N).mkQ_surjective.comp hfSurj
    exact hnonisoTop ⟨moduleTopLinearEquivOfSurjectiveToSimple
      M (quotientFGObj N (Module.jacobson R N)) hMtop hNtop g hgSurj⟩
  · have hrangeLe : f.range ≤ Module.jacobson R N :=
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hNtop hrangeTop
    have hrangeEq : f.range = Module.jacobson R N :=
      (isSimpleModule_iff_isAtom.mp hNrad).le_iff_eq hrangeNe |>.mp hrangeLe
    let g : M →ₗ[R] Module.jacobson R N :=
      f.codRestrict (Module.jacobson R N) (fun m ↦ hrangeLe ⟨m, rfl⟩)
    have hgSurj : Function.Surjective g := by
      intro n
      have hn : n.1 ∈ f.range := hrangeEq.symm ▸ n.2
      obtain ⟨m, hm⟩ := hn
      exact ⟨m, Subtype.ext hm⟩
    exact hnonisoRad ⟨moduleTopLinearEquivOfSurjectiveToSimple
      M (submoduleFGObj N (Module.jacobson R N)) hMtop hNrad g hgSurj⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- A linear map between nonisomorphic simple modules is zero. -/
theorem linearMap_eq_zero_of_nonisomorphic_simple
    (M N : FinitelyGeneratedCategory A)
    (hM : IsSimpleModule Aᵐᵒᵖ M)
    (hN : IsSimpleModule Aᵐᵒᵖ N)
    (hnoniso : ¬ Nonempty (M ≃ₗ[Aᵐᵒᵖ] N))
    (f : M →ₗ[Aᵐᵒᵖ] N) : f = 0 := by
  letI : IsSimpleModule Aᵐᵒᵖ M := hM
  letI : IsSimpleModule Aᵐᵒᵖ N := hN
  by_contra hf
  have hkerNe : f.ker ≠ ⊤ := by
    intro hker
    exact hf (LinearMap.ker_eq_top.mp hker)
  have hker : f.ker = ⊥ :=
    (IsSimpleOrder.eq_bot_or_eq_top f.ker).resolve_right hkerNe
  have hrangeNe : f.range ≠ ⊥ := by
    intro hrange
    exact hf (LinearMap.range_eq_bot.mp hrange)
  have hrange : f.range = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left hrangeNe
  exact hnoniso ⟨LinearEquiv.ofBijective f
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩⟩

/-- A map to a local module with simple radical vanishes when the source
radical is the sum of two simple modules, neither of which is isomorphic to
the target radical, and the source top is also nonisomorphic to that
radical.  A surjective map would have to map the source radical onto the
target radical, while a proper nonzero image would itself be the target
radical. -/
theorem linearMap_eq_zero_of_two_simple_radical_noniso_targetRadical
    (M N : FinitelyGeneratedCategory A)
    (hMtop : IsSimpleModule Aᵐᵒᵖ
      (M ⧸ Module.jacobson Aᵐᵒᵖ M))
    (hNtop : IsSimpleModule Aᵐᵒᵖ
      (N ⧸ Module.jacobson Aᵐᵒᵖ N))
    (hNrad : IsSimpleModule Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ N))
    (P Q : Submodule Aᵐᵒᵖ M)
    (hMrad : P ⊔ Q = Module.jacobson Aᵐᵒᵖ M)
    (hP : IsSimpleModule Aᵐᵒᵖ P)
    (hQ : IsSimpleModule Aᵐᵒᵖ Q)
    (hTopRad : ¬ Nonempty
      ((M ⧸ Module.jacobson Aᵐᵒᵖ M) ≃ₗ[Aᵐᵒᵖ]
        Module.jacobson Aᵐᵒᵖ N))
    (hPRad : ¬ Nonempty (P ≃ₗ[Aᵐᵒᵖ] Module.jacobson Aᵐᵒᵖ N))
    (hQRad : ¬ Nonempty (Q ≃ₗ[Aᵐᵒᵖ] Module.jacobson Aᵐᵒᵖ N))
    (f : M →ₗ[Aᵐᵒᵖ] N) : f = 0 := by
  let R := Aᵐᵒᵖ
  by_contra hf
  have hrangeNe : f.range ≠ ⊥ := by
    intro hrange
    exact hf (LinearMap.range_eq_bot.mp hrange)
  by_cases hrangeTop : f.range = ⊤
  · have hfSurj : Function.Surjective f :=
      LinearMap.range_eq_top.mp hrangeTop
    have hkerNeTop : f.ker ≠ ⊤ := by
      intro hker
      exact hf (LinearMap.ker_eq_top.mp hker)
    have hkerLe : f.ker ≤ Module.jacobson R M :=
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
        hMtop hkerNeTop
    have hmapRad : (Module.jacobson R M).map f =
        Module.jacobson R N :=
      Module.map_jacobson_of_ker_le hfSurj hkerLe
    have hPmap : P.map f = ⊥ := by
      let fP : P →ₗ[R] Module.jacobson R N :=
        (f.domRestrict P).codRestrict (Module.jacobson R N) (fun p ↦
          Module.map_jacobson_le f
            ⟨p.1, (show (p.1 : M) ∈ Module.jacobson R M by
              rw [← hMrad]
              exact Submodule.mem_sup_left p.2), rfl⟩)
      have hfP : fP = 0 :=
        linearMap_eq_zero_of_nonisomorphic_simple
          (submoduleFGObj M P)
          (submoduleFGObj N (Module.jacobson R N)) hP hNrad hPRad fP
      apply le_bot_iff.mp
      rintro y ⟨p, hp, rfl⟩
      have hpzero : fP ⟨p, hp⟩ = 0 := by rw [hfP]; rfl
      exact congrArg Subtype.val hpzero
    have hQmap : Q.map f = ⊥ := by
      let fQ : Q →ₗ[R] Module.jacobson R N :=
        (f.domRestrict Q).codRestrict (Module.jacobson R N) (fun q ↦
          Module.map_jacobson_le f
            ⟨q.1, (show (q.1 : M) ∈ Module.jacobson R M by
              rw [← hMrad]
              exact Submodule.mem_sup_right q.2), rfl⟩)
      have hfQ : fQ = 0 :=
        linearMap_eq_zero_of_nonisomorphic_simple
          (submoduleFGObj M Q)
          (submoduleFGObj N (Module.jacobson R N)) hQ hNrad hQRad fQ
      apply le_bot_iff.mp
      rintro y ⟨q, hq, rfl⟩
      have hqzero : fQ ⟨q, hq⟩ = 0 := by rw [hfQ]; rfl
      exact congrArg Subtype.val hqzero
    have hNradBot : Module.jacobson R N = ⊥ := by
      rw [← hmapRad, ← hMrad, Submodule.map_sup, hPmap, hQmap,
        sup_bot_eq]
    exact (isSimpleModule_iff_isAtom.mp hNrad).ne_bot hNradBot
  · have hrangeLe : f.range ≤ Module.jacobson R N :=
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top
        hNtop hrangeTop
    have hrangeEq : f.range = Module.jacobson R N :=
      (isSimpleModule_iff_isAtom.mp hNrad).le_iff_eq hrangeNe |>.mp hrangeLe
    let g : M →ₗ[R] Module.jacobson R N :=
      f.codRestrict (Module.jacobson R N) (fun m ↦ hrangeLe ⟨m, rfl⟩)
    have hgSurj : Function.Surjective g := by
      intro n
      have hn : n.1 ∈ f.range := hrangeEq.symm ▸ n.2
      obtain ⟨m, hm⟩ := hn
      exact ⟨m, Subtype.ext hm⟩
    exact hTopRad ⟨moduleTopLinearEquivOfSurjectiveToSimple
      M (submoduleFGObj N (Module.jacobson R N))
        hMtop hNrad g hgSurj⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The cokernel obtained by gluing two indecomposable branches along a
nonzero diagonal submodule is indecomposable if there are no cross maps from
either branch to the quotient of the other by the glued image.

The proof tests an idempotent endomorphism of the cokernel.  Cross-map
vanishing forces it to preserve both canonical branch images.  Its two
restrictions are therefore zero or one by branch indecomposability, and the
nonzero intersection of the branch images forces those choices to agree. -/
theorem isIndecomposableModule_diagonalCokernel_of_crossHom_eq_zero
    (S C D : FinitelyGeneratedCategory A)
    (sC : S →ₗ[Aᵐᵒᵖ] C) (sD : S →ₗ[Aᵐᵒᵖ] D)
    (hsC : Function.Injective sC) (hsD : Function.Injective sD)
    [Nontrivial S]
    (hC : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ C)
    (hD : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ D)
    (hCD : ∀ f : C →ₗ[Aᵐᵒᵖ] (D ⧸ sD.range), f = 0)
    (hDC : ∀ f : D →ₗ[Aᵐᵒᵖ] (C ⧸ sC.range), f = 0) :
    let h : S →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ (cokernelFGObj S (prodFGObj C D) h) := by
  let R := Aᵐᵒᵖ
  let h : S →ₗ[R] (C × D) := sC.prod sD
  let W := cokernelFGObj S (prodFGObj C D) h
  change QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R W
  let q : (C × D) →ₗ[R] W := h.range.mkQ
  let jC : C →ₗ[R] W := q.comp (LinearMap.inl R C D)
  let jD : D →ₗ[R] W := q.comp (LinearMap.inr R C D)
  have hjC : Function.Injective jC := by
    intro c c' hcc'
    apply sub_eq_zero.mp
    have hzero : q (c - c', 0) = 0 := by
      change jC (c - c') = 0
      rw [map_sub, hcc', sub_self]
    have hrange : (c - c', 0) ∈ h.range := by
      change h.range.mkQ (c - c', 0) = 0 at hzero
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
      exact hzero
    obtain ⟨s, hs⟩ := hrange
    have hsDzero : sD s = 0 := congrArg Prod.snd hs
    have hsZero : s = 0 := hsD (by simpa using hsDzero)
    have hcZero : c - c' = 0 := by
      calc
        c - c' = (h s).1 := congrArg Prod.fst hs.symm
        _ = 0 := by simp [h, hsZero]
    exact hcZero
  have hjD : Function.Injective jD := by
    intro d d' hdd'
    apply sub_eq_zero.mp
    have hzero : q (0, d - d') = 0 := by
      change jD (d - d') = 0
      rw [map_sub, hdd', sub_self]
    have hrange : (0, d - d') ∈ h.range := by
      change h.range.mkQ (0, d - d') = 0 at hzero
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
      exact hzero
    obtain ⟨s, hs⟩ := hrange
    have hsCzero : sC s = 0 := congrArg Prod.fst hs
    have hsZero : s = 0 := hsC (by simpa using hsCzero)
    have hdZero : d - d' = 0 := by
      calc
        d - d' = (h s).2 := congrArg Prod.snd hs.symm
        _ = 0 := by simp [h, hsZero]
    exact hdZero
  have hqSurj : Function.Surjective q := h.range.mkQ_surjective
  let pD0 : (C × D) →ₗ[R] (D ⧸ sD.range) :=
    sD.range.mkQ.comp (LinearMap.snd R C D)
  have hhD : h.range ≤ pD0.ker := by
    rintro cd ⟨s, rfl⟩
    apply LinearMap.mem_ker.mpr
    change sD.range.mkQ (sD s) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨s, rfl⟩
  let pD : W →ₗ[R] (D ⧸ sD.range) := h.range.liftQ pD0 hhD
  have hpDker : pD.ker = jC.range := by
    apply le_antisymm
    · intro w hw
      obtain ⟨cd, rfl⟩ := hqSurj w
      have hdZero : sD.range.mkQ cd.2 = 0 := by
        have := LinearMap.mem_ker.mp hw
        exact this
      have hdRange : cd.2 ∈ sD.range := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hdZero
        exact hdZero
      obtain ⟨s, hs⟩ := hdRange
      refine ⟨cd.1 - sC s, ?_⟩
      change q (cd.1 - sC s, 0) = q cd
      apply (Submodule.Quotient.eq h.range).2
      change (cd.1 - sC s, 0) - cd ∈ h.range
      refine ⟨-s, ?_⟩
      apply Prod.ext
      · simp [h]
      · simp [h, hs]
    · rintro w ⟨c, rfl⟩
      apply LinearMap.mem_ker.mpr
      change sD.range.mkQ 0 = 0
      simp
  let pC0 : (C × D) →ₗ[R] (C ⧸ sC.range) :=
    sC.range.mkQ.comp (LinearMap.fst R C D)
  have hhC : h.range ≤ pC0.ker := by
    rintro cd ⟨s, rfl⟩
    apply LinearMap.mem_ker.mpr
    change sC.range.mkQ (sC s) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨s, rfl⟩
  let pC : W →ₗ[R] (C ⧸ sC.range) := h.range.liftQ pC0 hhC
  have hpCker : pC.ker = jD.range := by
    apply le_antisymm
    · intro w hw
      obtain ⟨cd, rfl⟩ := hqSurj w
      have hcZero : sC.range.mkQ cd.1 = 0 := by
        have := LinearMap.mem_ker.mp hw
        exact this
      have hcRange : cd.1 ∈ sC.range := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hcZero
        exact hcZero
      obtain ⟨s, hs⟩ := hcRange
      refine ⟨cd.2 - sD s, ?_⟩
      change q (0, cd.2 - sD s) = q cd
      apply (Submodule.Quotient.eq h.range).2
      change (0, cd.2 - sD s) - cd ∈ h.range
      refine ⟨-s, ?_⟩
      apply Prod.ext
      · simp [h, hs]
      · simp [h]
    · rintro w ⟨d, rfl⟩
      apply LinearMap.mem_ker.mpr
      change sC.range.mkQ 0 = 0
      simp
  have hnonzeroInf : jC.range ⊓ jD.range ≠ ⊥ := by
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    let w : W := jC (sC s)
    have hwC : w ∈ jC.range := ⟨sC s, rfl⟩
    have hwD : w ∈ jD.range := by
      refine ⟨-sD s, ?_⟩
      change q (0, -sD s) = q (sC s, 0)
      apply (Submodule.Quotient.eq h.range).2
      change (0, -sD s) - (sC s, 0) ∈ h.range
      refine ⟨-s, ?_⟩
      apply Prod.ext <;> simp [h]
    have hwNe : w ≠ 0 := by
      intro hw
      have hsCzero : sC s = 0 := hjC (by simpa using hw)
      exact hs (hsC (by simpa using hsCzero))
    intro hbot
    have : w ∈ (⊥ : Submodule R W) := hbot ▸ ⟨hwC, hwD⟩
    exact hwNe this
  letI : Nontrivial C := Function.Injective.nontrivial hsC
  letI : Nontrivial W := Function.Injective.nontrivial hjC
  apply
    QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  have hinvC : ∀ c : C, f (jC c) ∈ jC.range := by
    intro c
    have hzero : pD (f (jC c)) = 0 := by
      have hz := congrArg (fun g : C →ₗ[R] (D ⧸ sD.range) ↦ g c)
        (hCD (pD.comp (f.comp jC)))
      simpa using hz
    rw [← hpDker]
    exact LinearMap.mem_ker.mpr hzero
  have hinvD : ∀ d : D, f (jD d) ∈ jD.range := by
    intro d
    have hzero : pC (f (jD d)) = 0 := by
      have hz := congrArg (fun g : D →ₗ[R] (C ⧸ sC.range) ↦ g d)
        (hDC (pC.comp (f.comp jD)))
      simpa using hz
    rw [← hpCker]
    exact LinearMap.mem_ker.mpr hzero
  let eC : C ≃ₗ[R] jC.range := LinearEquiv.ofInjective jC hjC
  let fC : C →ₗ[R] C := eC.symm.toLinearMap.comp
    ((f.comp jC).codRestrict jC.range hinvC)
  have hjCfC (c : C) : jC (fC c) = f (jC c) := by
    change ((eC (fC c) : jC.range) : W) = f (jC c)
    exact congrArg Subtype.val
      (eC.apply_symm_apply ⟨f (jC c), hinvC c⟩)
  have hfC : IsIdempotentElem fC := by
    apply LinearMap.ext
    intro c
    apply hjC
    change jC (fC (fC c)) = jC (fC c)
    rw [hjCfC, hjCfC]
    exact DFunLike.congr_fun hf (jC c)
  have hCaction :
      (∀ c : C, f (jC c) = 0) ∨ (∀ c : C, f (jC c) = jC c) := by
    rcases hC.eq_zero_or_eq_one_of_isIdempotentElem hfC with hzero | hone
    · left
      intro c
      rw [← hjCfC, hzero]
      rfl
    · right
      intro c
      rw [← hjCfC, hone]
      rfl
  let eD : D ≃ₗ[R] jD.range := LinearEquiv.ofInjective jD hjD
  let fD : D →ₗ[R] D := eD.symm.toLinearMap.comp
    ((f.comp jD).codRestrict jD.range hinvD)
  have hjDfD (d : D) : jD (fD d) = f (jD d) := by
    change ((eD (fD d) : jD.range) : W) = f (jD d)
    exact congrArg Subtype.val
      (eD.apply_symm_apply ⟨f (jD d), hinvD d⟩)
  have hfD : IsIdempotentElem fD := by
    apply LinearMap.ext
    intro d
    apply hjD
    change jD (fD (fD d)) = jD (fD d)
    rw [hjDfD, hjDfD]
    exact DFunLike.congr_fun hf (jD d)
  have hDaction :
      (∀ d : D, f (jD d) = 0) ∨ (∀ d : D, f (jD d) = jD d) := by
    rcases hD.eq_zero_or_eq_one_of_isIdempotentElem hfD with hzero | hone
    · left
      intro d
      rw [← hjDfD, hzero]
      rfl
    · right
      intro d
      rw [← hjDfD, hone]
      rfl
  rcases hCaction with hCzero | hCone <;>
    rcases hDaction with hDzero | hDone
  · left
    ext w
    obtain ⟨cd, rfl⟩ := hqSurj w
    have hdecomp : q cd = jC cd.1 + jD cd.2 := by
      change q cd = q (cd.1, 0) + q (0, cd.2)
      rw [← map_add]
      congr 2
      exact Prod.ext (add_zero cd.1).symm (zero_add cd.2).symm
    rw [hdecomp, map_add, hCzero, hDzero]
    simp
  · exfalso
    letI : Nontrivial ↥(jC.range ⊓ jD.range : Submodule R W) :=
      Submodule.nontrivial_iff_ne_bot.mpr hnonzeroInf
    obtain ⟨w, hw⟩ :=
      exists_ne (0 : ↥(jC.range ⊓ jD.range : Submodule R W))
    obtain ⟨c, hc⟩ := w.2.1
    obtain ⟨d, hd⟩ := w.2.2
    have hfzero : f w.1 = 0 := by
      rw [← hc]
      exact hCzero c
    have hfid : f w.1 = w.1 := by
      rw [← hd]
      exact hDone d
    apply hw
    apply Subtype.ext
    exact hfid.symm.trans hfzero
  · exfalso
    letI : Nontrivial ↥(jC.range ⊓ jD.range : Submodule R W) :=
      Submodule.nontrivial_iff_ne_bot.mpr hnonzeroInf
    obtain ⟨w, hw⟩ :=
      exists_ne (0 : ↥(jC.range ⊓ jD.range : Submodule R W))
    obtain ⟨c, hc⟩ := w.2.1
    obtain ⟨d, hd⟩ := w.2.2
    have hfzero : f w.1 = 0 := by
      rw [← hd]
      exact hDzero d
    have hfid : f w.1 = w.1 := by
      rw [← hc]
      exact hCone c
    apply hw
    apply Subtype.ext
    exact hfid.symm.trans hfzero
  · right
    ext w
    obtain ⟨cd, rfl⟩ := hqSurj w
    have hdecomp : q cd = jC cd.1 + jD cd.2 := by
      change q cd = q (cd.1, 0) + q (0, cd.2)
      rw [← map_add]
      congr 2
      exact Prod.ext (add_zero cd.1).symm (zero_add cd.2).symm
    rw [hdecomp, map_add, hCone, hDone]
    rfl

/-- A source-facing form of the diagonal-cokernel criterion.  It is enough
that both branches have simple top and that each quotient by the glued image
has simple top and simple radical, with neither layer isomorphic to the
opposite branch top. -/
theorem isIndecomposableModule_diagonalCokernel_of_crossLayers
    (S C D : FinitelyGeneratedCategory A)
    (sC : S →ₗ[Aᵐᵒᵖ] C) (sD : S →ₗ[Aᵐᵒᵖ] D)
    (hsC : Function.Injective sC) (hsD : Function.Injective sD)
    [Nontrivial S]
    (hCtop : IsSimpleModule Aᵐᵒᵖ
      (C ⧸ Module.jacobson Aᵐᵒᵖ C))
    (hDtop : IsSimpleModule Aᵐᵒᵖ
      (D ⧸ Module.jacobson Aᵐᵒᵖ D))
    (hDquotTop : IsSimpleModule Aᵐᵒᵖ
      ((D ⧸ sD.range) ⧸ Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range)))
    (hDquotRad : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range)))
    (hCtopDquotTop : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        ((D ⧸ sD.range) ⧸
          Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range))))
    (hCtopDquotRad : ¬ Nonempty
      ((C ⧸ Module.jacobson Aᵐᵒᵖ C) ≃ₗ[Aᵐᵒᵖ]
        Module.jacobson Aᵐᵒᵖ (D ⧸ sD.range)))
    (hCquotTop : IsSimpleModule Aᵐᵒᵖ
      ((C ⧸ sC.range) ⧸ Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range)))
    (hCquotRad : IsSimpleModule Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range)))
    (hDtopCquotTop : ¬ Nonempty
      ((D ⧸ Module.jacobson Aᵐᵒᵖ D) ≃ₗ[Aᵐᵒᵖ]
        ((C ⧸ sC.range) ⧸
          Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range))))
    (hDtopCquotRad : ¬ Nonempty
      ((D ⧸ Module.jacobson Aᵐᵒᵖ D) ≃ₗ[Aᵐᵒᵖ]
        Module.jacobson Aᵐᵒᵖ (C ⧸ sC.range))) :
    let h : S →ₗ[Aᵐᵒᵖ] (C × D) := sC.prod sD
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ (cokernelFGObj S (prodFGObj C D) h) := by
  apply isIndecomposableModule_diagonalCokernel_of_crossHom_eq_zero
    S C D sC sD hsC hsD
  · exact IsUniserialModule.isIndecomposableModule_of_simpleTop hCtop
  · exact IsUniserialModule.isIndecomposableModule_of_simpleTop hDtop
  · intro f
    exact linearMap_eq_zero_of_simpleTop_noniso_of_simpleRadical_target
      C (quotientFGObj D sD.range) hCtop hDquotTop hDquotRad
        hCtopDquotTop hCtopDquotRad f
  · intro f
    exact linearMap_eq_zero_of_simpleTop_noniso_of_simpleRadical_target
      D (quotientFGObj C sC.range) hDtop hCquotTop hCquotRad
        hDtopCquotTop hDtopCquotRad f

/-- Complete coordinate thinness therefore forces every such diagonal
submodule cokernel to be decomposable. -/
theorem not_indec_diagonalSubmoduleCokernel_of_all_coordinateThin
    {ι : Type w} [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (E C D : FinitelyGeneratedCategory A)
    (K : Submodule Aᵐᵒᵖ E)
    (iC : E →ₗ[Aᵐᵒᵖ] C) (iD : E →ₗ[Aᵐᵒᵖ] D)
    (hiC : Function.Injective iC) (hiD : Function.Injective iD)
    [Nontrivial (E ⧸ K)] :
    let h : K →ₗ[Aᵐᵒᵖ] (C × D) :=
      (iC.comp K.subtype).prod (iD.comp K.subtype)
    ¬ Indecomposable
      (cokernelFGObj (submoduleFGObj E K) (prodFGObj C D) h) := by
  intro h hind
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H _ hind
    (hasRepeatedSelfSubquotient_diagonalSubmoduleCokernel
      E C D K iC iD hiC hiD)


end MagnitudeConjecture.RightModule
