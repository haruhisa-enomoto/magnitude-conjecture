import MagnitudeConjecture.Algebra.BiserialFiberKernelElementCapture

/-!
# The quotient-branch element calculation

This file formalizes the remaining element calculation in the first
Pogorzały--Skowroński kernel obstruction.  In the source notation,
`X = L / rad³ L`, the second radical layer is the direct sum `S ⊕ T`,
and `Y = X/S`, `Z = X/T`.  A vector outside both branch radicals lifts to
a generator of `X`.  Sending that generator to a vector with one nonzero
component in each of `S` and `T` produces the mixed socle vector; vanishing
of the third radical layer makes the two branch actions agree.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

include k in
theorem quotientBranch_hasMixedSocleSmulWitness
    (X : FinitelyGeneratedCategory A)
    (S T : Submodule Aᵐᵒᵖ X)
    (hinf : S ⊓ T = ⊥)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hSTrad : S ⊔ T ≤ Module.jacobson Aᵐᵒᵖ X)
    (hXtop : IsSimpleModule Aᵐᵒᵖ
      (quotientFGObj X (Module.jacobson Aᵐᵒᵖ X)))
    (hradicalSquare : Ring.jacobson Aᵐᵒᵖ ^ 2 •
      (⊤ : Submodule Aᵐᵒᵖ X) = S ⊔ T)
    (hradicalCube : Ring.jacobson Aᵐᵒᵖ ^ 3 •
      (⊤ : Submodule Aᵐᵒᵖ X) = ⊥)
    (hYuniserial : IsUniserialModule Aᵐᵒᵖ (quotientFGObj X S))
    (hZuniserial : IsUniserialModule Aᵐᵒᵖ (quotientFGObj X T))
    (P : Submodule Aᵐᵒᵖ
      (quotientBranchFiberKernelFGObj X S T
        (Module.jacobson Aᵐᵒᵖ X) hSTrad))
    (houtside : ¬ P ≤ quotientBranchFiberKernelRadicalPreimage X S T
      (Module.jacobson Aᵐᵒᵖ X) hSTrad) :
    HasMixedSocleSmulWitness
      (quotientFGObj X S) (quotientFGObj X T)
      (quotientFGObj X (Module.jacobson Aᵐᵒᵖ X))
      (quotientFGMapQ X S (Module.jacobson Aᵐᵒᵖ X)
        (le_sup_left.trans hSTrad))
      (quotientFGMapQ X T (Module.jacobson Aᵐᵒᵖ X)
        (le_sup_right.trans hSTrad)) P := by
  let R := Aᵐᵒᵖ
  let J := Module.jacobson R X
  let Y := quotientFGObj X S
  let Z := quotientFGObj X T
  let Top := quotientFGObj X J
  let f := quotientFGMapQ X S J (le_sup_left.trans hSTrad)
  let g := quotientFGMapQ X T J (le_sup_right.trans hSTrad)
  let W := fiberKernelFGObj Y Z Top f g
  let j := fiberKernelInclusion Y Z Top f g
  have hSrad : S ≤ J := le_sup_left.trans hSTrad
  have hTrad : T ≤ J := le_sup_right.trans hSTrad
  have hYjac : Module.jacobson R Y = J.map S.mkQ := by
    exact Module.jacobson_quotient_of_le hSrad
  have hZjac : Module.jacobson R Z = J.map T.mkQ := by
    exact Module.jacobson_quotient_of_le hTrad
  have hYker : Module.jacobson R Y = f.ker := by
    rw [hYjac]
    exact (quotientFGMapQ_ker X S J hSrad).symm
  have hZker : Module.jacobson R Z = g.ker := by
    rw [hZjac]
    exact (quotientFGMapQ_ker X T J hTrad).symm
  obtain ⟨u, huP, huout⟩ := SetLike.not_le_iff_exists.mp houtside
  have huNotBoth : ¬
      ((j u).1 ∈ Module.jacobson R Y ∧
        (j u).2 ∈ Module.jacobson R Z) := by
    change ¬ ((j u).1 ∈ Module.jacobson R Y ∧
      (j u).2 ∈ Module.jacobson R Z) at huout
    exact huout
  have hfiber : f (j u).1 = g (j u).2 := by
    have huKer : fiberKernelMap Y Z Top f g (j u) = 0 :=
      LinearMap.mem_ker.mp
        ((fiberKernelFGObjLinearEquiv Y Z Top f g u).2)
    change f (j u).1 + -g (j u).2 = 0 at huKer
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using huKer
  have huY : (j u).1 ∉ Module.jacobson R Y := by
    intro huY
    apply huNotBoth
    refine ⟨huY, ?_⟩
    rw [hZker]
    apply LinearMap.mem_ker.mpr
    rw [← hfiber]
    exact LinearMap.mem_ker.mp (hYker ▸ huY)
  have huZ : (j u).2 ∉ Module.jacobson R Z := by
    intro huZ
    apply huNotBoth
    refine ⟨?_, huZ⟩
    rw [hYker]
    apply LinearMap.mem_ker.mpr
    rw [hfiber]
    exact LinearMap.mem_ker.mp (hZker ▸ huZ)
  obtain ⟨y, hy⟩ := quotientFGMkQ_surjective X S (j u).1
  obtain ⟨z, hz⟩ := quotientFGMkQ_surjective X T (j u).2
  have hyNotJ : y ∉ J := by
    intro hyJ
    apply huY
    rw [hYjac]
    exact ⟨y, hyJ, hy⟩
  have hyspan : Submodule.span R {y} = ⊤ := by
    by_contra hne
    have hspanJ : Submodule.span R {y} ≤ J :=
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hXtop hne
    exact hyNotJ (hspanJ (Submodule.subset_span (Set.mem_singleton y)))
  letI : Nontrivial S := hSsimple.nontrivial
  letI : Nontrivial T := hTsimple.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨t, ht⟩ := exists_ne (0 : T)
  have hsNotT : (s.1 : X) ∉ T := by
    intro hsT
    have hsZero : (s.1 : X) = 0 := by
      have hsBot : (s.1 : X) ∈ (⊥ : Submodule R X) := by
        rw [← hinf]
        exact ⟨s.2, hsT⟩
      simpa using hsBot
    exact hs (Subtype.ext hsZero)
  have htNotS : (t.1 : X) ∉ S := by
    intro htS
    have htZero : (t.1 : X) = 0 := by
      have htBot : (t.1 : X) ∈ (⊥ : Submodule R X) := by
        rw [← hinf]
        exact ⟨htS, t.2⟩
      simpa using htBot
    exact ht (Subtype.ext htZero)
  have hstRadicalSquare : (s.1 : X) + t.1 ∈
      Ring.jacobson R ^ 2 • (⊤ : Submodule R X) := by
    rw [hradicalSquare]
    exact (S ⊔ T).add_mem
      ((show S ≤ S ⊔ T from le_sup_left) s.2)
      ((show T ≤ S ⊔ T from le_sup_right) t.2)
  have hstSpan : (s.1 : X) + t.1 ∈
      Ring.jacobson R ^ 2 • Submodule.span R {y} := by
    rw [hyspan]
    exact hstRadicalSquare
  obtain ⟨r, hr, hry⟩ :=
    Submodule.mem_smul_span_singleton.mp hstSpan
  have htopEq : quotientFGMkQ X J y = quotientFGMkQ X J z := by
    calc
      quotientFGMkQ X J y = f (quotientFGMkQ X S y) := by
        exact (quotientFGMapQ_apply_mkQ X S J hSrad y).symm
      _ = f (j u).1 := by rw [hy]
      _ = g (j u).2 := hfiber
      _ = g (quotientFGMkQ X T z) := by rw [hz]
      _ = quotientFGMkQ X J z := by
        exact quotientFGMapQ_apply_mkQ X T J hTrad z
  have hydiff : y - z ∈ J := by
    change J.mkQ y = J.mkQ z at htopEq
    rw [← J.ker_mkQ]
    apply LinearMap.mem_ker.mpr
    rw [map_sub, htopEq, sub_self]
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  have hydiffRing : y - z ∈
      Ring.jacobson R • (⊤ : Submodule R X) := by
    rw [← moduleJacobson_eq_ringJacobson_smul_top]
    exact hydiff
  have hrdiffMem : r • (y - z) ∈
      Ring.jacobson R ^ 2 •
        (Ring.jacobson R • (⊤ : Submodule R X)) :=
    Submodule.smul_mem_smul hr hydiffRing
  have hrdiff : r • (y - z) = 0 := by
    have hpow : Ring.jacobson R ^ 3 =
        Ring.jacobson R ^ 2 * Ring.jacobson R := by
      calc
        Ring.jacobson R ^ 3 = Ring.jacobson R ^ (2 + 1) := by norm_num
        _ = Ring.jacobson R ^ 2 * Ring.jacobson R ^ 1 :=
          Ideal.IsTwoSided.pow_add (I := Ring.jacobson R) 2 1
        _ = Ring.jacobson R ^ 2 * Ring.jacobson R := by
          rw [Submodule.pow_one]
    have hmem : r • (y - z) ∈
        Ring.jacobson R ^ 3 • (⊤ : Submodule R X) := by
      rw [hpow, Submodule.mul_smul]
      exact hrdiffMem
    rw [hradicalCube] at hmem
    simpa using hmem
  have hrz : r • z = (s.1 : X) + t.1 := by
    have hryz : r • y = r • z := by
      apply sub_eq_zero.mp
      simpa [smul_sub] using hrdiff
    rw [← hryz]
    exact hry
  have hleft : r • (j u).1 = quotientFGMkQ X S t.1 := by
    rw [← hy, ← (quotientFGMkQ X S).map_smul, hry]
    rw [(quotientFGMkQ X S).map_add]
    have hsQuot : quotientFGMkQ X S s.1 = 0 := by
      change S.mkQ s.1 = 0
      exact (Submodule.Quotient.mk_eq_zero S).mpr s.2
    rw [hsQuot, zero_add]
  have hright : r • (j u).2 = quotientFGMkQ X T s.1 := by
    rw [← hz, ← (quotientFGMkQ X T).map_smul, hrz]
    rw [(quotientFGMkQ X T).map_add]
    have htQuot : quotientFGMkQ X T t.1 = 0 := by
      change T.mkQ t.1 = 0
      exact (Submodule.Quotient.mk_eq_zero T).mpr t.2
    rw [htQuot, add_zero]
  have hleftNe : r • (j u).1 ≠ 0 := by
    rw [hleft]
    intro hzero
    apply htNotS
    change S.mkQ t.1 = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero S).mp hzero
  have hrightNe : r • (j u).2 ≠ 0 := by
    rw [hright]
    intro hzero
    apply hsNotT
    change T.mkQ s.1 = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero T).mp hzero
  have hYsocleEq : moduleSocle R Y = (S ⊔ T).map S.mkQ :=
    moduleSocle_quotient_eq_sup_map X S T hinf hTsimple hYuniserial
  have hZsocleEq : moduleSocle R Z = (S ⊔ T).map T.mkQ := by
    have hzSocle := moduleSocle_quotient_eq_sup_map X T S
      (by simpa [inf_comm] using hinf) hSsimple hZuniserial
    simpa [sup_comm] using hzSocle
  refine ⟨u, r, huP, hleftNe, hrightNe, ?_, ?_⟩
  · rw [hleft, hYsocleEq]
    exact ⟨t.1, (show T ≤ S ⊔ T from le_sup_right) t.2, rfl⟩
  · rw [hright, hZsocleEq]
    exact ⟨s.1, (show S ≤ S ⊔ T from le_sup_left) s.2, rfl⟩

end MagnitudeConjecture.RightModule
