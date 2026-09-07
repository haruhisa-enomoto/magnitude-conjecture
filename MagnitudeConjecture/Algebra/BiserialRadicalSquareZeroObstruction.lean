import MagnitudeConjecture.Algebra.BiserialCokernelObstruction
import MagnitudeConjecture.Algebra.BiserialRadicalTruncation
import MagnitudeConjecture.Algebra.BiserialSemisimpleSubmodule
import MagnitudeConjecture.Algebra.BiserialQuotientBranch
import MagnitudeConjecture.Algebra.BiserialCommonRadicalCokernel
import MagnitudeConjecture.Algebra.BiserialCoordinateThinLocal

/-!
# The radical-square-zero obstruction in the biserial induction

A local coordinate-thin module cannot have three independent simple
summands in its square-zero radical.  From such summands one forms two
quotient branches with two-simple radicals, glues their common simple
summand diagonally, and obtains the highest-root `D₄` module: its top occurs
twice, but the cross-map criterion makes it indecomposable.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} { ι : Type w }
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- The range of the canonical map from a submodule to an ambient quotient
is its ordinary mapped submodule. -/
theorem submoduleToQuotientLinearMap_range
    (L : FinitelyGeneratedCategory A)
    (P K : Submodule Aᵐᵒᵖ L) :
    LinearMap.range
        (IsBiserialModule.submoduleToQuotientLinearMap P K) =
      P.map K.mkQ := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Every submodule of a quotient denominator maps to zero. -/
theorem map_quotientMk_eq_bot_of_le
    (L : FinitelyGeneratedCategory A)
    (P K : Submodule Aᵐᵒᵖ L) (hPK : P ≤ K) :
    P.map K.mkQ = ⊥ := by
  apply le_bot_iff.mp
  calc
    P.map K.mkQ ≤ K.map K.mkQ := Submodule.map_mono hPK
    _ = ⊥ := K.mkQ_map_self

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- A nested quotient by the image of a disjoint submodule is the quotient
by the sum of the two ambient denominators. -/
def quotientByMappedSubmoduleLinearEquiv
    (L : FinitelyGeneratedCategory A)
    (P K : Submodule Aᵐᵒᵖ L) :
    ((L ⧸ K) ⧸ P.map K.mkQ) ≃ₗ[Aᵐᵒᵖ] (L ⧸ (K ⊔ P)) := by
  let eEq : ((L ⧸ K) ⧸ P.map K.mkQ) ≃ₗ[Aᵐᵒᵖ]
      ((L ⧸ K) ⧸ (K ⊔ P).map K.mkQ) :=
    Submodule.quotEquivOfEq _ _ (by
      rw [Submodule.map_sup, K.mkQ_map_self, bot_sup_eq])
  exact eEq.trans
    (Submodule.quotientQuotientEquivQuotient K (K ⊔ P) le_sup_left)

/-- A four-summand radical configuration gives the forbidden `D₄`
diagonal cokernel.  The hypotheses are an ordered direct decomposition
`rad L = S ⊕ (T ⊕ (U ⊕ V))`; only `S`, `T`, and `U` are required to
be simple. -/
theorem false_of_three_simple_squareZero_radical_summands
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (L ⧸ Module.jacobson Aᵐᵒᵖ L))
    (S C T D U V : Submodule Aᵐᵒᵖ L)
    (hSsimple : IsSimpleModule Aᵐᵒᵖ S)
    (hTsimple : IsSimpleModule Aᵐᵒᵖ T)
    (hUsimple : IsSimpleModule Aᵐᵒᵖ U)
    (hSCsup : S ⊔ C = Module.jacobson Aᵐᵒᵖ L)
    (hSCinf : S ⊓ C = ⊥)
    (hTDsup : T ⊔ D = C)
    (hTDinf : T ⊓ D = ⊥)
    (hUVsup : U ⊔ V = D)
    (hUVinf : U ⊓ V = ⊥) :
    False := by
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  let K₁ : Submodule R L := T ⊔ V
  let K₂ : Submodule R L := D
  let N₁ : Submodule R L := K₁ ⊔ S
  let N₂ : Submodule R L := K₂ ⊔ S
  let Y := quotientFGObj L K₁
  let Z := quotientFGObj L K₂
  let Ycross := quotientFGObj L N₂
  let Zcross := quotientFGObj L N₁
  let Top := quotientFGObj L J
  have hTleC : T ≤ C := by rw [← hTDsup]; exact le_sup_left
  have hDleC : D ≤ C := by rw [← hTDsup]; exact le_sup_right
  have hUleD : U ≤ D := by rw [← hUVsup]; exact le_sup_left
  have hVleD : V ≤ D := by rw [← hUVsup]; exact le_sup_right
  have hSleJ : S ≤ J := by
    change S ≤ Module.jacobson R L
    rw [← hSCsup]
    exact le_sup_left
  have hCleJ : C ≤ J := by
    change C ≤ Module.jacobson R L
    rw [← hSCsup]
    exact le_sup_right
  have hTleJ : T ≤ J := hTleC.trans hCleJ
  have hDleJ : D ≤ J := hDleC.trans hCleJ
  have hUleJ : U ≤ J := hUleD.trans hDleJ
  have hVleJ : V ≤ J := hVleD.trans hDleJ
  have hK₁leJ : K₁ ≤ J := sup_le hTleJ hVleJ
  have hK₂leJ : K₂ ≤ J := hDleJ
  have hN₁leJ : N₁ ≤ J := sup_le hK₁leJ hSleJ
  have hN₂leJ : N₂ ≤ J := sup_le hK₂leJ hSleJ
  have hSinfK₁ : S ⊓ K₁ = ⊥ := by
    apply le_antisymm
    · rw [← hSCinf]
      exact inf_le_inf le_rfl (sup_le hTleC (hVleD.trans hDleC))
    · exact bot_le
  have hSinfK₂ : S ⊓ K₂ = ⊥ := by
    apply le_antisymm
    · rw [← hSCinf]
      exact inf_le_inf le_rfl hDleC
    · exact bot_le
  have hUinfK₁ : U ⊓ K₁ = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp hx.2
      have htD : t ∈ D := by
        have hxD : x ∈ D := hUleD hx.1
        have hvD : v ∈ D := hVleD hv
        have : t = x - v := by rw [← htv]; abel
        rw [this]
        exact D.sub_mem hxD hvD
      have htBot : t ∈ (⊥ : Submodule R L) := by
        rw [← hTDinf]
        exact ⟨ht, htD⟩
      have htzero : t = 0 := by simpa using htBot
      have hxV : x ∈ V := by
        rw [← htv, htzero, zero_add]
        exact hv
      rw [← hUVinf]
      exact ⟨hx.1, hxV⟩
    · exact bot_le
  have hTinfK₂ : T ⊓ K₂ = ⊥ := hTDinf
  have hTinfN₂ : T ⊓ N₂ = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨d, hd, s, hs, hds⟩ := Submodule.mem_sup.mp hx.2
      have hxC : x ∈ C := hTleC hx.1
      have hdC : d ∈ C := hDleC hd
      have hsC : s ∈ C := by
        have : s = x - d := by rw [← hds]; abel
        rw [this]
        exact C.sub_mem hxC hdC
      have hsBot : s ∈ (⊥ : Submodule R L) := by
        rw [← hSCinf]
        exact ⟨hs, hsC⟩
      have hszero : s = 0 := by simpa using hsBot
      have hxD : x ∈ D := by
        rw [← hds, hszero, add_zero]
        exact hd
      rw [← hTDinf]
      exact ⟨hx.1, hxD⟩
    · exact bot_le
  have hUinfN₁ : U ⊓ N₁ = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk, s, hs, hks⟩ := Submodule.mem_sup.mp hx.2
      have hxC : x ∈ C := hUleD.trans hDleC hx.1
      have hkC : k ∈ C :=
        (sup_le hTleC (hVleD.trans hDleC)) hk
      have hsC : s ∈ C := by
        have : s = x - k := by rw [← hks]; abel
        rw [this]
        exact C.sub_mem hxC hkC
      have hsBot : s ∈ (⊥ : Submodule R L) := by
        rw [← hSCinf]
        exact ⟨hs, hsC⟩
      have hszero : s = 0 := by simpa using hsBot
      have hxK : x ∈ K₁ := by
        rw [← hks, hszero, add_zero]
        exact hk
      have hxbot : x ∈ (U ⊓ K₁ : Submodule R L) := ⟨hx.1, hxK⟩
      rw [hUinfK₁] at hxbot
      exact hxbot
    · exact bot_le
  have hJYdecomp : S.map K₁.mkQ ⊔ U.map K₁.mkQ =
      Module.jacobson R Y := by
    change S.map K₁.mkQ ⊔ U.map K₁.mkQ =
      Module.jacobson R (L ⧸ K₁)
    rw [Module.jacobson_quotient_of_le hK₁leJ, ← Submodule.map_sup]
    change (S ⊔ U).map K₁.mkQ = J.map K₁.mkQ
    have hJfour : J = S ⊔ (T ⊔ (U ⊔ V)) := by
      calc
        J = S ⊔ C := hSCsup.symm
        _ = S ⊔ (T ⊔ D) := by rw [hTDsup]
        _ = S ⊔ (T ⊔ (U ⊔ V)) := by rw [hUVsup]
    rw [hJfour]
    simp only [Submodule.map_sup, K₁]
    rw [show T.map K₁.mkQ = ⊥ by
      exact map_quotientMk_eq_bot_of_le L T K₁ le_sup_left,
      show V.map K₁.mkQ = ⊥ by
        exact map_quotientMk_eq_bot_of_le L V K₁ le_sup_right]
    rw [bot_sup_eq, sup_bot_eq]
  have hJZdecomp : S.map K₂.mkQ ⊔ T.map K₂.mkQ =
      Module.jacobson R Z := by
    change S.map K₂.mkQ ⊔ T.map K₂.mkQ =
      Module.jacobson R (L ⧸ K₂)
    rw [Module.jacobson_quotient_of_le hK₂leJ, ← Submodule.map_sup]
    change (S ⊔ T).map K₂.mkQ = J.map K₂.mkQ
    have hJthree : J = S ⊔ (T ⊔ D) := by
      calc
        J = S ⊔ C := hSCsup.symm
        _ = S ⊔ (T ⊔ D) := by rw [hTDsup]
    rw [hJthree]
    simp only [Submodule.map_sup]
    rw [show D.map K₂.mkQ = ⊥ by
      exact map_quotientMk_eq_bot_of_le L D K₂ le_rfl]
    rw [sup_bot_eq]
  have hJYcross : Module.jacobson R Ycross = T.map N₂.mkQ := by
    change Module.jacobson R (L ⧸ N₂) = T.map N₂.mkQ
    rw [Module.jacobson_quotient_of_le hN₂leJ]
    change J.map N₂.mkQ = T.map N₂.mkQ
    have hJthree : J = S ⊔ (T ⊔ D) := by
      calc
        J = S ⊔ C := hSCsup.symm
        _ = S ⊔ (T ⊔ D) := by rw [hTDsup]
    rw [hJthree]
    simp only [Submodule.map_sup]
    rw [show S.map N₂.mkQ = ⊥ by
      exact map_quotientMk_eq_bot_of_le L S N₂ le_sup_right,
      show D.map N₂.mkQ = ⊥ by
        exact map_quotientMk_eq_bot_of_le L D N₂ le_sup_left]
    rw [bot_sup_eq, sup_bot_eq]
  have hJZcross : Module.jacobson R Zcross = U.map N₁.mkQ := by
    change Module.jacobson R (L ⧸ N₁) = U.map N₁.mkQ
    rw [Module.jacobson_quotient_of_le hN₁leJ]
    change J.map N₁.mkQ = U.map N₁.mkQ
    have hJfour : J = S ⊔ (T ⊔ (U ⊔ V)) := by
      calc
        J = S ⊔ C := hSCsup.symm
        _ = S ⊔ (T ⊔ D) := by rw [hTDsup]
        _ = S ⊔ (T ⊔ (U ⊔ V)) := by rw [hUVsup]
    rw [hJfour]
    simp only [Submodule.map_sup]
    rw [show S.map N₁.mkQ = ⊥ by
      exact map_quotientMk_eq_bot_of_le L S N₁ le_sup_right,
      show T.map N₁.mkQ = ⊥ by
        exact map_quotientMk_eq_bot_of_le L T N₁
          (le_sup_left.trans le_sup_left),
      show V.map N₁.mkQ = ⊥ by
        exact map_quotientMk_eq_bot_of_le L V N₁
          (le_sup_right.trans le_sup_left)]
    rw [bot_sup_eq, bot_sup_eq, sup_bot_eq]
  have hYtop : IsSimpleModule R (Y ⧸ Module.jacobson R Y) :=
    isSimpleModule_top_quotient_of_le_jacobson K₁ hK₁leJ hLtop
  have hZtop : IsSimpleModule R (Z ⧸ Module.jacobson R Z) :=
    isSimpleModule_top_quotient_of_le_jacobson K₂ hK₂leJ hLtop
  have hYcrossTop : IsSimpleModule R
      (Ycross ⧸ Module.jacobson R Ycross) :=
    isSimpleModule_top_quotient_of_le_jacobson N₂ hN₂leJ hLtop
  have hZcrossTop : IsSimpleModule R
      (Zcross ⧸ Module.jacobson R Zcross) :=
    isSimpleModule_top_quotient_of_le_jacobson N₁ hN₁leJ hLtop
  have hSYsimple : IsSimpleModule R (S.map K₁.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot L K₁ S
      (by simpa [inf_comm] using hSinfK₁) hSsimple
  have hUYsimple : IsSimpleModule R (U.map K₁.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot L K₁ U
      (by simpa [inf_comm] using hUinfK₁) hUsimple
  have hSZsimple : IsSimpleModule R (S.map K₂.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot L K₂ S
      (by simpa [inf_comm] using hSinfK₂) hSsimple
  have hTZsimple : IsSimpleModule R (T.map K₂.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot L K₂ T
      (by simpa [inf_comm] using hTinfK₂) hTsimple
  have hTYcrossSimple : IsSimpleModule R (T.map N₂.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot L N₂ T
      (by simpa [inf_comm] using hTinfN₂) hTsimple
  have hUZcrossSimple : IsSimpleModule R (U.map N₁.mkQ) :=
    isSimpleModule_map_quotientMk_of_inf_eq_bot L N₁ U
      (by simpa [inf_comm] using hUinfN₁) hUsimple
  let eSY : S ≃ₗ[R] S.map K₁.mkQ :=
    submoduleLinearEquivMapQuotientOfInfEqBot S K₁ hSinfK₁
  let eUY : U ≃ₗ[R] U.map K₁.mkQ :=
    submoduleLinearEquivMapQuotientOfInfEqBot U K₁ hUinfK₁
  let eSZ : S ≃ₗ[R] S.map K₂.mkQ :=
    submoduleLinearEquivMapQuotientOfInfEqBot S K₂ hSinfK₂
  let eTZ : T ≃ₗ[R] T.map K₂.mkQ :=
    submoduleLinearEquivMapQuotientOfInfEqBot T K₂ hTinfK₂
  let eTYcross : T ≃ₗ[R] T.map N₂.mkQ :=
    submoduleLinearEquivMapQuotientOfInfEqBot T N₂ hTinfN₂
  let eUZcross : U ≃ₗ[R] U.map N₁.mkQ :=
    submoduleLinearEquivMapQuotientOfInfEqBot U N₁ hUinfN₁
  have hLthin : IsCoordinateThin (k := k) e L :=
    coordinateThin_of_simpleTop e Hthin L hLtop
  have hSTinf : S ⊓ T = ⊥ := by
    apply le_antisymm
    · rw [← hSCinf]
      exact inf_le_inf le_rfl hTleC
    · exact bot_le
  have hSUinf : S ⊓ U = ⊥ := by
    apply le_antisymm
    · rw [← hSCinf]
      exact inf_le_inf le_rfl (hUleD.trans hDleC)
    · exact bot_le
  have hTUinf : T ⊓ U = ⊥ := by
    apply le_antisymm
    · rw [← hTDinf]
      exact inf_le_inf le_rfl hUleD
    · exact bot_le
  have hSTnoniso : ¬ Nonempty (S ≃ₗ[R] T) :=
    nonisomorphic_disjoint_simple_submodules_of_simpleTop
      (k := k) e hall Hthin L hLtop S T hSsimple hSTinf
  have hSUnoniso : ¬ Nonempty (S ≃ₗ[R] U) :=
    nonisomorphic_disjoint_simple_submodules_of_simpleTop
      (k := k) e hall Hthin L hLtop S U hSsimple hSUinf
  have hTUnoniso : ¬ Nonempty (T ≃ₗ[R] U) :=
    nonisomorphic_disjoint_simple_submodules_of_simpleTop
      (k := k) e hall Hthin L hLtop T U hTsimple hTUinf
  have hTopTnoniso : ¬ Nonempty ((L ⧸ J) ≃ₗ[R] T) :=
    nonisomorphic_top_and_nonzero_jacobson_submodule_of_simpleTop
      (k := k) e hall Hthin L hLtop T
        (Submodule.nontrivial_iff_ne_bot.mp hTsimple.nontrivial) hTleJ
  have hTopUnoniso : ¬ Nonempty ((L ⧸ J) ≃ₗ[R] U) :=
    nonisomorphic_top_and_nonzero_jacobson_submodule_of_simpleTop
      (k := k) e hall Hthin L hLtop U
        (Submodule.nontrivial_iff_ne_bot.mp hUsimple.nontrivial) hUleJ
  let eYtop : (Y ⧸ Module.jacobson R Y) ≃ₗ[R] Top :=
    moduleTopQuotientLinearEquiv L K₁ hK₁leJ
  let eZtop : (Z ⧸ Module.jacobson R Z) ≃ₗ[R] Top :=
    moduleTopQuotientLinearEquiv L K₂ hK₂leJ
  have hYTopTYcross : ¬ Nonempty
      ((Y ⧸ Module.jacobson R Y) ≃ₗ[R] Module.jacobson R Ycross) := by
    rw [hJYcross]
    rintro ⟨q⟩
    exact hTopTnoniso ⟨eYtop.symm.trans (q.trans eTYcross.symm)⟩
  have hZTopUZcross : ¬ Nonempty
      ((Z ⧸ Module.jacobson R Z) ≃ₗ[R] Module.jacobson R Zcross) := by
    rw [hJZcross]
    rintro ⟨q⟩
    exact hTopUnoniso ⟨eZtop.symm.trans (q.trans eUZcross.symm)⟩
  have hSYTYcross : ¬ Nonempty
      (S.map K₁.mkQ ≃ₗ[R] Module.jacobson R Ycross) := by
    rw [hJYcross]
    rintro ⟨q⟩
    exact hSTnoniso ⟨eSY.trans (q.trans eTYcross.symm)⟩
  have hUYTYcross : ¬ Nonempty
      (U.map K₁.mkQ ≃ₗ[R] Module.jacobson R Ycross) := by
    rw [hJYcross]
    rintro ⟨q⟩
    exact hTUnoniso ⟨(eUY.trans (q.trans eTYcross.symm)).symm⟩
  have hSZUZcross : ¬ Nonempty
      (S.map K₂.mkQ ≃ₗ[R] Module.jacobson R Zcross) := by
    rw [hJZcross]
    rintro ⟨q⟩
    exact hSUnoniso ⟨eSZ.trans (q.trans eUZcross.symm)⟩
  have hTZUZcross : ¬ Nonempty
      (T.map K₂.mkQ ≃ₗ[R] Module.jacobson R Zcross) := by
    rw [hJZcross]
    rintro ⟨q⟩
    exact hTUnoniso ⟨eTZ.trans (q.trans eUZcross.symm)⟩
  let sY : S →ₗ[R] Y :=
    IsBiserialModule.submoduleToQuotientLinearMap S K₁
  let sZ : S →ₗ[R] Z :=
    IsBiserialModule.submoduleToQuotientLinearMap S K₂
  have hsY : Function.Injective sY :=
    IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
      S K₁ hSinfK₁
  have hsZ : Function.Injective sZ :=
    IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
      S K₂ hSinfK₂
  have hsYrange : sY.range = S.map K₁.mkQ :=
    submoduleToQuotientLinearMap_range L S K₁
  have hsZrange : sZ.range = S.map K₂.mkQ :=
    submoduleToQuotientLinearMap_range L S K₂
  let eZcross : (Z ⧸ sZ.range) ≃ₗ[R] Ycross :=
    (Submodule.quotEquivOfEq _ _ hsZrange).trans
      (quotientByMappedSubmoduleLinearEquiv L S K₂)
  let eYcross : (Y ⧸ sY.range) ≃ₗ[R] Zcross :=
    (Submodule.quotEquivOfEq _ _ hsYrange).trans
      (quotientByMappedSubmoduleLinearEquiv L S K₁)
  have hYZ : ∀ f : Y →ₗ[R] (Z ⧸ sZ.range), f = 0 := by
    intro f
    have hf : eZcross.toLinearMap.comp f = 0 :=
      linearMap_eq_zero_of_two_simple_radical_noniso_targetRadical
        Y Ycross hYtop hYcrossTop
        (by rw [hJYcross]; exact hTYcrossSimple)
        (S.map K₁.mkQ) (U.map K₁.mkQ) hJYdecomp
        hSYsimple hUYsimple hYTopTYcross hSYTYcross hUYTYcross _
    ext y
    apply eZcross.injective
    change (eZcross.toLinearMap.comp f) y = eZcross 0
    rw [hf]
    rfl
  have hZY : ∀ f : Z →ₗ[R] (Y ⧸ sY.range), f = 0 := by
    intro f
    have hf : eYcross.toLinearMap.comp f = 0 :=
      linearMap_eq_zero_of_two_simple_radical_noniso_targetRadical
        Z Zcross hZtop hZcrossTop
        (by rw [hJZcross]; exact hUZcrossSimple)
        (S.map K₂.mkQ) (T.map K₂.mkQ) hJZdecomp
        hSZsimple hTZsimple hZTopUZcross hSZUZcross hTZUZcross _
    ext z
    apply eYcross.injective
    change (eYcross.toLinearMap.comp f) z = eYcross 0
    rw [hf]
    rfl
  let g : S →ₗ[R] (Y × Z) := sY.prod sZ
  let W := cokernelFGObj (submoduleFGObj L S) (prodFGObj Y Z) g
  letI : Nontrivial S := hSsimple.nontrivial
  letI : Nontrivial (submoduleFGObj L S) := hSsimple.nontrivial
  letI : Nontrivial Top := hLtop.nontrivial
  have hWindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        R W :=
    isIndecomposableModule_diagonalCokernel_of_crossHom_eq_zero
      (submoduleFGObj L S) Y Z sY sZ hsY hsZ
      (IsUniserialModule.isIndecomposableModule_of_simpleTop hYtop)
      (IsUniserialModule.isIndecomposableModule_of_simpleTop hZtop)
      hYZ hZY
  have hWind : Indecomposable W :=
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hWindModule
  have hrange : g.range ≤
      (Module.jacobson R Y).prod (Module.jacobson R Z) := by
    rintro yz ⟨s, rfl⟩
    constructor
    · change K₁.mkQ s.1 ∈ Module.jacobson R (L ⧸ K₁)
      have hJYdecomp' : S.map K₁.mkQ ⊔ U.map K₁.mkQ =
          Module.jacobson R (L ⧸ K₁) := hJYdecomp
      rw [← hJYdecomp']
      exact Submodule.mem_sup_left ⟨s.1, s.2, rfl⟩
    · change K₂.mkQ s.1 ∈ Module.jacobson R (L ⧸ K₂)
      have hJZdecomp' : S.map K₂.mkQ ⊔ T.map K₂.mkQ =
          Module.jacobson R (L ⧸ K₂) := hJZdecomp
      rw [← hJZdecomp']
      exact Submodule.mem_sup_left ⟨s.1, s.2, rfl⟩
  have hnot : ¬ Indecomposable W :=
    not_indec_cokernel_of_all_coordinateThin
      (k := k) e hall Hthin (submoduleFGObj L S) Y Z Top g
        (Module.jacobson R Y) (Module.jacobson R Z) hrange
        eYtop eZtop
  exact hnot hWind

set_option maxHeartbeats 800000 in
/-- A semisimple radical of a coordinate-thin local module has composition
length at most two.  If its length were larger, three successive simple
summands and their residual complement would instantiate the preceding
`D₄` obstruction. -/
theorem jacobson_length_le_two_of_semisimple_of_all_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hLtop : IsSimpleModule Aᵐᵒᵖ
      (L ⧸ Module.jacobson Aᵐᵒᵖ L))
    [IsArtinian Aᵐᵒᵖ L]
    [IsSemisimpleModule Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L)] :
    Module.length Aᵐᵒᵖ (Module.jacobson Aᵐᵒᵖ L) ≤ 2 := by
  let R := Aᵐᵒᵖ
  let J : Submodule R L := Module.jacobson R L
  by_contra hlength
  obtain ⟨S, C, T, D, U, V, hSsimple, hSC, hTsimple, hTD,
      hUsimple, hUV⟩ :=
    exists_three_simple_nested_complements_of_semisimple_of_length_not_le_two
      (R := R) (M := J) hlength
  let iJ : J →ₗ[R] L := J.subtype
  let iC : C →ₗ[R] L := iJ.comp C.subtype
  let iD : D →ₗ[R] L := iC.comp D.subtype
  let S₀ : Submodule R L := S.map iJ
  let C₀ : Submodule R L := C.map iJ
  let T₀ : Submodule R L := T.map iC
  let D₀ : Submodule R L := D.map iC
  let U₀ : Submodule R L := U.map iD
  let V₀ : Submodule R L := V.map iD
  have hiJ : Function.Injective iJ := J.subtype_injective
  have hiC : Function.Injective iC :=
    hiJ.comp C.subtype_injective
  have hiD : Function.Injective iD :=
    hiC.comp D.subtype_injective
  have hS₀simple : IsSimpleModule R S₀ :=
    isSimpleModule_map_of_injective iJ hiJ S hSsimple
  have hT₀simple : IsSimpleModule R T₀ :=
    isSimpleModule_map_of_injective iC hiC T hTsimple
  have hU₀simple : IsSimpleModule R U₀ :=
    by
      change IsSimpleModule R (U.map iD)
      exact isSimpleModule_map_of_injective
        (R := R) (M := D) (N := L) iD hiD U hUsimple
  have hSCsup : S₀ ⊔ C₀ = Module.jacobson R L := by
    change S.map iJ ⊔ C.map iJ = J
    rw [← Submodule.map_sup, hSC.sup_eq_top, Submodule.map_top]
    exact Submodule.range_subtype J
  have hSCinf : S₀ ⊓ C₀ = ⊥ := by
    change S.map iJ ⊓ C.map iJ = ⊥
    rw [← Submodule.map_inf iJ hiJ, hSC.inf_eq_bot, Submodule.map_bot]
  have hiCrange : iC.range = C₀ := by
    change (iJ.comp C.subtype).range = C.map iJ
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hTDsup : T₀ ⊔ D₀ = C₀ := by
    change T.map iC ⊔ D.map iC = C₀
    rw [← Submodule.map_sup, hTD.sup_eq_top, Submodule.map_top,
      hiCrange]
  have hTDinf : T₀ ⊓ D₀ = ⊥ := by
    change T.map iC ⊓ D.map iC = ⊥
    rw [← Submodule.map_inf iC hiC, hTD.inf_eq_bot, Submodule.map_bot]
  have hiDrange : iD.range = D₀ := by
    change (iC.comp D.subtype).range = D.map iC
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hUVsup : U₀ ⊔ V₀ = D₀ := by
    change U.map iD ⊔ V.map iD = D₀
    rw [← Submodule.map_sup, hUV.sup_eq_top, Submodule.map_top,
      hiDrange]
  have hUVinf : U₀ ⊓ V₀ = ⊥ := by
    change U.map iD ⊓ V.map iD = ⊥
    rw [← Submodule.map_inf iD hiD, hUV.inf_eq_bot, Submodule.map_bot]
  exact false_of_three_simple_squareZero_radical_summands
    (k := k) e hall Hthin L hLtop S₀ C₀ T₀ D₀ U₀ V₀
      hS₀simple hT₀simple hU₀simple hSCsup hSCinf
      hTDsup hTDinf hUVsup hUVinf

end MagnitudeConjecture.RightModule
