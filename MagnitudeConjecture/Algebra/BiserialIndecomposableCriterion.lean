import MagnitudeConjecture.Algebra.BiserialModule
import MagnitudeConjecture.Algebra.SocleModule

/-!
# An indecomposability criterion for the biserial obstruction modules

The kernel modules in the Pogorzały--Skowroński proof are shown
indecomposable by considering a hypothetical complementary decomposition.
Induction makes both summands uniserial; one summand escapes an ambient
radical and the element calculation then forces that summand to contain the
whole socle.  The other nonzero summand must meet the socle, contradicting
disjointness.  This file packages the general lattice argument, leaving only
the source-specific element calculation as a later obligation.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If the ambient socle has composition length two, the two nonzero
summands in any complementary decomposition both have simple socle. -/
theorem simple_moduleSocles_of_isCompl_of_length_eq_two
    [IsArtinian R M]
    (P Q : Submodule R M) (hPQ : IsCompl P Q)
    (hP : P ≠ ⊥) (hQ : Q ≠ ⊥)
    (hlength : Module.length R (moduleSocle R M) = 2) :
    IsSimpleModule R (moduleSocle R P) ∧
      IsSimpleModule R (moduleSocle R Q) := by
  letI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hP
  letI : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
  have hPsocle : moduleSocle R P ≠ ⊥ := moduleSocle_ne_bot
  have hQsocle : moduleSocle R Q ≠ ⊥ := moduleSocle_ne_bot
  have hPlengthPos : 0 < Module.length R (moduleSocle R P) :=
    Module.length_pos_iff.mpr
      (Submodule.nontrivial_iff_ne_bot.mpr hPsocle)
  have hQlengthPos : 0 < Module.length R (moduleSocle R Q) :=
    Module.length_pos_iff.mpr
      (Submodule.nontrivial_iff_ne_bot.mpr hQsocle)
  have hsum :
      Module.length R (moduleSocle R P) +
          Module.length R (moduleSocle R Q) = 2 := by
    rw [← length_moduleSocle_eq_add_of_isCompl P Q hPQ]
    exact hlength
  have hPlengthNeTop :
      Module.length R (moduleSocle R P) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hsum
    exact ENat.top_ne_ofNat 2 hsum
  have hQlengthNeTop :
      Module.length R (moduleSocle R Q) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsum
    exact ENat.top_ne_ofNat 2 hsum
  have hPlength : Module.length R (moduleSocle R P) = 1 := by
    apply le_antisymm
    · apply ENat.lt_two_iff.mp
      have hlt : Module.length R (moduleSocle R P) <
          Module.length R (moduleSocle R P) +
            Module.length R (moduleSocle R Q) := by
        calc
          Module.length R (moduleSocle R P) =
              Module.length R (moduleSocle R P) + 0 :=
            (add_zero _).symm
          _ < Module.length R (moduleSocle R P) +
              Module.length R (moduleSocle R Q) :=
            WithTop.add_lt_add_left hPlengthNeTop hQlengthPos
      exact hlt.trans_eq hsum
    · exact Order.one_le_iff_ne_zero.mpr hPlengthPos.ne'
  have hQlength : Module.length R (moduleSocle R Q) = 1 := by
    apply le_antisymm
    · apply ENat.lt_two_iff.mp
      have hlt : Module.length R (moduleSocle R Q) <
          Module.length R (moduleSocle R P) +
            Module.length R (moduleSocle R Q) := by
        calc
          Module.length R (moduleSocle R Q) =
              0 + Module.length R (moduleSocle R Q) :=
            (zero_add _).symm
          _ < Module.length R (moduleSocle R P) +
              Module.length R (moduleSocle R Q) :=
            WithTop.add_lt_add_right hQlengthNeTop hPlengthPos
      exact hlt.trans_eq hsum
    · exact Order.one_le_iff_ne_zero.mpr hQlengthPos.ne'
  exact ⟨Module.length_eq_one_iff.mp hPlength,
    Module.length_eq_one_iff.mp hQlength⟩

/-- A complementary decomposition is impossible if induction makes both
nonzero summands uniserial and every uniserial summand escaping `J` contains
the whole socle. -/
theorem isIndecomposableModule_of_complement_uniserial_of_capture_socle
    [IsArtinian R M] [Nontrivial M]
    (J : Submodule R M) (hJ : J ≠ ⊤)
    (huniserial : ∀ P Q : Submodule R M,
      IsCompl P Q → P ≠ ⊥ → Q ≠ ⊥ →
        IsUniserialModule R P ∧ IsUniserialModule R Q)
    (hcapture : ∀ P : Submodule R M,
      P ≠ ⊥ → IsUniserialModule R P → ¬ P ≤ J →
        moduleSocle R M ≤ P) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  apply
    QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
  intro P Q hPQ
  by_cases hP : P = ⊥
  · exact Or.inl hP
  by_cases hQ : Q = ⊥
  · exact Or.inr hQ
  exfalso
  obtain ⟨hPuniserial, hQuniserial⟩ :=
    huniserial P Q hPQ hP hQ
  have houtside : ¬ P ≤ J ∨ ¬ Q ≤ J := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hJ
    apply top_unique
    rw [← hPQ.sup_eq_top]
    exact sup_le h.1 h.2
  have contradiction_of_capture
      (U V : Submodule R M) (hUV : IsCompl U V)
      (hV : V ≠ ⊥) (hsocleU : moduleSocle R M ≤ U) : False := by
    letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
    obtain ⟨S, hSsimple, -⟩ :=
      exists_simple_submodule_le
        (R := R) (M := V) (⊤ : Submodule R V) top_ne_bot
    let T : Submodule R M := S.map V.subtype
    have hTsimple : IsSimpleModule R T :=
      IsBiserialModule.simple_map_of_injective
        V.subtype V.subtype_injective S hSsimple
    have hTsocle : T ≤ moduleSocle R M :=
      le_moduleSocle_of_simple T hTsimple
    have hTV : T ≤ V := Submodule.map_subtype_le V S
    have hTbot : T ≤ ⊥ := by
      rw [← hUV.inf_eq_bot]
      exact le_inf (hTsocle.trans hsocleU) hTV
    exact (isSimpleModule_iff_isAtom.mp hTsimple).ne_bot
      (bot_unique hTbot)
  rcases houtside with hPJ | hQJ
  · exact contradiction_of_capture P Q hPQ hQ
      (hcapture P hP hPuniserial hPJ)
  · exact contradiction_of_capture Q P hPQ.symm hP
      (hcapture Q hQ hQuniserial hQJ)

/-- The precise two-layer length argument behind the source's assertion that
the two nonzero summands of its length-five kernel are uniserial.  The final
two premises are the summand-specific multiplicity-free bounds: neither
complement can contribute both factors in the next socle layer. -/
theorem complement_uniserial_of_length_five_of_two_socle_layers
    [IsArtinian R M] [IsNoetherian R M]
    (hlength : Module.length R M = 5)
    (hsocleLength : Module.length R (moduleSocle R M) = 2)
    (hnextLength : Module.length R
      (moduleSocle R (M ⧸ moduleSocle R M)) = 2)
    (P Q : Submodule R M) (hPQ : IsCompl P Q)
    (hP : P ≠ ⊥) (hQ : Q ≠ ⊥)
    (hpNextLe : Module.length R
      (moduleSocle R (P ⧸ moduleSocle R P)) ≤ 1)
    (hqNextLe : Module.length R
      (moduleSocle R (Q ⧸ moduleSocle R Q)) ≤ 1) :
    IsUniserialModule R P ∧ IsUniserialModule R Q := by
  obtain ⟨hPsocle, hQsocle⟩ :=
    simple_moduleSocles_of_isCompl_of_length_eq_two
      P Q hPQ hP hQ hsocleLength
  let pNext := Module.length R
    (moduleSocle R (P ⧸ moduleSocle R P))
  let qNext := Module.length R
    (moduleSocle R (Q ⧸ moduleSocle R Q))
  have hnextSum : pNext + qNext = 2 := by
    rw [← length_quotientModuleSocleLayer_eq_add_of_isCompl P Q hPQ]
    exact hnextLength
  change pNext ≤ 1 at hpNextLe
  change qNext ≤ 1 at hqNextLe
  have hpqNext : pNext = 1 ∧ qNext = 1 := by
    rcases Order.le_one_iff.mp hpNextLe with hp | hp
    · rcases Order.le_one_iff.mp hqNextLe with hq | hq
      · rw [hp, hq] at hnextSum
        norm_num at hnextSum
      · rw [hp, hq] at hnextSum
        norm_num at hnextSum
    · rcases Order.le_one_iff.mp hqNextLe with hq | hq
      · rw [hp, hq] at hnextSum
        norm_num at hnextSum
      · exact ⟨hp, hq⟩
  have hPnextSimple : IsSimpleModule R
      (moduleSocle R (P ⧸ moduleSocle R P)) :=
    Module.length_eq_one_iff.mp hpqNext.1
  have hQnextSimple : IsSimpleModule R
      (moduleSocle R (Q ⧸ moduleSocle R Q)) :=
    Module.length_eq_one_iff.mp hpqNext.2
  have hPsocleLength : Module.length R (moduleSocle R P) = 1 :=
    Module.length_eq_one_iff.mpr hPsocle
  have hQsocleLength : Module.length R (moduleSocle R Q) = 1 :=
    Module.length_eq_one_iff.mpr hQsocle
  have hPexact : Module.length R P =
      Module.length R (moduleSocle R P) +
        Module.length R (P ⧸ moduleSocle R P) :=
    Module.length_eq_add_of_exact
      (moduleSocle R P).subtype (moduleSocle R P).mkQ
      (moduleSocle R P).subtype_injective
      (moduleSocle R P).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (moduleSocle R P))
  have hQexact : Module.length R Q =
      Module.length R (moduleSocle R Q) +
        Module.length R (Q ⧸ moduleSocle R Q) :=
    Module.length_eq_add_of_exact
      (moduleSocle R Q).subtype (moduleSocle R Q).mkQ
      (moduleSocle R Q).subtype_injective
      (moduleSocle R Q).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (moduleSocle R Q))
  have hPquotOne : 1 ≤ Module.length R (P ⧸ moduleSocle R P) := by
    calc
      1 = Module.length R
          (moduleSocle R (P ⧸ moduleSocle R P)) := hpqNext.1.symm
      _ ≤ Module.length R (P ⧸ moduleSocle R P) :=
        Module.length_le_of_injective
          (moduleSocle R (P ⧸ moduleSocle R P)).subtype
          (moduleSocle R (P ⧸ moduleSocle R P)).subtype_injective
  have hQquotOne : 1 ≤ Module.length R (Q ⧸ moduleSocle R Q) := by
    calc
      1 = Module.length R
          (moduleSocle R (Q ⧸ moduleSocle R Q)) := hpqNext.2.symm
      _ ≤ Module.length R (Q ⧸ moduleSocle R Q) :=
        Module.length_le_of_injective
          (moduleSocle R (Q ⧸ moduleSocle R Q)).subtype
          (moduleSocle R (Q ⧸ moduleSocle R Q)).subtype_injective
  have hPtwo : 2 ≤ Module.length R P := by
    calc
      2 = 1 + 1 := by norm_num
      _ ≤ 1 + Module.length R (P ⧸ moduleSocle R P) :=
        add_le_add_right hPquotOne 1
      _ = Module.length R P := by rw [hPsocleLength] at hPexact; exact hPexact.symm
  have hQtwo : 2 ≤ Module.length R Q := by
    calc
      2 = 1 + 1 := by norm_num
      _ ≤ 1 + Module.length R (Q ⧸ moduleSocle R Q) :=
        add_le_add_right hQquotOne 1
      _ = Module.length R Q := by rw [hQsocleLength] at hQexact; exact hQexact.symm
  have hlengthSum : Module.length R P + Module.length R Q = 5 := by
    calc
      Module.length R P + Module.length R Q =
          Module.length R (P × Q) := (Module.length_prod R P Q).symm
      _ = Module.length R M := (P.prodEquivOfIsCompl Q hPQ).length_eq
      _ = 5 := hlength
  have hPleThree : Module.length R P ≤ 3 := by
    apply (ENat.add_le_add_iff_right (by norm_num : (2 : ℕ∞) ≠ ⊤)).mp
    calc
      Module.length R P + 2 ≤
          Module.length R P + Module.length R Q :=
        add_le_add_right hQtwo _
      _ = 5 := hlengthSum
      _ = 3 + 2 := by norm_num
  have hQleThree : Module.length R Q ≤ 3 := by
    apply (ENat.add_le_add_iff_left (by norm_num : (2 : ℕ∞) ≠ ⊤)).mp
    calc
      2 + Module.length R Q ≤
          Module.length R P + Module.length R Q :=
        add_le_add_left hPtwo _
      _ = 5 := hlengthSum
      _ = 2 + 3 := by norm_num
  have hPtwoOrThree : Module.length R P = 2 ∨ Module.length R P = 3 := by
    have hPfinite : Module.length R P ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num) hPleThree
    have hPcoe : (ENat.toNat (Module.length R P) : ℕ∞) =
        Module.length R P := ENat.coe_toNat hPfinite
    have hPnatTwo : 2 ≤ ENat.toNat (Module.length R P) := by
      rw [← hPcoe] at hPtwo
      exact_mod_cast hPtwo
    have hPnatThree : ENat.toNat (Module.length R P) ≤ 3 :=
      ENat.toNat_le_of_le_coe hPleThree
    have hPnat : ENat.toNat (Module.length R P) = 2 ∨
        ENat.toNat (Module.length R P) = 3 := by omega
    rcases hPnat with hPnat | hPnat
    · left
      calc
        Module.length R P = (ENat.toNat (Module.length R P) : ℕ∞) :=
          hPcoe.symm
        _ = 2 := by rw [hPnat]; norm_num
    · right
      calc
        Module.length R P = (ENat.toNat (Module.length R P) : ℕ∞) :=
          hPcoe.symm
        _ = 3 := by rw [hPnat]; norm_num
  have hQtwoOrThree : Module.length R Q = 2 ∨ Module.length R Q = 3 := by
    have hQfinite : Module.length R Q ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num) hQleThree
    have hQcoe : (ENat.toNat (Module.length R Q) : ℕ∞) =
        Module.length R Q := ENat.coe_toNat hQfinite
    have hQnatTwo : 2 ≤ ENat.toNat (Module.length R Q) := by
      rw [← hQcoe] at hQtwo
      exact_mod_cast hQtwo
    have hQnatThree : ENat.toNat (Module.length R Q) ≤ 3 :=
      ENat.toNat_le_of_le_coe hQleThree
    have hQnat : ENat.toNat (Module.length R Q) = 2 ∨
        ENat.toNat (Module.length R Q) = 3 := by omega
    rcases hQnat with hQnat | hQnat
    · left
      calc
        Module.length R Q = (ENat.toNat (Module.length R Q) : ℕ∞) :=
          hQcoe.symm
        _ = 2 := by rw [hQnat]; norm_num
    · right
      calc
        Module.length R Q = (ENat.toNat (Module.length R Q) : ℕ∞) :=
          hQcoe.symm
        _ = 3 := by rw [hQnat]; norm_num
  constructor
  · rcases hPtwoOrThree with hPtwo' | hPthree
    · exact uniserial_of_simpleSocle_of_length_eq_two hPsocle hPtwo'
    · exact uniserial_of_two_simple_socle_layers_of_length_eq_three
        hPsocle hPnextSimple hPthree
  · rcases hQtwoOrThree with hQtwo' | hQthree
    · exact uniserial_of_simpleSocle_of_length_eq_two hQsocle hQtwo'
    · exact uniserial_of_two_simple_socle_layers_of_length_eq_three
        hQsocle hQnextSimple hQthree

end MagnitudeConjecture
