import MagnitudeConjecture.Algebra.BiserialRadicalTop
import MagnitudeConjecture.Algebra.SocleModule

/-!
# Semisimple submodules of biserial modules

A semisimple submodule contained in the sum of two uniserial branches has
composition length at most two.  This is the structural length bound used for
the intersection of the two local branches in the Pogorzały--Skowroński
induction.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Every semisimple submodule is contained in the socle of the ambient
module. -/
theorem semisimple_submodule_le_moduleSocle
    (P : Submodule R M) [IsSemisimpleModule R P] :
    P ≤ moduleSocle R M := by
  have hmap : (moduleSocle R P).map P.subtype ≤ moduleSocle R M :=
    map_moduleSocle_le_of_injective P.subtype P.subtype_injective
  rw [show moduleSocle R P = ⊤ from
    IsSemisimpleModule.sSup_simples_eq_top R P,
    Submodule.map_top, Submodule.range_subtype] at hmap
  exact hmap

/-- A semisimple submodule contained in the sum of two uniserial submodules
has composition length at most two.  Quotienting by the first branch makes
the kernel embed in the first branch and the range embed in the second. -/
theorem semisimple_submodule_length_le_two_of_le_sup_uniserial
    [IsArtinian R M] [IsNoetherian R M]
    (U V P : Submodule R M)
    (hU : IsUniserialModule R U)
    (hV : IsUniserialModule R V)
    (hP : P ≤ U ⊔ V)
    [IsSemisimpleModule R P] :
    Module.length R P ≤ 2 := by
  let f : P →ₗ[R] (M ⧸ U) := U.mkQ.comp P.subtype
  let g : V →ₗ[R] (M ⧸ U) := U.mkQ.comp V.subtype
  let K : Submodule R P := LinearMap.ker f
  let Q : Submodule R (M ⧸ U) := LinearMap.range f
  let G : Submodule R (M ⧸ U) := LinearMap.range g
  let jK : K →ₗ[R] U :=
    (P.subtype.comp K.subtype).codRestrict U (by
      intro x
      have hx : f x.1 = 0 := LinearMap.mem_ker.mp x.2
      change U.mkQ x.1.1 = 0 at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact hx)
  have hjK : Function.Injective jK := by
    intro x y hxy
    have hval : (x.1.1 : M) = y.1.1 :=
      congrArg (fun z : U ↦ (z : M)) hxy
    exact Subtype.ext (Subtype.ext hval)
  have hKuni : IsUniserialModule R K :=
    IsUniserialModule.of_injective hU jK hjK
  letI : IsSemisimpleModule R K := inferInstance
  have hKlength : Module.length R K ≤ 1 :=
    (isSimpleOrZeroModule_of_uniserial_of_semisimple hKuni).length_le_one
  have hQG : Q ≤ G := by
    rintro q ⟨p, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hP p.2)
    refine ⟨⟨v, hv⟩, ?_⟩
    change U.mkQ v = U.mkQ p.1
    rw [← huv, map_add]
    have hu0 : U.mkQ u = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hu
    rw [hu0, zero_add]
  have hGuni : IsUniserialModule R G := hV.range g
  let jQ : Q →ₗ[R] G :=
    Q.subtype.codRestrict G (fun x ↦ hQG x.2)
  have hjQ : Function.Injective jQ := by
    intro x y hxy
    have hval : (x.1 : M ⧸ U) = y.1 :=
      congrArg (fun z : G ↦ (z : M ⧸ U)) hxy
    exact Subtype.ext hval
  have hQuni : IsUniserialModule R Q :=
    IsUniserialModule.of_injective hGuni jQ hjQ
  letI : IsSemisimpleModule R Q := IsSemisimpleModule.range f
  have hQlength : Module.length R Q ≤ 1 :=
    (isSimpleOrZeroModule_of_uniserial_of_semisimple hQuni).length_le_one
  have hlength : Module.length R P = Module.length R K + Module.length R Q := by
    change Module.length R P =
      Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f)
    have hexact : Function.Exact
        (LinearMap.ker f).subtype f.rangeRestrict := by
      rw [← LinearMap.ker_rangeRestrict f]
      exact f.rangeRestrict.exact_subtype_ker_map
    exact Module.length_eq_add_of_exact
      (LinearMap.ker f).subtype f.rangeRestrict
      (LinearMap.ker f).subtype_injective f.surjective_rangeRestrict
      hexact
  rw [hlength]
  calc
    Module.length R K + Module.length R Q ≤ 1 + 1 :=
      add_le_add hKlength hQlength
    _ = 2 := by norm_num

/-- A semisimple submodule of the radical of a biserial module has
composition length at most two. -/
theorem semisimple_submodule_length_le_two_of_biserial_of_le_jacobson
    [IsArtinian R M] [IsNoetherian R M]
    (hM : IsBiserialModule R M)
    (P : Submodule R M) (hP : P ≤ Module.jacobson R M)
    [IsSemisimpleModule R P] :
    Module.length R P ≤ 2 := by
  obtain ⟨U, V, hsup, hU, hV, -⟩ := hM
  apply semisimple_submodule_length_le_two_of_le_sup_uniserial
    U V P hU hV
  rwa [hsup]

/-- A semisimple length-two submodule of the radical of a local biserial
module is its whole socle. -/
theorem semisimple_submodule_eq_moduleSocle_of_biserial_of_simple_top_of_length_eq_two
    [IsArtinian R M] [IsNoetherian R M]
    (hMbis : IsBiserialModule R M)
    (hMtop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (P : Submodule R M) [IsSemisimpleModule R P]
    (hPjac : P ≤ Module.jacobson R M)
    (hPlength : Module.length R P = 2) :
    P = moduleSocle R M := by
  apply le_antisymm
  · exact semisimple_submodule_le_moduleSocle P
  · unfold moduleSocle
    apply sSup_le
    intro S hSsimple
    have hSneTop : S ≠ ⊤ := by
      intro hStop
      letI : IsSimpleModule R S := hSsimple
      have hMsimple : IsSimpleModule R M :=
        IsSimpleModule.congr (LinearEquiv.ofTop S hStop).symm
      have hMlength : Module.length R M = 1 :=
        Module.length_eq_one_iff.mpr hMsimple
      have hPleM : Module.length R P ≤ Module.length R M :=
        Module.length_le_of_injective P.subtype P.subtype_injective
      rw [hPlength, hMlength] at hPleM
      norm_num at hPleM
    have hSjac : S ≤ Module.jacobson R M :=
      IsUniserialModule.le_jacobson_of_ne_top_of_simple_top hMtop hSneTop
    letI : IsSimpleModule R S := hSsimple
    letI : IsSemisimpleModule R ↥(P ⊔ S : Submodule R M) :=
      IsSemisimpleModule.sup (R := R) inferInstance inferInstance
    have hsupLength :
        Module.length R ↥(P ⊔ S : Submodule R M) ≤ 2 :=
      semisimple_submodule_length_le_two_of_biserial_of_le_jacobson
        hMbis (P ⊔ S) (sup_le hPjac hSjac)
    by_contra hSle
    have hPlt : P < P ⊔ S :=
      lt_of_le_of_ne le_sup_left (by
        intro hEq
        apply hSle
        exact le_sup_right.trans hEq.symm.le)
    have hlengthLt :
        Module.length R P < Module.length R ↥(P ⊔ S : Submodule R M) := by
      simpa only [Module.length_submodule] using
        (Submodule.height_strictMono hPlt)
    rw [hPlength] at hlengthLt
    exact (not_lt_of_ge hsupLength) hlengthLt

/-- A nonzero finite-length module of length at most two is simple as soon
as the length-two case has been excluded. -/
theorem isSimpleModule_of_nontrivial_of_length_le_two_of_ne_two
    [Nontrivial M]
    (hle : Module.length R M ≤ 2)
    (hne : Module.length R M ≠ 2) :
    IsSimpleModule R M := by
  have hlt : Module.length R M < 2 := lt_of_le_of_ne hle hne
  have hleOne : Module.length R M ≤ 1 := ENat.lt_two_iff.mp hlt
  have hpos : 0 < Module.length R M := Module.length_pos
  have hOneLe : 1 ≤ Module.length R M :=
    Order.one_le_iff_ne_zero.mpr hpos.ne'
  exact Module.length_eq_one_iff.mp (le_antisymm hleOne hOneLe)

/-- A semisimple module of composition length two is a direct sum of two
simple submodules. -/
theorem exists_complementary_simple_of_semisimple_of_length_eq_two
    [IsArtinian R M] [IsNoetherian R M] [IsSemisimpleModule R M]
    (hlength : Module.length R M = 2) :
    ∃ S T : Submodule R M,
      IsSimpleModule R S ∧ IsSimpleModule R T ∧ IsCompl S T := by
  have hnotUniserial : ¬ IsUniserialModule R M := by
    intro huni
    rcases isSimpleOrZeroModule_of_uniserial_of_semisimple huni with
      hzero | hsimple
    · have hzeroLength : Module.length R M = 0 :=
        Module.length_eq_zero_iff.mpr hzero
      rw [hlength] at hzeroLength
      norm_num at hzeroLength
    · have honeLength : Module.length R M = 1 :=
        Module.length_eq_one_iff.mpr hsimple
      rw [hlength] at honeLength
      norm_num at honeLength
  rw [IsUniserialModule, total_def] at hnotUniserial
  push Not at hnotUniserial
  obtain ⟨S, T, hST, hTS⟩ := hnotUniserial
  obtain ⟨hSsimple, hTsimple, hcompl⟩ :=
    IsBiserialModule.simple_isCompl_of_length_eq_two_of_incomparable
      hlength hST hTS
  exact ⟨S, T, hSsimple, hTsimple, hcompl⟩

/-- A module whose Jacobson radical is semisimple of composition length at
most two is biserial.  At length two, split the radical into two simple
summands; below length two, the radical is simple or zero. -/
theorem IsBiserialModule.of_semisimple_jacobson_length_le_two
    [IsArtinian R M] [IsNoetherian R M]
    [IsSemisimpleModule R (Module.jacobson R M)]
    (hlength : Module.length R (Module.jacobson R M) ≤ 2) :
    IsBiserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  by_cases htwo : Module.length R J = 2
  · obtain ⟨S, T, hSsimple, hTsimple, hcompl⟩ :=
      exists_complementary_simple_of_semisimple_of_length_eq_two htwo
    let S' : Submodule R M := S.map J.subtype
    let T' : Submodule R M := T.map J.subtype
    have hS'equiv : S ≃ₗ[R] S' :=
      Submodule.equivMapOfInjective J.subtype J.subtype_injective S
    have hT'equiv : T ≃ₗ[R] T' :=
      Submodule.equivMapOfInjective J.subtype J.subtype_injective T
    have hsup : S' ⊔ T' = Module.jacobson R M := by
      change S.map J.subtype ⊔ T.map J.subtype = J
      rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top,
        Submodule.range_subtype]
    have hinf : S' ⊓ T' = ⊥ := by
      change S.map J.subtype ⊓ T.map J.subtype = ⊥
      rw [← Submodule.map_inf J.subtype J.subtype_injective,
        hcompl.inf_eq_bot, Submodule.map_bot]
    refine ⟨S', T', hsup, ?_, ?_, ?_⟩
    · exact IsUniserialModule.congr hS'equiv
        (IsBiserialModule.uniserial_of_simple hSsimple)
    · exact IsUniserialModule.congr hT'equiv
        (IsBiserialModule.uniserial_of_simple hTsimple)
    · rw [hinf]
      exact IsSimpleOrZeroModule.of_subsingleton
  · by_cases hJ : J = ⊥
    · exact IsBiserialModule.of_jacobson_eq_bot hJ
    · have hJnontrivial : Nontrivial J :=
        Submodule.nontrivial_iff_ne_bot.mpr hJ
      letI : Nontrivial J := hJnontrivial
      have hJsimple : IsSimpleModule R J :=
        isSimpleModule_of_nontrivial_of_length_le_two_of_ne_two
          hlength htwo
      exact IsBiserialModule.of_uniserial_jacobson
        (IsBiserialModule.uniserial_of_simple hJsimple)

/-- A semisimple finite-length module of length greater than two admits
three successive simple summands.  The nested complement form is convenient
for later quotient constructions: `M = S ⊕ C`, `C = T ⊕ D`, and
`D = U ⊕ V`. -/
theorem exists_three_simple_nested_complements_of_semisimple_of_length_not_le_two
    [IsArtinian R M] [IsNoetherian R M] [IsSemisimpleModule R M]
    (hlength : ¬ Module.length R M ≤ 2) :
    ∃ (S C : Submodule R M) (T D : Submodule R C)
        (U V : Submodule R D),
      IsSimpleModule R S ∧ IsCompl S C ∧
      IsSimpleModule R T ∧ IsCompl T D ∧
      IsSimpleModule R U ∧ IsCompl U V := by
  have hMnontrivial : Nontrivial M := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hMzero
    apply hlength
    rw [Module.length_eq_zero_iff.mpr hMzero]
    norm_num
  letI : Nontrivial M := hMnontrivial
  obtain ⟨S, hSsimple⟩ :=
    IsSemisimpleModule.exists_simple_submodule R M
  obtain ⟨C, hSC⟩ := exists_isCompl S
  have hSCength : Module.length R M =
      Module.length R S + Module.length R C := by
    calc
      Module.length R M = Module.length R (S × C) :=
        (S.prodEquivOfIsCompl C hSC).length_eq.symm
      _ = Module.length R S + Module.length R C :=
        Module.length_prod R S C
  have hClength : 2 ≤ Module.length R C := by
    by_contra hC
    have hCleOne : Module.length R C ≤ 1 :=
      ENat.lt_two_iff.mp (lt_of_not_ge hC)
    apply hlength
    calc
      Module.length R M = 1 + Module.length R C := by
        rw [hSCength, Module.length_eq_one_iff.mpr hSsimple]
      _ ≤ 1 + 1 := add_le_add_right hCleOne 1
      _ = 2 := by norm_num
  have hCnontrivial : Nontrivial C := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hCzero
    have hCzeroLength : Module.length R C = 0 :=
      Module.length_eq_zero_iff.mpr hCzero
    rw [hCzeroLength] at hClength
    norm_num at hClength
  letI : Nontrivial C := hCnontrivial
  obtain ⟨T, hTsimple⟩ :=
    IsSemisimpleModule.exists_simple_submodule R C
  obtain ⟨D, hTD⟩ := exists_isCompl T
  have hTDeength : Module.length R C =
      Module.length R T + Module.length R D := by
    calc
      Module.length R C = Module.length R (T × D) :=
        (T.prodEquivOfIsCompl D hTD).length_eq.symm
      _ = Module.length R T + Module.length R D :=
        Module.length_prod R T D
  have hDnontrivial : Nontrivial D := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hDzero
    have hDzeroLength : Module.length R D = 0 :=
      Module.length_eq_zero_iff.mpr hDzero
    have hCone : Module.length R C = 1 := by
      rw [hTDeength, Module.length_eq_one_iff.mpr hTsimple,
        hDzeroLength]
      norm_num
    rw [hCone] at hClength
    norm_num at hClength
  letI : Nontrivial D := hDnontrivial
  obtain ⟨U, hUsimple⟩ :=
    IsSemisimpleModule.exists_simple_submodule R D
  obtain ⟨V, hUV⟩ := exists_isCompl U
  exact ⟨S, C, T, D, U, V, hSsimple, hSC, hTsimple, hTD,
    hUsimple, hUV⟩

end MagnitudeConjecture
