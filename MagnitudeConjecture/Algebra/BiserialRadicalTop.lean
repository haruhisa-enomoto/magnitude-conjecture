import MagnitudeConjecture.Algebra.BiserialModule

/-!
# The first radical layer of a nonuniserial biserial module

For a finite-length biserial module with simple top, nonuniseriality forces
the top of its Jacobson radical to have composition length two.  Consequently
that semisimple layer is the direct sum of two simple submodules.  This is the
radical-layer decomposition used in the direct Pogorzały--Skowroński
induction.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A semisimple uniserial module is simple unless it is zero. -/
theorem isSimpleOrZeroModule_of_uniserial_of_semisimple
    [IsSemisimpleModule R M]
    (hM : IsUniserialModule R M) :
    IsSimpleOrZeroModule R M := by
  by_cases hzero : Subsingleton M
  · exact Or.inl hzero
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hzero
    exact Or.inr
      (IsUniserialModule.isSimpleModule_of_semisimple_of_isIndecomposableModule
        hM.isIndecomposableModule)

/-- A simple-or-zero finite-length module has length at most one. -/
theorem IsSimpleOrZeroModule.length_le_one
    [IsArtinian R M] [IsNoetherian R M]
    (hM : IsSimpleOrZeroModule R M) :
    Module.length R M ≤ 1 := by
  rcases hM with hzero | hsimple
  · have hlen : Module.length R M = 0 :=
      Module.length_eq_zero_iff.mpr hzero
    rw [hlen]
    norm_num
  · rw [Module.length_eq_one_iff.mpr hsimple]

/-- The image of a uniserial module under a linear map is uniserial. -/
theorem IsUniserialModule.range
    {N : Type v} [AddCommGroup N] [Module R N]
    (hM : IsUniserialModule R M) (f : M →ₗ[R] N) :
    IsUniserialModule R (LinearMap.range f) :=
  IsUniserialModule.congr f.quotKerEquivRange (hM.quotient f.ker)

/-- The top of the Jacobson radical of a finite-length biserial module has
composition length at most two. -/
theorem top_jacobson_length_le_two_of_biserial
    [IsSemiprimaryRing R] [IsArtinian R M] [IsNoetherian R M]
    (hbis : IsBiserialModule R M) :
    Module.length R
      (Module.jacobson R M ⧸
        Module.jacobson R (Module.jacobson R M)) ≤ 2 := by
  let J := Module.jacobson R M
  let TopJ := J ⧸ Module.jacobson R J
  letI : IsSemisimpleModule R TopJ := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson R J
  rcases hbis with ⟨U, V, hsup, hU, hV, _⟩
  have hUJ : U ≤ J := by
    change U ≤ Module.jacobson R M
    rw [← hsup]
    exact le_sup_left
  have hVJ : V ≤ J := by
    change V ≤ Module.jacobson R M
    rw [← hsup]
    exact le_sup_right
  let UJ : Submodule R J := U.comap J.subtype
  let VJ : Submodule R J := V.comap J.subtype
  have hUJuni : IsUniserialModule R UJ :=
    IsUniserialModule.congr
      (Submodule.comapSubtypeEquivOfLe hUJ).symm hU
  have hVJuni : IsUniserialModule R VJ :=
    IsUniserialModule.congr
      (Submodule.comapSubtypeEquivOfLe hVJ).symm hV
  have hUVtop : UJ ⊔ VJ = ⊤ := by
    apply Submodule.map_injective_of_injective J.subtype_injective
    rw [Submodule.map_sup, Submodule.map_comap_subtype,
      Submodule.map_comap_subtype, inf_eq_right.mpr hUJ,
      inf_eq_right.mpr hVJ, hsup]
    simp [J]
  let q : J →ₗ[R] TopJ := (Module.jacobson R J).mkQ
  let Ubar : Submodule R TopJ := UJ.map q
  let Vbar : Submodule R TopJ := VJ.map q
  have hUbarUni : IsUniserialModule R Ubar := by
    let fU : UJ →ₗ[R] TopJ := q.domRestrict UJ
    have hrange : LinearMap.range fU = Ubar := by
      ext x
      simp [fU, Ubar]
    rw [← hrange]
    exact hUJuni.range fU
  have hVbarUni : IsUniserialModule R Vbar := by
    let fV : VJ →ₗ[R] TopJ := q.domRestrict VJ
    have hrange : LinearMap.range fV = Vbar := by
      ext x
      simp [fV, Vbar]
    rw [← hrange]
    exact hVJuni.range fV
  have hUbarSOZ : IsSimpleOrZeroModule R Ubar := by
    letI : IsSemisimpleModule R Ubar := inferInstance
    exact isSimpleOrZeroModule_of_uniserial_of_semisimple hUbarUni
  have hVbarSOZ : IsSimpleOrZeroModule R Vbar := by
    letI : IsSemisimpleModule R Vbar := inferInstance
    exact isSimpleOrZeroModule_of_uniserial_of_semisimple hVbarUni
  have hUbarLength : Module.length R Ubar ≤ 1 := hUbarSOZ.length_le_one
  have hVbarLength : Module.length R Vbar ≤ 1 := hVbarSOZ.length_le_one
  have hUVbarTop : Ubar ⊔ Vbar = ⊤ := by
    change UJ.map q ⊔ VJ.map q = ⊤
    rw [← Submodule.map_sup, hUVtop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr
      (Module.jacobson R J).mkQ_surjective
  let f : (Ubar × Vbar) →ₗ[R] TopJ :=
    Ubar.subtype.coprod Vbar.subtype
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    dsimp only [f]
    rw [LinearMap.range_coprod,
      Submodule.range_subtype, Submodule.range_subtype, hUVbarTop]
  have hTopJLengthLeProd : Module.length R TopJ ≤
      Module.length R (Ubar × Vbar) :=
    Module.length_le_of_surjective f hf
  rw [Module.length_prod] at hTopJLengthLeProd
  exact hTopJLengthLeProd.trans (by
    calc
      Module.length R Ubar + Module.length R Vbar ≤ 1 + 1 :=
        add_le_add hUbarLength hVbarLength
      _ = 2 := by norm_num)

/-- If a finite-length module with simple top is biserial but not uniserial,
then the top of its Jacobson radical has composition length two. -/
theorem top_jacobson_length_eq_two_of_biserial_of_not_uniserial
    [IsSemiprimaryRing R] [IsArtinian R M] [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hbis : IsBiserialModule R M)
    (hnotuni : ¬ IsUniserialModule R M) :
    Module.length R
      (Module.jacobson R M ⧸
        Module.jacobson R (Module.jacobson R M)) = 2 := by
  let J := Module.jacobson R M
  let TopJ := J ⧸ Module.jacobson R J
  have hJnontrivial : Nontrivial J := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hJzero
    apply hnotuni
    exact IsUniserialModule.of_simpleTop_of_jacobson htop
      (IsUniserialModule.of_subsingleton (R := R) (M := J))
  letI : Nontrivial J := hJnontrivial
  have hTopJLengthLe : Module.length R TopJ ≤ 2 :=
    top_jacobson_length_le_two_of_biserial hbis
  have hTopJnontrivial : Nontrivial TopJ :=
    Submodule.Quotient.nontrivial_iff.mpr
      (Module.jacobson_lt_top R J).ne
  have hTopJLengthPos : 0 < Module.length R TopJ := by
    rw [Module.length_pos_iff]
    exact hTopJnontrivial
  have hTopJnotSimple : ¬ IsSimpleModule R TopJ := by
    intro hsimple
    exact hnotuni
      (IsBiserialModule.uniserial_of_biserial_of_simple_top_of_jacobson
        htop hbis hsimple)
  apply le_antisymm hTopJLengthLe
  by_contra hnotTwoLe
  have hltTwo : Module.length R TopJ < 2 := lt_of_not_ge hnotTwoLe
  have hleOne : Module.length R TopJ ≤ 1 := ENat.lt_two_iff.mp hltTwo
  have honeLe : 1 ≤ Module.length R TopJ :=
    Order.one_le_iff_ne_zero.mpr hTopJLengthPos.ne'
  have hlengthOne : Module.length R TopJ = 1 :=
    le_antisymm hleOne honeLe
  exact hTopJnotSimple (Module.length_eq_one_iff.mp hlengthOne)

/-- The length-two semisimple top of the radical splits as two complementary
simple submodules. -/
theorem exists_complementary_simple_top_jacobson_of_biserial_of_not_uniserial
    [IsSemiprimaryRing R] [IsArtinian R M] [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hbis : IsBiserialModule R M)
    (hnotuni : ¬ IsUniserialModule R M) :
    ∃ S T : Submodule R
        (Module.jacobson R M ⧸
          Module.jacobson R (Module.jacobson R M)),
      IsSimpleModule R S ∧ IsSimpleModule R T ∧ IsCompl S T := by
  let J := Module.jacobson R M
  let TopJ := J ⧸ Module.jacobson R J
  have hlength : Module.length R TopJ = 2 :=
    top_jacobson_length_eq_two_of_biserial_of_not_uniserial
      htop hbis hnotuni
  letI : IsSemisimpleModule R TopJ := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson R J
  have hTopJnotSimple : ¬ IsSimpleModule R TopJ := by
    intro hsimple
    exact hnotuni
      (IsBiserialModule.uniserial_of_biserial_of_simple_top_of_jacobson
        htop hbis hsimple)
  have hTopJnotUniserial : ¬ IsUniserialModule R TopJ := by
    intro huni
    rcases isSimpleOrZeroModule_of_uniserial_of_semisimple huni with
      hzero | hsimple
    · have hlenzero : Module.length R TopJ = 0 :=
        Module.length_eq_zero_iff.mpr hzero
      rw [hlength] at hlenzero
      norm_num at hlenzero
    · exact hTopJnotSimple hsimple
  rw [IsUniserialModule, total_def] at hTopJnotUniserial
  push Not at hTopJnotUniserial
  obtain ⟨S, T, hST, hTS⟩ := hTopJnotUniserial
  obtain ⟨hSsimple, hTsimple, hcompl⟩ :=
    IsBiserialModule.simple_isCompl_of_length_eq_two_of_incomparable
      hlength hST hTS
  exact ⟨S, T, hSsimple, hTsimple, hcompl⟩

end MagnitudeConjecture
