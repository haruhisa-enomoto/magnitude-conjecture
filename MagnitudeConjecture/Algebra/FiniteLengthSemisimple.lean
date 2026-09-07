import MagnitudeConjecture.Algebra.UniserialModule

/-!
# Finite-length semisimplicity reductions

A nonsemisimple finite-length module contains a nonsimple indecomposable
submodule.  The proof uses a submodule of minimal nonsemisimple length and
does not require a separately chosen Krull--Schmidt decomposition.
-/

set_option autoImplicit false

noncomputable section

open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite-length nonsemisimple module has a nonsimple indecomposable
submodule. -/
theorem exists_nonsimple_indecomposable_submodule_of_not_semisimple
    [IsArtinian R M] [IsNoetherian R M]
    (hM : ¬ IsSemisimpleModule R M) :
    ∃ E : Submodule R M,
      Foundation.IsIndecomposableModule R E ∧
        ¬ IsSimpleModule R E := by
  classical
  let p : ℕ → Prop := fun n ↦
    ∃ E : Submodule R M,
      ¬ IsSemisimpleModule R E ∧
        ENat.toNat (Module.length R E) = n
  have hp : ∃ n, p n := by
    let T : Submodule R M := ⊤
    have hT : ¬ IsSemisimpleModule R T := by
      intro h
      letI : IsSemisimpleModule R T := h
      exact hM (IsSemisimpleModule.congr Submodule.topEquiv.symm)
    exact ⟨ENat.toNat (Module.length R T), T, hT, rfl⟩
  let n := Nat.find hp
  obtain ⟨E, hEnot, hElen⟩ := Nat.find_spec hp
  have hminimal {F : Submodule R M}
      (hFlen : ENat.toNat (Module.length R F) <
        ENat.toNat (Module.length R E)) :
      IsSemisimpleModule R F := by
    by_contra hFnot
    have hpf : p (ENat.toNat (Module.length R F)) :=
      ⟨F, hFnot, rfl⟩
    have hnle := Nat.find_min' hp hpf
    rw [hElen] at hFlen
    omega
  letI : Nontrivial E := by
    by_contra hnt
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hnt
    haveI : Subsingleton (Submodule R E) := by
      constructor
      intro P Q
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    exact hEnot ((isSemisimpleModule_iff R E).mpr
      Subsingleton.instComplementedLattice)
  have hEindec : Foundation.IsIndecomposableModule R E := by
    apply Foundation.isIndecomposableModule_of_forall_isCompl
    intro U V hUV
    by_contra hne
    push Not at hne
    obtain ⟨hUne, hVne⟩ := hne
    have hUtop : U ≠ ⊤ := by
      intro hU
      exact hVne (eq_bot_of_top_isCompl (hU ▸ hUV))
    have hVtop : V ≠ ⊤ := by
      intro hV
      exact hUne (eq_bot_of_isCompl_top (hV ▸ hUV))
    let Umap : Submodule R M := U.map E.subtype
    let Vmap : Submodule R M := V.map E.subtype
    let eU : U ≃ₗ[R] Umap :=
      Submodule.equivMapOfInjective E.subtype E.subtype_injective U
    let eV : V ≃ₗ[R] Vmap :=
      Submodule.equivMapOfInjective E.subtype E.subtype_injective V
    have hUlen : Module.length R U < Module.length R E :=
      Submodule.length_lt (R := R) hUtop
    have hVlen : Module.length R V < Module.length R E :=
      Submodule.length_lt (R := R) hVtop
    have hUnat : ENat.toNat (Module.length R Umap) <
        ENat.toNat (Module.length R E) := by
      rw [← eU.length_eq]
      have hUfinite : Module.length R U ≠ ⊤ := Module.length_ne_top
      have hEfinite : Module.length R E ≠ ⊤ := Module.length_ne_top
      rw [← ENat.coe_toNat hUfinite, ← ENat.coe_toNat hEfinite] at hUlen
      exact_mod_cast hUlen
    have hVnat : ENat.toNat (Module.length R Vmap) <
        ENat.toNat (Module.length R E) := by
      rw [← eV.length_eq]
      have hVfinite : Module.length R V ≠ ⊤ := Module.length_ne_top
      have hEfinite : Module.length R E ≠ ⊤ := Module.length_ne_top
      rw [← ENat.coe_toNat hVfinite, ← ENat.coe_toNat hEfinite] at hVlen
      exact_mod_cast hVlen
    have hUsemiMap : IsSemisimpleModule R Umap := hminimal hUnat
    have hVsemiMap : IsSemisimpleModule R Vmap := hminimal hVnat
    letI : IsSemisimpleModule R Umap := hUsemiMap
    letI : IsSemisimpleModule R Vmap := hVsemiMap
    letI : IsSemisimpleModule R U := IsSemisimpleModule.congr eU
    letI : IsSemisimpleModule R V := IsSemisimpleModule.congr eV
    apply hEnot
    exact isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun b : Bool ↦ Bool.rec V U b)
      (by rintro (_ | _) <;> assumption)
      (by simpa [iSup_bool_eq] using hUV.sup_eq_top)
  refine ⟨E, hEindec, ?_⟩
  intro hEsimple
  letI : IsSimpleModule R E := hEsimple
  exact hEnot inferInstance

/-- A finite-length nonsemisimple module contains a nonsimple
indecomposable submodule with simple top.  Choose a minimal nonsemisimple
submodule.  If its top split into two nonzero summands, their two proper
inverse images would be semisimple and would sum to the chosen submodule. -/
theorem exists_nonsimple_indecomposable_simpleTop_submodule_of_not_semisimple
    [IsArtinian R M] [IsNoetherian R M]
    (hM : ¬ IsSemisimpleModule R M) :
    ∃ E : Submodule R M,
      Foundation.IsIndecomposableModule R E ∧
        ¬ IsSimpleModule R E ∧
        IsSimpleModule R (E ⧸ Module.jacobson R E) := by
  let T : Submodule R M := ⊤
  have hT : ¬ IsSemisimpleModule R T := by
    intro h
    letI : IsSemisimpleModule R T := h
    exact hM (IsSemisimpleModule.congr Submodule.topEquiv.symm)
  obtain ⟨E, -, hEmin⟩ :=
    exists_minimal_le_of_wellFoundedLT
      (fun E : Submodule R M ↦ ¬ IsSemisimpleModule R E) T hT
  have hEnot : ¬ IsSemisimpleModule R E := hEmin.1
  letI : Nontrivial E := by
    by_contra hnt
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hnt
    haveI : Subsingleton (Submodule R E) := by
      constructor
      intro P Q
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    exact hEnot ((isSemisimpleModule_iff R E).mpr
      Subsingleton.instComplementedLattice)
  let J : Submodule R E := Module.jacobson R E
  have hJne : J ≠ ⊤ := (Module.jacobson_lt_top R E).ne
  letI : Nontrivial (E ⧸ J) :=
    Submodule.Quotient.nontrivial_iff.mpr hJne
  letI : IsSemisimpleModule R (E ⧸ J) := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson R E
  have hEtop : IsSimpleModule R (E ⧸ J) := by
    by_contra hnot
    have hsplit : ∃ P : Submodule R (E ⧸ J), P ≠ ⊥ ∧ P ≠ ⊤ := by
      by_contra h
      push Not at h
      letI : IsSimpleOrder (Submodule R (E ⧸ J)) := {
        exists_pair_ne := exists_pair_ne
          (α := Submodule R (E ⧸ J))
        eq_bot_or_eq_top := fun P ↦ by
          by_cases hP : P = ⊥
          · exact Or.inl hP
          · exact Or.inr (h P hP) }
      exact hnot IsSimpleModule.mk
    obtain ⟨P, hPbot, hPtop⟩ := hsplit
    obtain ⟨Q, hPQ⟩ := exists_isCompl P
    have hQbot : Q ≠ ⊥ := by
      intro hQ
      apply hPtop
      simpa [hQ] using hPQ.sup_eq_top
    have hQtop : Q ≠ ⊤ := by
      intro hQ
      apply hPbot
      simpa [hQ] using hPQ.inf_eq_bot
    let P' : Submodule R E := P.comap J.mkQ
    let Q' : Submodule R E := Q.comap J.mkQ
    have hP'proper : P' ≠ ⊤ := by
      intro hP'
      apply hPtop
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := J.mkQ_surjective y
      change J.mkQ x ∈ P
      change x ∈ P'
      rw [hP']
      trivial
    have hQ'proper : Q' ≠ ⊤ := by
      intro hQ'
      apply hQtop
      apply top_unique
      intro y _
      obtain ⟨x, rfl⟩ := J.mkQ_surjective y
      change J.mkQ x ∈ Q
      change x ∈ Q'
      rw [hQ']
      trivial
    have hP'Q'top : P' ⊔ Q' = ⊤ := by
      have hmap : (P' ⊔ Q').map J.mkQ = ⊤ := by
        dsimp only [P', Q']
        rw [Submodule.map_sup, Submodule.map_comap_eq_self,
          Submodule.map_comap_eq_self, hPQ.sup_eq_top]
        · rw [LinearMap.range_eq_top.mpr J.mkQ_surjective]
          exact le_top
        · rw [LinearMap.range_eq_top.mpr J.mkQ_surjective]
          exact le_top
      have hJleP' : J ≤ P' := by
        intro x hx
        change J.mkQ x ∈ P
        rw [show J.mkQ x = 0 by
          exact (Submodule.Quotient.mk_eq_zero J).mpr hx]
        exact P.zero_mem
      have hcomap : J ⊔ (P' ⊔ Q') = ⊤ := by
        rw [← Submodule.comap_map_mkQ J (P' ⊔ Q'), hmap,
          Submodule.comap_top]
      rw [sup_eq_right.mpr (hJleP'.trans le_sup_left)] at hcomap
      exact hcomap
    let Pamb : Submodule R M := P'.map E.subtype
    let Qamb : Submodule R M := Q'.map E.subtype
    have hPambLe : Pamb ≤ E := Submodule.map_subtype_le E P'
    have hQambLe : Qamb ≤ E := Submodule.map_subtype_le E Q'
    have hPambProper : Pamb ≠ E := by
      intro hEq
      apply hP'proper
      apply Submodule.map_injective_of_injective E.subtype_injective
      change P'.map E.subtype = E at hEq
      rw [Submodule.map_top, Submodule.range_subtype, hEq]
    have hQambProper : Qamb ≠ E := by
      intro hEq
      apply hQ'proper
      apply Submodule.map_injective_of_injective E.subtype_injective
      change Q'.map E.subtype = E at hEq
      rw [Submodule.map_top, Submodule.range_subtype, hEq]
    have hPambSemi : IsSemisimpleModule R Pamb := by
      by_contra hPnot
      exact hPambProper (hEmin.eq_of_ge hPnot hPambLe).symm
    have hQambSemi : IsSemisimpleModule R Qamb := by
      by_contra hQnot
      exact hQambProper (hEmin.eq_of_ge hQnot hQambLe).symm
    let eP : P' ≃ₗ[R] Pamb :=
      Submodule.equivMapOfInjective E.subtype E.subtype_injective P'
    let eQ : Q' ≃ₗ[R] Qamb :=
      Submodule.equivMapOfInjective E.subtype E.subtype_injective Q'
    letI : IsSemisimpleModule R Pamb := hPambSemi
    letI : IsSemisimpleModule R Qamb := hQambSemi
    letI : IsSemisimpleModule R P' := IsSemisimpleModule.congr eP
    letI : IsSemisimpleModule R Q' := IsSemisimpleModule.congr eQ
    apply hEnot
    exact isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun b : Bool ↦ Bool.rec Q' P' b)
      (by rintro (_ | _) <;> infer_instance)
      (by simpa [iSup_bool_eq] using hP'Q'top)
  have hEind : Foundation.IsIndecomposableModule R E :=
    IsUniserialModule.isIndecomposableModule_of_simpleTop hEtop
  have hEnonsimple : ¬ IsSimpleModule R E := by
    intro hsimple
    letI : IsSimpleModule R E := hsimple
    exact hEnot inferInstance
  exact ⟨E, hEind, hEnonsimple, hEtop⟩

/-- A finite-length nonsemisimple module has a maximal nonsimple
indecomposable submodule.  Maximality is by inclusion among submodules with
those two intrinsic properties. -/
theorem exists_maximal_nonsimple_indecomposable_submodule_of_not_semisimple
    [IsArtinian R M] [IsNoetherian R M]
    (hM : ¬ IsSemisimpleModule R M) :
    ∃ E : Submodule R M,
      Foundation.IsIndecomposableModule R E ∧
        ¬ IsSimpleModule R E ∧
        ∀ F : Submodule R M, E ≤ F →
          Foundation.IsIndecomposableModule R F →
          ¬ IsSimpleModule R F → F = E := by
  let p : Submodule R M → Prop := fun E ↦
    Foundation.IsIndecomposableModule R E ∧
      ¬ IsSimpleModule R E
  obtain ⟨E₀, hE₀ind, hE₀nonsimple⟩ :=
    exists_nonsimple_indecomposable_submodule_of_not_semisimple hM
  obtain ⟨E, -, hEmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT p E₀
      ⟨hE₀ind, hE₀nonsimple⟩
  refine ⟨E, hEmax.1.1, hEmax.1.2, ?_⟩
  intro F hEF hFind hFnonsimple
  exact (hEmax.eq_of_le ⟨hFind, hFnonsimple⟩ hEF).symm

/-- Ambient form of the maximal extraction: a nonsemisimple submodule
contains an ambient submodule maximal among the nonsimple indecomposables
which it contains. -/
theorem exists_maximal_nonsimple_indecomposable_submodule_le_of_not_semisimple
    [IsArtinian R M] [IsNoetherian R M]
    (I : Submodule R M) (hI : ¬ IsSemisimpleModule R I) :
    ∃ E : Submodule R M,
      E ≤ I ∧
        Foundation.IsIndecomposableModule R E ∧
        ¬ IsSimpleModule R E ∧
        ∀ F : Submodule R M, E ≤ F → F ≤ I →
          Foundation.IsIndecomposableModule R F →
          ¬ IsSimpleModule R F → F = E := by
  let p : Submodule R M → Prop := fun E ↦
    E ≤ I ∧ Foundation.IsIndecomposableModule R E ∧
      ¬ IsSimpleModule R E
  obtain ⟨E₀, hE₀ind, hE₀nonsimple⟩ :=
    exists_nonsimple_indecomposable_submodule_of_not_semisimple hI
  let E₁ : Submodule R M := E₀.map I.subtype
  let eE₀ : E₀ ≃ₗ[R] E₁ :=
    Submodule.equivMapOfInjective I.subtype I.subtype_injective E₀
  have hE₁I : E₁ ≤ I := Submodule.map_subtype_le I E₀
  have hE₁ind : Foundation.IsIndecomposableModule R E₁ :=
    hE₀ind.of_linearEquiv eE₀
  have hE₁nonsimple : ¬ IsSimpleModule R E₁ := by
    intro hsimple
    letI : IsSimpleModule R E₁ := hsimple
    exact hE₀nonsimple (IsSimpleModule.congr eE₀)
  obtain ⟨E, -, hEmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT p E₁
      ⟨hE₁I, hE₁ind, hE₁nonsimple⟩
  refine ⟨E, hEmax.1.1, hEmax.1.2.1, hEmax.1.2.2, ?_⟩
  intro F hEF hFI hFind hFnonsimple
  exact (hEmax.eq_of_le ⟨hFI, hFind, hFnonsimple⟩ hEF).symm

end MagnitudeConjecture
