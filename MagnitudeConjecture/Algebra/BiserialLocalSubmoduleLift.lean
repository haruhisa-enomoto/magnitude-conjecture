import MagnitudeConjecture.Algebra.BiserialRadicalTruncation

/-!
# Minimal local lifts of simple quotient submodules

The direct biserial induction lifts two simple summands of
`rad L / rad² L` to local submodules of `rad L`.  Full inverse images need not
be local.  The correct construction chooses a minimal submodule mapping onto
each simple summand; minimality makes the kernel its unique maximal submodule.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture

universe u v w

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A simple submodule in the range of a map has a minimal lift whose top is
canonically that simple module. -/
theorem exists_local_submodule_mapping_onto_simple
    [IsArtinian R M]
    (f : M →ₗ[R] N) (S : Submodule R N)
    (hSsimple : IsSimpleModule R S)
    (hSrange : S ≤ LinearMap.range f) :
    ∃ P : Submodule R M,
      P.map f = S ∧
        IsSimpleModule R (P ⧸ Module.jacobson R P) ∧
        Nonempty ((P ⧸ Module.jacobson R P) ≃ₗ[R] S) := by
  let P₀ : Submodule R M := S.comap f
  have hP₀ : P₀.map f = S := by
    exact Submodule.map_comap_eq_self hSrange
  obtain ⟨P, -, hPmin⟩ :=
    exists_minimal_le_of_wellFoundedLT
      (fun P : Submodule R M ↦ P.map f = S) P₀ hP₀
  have hPmap : P.map f = S := hPmin.1
  let g : P →ₗ[R] S :=
    (f.comp P.subtype).codRestrict S (by
      intro x
      rw [← hPmap]
      exact ⟨x.1, x.2, rfl⟩)
  have hgSurjective : Function.Surjective g := by
    intro s
    have hs : (s : N) ∈ P.map f := hPmap.symm ▸ s.2
    obtain ⟨x, hxP, hfx⟩ := hs
    exact ⟨⟨x, hxP⟩, Subtype.ext hfx⟩
  letI : IsSimpleModule R S := hSsimple
  letI : Nontrivial S := hSsimple.nontrivial
  have hproper_le_ker
      (T : Submodule R P) (hT : T ≠ ⊤) : T ≤ g.ker := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (T.map g) with hbot | htop
    · change T ≤ (⊥ : Submodule R S).comap g
      rw [← Submodule.map_le_iff_le_comap, hbot]
    · exfalso
      have hTPmap : (T.map P.subtype).map f = S := by
        calc
          (T.map P.subtype).map f = T.map (f.comp P.subtype) := by
            exact (Submodule.map_comp P.subtype f T).symm
          _ = T.map (S.subtype.comp g) := by
            congr 1
          _ = (T.map g).map S.subtype := by
            exact Submodule.map_comp g S.subtype T
          _ = S := by
            rw [htop, Submodule.map_top, Submodule.range_subtype]
      have hTPle : T.map P.subtype ≤ P :=
        Submodule.map_subtype_le P T
      have hTPeq : P = T.map P.subtype :=
        hPmin.eq_of_ge hTPmap hTPle
      apply hT
      apply Submodule.map_injective_of_injective P.subtype_injective
      rw [Submodule.map_top, Submodule.range_subtype, ← hTPeq]
  have hkerNeTop : g.ker ≠ ⊤ := by
    intro hker
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    obtain ⟨x, hx⟩ := hgSurjective s
    have hxker : x ∈ g.ker := hker.symm ▸ trivial
    exact hs (by
      rw [← hx]
      exact LinearMap.mem_ker.mp hxker)
  have hjacEq : Module.jacobson R P = g.ker := by
    apply le_antisymm
    · exact IsSemisimpleModule.jacobson_le_ker R R P S g
    · rw [Module.jacobson]
      apply le_sInf
      intro C hC
      have hCle : C ≤ g.ker := hproper_le_ker C hC.1
      exact ((hC.le_iff.mp hCle).resolve_left hkerNeTop).le
  let eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S :=
    (Submodule.quotEquivOfEq _ _ hjacEq).trans
      (g.quotKerEquivOfSurjective hgSurjective)
  refine ⟨P, hPmap, ?_, ⟨eTop⟩⟩
  exact eTop.isSimpleModule_iff.mpr hSsimple

/-- Complementary nonisomorphic simple submodules of the top of a
finite-length module lift to nonisomorphic local submodules which span the
whole module. -/
theorem exists_spanning_local_lifts_of_complementary_simples
    [IsArtinian R M] [IsNoetherian R M]
    (S T : Submodule R (M ⧸ Module.jacobson R M))
    (hSsimple : IsSimpleModule R S)
    (hTsimple : IsSimpleModule R T)
    (hcompl : IsCompl S T)
    (hSTnoniso : ¬ Nonempty (S ≃ₗ[R] T)) :
    ∃ P Q : Submodule R M,
      P ⊔ Q = ⊤ ∧
        IsSimpleModule R (P ⧸ Module.jacobson R P) ∧
        IsSimpleModule R (Q ⧸ Module.jacobson R Q) ∧
        Nonempty ((P ⧸ Module.jacobson R P) ≃ₗ[R] S) ∧
        Nonempty ((Q ⧸ Module.jacobson R Q) ≃ₗ[R] T) ∧
        (¬ Nonempty
          ((P ⧸ Module.jacobson R P) ≃ₗ[R]
            (Q ⧸ Module.jacobson R Q))) ∧
        ¬ Nonempty (P ≃ₗ[R] Q) := by
  let J := Module.jacobson R M
  let q : M →ₗ[R] (M ⧸ J) := J.mkQ
  have hSrange : S ≤ LinearMap.range q := by
    rw [LinearMap.range_eq_top.mpr J.mkQ_surjective]
    exact le_top
  have hTrange : T ≤ LinearMap.range q := by
    rw [LinearMap.range_eq_top.mpr J.mkQ_surjective]
    exact le_top
  obtain ⟨P, hPmap, hPtop, ⟨eP⟩⟩ :=
    exists_local_submodule_mapping_onto_simple q S hSsimple hSrange
  obtain ⟨Q, hQmap, hQtop, ⟨eQ⟩⟩ :=
    exists_local_submodule_mapping_onto_simple q T hTsimple hTrange
  have hmapSup : (P ⊔ Q).map q = ⊤ := by
    rw [Submodule.map_sup, hPmap, hQmap, hcompl.sup_eq_top]
  have hJsup : J ⊔ (P ⊔ Q) = ⊤ :=
    (J.map_mkQ_eq_top (P ⊔ Q)).mp hmapSup
  have hsup : P ⊔ Q = ⊤ := by
    rcases eq_top_or_exists_le_coatom (P ⊔ Q) with htop | ⟨C, hC, hleC⟩
    · exact htop
    · exfalso
      have hJleC : J ≤ C := sInf_le hC
      have htopLe : (⊤ : Submodule R M) ≤ C := by
        rw [← hJsup]
        exact sup_le hJleC hleC
      exact hC.1 (top_unique htopLe)
  have hPQtopNoniso : ¬ Nonempty
      ((P ⧸ Module.jacobson R P) ≃ₗ[R]
        (Q ⧸ Module.jacobson R Q)) := by
    rintro ⟨ePQtop⟩
    apply hSTnoniso
    exact ⟨eP.symm.trans (ePQtop.trans eQ)⟩
  have hPQnoniso : ¬ Nonempty (P ≃ₗ[R] Q) := by
    rintro ⟨ePQ⟩
    exact hPQtopNoniso ⟨moduleTopLinearEquiv ePQ⟩
  exact ⟨P, Q, hsup, hPtop, hQtop, ⟨eP⟩, ⟨eQ⟩,
    hPQtopNoniso, hPQnoniso⟩

end MagnitudeConjecture
